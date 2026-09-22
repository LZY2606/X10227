use std::collections::BTreeMap;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

use fnv::{FnvHashMap, FnvHashSet};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::{ReadLeNumber, WriteLeNumber};

// ========================================================================= //
// Public report types

/// Which of the CFB allocation structures a piece of corruption evidence
/// concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum AuditTable {
    /// The double-indirect FAT (the chain that locates FAT sectors).
    Difat,
    /// The file allocation table.
    Fat,
    /// The mini-stream allocation table.
    MiniFat,
    /// The directory-entry chain (and the sibling trees of its entries).
    Directory,
}

/// The distinct classes of chain damage.  These are kept separate so that a
/// cycle is never reported as an out-of-bounds pointer, a doubly claimed
/// sector is distinct from an orphan, and so on.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum CorruptionKind {
    /// A chain points back to a sector it has already visited.
    Cycle,
    /// A table entry points past the end of the file or past the table.
    OutOfBounds,
    /// The same sector/mini-sector is claimed by two different owners.
    DuplicateOwner,
    /// A sector/mini-sector that looks allocated is claimed by nobody.
    Orphan,
    /// A declared length (stream byte length, header sector count, chain
    /// length) does not agree with what the tables actually provide.
    LengthMismatch,
}

/// Who owns a claimed sector: one of the well-known tables, a directory-entry
/// chain, or a user stream.
#[derive(Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum ChainOwner {
    /// The FAT sector chain itself.
    FatChain(u32),
    /// A DIFAT sector chain.
    DifatChain,
    /// The directory-entry chain starting at the given sector.
    DirectoryChain,
    /// The MiniFAT sector chain starting at the given sector.
    MiniFatChain,
    /// The root mini stream.
    MiniStream,
    /// A named user stream (directory-entry stream id and name).
    Stream {
        /// Directory-entry stream id of the owning stream.
        id: u32,
        /// Name of the owning stream.
        name: String,
    },
}

/// Evidence for a single corruption finding.  Each variant exposes the first
/// offending location and enough surrounding context to explain the failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evidence {
    /// A chain edge points to a sector the table does not describe.
    OutOfBoundsPointer {
        /// File byte offset of the offending table entry, when known.
        entry_offset: Option<u64>,
        /// Sector or mini-sector holding the offending entry.
        from: u32,
        /// The invalid value the entry points to.
        to: u32,
        /// Number of sectors/entries that actually exist.
        bound: u32,
    },
    /// Following a chain revisits a sector already seen.
    ChainCycle {
        /// File byte offset of the back-edge entry, when known.
        edge_offset: Option<u64>,
        /// First sector revisited by the cycle.
        sector: u32,
        /// The chain of owners involved.
        owners: Vec<ChainOwner>,
    },
    /// One sector is the target of two distinct chain owners.
    SectorClaimedTwice {
        /// Sector or mini-sector that is claimed twice.
        sector: u32,
        /// The owner that already claimed it.
        first_owner: ChainOwner,
        /// The second owner claiming it.
        second_owner: ChainOwner,
    },
    /// A sector/mini-sector is reachable from no known chain root.
    UnclaimedSector {
        /// The orphan sector or mini-sector id.
        sector: u32,
    },
    /// A declared length is inconsistent with the tables.
    DeclaredLengthMismatch {
        /// File byte offset of the offending length field, when known.
        field_offset: Option<u64>,
        /// The declared value.
        declared: u64,
        /// The value implied by the allocation tables.
        actual: u64,
        /// What the length describes.
        what: String,
    },
}

/// A single corruption finding: which structure is damaged, which class of
/// damage it is, where it was first detected, and the supporting evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Corruption {
    pub(crate) table: AuditTable,
    pub(crate) kind: CorruptionKind,
    pub(crate) evidence: Evidence,
}

impl Corruption {
    /// The allocation structure this finding concerns.
    pub fn table(&self) -> AuditTable {
        self.table
    }
    /// The class of damage (cycle, out-of-bounds, etc.).
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }
    /// The evidence for this finding, including the first offending location.
    pub fn evidence(&self) -> &Evidence {
        &self.evidence
    }
}

impl std::fmt::Display for Corruption {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let table = match self.table {
            AuditTable::Difat => "DIFAT",
            AuditTable::Fat => "FAT",
            AuditTable::MiniFat => "MiniFAT",
            AuditTable::Directory => "directory chain",
        };
        match &self.evidence {
            Evidence::OutOfBoundsPointer {
                from,
                to,
                bound,
                entry_offset,
            } => write!(
                f,
                "{table}: sector {from} points to {to} but bound is {bound} (entry at {:?})",
                entry_offset
            ),
            Evidence::ChainCycle {
                sector,
                owners,
                edge_offset,
            } => write!(
                f,
                "{table}: cycle revisits sector {sector} owned by {:?} (edge at {:?})",
                owners, edge_offset
            ),
            Evidence::SectorClaimedTwice {
                sector,
                first_owner,
                second_owner,
            } => write!(
                f,
                "{table}: sector {sector} claimed by {first_owner:?} and {second_owner:?}"
            ),
            Evidence::UnclaimedSector { sector } => {
                write!(f, "{table}: orphan sector {sector}")
            }
            Evidence::DeclaredLengthMismatch {
                declared,
                actual,
                what,
                field_offset,
            } => write!(
                f,
                "{table}: declared {what} is {declared} but tables provide {actual} (field at {:?})",
                field_offset
            ),
        }
    }
}

// ========================================================================= //
// Minimal dependency-free SHA-256, used only to fingerprint the audited
// bytes.  Keeping this local avoids adding a dependency just for a digest.

mod sha256 {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];

    pub struct Sha256 {
        state: [u32; 8],
        buffer: [u8; 64],
        buffer_len: usize,
        total_len: u64,
    }

    impl Sha256 {
        pub fn new() -> Sha256 {
            Sha256 {
                state: [
                    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f,
                    0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
                ],
                buffer: [0; 64],
                buffer_len: 0,
                total_len: 0,
            }
        }

        pub fn update(&mut self, mut data: &[u8]) {
            self.total_len = self.total_len.wrapping_add(data.len() as u64);
            if self.buffer_len > 0 {
                let needed = 64 - self.buffer_len;
                let take = needed.min(data.len());
                self.buffer[self.buffer_len..self.buffer_len + take]
                    .copy_from_slice(&data[..take]);
                self.buffer_len += take;
                data = &data[take..];
                if self.buffer_len == 64 {
                    let block = self.buffer;
                    self.process(&block);
                    self.buffer_len = 0;
                }
            }
            while data.len() >= 64 {
                let mut block = [0u8; 64];
                block.copy_from_slice(&data[..64]);
                self.process(&block);
                data = &data[64..];
            }
            if !data.is_empty() {
                self.buffer[..data.len()].copy_from_slice(data);
                self.buffer_len = data.len();
            }
        }

        pub fn finish(mut self) -> [u8; 32] {
            let bit_len = self.total_len.wrapping_mul(8);
            self.buffer[self.buffer_len] = 0x80;
            for b in &mut self.buffer[self.buffer_len + 1..] {
                *b = 0;
            }
            if self.buffer_len + 1 > 56 {
                let block = self.buffer;
                self.process(&block);
                self.buffer = [0; 64];
            }
            self.buffer[56..64].copy_from_slice(&bit_len.to_be_bytes());
            let block = self.buffer;
            self.process(&block);
            let mut out = [0u8; 32];
            for (i, word) in self.state.iter().enumerate() {
                out[4 * i..4 * i + 4].copy_from_slice(&word.to_be_bytes());
            }
            out
        }

        fn process(&mut self, block: &[u8; 64]) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    block[4 * i],
                    block[4 * i + 1],
                    block[4 * i + 2],
                    block[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7)
                    ^ w[i - 15].rotate_right(18)
                    ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17)
                    ^ w[i - 2].rotate_right(19)
                    ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] =
                self.state;
            for i in 0..64 {
                let s1 =
                    e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ ((!e) & g);
                let temp1 = h
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 =
                    a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let temp2 = s0.wrapping_add(maj);
                h = g;
                g = f;
                f = e;
                e = d.wrapping_add(temp1);
                d = c;
                c = b;
                b = a;
                a = temp1.wrapping_add(temp2);
            }
            self.state[0] = self.state[0].wrapping_add(a);
            self.state[1] = self.state[1].wrapping_add(b);
            self.state[2] = self.state[2].wrapping_add(c);
            self.state[3] = self.state[3].wrapping_add(d);
            self.state[4] = self.state[4].wrapping_add(e);
            self.state[5] = self.state[5].wrapping_add(f);
            self.state[6] = self.state[6].wrapping_add(g);
            self.state[7] = self.state[7].wrapping_add(h);
        }
    }

    pub fn digest(data: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(data);
        hasher.finish()
    }
}

fn hex_digest(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

// ========================================================================= //
// Report and plan types

/// One four-byte word that the repair plan would overwrite.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WordPatch {
    offset: u64,
    old_value: u32,
    new_value: u32,
}

impl WordPatch {
    /// Absolute byte offset of the word within the CFB file.
    pub fn offset(&self) -> u64 {
        self.offset
    }
    /// Value currently at the offset.
    pub fn old_value(&self) -> u32 {
        self.old_value
    }
    /// Value the plan would write.
    pub fn new_value(&self) -> u32 {
        self.new_value
    }
}

/// The result of an opt-in structural audit: corruption evidence for the FAT,
/// DIFAT, MiniFAT and directory chain, plus an optional read-only repair
/// plan.  An audit never mutates its input.
#[derive(Clone, Debug)]
pub struct AuditReport {
    input_len: u64,
    version: Version,
    input_digest: [u8; 32],
    findings: Vec<Corruption>,
    patches: Vec<WordPatch>,
    /// Digest of the bytes after applying `patches`, but only when those
    /// bytes form a file that passes strict validation; otherwise `None`.
    repaired_digest: Option<[u8; 32]>,
}

impl AuditReport {
    /// The CFB version declared by the audited header.
    pub fn version(&self) -> Version {
        self.version
    }
    /// Length in bytes of the audited input.
    pub fn input_len(&self) -> u64 {
        self.input_len
    }
    /// Hex-encoded SHA-256 digest of the audited input bytes.  The repair
    /// plan carries this as its precondition.
    pub fn input_digest(&self) -> String {
        hex_digest(&self.input_digest)
    }
    /// All corruption findings, in a deterministic order.  Each finding
    /// records its first offending location and supporting context.
    pub fn findings(&self) -> &[Corruption] {
        &self.findings
    }
    /// Returns true when no corruption was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
    /// Returns the read-only repair plan, but only when applying it would
    /// yield a file that passes strict CFB validation.  Returns `None` when
    /// the file is already clean, or when the damage cannot be made
    /// consistent solely by the planned word-level changes.
    pub fn repair_plan(&self) -> Option<RepairPlan> {
        let repaired_digest = self.repaired_digest?;
        Some(RepairPlan {
            input_len: self.input_len,
            input_digest: self.input_digest,
            repaired_digest,
            patches: self.patches.clone(),
        })
    }
}

/// A read-only, word-level repair plan bound to a precondition digest of the
/// input bytes.  Construct one via [`AuditReport::repair_plan`].
#[derive(Clone, Debug)]
pub struct RepairPlan {
    input_len: u64,
    input_digest: [u8; 32],
    repaired_digest: [u8; 32],
    patches: Vec<WordPatch>,
}

impl RepairPlan {
    /// Hex digest the input must have for [`RepairPlan::apply`] to proceed.
    pub fn precondition_digest(&self) -> String {
        hex_digest(&self.input_digest)
    }
    /// Hex digest the bytes are expected to have after a successful apply.
    pub fn expected_digest(&self) -> String {
        hex_digest(&self.repaired_digest)
    }
    /// The word changes this plan would make.  This performs no I/O and
    /// never writes.
    pub fn dry_run(&self) -> &[WordPatch] {
        &self.patches
    }
    /// True when the plan changes no bytes (a clean input).
    pub fn is_noop(&self) -> bool {
        self.patches.is_empty()
    }

    /// Applies the plan to `file`, but only while every precondition still
    /// holds: the file length and digest must match those recorded by the
    /// audit, and every patched word must still hold its audited value.
    ///
    /// The write is all-or-nothing: if any write (or the final verification)
    /// fails, every word already written is restored, so on error the file
    /// is byte-for-byte unchanged.  A digest mismatch after the planned
    /// changes also rolls everything back.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        file: &mut F,
    ) -> io::Result<String> {
        let actual_len = file.seek(SeekFrom::End(0))?;
        if actual_len != self.input_len {
            invalid_data!(
                "Refusing to apply repair plan: file length changed since \
                 audit ({} now, {} at audit time)",
                actual_len,
                self.input_len
            );
        }
        let current_digest = hash_seekable(file)?;
        if current_digest != self.input_digest {
            invalid_data!(
                "Refusing to apply repair plan: precondition digest no \
                 longer matches (file changed since audit)"
            );
        }
        // Re-check every word still has its audited value before writing.
        for patch in self.patches.iter() {
            let current = read_u32_at(file, patch.offset)?;
            if current != patch.old_value {
                invalid_data!(
                    "Refusing to apply repair plan: word at offset {} \
                     changed since audit (was 0x{:08X}, now 0x{:08X})",
                    patch.offset,
                    patch.old_value,
                    current
                );
            }
        }

        let mut applied: Vec<(u64, u32)> = Vec::new();
        let outcome = self.write_all(file, &mut applied);
        if let Err(error) = outcome {
            // Best-effort rollback so the input is left exactly as found.
            let _ = rollback(file, &applied);
            return Err(error);
        }
        file.flush()?;
        let final_digest = hash_seekable(file)?;
        if final_digest != self.repaired_digest {
            let _ = rollback(file, &applied);
            invalid_data!(
                "Repair plan applied but post-condition digest did not \
                 match; all changes were rolled back"
            );
        }
        Ok(hex_digest(&final_digest))
    }

    fn write_all<F: Read + Write + Seek>(
        &self,
        file: &mut F,
        applied: &mut Vec<(u64, u32)>,
    ) -> io::Result<()> {
        for patch in self.patches.iter() {
            write_u32_at(file, patch.offset, patch.new_value)?;
            applied.push((patch.offset, patch.old_value));
        }
        Ok(())
    }
}

fn rollback<F: Read + Write + Seek>(
    file: &mut F,
    applied: &[(u64, u32)],
) -> io::Result<()> {
    for &(offset, old_value) in applied.iter().rev() {
        write_u32_at(file, offset, old_value)?;
    }
    file.flush()
}

fn read_u32_at<F: Read + Seek>(file: &mut F, offset: u64) -> io::Result<u32> {
    file.seek(SeekFrom::Start(offset))?;
    file.read_le_u32()
}

fn write_u32_at<F: Write + Seek>(
    file: &mut F,
    offset: u64,
    value: u32,
) -> io::Result<()> {
    file.seek(SeekFrom::Start(offset))?;
    file.write_le_u32(value)
}

fn hash_seekable<F: Read + Seek>(file: &mut F) -> io::Result<[u8; 32]> {
    file.seek(SeekFrom::Start(0))?;
    let mut hasher = sha256::Sha256::new();
    let mut buf = vec![0u8; 16 * 1024];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(hasher.finish())
}

// ========================================================================= //
// Scanner: a read-only analysis that shares the production parsers
// (Header::read_from and DirEntry::read_from) but never gives up after the
// first error; instead it records structured evidence and keeps going.

struct Scanner {
    data: Vec<u8>,
    version: Version,
    sector_len: u64,
    num_sectors: u32,
    header: Header,
    difat: Vec<u32>,
    difat_sector_ids: Vec<u32>,
    dir_sectors: Vec<u32>,
    fat: Vec<u32>,
    /// Fat entry -> byte offset of the word in the file, when it lies inside
    /// the file.
    fat_offsets: Vec<Option<u64>>,
    minifat: Vec<u32>,
    minifat_entry_offsets: Vec<Option<u64>>,
    /// Entries parsed from the reachable directory chain slots.
    entries: Vec<Option<DirEntry>>,
    /// Byte offset of each reachable directory slot.
    entry_offsets: Vec<u64>,
    findings: Vec<Corruption>,
}

impl Scanner {
    fn sector_offset(&self, sector: u32) -> u64 {
        self.sector_len + sector as u64 * self.sector_len
    }

    fn finding(&mut self, table: AuditTable, kind: CorruptionKind, evidence: Evidence) {
        self.findings.push(Corruption { table, kind, evidence });
    }

    /// Walks a FAT chain starting at `start`, bounded by `num_entries`.
    /// `entry_offset(i)` maps a FAT index to the offset of its word.
    /// Records out-of-bounds and cycle findings on `table`, claims sectors
    /// via `claim`, and returns the visited sector ids.
    fn walk_fat_chain(
        &mut self,
        table: AuditTable,
        start: u32,
        owner: ChainOwner,
        claim: &mut FnvHashMap<u32, ChainOwner>,
    ) -> Vec<u32> {
        if start != consts::END_OF_CHAIN && start >= self.fat.len() as u32 {
            self.finding(
                table,
                CorruptionKind::OutOfBounds,
                Evidence::OutOfBoundsPointer {
                    entry_offset: None,
                    from: consts::MAX_REGULAR_SECTOR.wrapping_add(1),
                    to: start,
                    bound: self.fat.len() as u32,
                },
            );
            return Vec::new();
        }
        let mut visited = Vec::new();
        let mut seen = FnvHashSet::default();
        let mut current = start;
        while current != consts::END_OF_CHAIN {
            if !seen.insert(current) {
                let edge_offset = visited
                    .last()
                    .and_then(|&from| *self.fat_offsets.get(from as usize).unwrap_or(&None));
                self.finding(
                    table,
                    CorruptionKind::Cycle,
                    Evidence::ChainCycle {
                        edge_offset,
                        sector: current,
                        owners: vec![owner.clone()],
                    },
                );
                break;
            }
            if let Some(first_owner) = claim.get(&current).cloned() {
                if first_owner != owner {
                    self.finding(
                        AuditTable::Fat,
                        CorruptionKind::DuplicateOwner,
                        Evidence::SectorClaimedTwice {
                            sector: current,
                            first_owner,
                            second_owner: owner.clone(),
                        },
                    );
                }
            } else {
                claim.insert(current, owner.clone());
            }
            visited.push(current);
            let edge = self.fat.get(current as usize).copied();
            match edge {
                Some(next) if next <= consts::MAX_REGULAR_SECTOR => {
                    if next as usize >= self.fat.len() {
                        let entry_offset =
                            *self.fat_offsets.get(current as usize).unwrap_or(&None);
                        self.finding(
                            AuditTable::Fat,
                            CorruptionKind::OutOfBounds,
                            Evidence::OutOfBoundsPointer {
                                entry_offset,
                                from: current,
                                to: next,
                                bound: self.fat.len() as u32,
                            },
                        );
                        break;
                    }
                    current = next;
                }
                Some(consts::END_OF_CHAIN) => break,
                Some(other) => {
                    let entry_offset =
                        *self.fat_offsets.get(current as usize).unwrap_or(&None);
                    if other == consts::INVALID_SECTOR {
                        let bound = self.fat.len() as u32;
                        self.finding(
                            AuditTable::Fat,
                            CorruptionKind::OutOfBounds,
                            Evidence::OutOfBoundsPointer {
                                entry_offset,
                                from: current,
                                to: other,
                                bound,
                            },
                        );
                    }
                    break;
                }
                None => break,
            }
        }
        visited
    }
}

// ========================================================================= //
// The main audit entry point.

/// Audits `reader` without mutating it, returning structured corruption
/// evidence for the FAT, DIFAT, MiniFAT and directory chain.  This is the
/// implementation shared by the public opt-in entry points.
pub(crate) fn audit_structure<F: Read + Seek>(
    mut reader: F,
    validation: Validation,
) -> io::Result<AuditReport> {
    let input_len = reader.seek(SeekFrom::End(0))?;
    reader.seek(SeekFrom::Start(0))?;
    let mut data = Vec::with_capacity(input_len as usize);
    reader.read_to_end(&mut data)?;
    let input_digest = sha256::digest(&data);

    if input_len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small to audit)",
            input_len
        );
    }

    // Parse the header with the same production parser used by open().
    let header = match Header::read_from(&mut Cursor::new(&data), validation) {
        Ok(header) => header,
        Err(error) => return Err(error),
    };
    let version = header.version;
    let sector_len = version.sector_len() as u64;
    let num_sectors = if input_len < sector_len {
        0
    } else {
        (input_len / sector_len - 1) as u32
    };

    let mut scanner = Scanner {
        data,
        version,
        sector_len,
        num_sectors,
        header,
        difat: Vec::new(),
        difat_sector_ids: Vec::new(),
        dir_sectors: Vec::new(),
        fat: Vec::new(),
        fat_offsets: Vec::new(),
        minifat: Vec::new(),
        minifat_entry_offsets: Vec::new(),
        entries: Vec::new(),
        entry_offsets: Vec::new(),
        findings: Vec::new(),
    };
    scanner.scan_difat_and_fat(validation);
    scanner.scan_directory(validation);
    scanner.scan_minifat_and_streams(validation);
    scanner.finalize_findings();

    let findings = scanner.findings.clone();
    let (patches, repaired_digest) = scanner.build_plan(&findings, input_digest);

    Ok(AuditReport {
        input_len,
        version,
        input_digest,
        findings: scanner.findings,
        patches,
        repaired_digest,
    })
}

impl Scanner {
    fn sector_bytes(&self, sector: u32) -> Option<&[u8]> {
        if sector >= self.num_sectors {
            return None;
        }
        let start = self.sector_offset(sector) as usize;
        self.data.get(start..start + self.sector_len as usize)
    }

    fn scan_difat_and_fat(&mut self, _validation: Validation) {
        let entries_per_sector = (self.sector_len / 4) as u32;

        // --- Walk the DIFAT chain itself --------------------------------
        let mut difat: Vec<u32> = Vec::new();
        let mut difat_sector_ids = Vec::new();
        difat.extend(self.header.initial_difat_entries.iter().copied());
        let mut seen_difat = FnvHashSet::default();
        let mut current = self.header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR || current >= self.num_sectors
            {
                self.finding(
                    AuditTable::Difat,
                    CorruptionKind::OutOfBounds,
                    Evidence::OutOfBoundsPointer {
                        entry_offset: Some(68),
                        from: consts::MAX_REGULAR_SECTOR.wrapping_add(1),
                        to: current,
                        bound: self.num_sectors,
                    },
                );
                break;
            }
            if !seen_difat.insert(current) {
                self.finding(
                    AuditTable::Difat,
                    CorruptionKind::Cycle,
                    Evidence::ChainCycle {
                        edge_offset: None,
                        sector: current,
                        owners: vec![ChainOwner::DifatChain],
                    },
                );
                break;
            }
            difat_sector_ids.push(current);
            if let Some(bytes) = self.sector_bytes(current) {
                for i in 0..entries_per_sector - 1 {
                    difat.push(u32::from_le_bytes([
                        bytes[(4 * i) as usize],
                        bytes[(4 * i + 1) as usize],
                        bytes[(4 * i + 2) as usize],
                        bytes[(4 * i + 3) as usize],
                    ]));
                }
                let next = u32::from_le_bytes([
                    bytes[self.sector_len as usize - 4],
                    bytes[self.sector_len as usize - 3],
                    bytes[self.sector_len as usize - 2],
                    bytes[self.sector_len as usize - 1],
                ]);
                current = next;
            } else {
                break;
            }
        }

        if self.header.num_difat_sectors as usize != difat_sector_ids.len()
            && self.header.first_difat_sector != consts::END_OF_CHAIN
        {
            self.finding(
                AuditTable::Difat,
                CorruptionKind::LengthMismatch,
                Evidence::DeclaredLengthMismatch {
                    field_offset: Some(72),
                    declared: self.header.num_difat_sectors as u64,
                    actual: difat_sector_ids.len() as u64,
                    what: "num DIFAT sectors".to_string(),
                },
            );
        }

        // Trim trailing FREE entries; keep the header portion intact (these
        // are FREE by construction in an empty file).
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }

        // --- Read the FAT via the DIFAT, recording entry offsets --------
        let mut fat = vec![consts::FREE_SECTOR; self.num_sectors as usize];
        let mut fat_offsets = vec![None; self.num_sectors as usize];
        let mut seen_fat_sectors = FnvHashSet::default();
        for (difat_index, &fat_sector) in difat.iter().enumerate() {
            if fat_sector == consts::FREE_SECTOR {
                continue;
            }
            if fat_sector > consts::MAX_REGULAR_SECTOR || fat_sector >= self.num_sectors
            {
                self.finding(
                    AuditTable::Difat,
                    CorruptionKind::OutOfBounds,
                    Evidence::OutOfBoundsPointer {
                        entry_offset: difat_entry_offset(
                            self.sector_len,
                            &difat_sector_ids,
                            difat_index,
                        ),
                        from: consts::MAX_REGULAR_SECTOR.wrapping_add(1),
                        to: fat_sector,
                        bound: self.num_sectors,
                    },
                );
                continue;
            }
            if !seen_fat_sectors.insert(fat_sector) {
                self.finding(
                    AuditTable::Difat,
                    CorruptionKind::DuplicateOwner,
                    Evidence::SectorClaimedTwice {
                        sector: fat_sector,
                        first_owner: ChainOwner::FatChain(fat_sector),
                        second_owner: ChainOwner::FatChain(fat_sector),
                    },
                );
                continue;
            }
            if let Some(bytes) = self.sector_bytes(fat_sector) {
                let base = self.sector_offset(fat_sector);
                for i in 0..entries_per_sector {
                    let fat_index = difat_index as u32 * entries_per_sector + i;
                    if fat_index >= self.num_sectors {
                        break;
                    }
                    let value = u32::from_le_bytes([
                        bytes[(4 * i) as usize],
                        bytes[(4 * i + 1) as usize],
                        bytes[(4 * i + 2) as usize],
                        bytes[(4 * i + 3) as usize],
                    ]);
                    fat[fat_index as usize] = value;
                    fat_offsets[fat_index as usize] = Some(base + 4 * i as u64);
                }
            }
        }
        self.fat = fat;
        self.fat_offsets = fat_offsets;
        self.difat = difat.clone();
        self.difat_sector_ids = difat_sector_ids.clone();
        self.scan_fat_edges(difat_sector_ids, &difat);
    }

    fn scan_fat_edges(
        &mut self,
        difat_sector_ids: Vec<u32>,
        difat: &[u32],
    ) {
        let fat: Vec<u32> = self.fat.clone();
        let fat_offsets: Vec<Option<u64>> = self.fat_offsets.clone();
        let mut pointees = FnvHashSet::default();
        for (from, &to) in fat.iter().enumerate() {
            let from = from as u32;
            if to <= consts::MAX_REGULAR_SECTOR {
                if to as usize >= self.fat.len() {
                    self.finding(
                        AuditTable::Fat,
                        CorruptionKind::OutOfBounds,
                        Evidence::OutOfBoundsPointer {
                            entry_offset: self.fat_offsets[from as usize],
                            from,
                            to,
                            bound: self.fat.len() as u32,
                        },
                    );
                    continue;
                }
                if !pointees.insert(to) {
                    self.finding(
                        AuditTable::Fat,
                        CorruptionKind::DuplicateOwner,
                        Evidence::SectorClaimedTwice {
                            sector: to,
                            first_owner: ChainOwner::FatChain(to),
                            second_owner: ChainOwner::FatChain(from),
                        },
                    );
                }
            } else if to == consts::INVALID_SECTOR {
                self.finding(
                    AuditTable::Fat,
                    CorruptionKind::OutOfBounds,
                    Evidence::OutOfBoundsPointer {
                        entry_offset: self.fat_offsets[from as usize],
                        from,
                        to,
                        bound: self.fat.len() as u32,
                    },
                );
            }
        }

        // DIFAT/FAT sectors must be marked as such in the FAT.
        for &difat_sector in difat_sector_ids.iter() {
            if (difat_sector as usize) < fat.len()
                && fat[difat_sector as usize] != consts::DIFAT_SECTOR
            {
                self.finding(
                    AuditTable::Difat,
                    CorruptionKind::LengthMismatch,
                    Evidence::DeclaredLengthMismatch {
                        field_offset: fat_offsets[difat_sector as usize],
                        declared: fat[difat_sector as usize] as u64,
                        actual: consts::DIFAT_SECTOR as u64,
                        what: format!("FAT mark for DIFAT sector {difat_sector}"),
                    },
                );
            }
        }
        for &fat_sector in difat.iter() {
            if fat_sector == consts::FREE_SECTOR
                || fat_sector as usize >= fat.len()
            {
                continue;
            }
            if fat[fat_sector as usize] != consts::FAT_SECTOR {
                self.finding(
                    AuditTable::Fat,
                    CorruptionKind::LengthMismatch,
                    Evidence::DeclaredLengthMismatch {
                        field_offset: fat_offsets[fat_sector as usize],
                        declared: fat[fat_sector as usize] as u64,
                        actual: consts::FAT_SECTOR as u64,
                        what: format!("FAT mark for FAT sector {fat_sector}"),
                    },
                );
            }
        }
    }
}

fn difat_entry_offset(
    sector_len: u64,
    difat_sector_ids: &[u32],
    difat_index: usize,
) -> Option<u64> {
    if difat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
        Some(76 + 4 * difat_index as u64)
    } else {
        let entries_per_sector = (sector_len / 4 - 1) as usize;
        let idx = difat_index - consts::NUM_DIFAT_ENTRIES_IN_HEADER;
        let sector_index = idx / entries_per_sector;
        let within = (idx % entries_per_sector) as u64;
        let sector = *difat_sector_ids.get(sector_index)?;
        Some(sector_len + sector as u64 * sector_len + 4 * within)
    }
}

impl Scanner {
    fn scan_directory(&mut self, validation: Validation) {
        if self.fat.is_empty() {
            return;
        }
        let entries_per_sector =
            (self.version.dir_entries_per_sector()) as u32;

        // Walk the directory chain from the header, collecting slots even if
        // an entry fails to parse.
        let mut claim = FnvHashMap::default();
        let dir_sectors = self.walk_fat_chain(
            AuditTable::Directory,
            self.header.first_dir_sector,
            ChainOwner::DirectoryChain,
            &mut claim,
        );
        self.dir_sectors = dir_sectors.clone();

        let mut slots: Vec<Option<DirEntry>> = Vec::new();
        let mut slot_offsets: Vec<u64> = Vec::new();
        for &sector in dir_sectors.iter() {
            let base = self.sector_offset(sector);
            for slot in 0..entries_per_sector {
                let offset = base + slot as u64 * consts::DIR_ENTRY_LEN as u64;
                slot_offsets.push(offset);
                let raw = match self.data.get(
                    offset as usize..offset as usize
                        + consts::DIR_ENTRY_LEN,
                ) {
                    Some(raw) => raw,
                    None => {
                        self.finding(
                            AuditTable::Directory,
                            CorruptionKind::LengthMismatch,
                            Evidence::DeclaredLengthMismatch {
                                field_offset: Some(offset),
                                declared: offset as u64
                                    + consts::DIR_ENTRY_LEN as u64,
                                actual: self.data.len() as u64,
                                what: "directory chain ends mid-entry"
                                    .to_string(),
                            },
                        );
                        slots.push(None);
                        continue;
                    }
                };
                match DirEntry::read_from(
                    &mut Cursor::new(raw),
                    self.version,
                    validation,
                ) {
                    Ok(entry) => slots.push(Some(entry)),
                    Err(_) => slots.push(None),
                }
            }
        }
        self.entries = slots;
        self.entry_offsets = slot_offsets;

        if self.entries.is_empty()
            || self.entries[0].as_ref().map(|e| e.obj_type)
                != Some(ObjType::Root)
        {
            self.finding(
                AuditTable::Directory,
                CorruptionKind::LengthMismatch,
                Evidence::DeclaredLengthMismatch {
                    field_offset: Some(self.header_offset(48)),
                    declared: self.header.first_dir_sector as u64,
                    actual: consts::END_OF_CHAIN as u64,
                    what: "root directory entry is missing".to_string(),
                },
            );
            return;
        }

        self.audit_directory_tree();
    }

    fn header_offset(&self, offset: u64) -> u64 {
        offset
    }

    /// Checks sibling/child pointers for out-of-range values and cycles, and
    /// finds directory entries that are not reachable from the root tree.
    fn audit_directory_tree(&mut self) {
        let count = self.entries.len();

        // Validate every explicit pointer field of allocated entries.
        let mut pointer_checks: Vec<(u32, u32, u64)> = Vec::new();
        for (id, entry) in self.entries.iter().enumerate() {
            let Some(entry) = entry else { continue };
            if entry.obj_type == ObjType::Unallocated {
                continue;
            }
            let entry_offset = self.entry_offsets[id];
            pointer_checks.push((
                id as u32,
                entry.left_sibling,
                entry_offset + sibling_field_offset("left sibling"),
            ));
            pointer_checks.push((
                id as u32,
                entry.right_sibling,
                entry_offset + sibling_field_offset("right sibling"),
            ));
            pointer_checks.push((
                id as u32,
                entry.child,
                entry_offset + sibling_field_offset("child"),
            ));
        }
        let pointer_checks: Vec<(u32, u32, u64)> = pointer_checks
            .into_iter()
            .filter(|(_, value, _)| *value != consts::NO_STREAM)
            .collect();
        for (id, value, offset) in pointer_checks {
            if value as usize >= count {
                self.finding(
                    AuditTable::Directory,
                    CorruptionKind::OutOfBounds,
                    Evidence::OutOfBoundsPointer {
                        entry_offset: Some(offset),
                        from: id,
                        to: value,
                        bound: count as u32,
                    },
                );
            }
        }

        // Reachability over the sibling/child tree with iterative DFS.  Each
        // frame is (node id, next-neighbor index); a neighbor that is already
        // on the active path closes a cycle.
        let mut reachable: FnvHashSet<u32> = FnvHashSet::default();
        let mut on_path: FnvHashSet<u32> = FnvHashSet::default();
        // (node, neighbor index, node name)
        let mut stack: Vec<(u32, usize, String)> = Vec::new();
        reachable.insert(consts::ROOT_STREAM_ID);
        on_path.insert(consts::ROOT_STREAM_ID);
        stack.push((
            consts::ROOT_STREAM_ID,
            0,
            consts::ROOT_DIR_NAME.to_string(),
        ));
        while let Some((id, next_index, name)) = stack.pop() {
            let Some(entry) = self.entries.get(id as usize).and_then(|e| e.as_ref())
            else {
                on_path.remove(&id);
                continue;
            };
            let neighbors =
                [entry.left_sibling, entry.right_sibling, entry.child];
            if next_index >= neighbors.len() {
                on_path.remove(&id);
                continue;
            }
            // Re-push this node with the advanced cursor.
            stack.push((id, next_index + 1, name.clone()));
            let neighbor = neighbors[next_index];
            if neighbor == consts::NO_STREAM || neighbor as usize >= count {
                continue;
            }
            if on_path.contains(&neighbor) {
                let what = if next_index == 0 {
                    "left sibling"
                } else if next_index == 1 {
                    "right sibling"
                } else {
                    "child"
                };
                self.finding(
                    AuditTable::Directory,
                    CorruptionKind::Cycle,
                    Evidence::ChainCycle {
                        edge_offset: Some(
                            self.entry_offsets[id as usize]
                                + sibling_field_offset(what),
                        ),
                        sector: neighbor,
                        owners: vec![ChainOwner::Stream {
                            id,
                            name: name.clone(),
                        }],
                    },
                );
                continue;
            }
            if !reachable.insert(neighbor) {
                continue;
            }
            on_path.insert(neighbor);
            stack.push((neighbor, 0, neighbor_name(self, neighbor)));
        }

        // Orphan (unreachable) allocated directory entries.
        let orphan_ids: Vec<u32> = self
            .entries
            .iter()
            .enumerate()
            .filter(|(id, entry)| {
                *id as u32 != consts::ROOT_STREAM_ID
                    && entry.as_ref().map(|e| e.obj_type)
                        != Some(ObjType::Unallocated)
                    && !reachable.contains(&(*id as u32))
            })
            .map(|(id, _)| id as u32)
            .collect();
        for orphan_id in orphan_ids {
            self.finding(
                AuditTable::Directory,
                CorruptionKind::Orphan,
                Evidence::UnclaimedSector { sector: orphan_id },
            );
        }
    }
}

fn sibling_field_offset(what: &str) -> u64 {
    match what {
        "left sibling" => 68,
        "right sibling" => 72,
        _ => 76, // child
    }
}

fn neighbor_name(scanner: &Scanner, id: u32) -> String {
    scanner
        .entries
        .get(id as usize)
        .and_then(|entry| entry.as_ref())
        .map(|entry| entry.name.clone())
        .unwrap_or_default()
}

impl Scanner {
    fn scan_minifat_and_streams(&mut self, _validation: Validation) {
        if self.entries.is_empty() {
            return;
        }
        let entries_per_sector = (self.sector_len / 4) as u32;

        // Ownership of regular sectors, seeded deterministically with the
        // metadata chains so that a stream sharing a metadata sector is the
        // "second" claimant.
        let mut fat_claim: FnvHashMap<u32, ChainOwner> = FnvHashMap::default();
        for &fat_sector in self.difat.iter() {
            if fat_sector != consts::FREE_SECTOR && fat_sector < self.num_sectors
            {
                fat_claim.insert(fat_sector, ChainOwner::FatChain(fat_sector));
            }
        }
        for &difat_sector in self.difat_sector_ids.iter() {
            fat_claim.insert(difat_sector, ChainOwner::DifatChain);
        }
        for &dir_sector in self.dir_sectors.iter() {
            fat_claim.insert(dir_sector, ChainOwner::DirectoryChain);
        }

        // --- MiniFAT chain (regular sectors) ----------------------------
        let minifat_sectors = self.walk_fat_chain(
            AuditTable::MiniFat,
            self.header.first_minifat_sector,
            ChainOwner::MiniFatChain,
            &mut fat_claim,
        );

        // Only as many sectors as the header declares hold MiniFAT data;
        // if the chain itself is longer (e.g. cross-linked into another
        // chain), the extra sectors are not MiniFAT and must not be parsed.
        let declared_minifat_sectors =
            self.header.num_minifat_sectors.max(1) as usize;
        let minifat_sectors_to_read =
            &minifat_sectors[..minifat_sectors.len().min(declared_minifat_sectors)];

        // Read the MiniFAT entries.
        let mut minifat = Vec::new();
        let mut minifat_offsets = Vec::new();
        for &sector in minifat_sectors_to_read.iter() {
            let base = self.sector_offset(sector);
            if let Some(bytes) = self.sector_bytes(sector) {
                for i in 0..entries_per_sector {
                    let value = u32::from_le_bytes([
                        bytes[(4 * i) as usize],
                        bytes[(4 * i + 1) as usize],
                        bytes[(4 * i + 2) as usize],
                        bytes[(4 * i + 3) as usize],
                    ]);
                    minifat.push(value);
                    minifat_offsets.push(Some(base + 4 * i as u64));
                }
            }
        }
        // Trim trailing FREE entries, mirroring the production open path;
        // a final MiniFAT sector is padded with FREE mini sectors.
        while minifat.last() == Some(&consts::FREE_SECTOR) {
            minifat.pop();
            minifat_offsets.pop();
        }
        self.minifat = minifat;
        self.minifat_entry_offsets = minifat_offsets;
        self.scan_minifat_edges();

        // --- Root mini stream chain (regular sectors) -------------------
        let root = self.entries[0].clone();
        let root = match root {
            Some(root) if root.obj_type == ObjType::Root => root,
            _ => return,
        };
        if root.stream_len > 0 {
            self.walk_fat_chain(
                AuditTable::MiniFat,
                root.start_sector,
                ChainOwner::MiniStream,
                &mut fat_claim,
            );
        }

        // MiniFAT must not be longer than the root mini stream.
        let mini_capacity_sectors =
            root.stream_len / consts::MINI_SECTOR_LEN as u64;
        if self.minifat.len() as u64 > mini_capacity_sectors {
            self.finding(
                AuditTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Evidence::DeclaredLengthMismatch {
                    field_offset: Some(116),
                    declared: self.minifat.len() as u64,
                    actual: mini_capacity_sectors,
                    what: "MiniFAT entries vs root mini stream length"
                        .to_string(),
                },
            );
        }

        // Header num_minifat_sectors check.
        if self.header.first_minifat_sector != consts::END_OF_CHAIN
            && self.header.num_minifat_sectors as usize
                != minifat_sectors.len()
        {
            self.finding(
                AuditTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Evidence::DeclaredLengthMismatch {
                    field_offset: Some(64),
                    declared: self.header.num_minifat_sectors as u64,
                    actual: minifat_sectors.len() as u64,
                    what: "num MiniFAT sectors".to_string(),
                },
            );
        }

        // --- User streams ------------------------------------------------
        self.scan_stream_chains(&mut fat_claim);

        // --- Orphan regular sectors -------------------------------------
        let fat: Vec<u32> = self.fat.clone();
        for sector in 0..self.num_sectors {
            let entry = fat
                .get(sector as usize)
                .copied()
                .unwrap_or(consts::FREE_SECTOR);
            let looks_allocated = entry != consts::FREE_SECTOR;
            if looks_allocated && !fat_claim.contains_key(&sector) {
                self.finding(
                    AuditTable::Fat,
                    CorruptionKind::Orphan,
                    Evidence::UnclaimedSector { sector },
                );
            }
        }

        // --- Mini streams and orphan mini sectors ------------------------
        self.scan_mini_chains();
    }

    fn scan_minifat_edges(&mut self) {
        let minifat: Vec<u32> = self.minifat.clone();
        let minifat_offsets: Vec<Option<u64>> =
            self.minifat_entry_offsets.clone();
        let mut pointees = FnvHashSet::default();
        for (from, &to) in minifat.iter().enumerate() {
            let from = from as u32;
            if to <= consts::MAX_REGULAR_SECTOR {
                if to as usize >= minifat.len() {
                    self.finding(
                        AuditTable::MiniFat,
                        CorruptionKind::OutOfBounds,
                        Evidence::OutOfBoundsPointer {
                            entry_offset: minifat_offsets[from as usize],
                            from,
                            to,
                            bound: minifat.len() as u32,
                        },
                    );
                    continue;
                }
                if !pointees.insert(to) {
                    self.finding(
                        AuditTable::MiniFat,
                        CorruptionKind::DuplicateOwner,
                        Evidence::SectorClaimedTwice {
                            sector: to,
                            first_owner: ChainOwner::Stream {
                                id: from,
                                name: format!("mini sector {from}"),
                            },
                            second_owner: ChainOwner::Stream {
                                id: to,
                                name: format!("mini sector {to}"),
                            },
                        },
                    );
                }
            }
        }
    }

    fn scan_stream_chains(
        &mut self,
        fat_claim: &mut FnvHashMap<u32, ChainOwner>,
    ) {
        let sector_len = self.sector_len;
        let entries: Vec<(usize, DirEntry)> = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(id, entry)| entry.clone().map(|entry| (id, entry)))
            .filter(|(_, entry)| entry.obj_type == ObjType::Stream)
            .collect();
        for (id, entry) in entries {
            let owner = ChainOwner::Stream {
                id: id as u32,
                name: entry.name.clone(),
            };
            if entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64 {
                let chain = if entry.start_sector == consts::END_OF_CHAIN {
                    Vec::new()
                } else {
                    self.walk_fat_chain(
                        AuditTable::Fat,
                        entry.start_sector,
                        owner,
                        fat_claim,
                    )
                };
                let capacity = chain.len() as u64 * sector_len;
                if entry.stream_len > capacity {
                    self.finding(
                        AuditTable::Fat,
                        CorruptionKind::LengthMismatch,
                        Evidence::DeclaredLengthMismatch {
                            field_offset: Some(self.entry_offsets[id] + 120),
                            declared: entry.stream_len,
                            actual: capacity,
                            what: format!(
                                "stream {:?} length vs FAT chain",
                                entry.name
                            ),
                        },
                    );
                }
            }
        }
    }

    /// Walks every mini stream's chain once, emitting cycle/out-of-bounds and
    /// length-mismatch findings, claiming mini sectors, then reports any mini
    /// sectors that no stream owns.
    fn scan_mini_chains(&mut self) {
        let mini_len = consts::MINI_SECTOR_LEN as u64;
        let mut mini_claim: FnvHashMap<u32, ChainOwner> = FnvHashMap::default();
        let entries: Vec<(usize, DirEntry)> = self
            .entries
            .iter()
            .enumerate()
            .filter_map(|(id, entry)| entry.clone().map(|entry| (id, entry)))
            .filter(|(_, entry)| {
                entry.obj_type == ObjType::Stream
                    && entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
            })
            .collect();
        for (id, entry) in entries {
            let owner = ChainOwner::Stream {
                id: id as u32,
                name: entry.name.clone(),
            };
            let start_offset = self.entry_offsets[id] + 116;
            let chain = self.walk_mini_chain(
                entry.start_sector,
                owner,
                &mut mini_claim,
                Some(start_offset),
            );
            if entry.stream_len > 0 {
                let capacity = chain.len() as u64 * mini_len;
                if entry.stream_len > capacity {
                    self.finding(
                        AuditTable::MiniFat,
                        CorruptionKind::LengthMismatch,
                        Evidence::DeclaredLengthMismatch {
                            field_offset: Some(self.entry_offsets[id] + 120),
                            declared: entry.stream_len,
                            actual: capacity,
                            what: format!(
                                "stream {:?} length vs MiniFAT chain",
                                entry.name
                            ),
                        },
                    );
                }
            }
        }
        let minifat: Vec<u32> = self.minifat.clone();
        for mini in 0..minifat.len() as u32 {
            if minifat[mini as usize] != consts::FREE_SECTOR
                && !mini_claim.contains_key(&mini)
            {
                self.finding(
                    AuditTable::MiniFat,
                    CorruptionKind::Orphan,
                    Evidence::UnclaimedSector { sector: mini },
                );
            }
        }
    }

    fn walk_mini_chain(
        &mut self,
        start: u32,
        owner: ChainOwner,
        claim: &mut FnvHashMap<u32, ChainOwner>,
        start_offset: Option<u64>,
    ) -> Vec<u32> {
        let mut visited = Vec::new();
        if start == consts::END_OF_CHAIN {
            return visited;
        }
        if start as usize >= self.minifat.len() {
            self.finding(
                AuditTable::MiniFat,
                CorruptionKind::OutOfBounds,
                Evidence::OutOfBoundsPointer {
                    entry_offset: start_offset,
                    from: consts::MAX_REGULAR_SECTOR.wrapping_add(1),
                    to: start,
                    bound: self.minifat.len() as u32,
                },
            );
            return visited;
        }
        let mut seen = FnvHashSet::default();
        let mut current = start;
        while current != consts::END_OF_CHAIN {
            if !seen.insert(current) {
                let edge_offset = visited
                    .last()
                    .and_then(|&from| self.minifat_entry_offsets.get(from as usize).copied().flatten());
                self.finding(
                    AuditTable::MiniFat,
                    CorruptionKind::Cycle,
                    Evidence::ChainCycle {
                        edge_offset,
                        sector: current,
                        owners: vec![owner.clone()],
                    },
                );
                break;
            }
            if let Some(first_owner) = claim.get(&current).cloned() {
                if first_owner != owner {
                    self.finding(
                        AuditTable::MiniFat,
                        CorruptionKind::DuplicateOwner,
                        Evidence::SectorClaimedTwice {
                            sector: current,
                            first_owner,
                            second_owner: owner.clone(),
                        },
                    );
                }
            } else {
                claim.insert(current, owner.clone());
            }
            visited.push(current);
            match self.minifat.get(current as usize).copied() {
                Some(next) if next <= consts::MAX_REGULAR_SECTOR => {
                    if next as usize >= self.minifat.len() {
                        self.finding(
                            AuditTable::MiniFat,
                            CorruptionKind::OutOfBounds,
                            Evidence::OutOfBoundsPointer {
                                entry_offset: self.minifat_entry_offsets
                                    [current as usize],
                                from: current,
                                to: next,
                                bound: self.minifat.len() as u32,
                            },
                        );
                        break;
                    }
                    current = next;
                }
                Some(consts::END_OF_CHAIN) => break,
                _ => break,
            }
        }
        visited
    }
}

impl Scanner {
    /// Sorts findings into a stable order so that re-running the audit with a
    /// different visitation order or cache state yields the same report.
    fn finalize_findings(&mut self) {
        self.findings.sort_by(|a, b| {
            finding_sort_key(a).cmp(&finding_sort_key(b))
        });
        self.findings.dedup();
    }

    /// Derives the deterministic word-level repair plan, then verifies (using
    /// the production open path) that the repaired bytes pass strict
    /// validation.  Never mutates the audited input.
    fn build_plan(
        &self,
        findings: &[Corruption],
        input_digest: [u8; 32],
    ) -> (Vec<WordPatch>, Option<[u8; 32]>) {
        if findings.is_empty() {
            return (Vec::new(), Some(input_digest));
        }
        let mut patches: BTreeMap<u64, WordPatch> = BTreeMap::new();
        for finding in findings {
            for patch in self.patches_for(finding) {
                patches
                    .entry(patch.offset)
                    .or_insert(patch);
            }
        }
        let patches: Vec<WordPatch> = patches.into_values().collect();

        let mut repaired = self.data.clone();
        for patch in patches.iter() {
            let offset = patch.offset as usize;
            if offset + 4 > repaired.len()
                || u32::from_le_bytes([
                    repaired[offset],
                    repaired[offset + 1],
                    repaired[offset + 2],
                    repaired[offset + 3],
                ]) != patch.old_value
            {
                return (patches, None);
            }
            repaired[offset..offset + 4]
                .copy_from_slice(&patch.new_value.to_le_bytes());
        }
        let repaired_digest = sha256::digest(&repaired);
        // The same production entry point users have must accept the result
        // under Strict validation.
        match crate::CompoundFile::open_strict(Cursor::new(repaired)) {
            Ok(comp) => {
                drop(comp);
                (patches, Some(repaired_digest))
            }
            Err(_) => (patches, None),
        }
    }

    fn patches_for(&self, finding: &Corruption) -> Vec<WordPatch> {
        let eoc = consts::END_OF_CHAIN.to_le_bytes();
        let _ = eoc;
        match &finding.evidence {
            Evidence::OutOfBoundsPointer {
                entry_offset: Some(offset),
                ..
            } => self.replace_word(*offset, consts::END_OF_CHAIN),
            Evidence::ChainCycle {
                edge_offset: Some(offset),
                ..
            } => self.replace_word(*offset, consts::END_OF_CHAIN),
            Evidence::UnclaimedSector { sector } => {
                // Orphan FAT regular sector: mark it FREE in the FAT.
                if finding.table == AuditTable::Fat {
                    if let Some(Some(offset)) =
                        self.fat_offsets.get(*sector as usize)
                    {
                        return self.replace_word(*offset, consts::FREE_SECTOR);
                    }
                } else if finding.table == AuditTable::MiniFat {
                    if let Some(Some(offset)) = self
                        .minifat_entry_offsets
                        .get(*sector as usize)
                    {
                        return self.replace_word(*offset, consts::FREE_SECTOR);
                    }
                }
                Vec::new()
            }
            Evidence::SectorClaimedTwice {
                sector,
                second_owner,
                ..
            } => {
                // Detach the second owner's back-edge so the shared sector is
                // owned only by the first claimant.
                match second_owner {
                    ChainOwner::Stream { id, .. } => {
                        let entry_offset = match finding.table {
                            AuditTable::MiniFat => {
                                self.entry_offsets.get(*id as usize).copied()
                                    .map(|off| off + 116)
                            }
                            _ => self.entry_offsets.get(*id as usize).copied()
                                .map(|off| off + 116),
                        };
                        if let Some(offset) = entry_offset {
                            self.replace_word(offset, consts::END_OF_CHAIN)
                        } else {
                            Vec::new()
                        }
                    }
                    _ => {
                        if let Some(Some(offset)) =
                            self.fat_offsets.get(*sector as usize)
                        {
                            self.replace_word(*offset, consts::END_OF_CHAIN)
                        } else {
                            Vec::new()
                        }
                    }
                }
            }
            Evidence::DeclaredLengthMismatch {
                field_offset: Some(offset),
                actual,
                what,
                ..
            } => {
                if what.starts_with("stream ") {
                    let declared_len = finding_declared(finding);
                    let _ = declared_len;
                    // Shrink the stream's declared length to the capacity the
                    // tables actually provide (stored in `actual`).
                    self.replace_u64_word(*offset, *actual)
                } else if what.contains("FAT mark") {
                    let expected = if what.contains("DIFAT") {
                        consts::DIFAT_SECTOR
                    } else {
                        consts::FAT_SECTOR
                    };
                    self.replace_word(*offset, expected)
                } else {
                    // Header count mismatches and other structural length
                    // discrepancies are not safely repairable by a single word.
                    Vec::new()
                }
            }
            _ => Vec::new(),
        }
    }

    fn replace_word(&self, offset: u64, new_value: u32) -> Vec<WordPatch> {
        let offset = offset as usize;
        if let Some(bytes) = self.data.get(offset..offset + 4) {
            let old_value = u32::from_le_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3],
            ]);
            if old_value != new_value {
                return vec![WordPatch {
                    offset: offset as u64,
                    old_value,
                    new_value,
                }];
            }
        }
        Vec::new()
    }

    fn replace_u64_word(&self, offset: u64, new_value: u64) -> Vec<WordPatch> {
        let offset = offset as usize;
        if offset + 8 > self.data.len() {
            return Vec::new();
        }
        let old_value = u64::from_le_bytes([
            self.data[offset],
            self.data[offset + 1],
            self.data[offset + 2],
            self.data[offset + 3],
            self.data[offset + 4],
            self.data[offset + 5],
            self.data[offset + 6],
            self.data[offset + 7],
        ]);
        if old_value == new_value {
            return Vec::new();
        }
        let new_bytes = new_value.to_le_bytes();
        let mut patches = Vec::new();
        for word_index in 0..2 {
            let word_offset = offset + 4 * word_index;
            let old_word = u32::from_le_bytes([
                self.data[word_offset],
                self.data[word_offset + 1],
                self.data[word_offset + 2],
                self.data[word_offset + 3],
            ]);
            let new_word = u32::from_le_bytes([
                new_bytes[4 * word_index],
                new_bytes[4 * word_index + 1],
                new_bytes[4 * word_index + 2],
                new_bytes[4 * word_index + 3],
            ]);
            if old_word != new_word {
                patches.push(WordPatch {
                    offset: word_offset as u64,
                    old_value: old_word,
                    new_value: new_word,
                });
            }
        }
        patches
    }
}

fn finding_declared(finding: &Corruption) -> u64 {
    match &finding.evidence {
        Evidence::DeclaredLengthMismatch { declared, .. } => *declared,
        _ => 0,
    }
}

fn finding_sort_key(
    finding: &Corruption,
) -> (u8, u8, u64, u32, String) {
    let table = match finding.table {
        AuditTable::Difat => 0,
        AuditTable::Fat => 1,
        AuditTable::MiniFat => 2,
        AuditTable::Directory => 3,
    };
    let kind = match finding.kind {
        CorruptionKind::OutOfBounds => 0,
        CorruptionKind::Cycle => 1,
        CorruptionKind::DuplicateOwner => 2,
        CorruptionKind::LengthMismatch => 3,
        CorruptionKind::Orphan => 4,
    };
    let (offset, sector, detail) = match &finding.evidence {
        Evidence::OutOfBoundsPointer {
            entry_offset,
            from,
            to,
            ..
        } => (entry_offset.unwrap_or(u64::MAX), *from, format!("to {to}")),
        Evidence::ChainCycle {
            edge_offset,
            sector,
            ..
        } => (edge_offset.unwrap_or(u64::MAX), *sector, String::new()),
        Evidence::SectorClaimedTwice {
            sector,
            second_owner,
            ..
        } => (u64::MAX, *sector, format!("{second_owner:?}")),
        Evidence::UnclaimedSector { sector } => {
            (u64::MAX, *sector, String::new())
        }
        Evidence::DeclaredLengthMismatch {
            field_offset,
            what,
            ..
        } => (field_offset.unwrap_or(u64::MAX), 0, what.clone()),
    };
    (table, kind, offset, sector, detail)
}

// ========================================================================= //
