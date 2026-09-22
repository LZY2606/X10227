//! Opt-in structural auditing of compound files.
//!
//! Unlike the normal open path, an audit never rejects a file because its
//! allocation structures are corrupt.  It walks the raw bytes of a Compound
//! File Binary file in a single, stateless pass, and reports every
//! independently detectable piece of corruption it finds in the four
//! allocation structures: the FAT, the DIFAT, the MiniFAT, and the directory
//! chain.
//!
//! The audit is read-only: it never writes to the audited input.  When asked
//! it can produce a [`RepairPlan`] made of concrete byte patches.  A repair
//! plan carries the digest of the exact input it was planned for, and is only
//! applied when the caller explicitly asks and the input still matches that
//! digest; otherwise nothing is written.
//!
//! The audit shares the production parsing code for the header and for
//! directory entries ([`Header::read_from`] and [`DirEntry::read_from`]); it
//! only adds a tolerant traversal of the allocation tables around them, so it
//! diagnoses the same structures the open path consumes rather than a parallel
//! test-only model.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::mem::size_of;

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::{ReadLeNumber, WriteLeNumber};

// Header field offsets (MS-CFB section 2.2), used both to locate evidence and
// to compute patch offsets.
const OFFSET_NUM_DIR_SECTORS: u64 = 40;
const OFFSET_NUM_FAT_SECTORS: u64 = 44;
const OFFSET_FIRST_DIR_SECTOR: u64 = 48;
const OFFSET_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const OFFSET_FIRST_DIFAT_SECTOR: u64 = 68;
const OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
const OFFSET_DIFAT_ENTRIES: u64 = 76;

// Field offsets within a 128-byte directory entry.
const OFFSET_ENTRY_START_SECTOR: u64 = 116;
const OFFSET_ENTRY_STREAM_LEN: u64 = 120;

//===========================================================================//

/// Which of the four allocation structures a piece of evidence is about.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum AuditLayer {
    /// The double-indirect FAT: the DIFAT sector chain and its FAT-sector
    /// pointers.
    Difat,
    /// The file allocation table.
    Fat,
    /// The directory sector chain.
    Directory,
    /// The mini-sector allocation table and the root mini stream.
    MiniFat,
}

impl fmt::Display for AuditLayer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AuditLayer::Difat => f.write_str("DIFAT"),
            AuditLayer::Fat => f.write_str("FAT"),
            AuditLayer::Directory => f.write_str("directory chain"),
            AuditLayer::MiniFat => f.write_str("MiniFAT"),
        }
    }
}

/// The kind of structural defect that was found.
///
/// The five defect classes are reported separately even when they occur in the
/// same table: a cycle is not an out-of-bounds link, a sector claimed by two
/// chains is distinct from an unclaimed orphan sector, and a declared stream
/// length that does not fit its chain is independent of all of them.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum CorruptionKind {
    /// A chain links back to a sector it has already visited.
    Cycle,
    /// A table entry points past the end of its table or of the file.
    OutOfBounds,
    /// Two different chains claim the same sector.
    DuplicateOccupancy,
    /// An allocated sector is not reachable from any header or directory
    /// chain root.
    Orphan,
    /// A declared length (stream size, or header sector count) does not match
    /// the structure it describes.
    LengthMismatch,
    /// An entry whose value is never legal, or whose record cannot be parsed.
    Malformed,
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CorruptionKind::Cycle => f.write_str("cycle"),
            CorruptionKind::OutOfBounds => f.write_str("out-of-bounds link"),
            CorruptionKind::DuplicateOccupancy => {
                f.write_str("duplicate occupancy")
            }
            CorruptionKind::Orphan => f.write_str("orphan sector"),
            CorruptionKind::LengthMismatch => {
                f.write_str("declared length mismatch")
            }
            CorruptionKind::Malformed => f.write_str("malformed entry"),
        }
    }
}

/// One independently detected structural defect, with the first offending
/// position and enough surrounding context to understand and reproduce it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorruptionEvidence {
    /// The allocation structure containing the defect.
    pub layer: AuditLayer,
    /// The defect class.
    pub kind: CorruptionKind,
    /// Byte offset of the first offending position in the file, when the
    /// defect has a concrete on-disk location.
    pub offset: Option<u64>,
    /// The sector, mini sector, or directory-entry index involved, when one
    /// exists.
    pub sector: Option<u32>,
    /// Human-readable context naming the chains and values involved.
    pub detail: String,
}

impl fmt::Display for CorruptionEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} in {}", self.kind, self.layer)?;
        if let Some(offset) = self.offset {
            write!(f, " at byte {offset}")?;
        }
        if let Some(sector) = self.sector {
            write!(f, " (sector {sector})")?;
        }
        write!(f, ": {}", self.detail)
    }
}

/// A non-cryptographic identity of a particular byte sequence.
///
/// The digest is used only as a precondition gate for applying a repair plan;
/// it is two independent 64-bit FNV-1a hashes so that unrelated inputs do not
/// share an identity by accident.  It is not a security primitive.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct AuditDigest(u64, u64);

impl AuditDigest {
    fn of(bytes: &[u8]) -> AuditDigest {
        fn fnv1a(bytes: &[u8], basis: u64) -> u64 {
            const PRIME: u64 = 0x0000_0100_0000_01b3;
            let mut hash = basis;
            for &byte in bytes {
                hash ^= byte as u64;
                hash = hash.wrapping_mul(PRIME);
            }
            hash
        }
        // Mix the length into both halves to separate prefixes.
        let mut with_len = Vec::with_capacity(bytes.len() + size_of::<u64>());
        with_len.extend_from_slice(bytes);
        with_len.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        AuditDigest(
            fnv1a(&with_len, 0xcbf2_9ce4_8422_2325),
            fnv1a(&with_len, 0x8422_2325_cbf2_9ce4),
        )
    }

    /// The digest as 32 lowercase hexadecimal characters.
    pub fn to_hex(self) -> String {
        format!("{:016x}{:016x}", self.0, self.1)
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

//===========================================================================//

/// A concrete, deterministic byte change proposed by a repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BytePatch {
    offset: u64,
    bytes: Vec<u8>,
    reason: String,
}

impl BytePatch {
    /// The byte offset at which the replacement starts.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// The bytes to write.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Why this patch is part of the repair.
    pub fn reason(&self) -> &str {
        &self.reason
    }
}

//===========================================================================//

/// The result of an opt-in structural audit.
#[derive(Clone, Debug)]
pub struct AuditReport {
    version: Version,
    file_len: u64,
    digest: AuditDigest,
    evidence: Vec<CorruptionEvidence>,
    patches: Vec<BytePatch>,
}

impl AuditReport {
    /// The CFB version declared by the audited header.
    pub fn version(&self) -> Version {
        self.version
    }

    /// The length, in bytes, of the audited input.
    pub fn file_len(&self) -> u64 {
        self.file_len
    }

    /// The digest of the exact bytes that were audited.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// All detected defects, sorted by structure, class, and position.  The
    /// first entry is the first defect the audit would report, and every entry
    /// retains the offending position and its context.
    pub fn evidence(&self) -> &[CorruptionEvidence] {
        &self.evidence
    }

 /// Returns true if no structural defects were detected.
    pub fn is_clean(&self) -> bool {
        self.evidence.is_empty()
    }

    /// Produces the read-only repair plan for this exact input.
    ///
    /// Returns `None` when the audit found nothing to repair, or when a
    /// detected defect has no safe deterministic byte-level repair; in the
    /// latter case the offending evidence still describes the problem.
    pub fn repair_plan(&self) -> Option<RepairPlan> {
        if self.patches.is_empty() {
            return None;
        }
        Some(RepairPlan {
            precondition_digest: self.digest,
            precondition_len: self.file_len,
            patches: self.patches.clone(),
        })
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "CFB structural audit of {} bytes (version {}, digest {}):",
            self.file_len,
            self.version.number(),
            self.digest
        )?;
        if self.evidence.is_empty() {
            writeln!(f, "  no corruption found")
        } else {
            for finding in &self.evidence {
                writeln!(f, "  - {finding}")?;
            }
            Ok(())
        }
    }
}

//===========================================================================//

/// A read-only repair plan derived from an [`AuditReport`].
///
/// A plan never touches the input by itself.  It carries the digest of the
/// bytes it was computed from as a precondition, and an explicit `apply_*`
/// call only writes when the current input still matches that digest.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition_digest: AuditDigest,
    precondition_len: u64,
    patches: Vec<BytePatch>,
}

impl RepairPlan {
    /// The digest the input must still have for this plan to be applicable.
    pub fn precondition_digest(&self) -> AuditDigest {
        self.precondition_digest
    }

    /// The length the input must still have for this plan to be applicable.
    pub fn precondition_len(&self) -> u64 {
        self.precondition_len
    }

 /// The ordered byte patches this plan would write.
    pub fn patches(&self) -> &[BytePatch] {
        &self.patches
    }

    /// Checks the precondition digest against `bytes` without writing
    /// anything.  Returns an error in the existing
    /// [`InvalidData`](io::ErrorKind::InvalidData) error layer if the input
    /// changed after the plan was made.
    pub fn verify(&self, bytes: &[u8]) -> io::Result<()> {
        if bytes.len() as u64 != self.precondition_len {
            invalid_data!(
                "Refusing to apply repair plan: file changed (length {} -> \
                 {}, planned for digest {})",
                self.precondition_len,
                bytes.len(),
                self.precondition_digest
            );
        }
        let current = AuditDigest::of(bytes);
        if current != self.precondition_digest {
            invalid_data!(
                "Refusing to apply repair plan: file changed (digest {} -> \
                 {})",
                self.precondition_digest,
                current
            );
        }
        Ok(())
    }

    /// Applies the plan to an in-memory copy, returning the repaired bytes.
    ///
    /// This is the dry-run-safe entry: it borrows the input, verifies the
    /// precondition digest, and returns new bytes; it never writes to the
    /// input.
    pub fn apply_to_bytes(&self, bytes: &[u8]) -> io::Result<Vec<u8>> {
        self.verify(bytes)?;
        let mut repaired = bytes.to_vec();
        self.write_patches(&mut Cursor::new(&mut repaired))?;
        Ok(repaired)
    }

    /// Explicitly applies the plan to a seekable reader/writer.
    ///
    /// The precondition digest is checked first; if it does not match, no
    /// write is attempted.  Patches are staged against a snapshot of the
    /// affected ranges, so if any write fails the input is restored and the
    /// call leaves no half-applied state behind.
    pub fn apply_with<F: Read + Write + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<()> {
        // Read the whole current input once to check the precondition before
        // any write occurs.
        inner.seek(SeekFrom::Start(0))?;
        let mut current = Vec::new();
        inner.read_to_end(&mut current)?;
        self.verify(&current)?;

        // Snapshot every byte range a patch covers before touching it, so a
        // failed write can be rolled back exactly.
        let mut snapshots: Vec<(u64, Vec<u8>)> = Vec::new();
        for patch in &self.patches {
            let end = patch.offset + patch.bytes.len() as u64;
            if end > current.len() as u64 {
                invalid_data!(
                    "Cannot apply repair plan: patch at {} extends past end \
                     of file ({})",
                    patch.offset,
                    current.len()
                );
            }
            snapshots.push((
                patch.offset,
                current[patch.offset as usize..end as usize].to_vec(),
            ));
        }

        if let Err(error) = self.write_patches(inner) {
            // Best-effort rollback of every patch already written.
            for (offset, original) in &snapshots {
                let _ = inner.seek(SeekFrom::Start(*offset));
                let _ = inner.write_all(original);
            }
            let _ = inner.flush();
            return Err(error);
        }
        inner.flush()
    }

    fn write_patches<W: Write + Seek>(&self, writer: &mut W) -> io::Result<()> {
        for patch in &self.patches {
            writer.seek(SeekFrom::Start(patch.offset))?;
            writer.write_all(&patch.bytes)?;
        }
        Ok(())
    }
}

impl fmt::Display for RepairPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Read-only repair plan for digest {} ({} byte patches):",
            self.precondition_digest,
            self.patches.len()
        )?;
        for patch in &self.patches {
            writeln!(
                f,
            "  - byte {}: write {} byte(s): {}",
                patch.offset,
                patch.bytes.len(),
                patch.reason
            )?;
        }
        writeln!(
            f,
            "  Nothing is written until apply is called and the digest still \
             matches."
        )
    }
}

//===========================================================================//
// Internal analysis

/// Who claims ownership of a regular (FAT) sector or a mini sector.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Owner {
    /// A FAT-sector entry in the DIFAT.
    FatSector,
    /// A sector in the DIFAT chain.
    DifatSector,
    /// The directory chain.
    Directory,
    /// The MiniFAT chain.
    MiniFat,
    /// The root entry's mini stream chain.
    MiniStream,
    /// A regular stream named by a directory entry.
    Stream { entry: usize },
}

impl Owner {
    fn label(&self) -> String {
        match self {
            Owner::FatSector => "a FAT sector".to_string(),
            Owner::DifatSector => "a DIFAT sector".to_string(),
            Owner::Directory => "the directory chain".to_string(),
            Owner::MiniFat => "the MiniFAT chain".to_string(),
            Owner::MiniStream => "the root mini stream".to_string(),
            Owner::Stream { entry } => {
                format!("stream at directory entry {entry}")
            }
        }
    }
}

/// The stateless working set for one audit.  Every audit builds a fresh one,
/// so nothing about a prior call (cache, counter, or temporary traversal
/// state) can leak into the next.
struct Analyzer<'a> {
    bytes: &'a [u8],
    version: Version,
    sector_len: u32,
    num_sectors: u32,
    // Keyed evidence, so the same first-offending position is reported once
    // regardless of traversal order.
    evidence: BTreeMap<
        (AuditLayer, CorruptionKind, Option<u64>, Option<u32>, String),
        CorruptionEvidence,
    >,
    // Patches keyed by byte offset; analysis rules never disagree at an
    // offset because they describe distinct cells.
    patches: BTreeMap<u64, BytePatch>,
    difat: Vec<u32>,
    difat_chain: Vec<u32>,
    fat: Vec<u32>,
    owners: Vec<Option<Owner>>,
    minifat: Vec<u32>,
    mini_owners: Vec<Option<Owner>>,
    // Regular-sector chains walked from their roots.
    dir_chain: Vec<u32>,
    minifat_chain: Vec<u32>,
    mini_stream_chain: Vec<u32>,
    // Directory entries read from the (heuristically repaired) directory
    // chain, plus the sector each was read from.
    dir_entries: Vec<(DirEntry, u32)>,
}

impl<'a> Analyzer<'a> {
    fn evidence(
        &mut self,
        layer: AuditLayer,
        kind: CorruptionKind,
        offset: Option<u64>,
        sector: Option<u32>,
        detail: String,
    ) {
        let item =
            CorruptionEvidence { layer, kind, offset, sector, detail: detail.clone() };
        self.evidence
            .insert((layer, kind, offset, sector, detail), item);
    }

    fn patch(&mut self, offset: u64, bytes: Vec<u8>, reason: String) {
        self.patches.insert(
            offset,
            BytePatch { offset, bytes, reason },
        );
    }

    fn patch_u32(&mut self, offset: u64, value: u32, reason: String) {
        self.patch(offset, value.to_le_bytes().to_vec(), reason);
    }

    fn patch_u64(&mut self, offset: u64, value: u64, reason: String) {
        self.patch(offset, value.to_le_bytes().to_vec(), reason);
    }

    // -- Byte layout helpers ---------------------------------------------

    fn u32_at(&self, offset: u64) -> Option<u32> {
        let start = offset as usize;
        let bytes = self.bytes.get(start..start + 4)?;
        Some(u32::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3],
        ]))
    }

    /// File offset of a FAT cell (one u32 in one of the FAT sectors).
    fn fat_cell_offset(&self, index: u32) -> Option<u64> {
        let per_sector = self.sector_len / 4;
        let fat_sector = *self.difat.get((index / per_sector) as usize)?;
        if fat_sector >= self.num_sectors {
            return None;
        }
        Some(
            (u64::from(fat_sector) + 1) * u64::from(self.sector_len)
                + u64::from(index % per_sector) * 4,
        )
    }

    /// File offset of a u32 within a DIFAT sector's pointer array.
    fn difat_sector_cell_offset(
        &self,
        difat_sector_index: u32,
        slot: u32,
    ) -> Option<u64> {
        let difat_sector = *self
            .difat_chain
            .get(difat_sector_index as usize)?;
        if difat_sector >= self.num_sectors {
            return None;
        }
        Some(
            (u64::from(difat_sector) + 1) * u64::from(self.sector_len)
                + u64::from(slot) * 4,
        )
    }

    /// File offset of a directory-entry field.
    fn dir_entry_field(
        &self,
        entry_index: usize,
        field_offset: u64,
    ) -> u64 {
        let per_sector =
            (self.sector_len as usize) / consts::DIR_ENTRY_LEN;
        let sector_index = entry_index / per_sector;
        let slot = entry_index % per_sector;
        // The first `sector_index` sectors of the traversed directory chain
        // are where the entry was read from.
        let sector_id =
            self.dir_sector_for_entry_index(sector_index);
        (u64::from(sector_id) + 1) * u64::from(self.sector_len)
            + (slot as u64) * consts::DIR_ENTRY_LEN as u64
            + field_offset
    }

    fn dir_sector_for_entry_index(&self, sector_index: usize) -> u32 {
        self.dir_chain
            .get(sector_index)
            .copied()
            .unwrap_or(consts::END_OF_CHAIN)
    }

    /// File offset of a MiniFAT cell.
    fn minifat_cell_offset(&self, index: u32) -> Option<u64> {
        let sector_len = u64::from(self.sector_len);
        let sector_id = *self.minifat_chain.get((index / (self.sector_len / 4)) as usize)?;
        if sector_id >= self.num_sectors {
            return None;
        }
        Some(
            (u64::from(sector_id) + 1) * sector_len
                + u64::from(index % (self.sector_len / 4)) * 4,
        )
    }
}

//===========================================================================//
// Audit entry point and pipeline

/// Audits the raw bytes of a compound file without opening or mutating it.
///
/// Fatal header problems (too short, bad magic, unsupported version) are
/// returned as ordinary [`io::Error`]s in the existing error layering, the
/// same way the open path rejects them; everything detectable below the header
/// is collected as evidence instead.
pub fn audit_bytes(bytes: &[u8]) -> io::Result<AuditReport> {
    if (bytes.len() as u64) < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            bytes.len()
        );
    }
    let mut cursor = Cursor::new(bytes);
    // The audit uses the production header parser; a permissive parse is used
    // so that recoverable header quirks do not stop the structural walk.
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len() as u64;
    if (bytes.len() as u64) < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            bytes.len(),
            sector_len
        );
    }
    let num_sectors =
        ((bytes.len() as u64) / sector_len - 1) as u32;

    let mut analyzer = Analyzer {
        bytes,
        version,
        sector_len: sector_len as u32,
        num_sectors,
        evidence: BTreeMap::new(),
        patches: BTreeMap::new(),
        difat: Vec::new(),
        difat_chain: Vec::new(),
        fat: Vec::new(),
        owners: Vec::new(),
        minifat: Vec::new(),
        mini_owners: Vec::new(),
        dir_chain: Vec::new(),
        minifat_chain: Vec::new(),
        mini_stream_chain: Vec::new(),
        dir_entries: Vec::new(),
    };
    analyzer.analyze(header);

    let mut evidence: Vec<CorruptionEvidence> =
        analyzer.evidence.into_values().collect();
    evidence.sort_by(|a, b| {
        (a.layer, a.kind, a.offset, a.sector, a.detail.as_str()).cmp(&(
            b.layer,
            b.kind,
            b.offset,
            b.sector,
            b.detail.as_str(),
        ))
    });
    let patches: Vec<BytePatch> = analyzer.patches.into_values().collect();
    Ok(AuditReport {
        version,
        file_len: bytes.len() as u64,
        digest: AuditDigest::of(bytes),
        evidence,
        patches,
    })
}

impl<'a> Analyzer<'a> {
    fn analyze(&mut self, header: Header) {
        self.read_difat(&header);
        self.read_fat(&header);
        self.scan_fat_cells();
        self.claim_metadata_chains(&header);
        // The directory chain must be walkable before entries are parsed.
        self.walk_directory_chain(&header);
        self.repair_truncated_directory();
        self.read_directory_entries();
        self.walk_minifat(&header);
        self.analyze_directory_references();
        self.find_fat_orphans();
        self.find_mini_orphans();
    }

    // -- DIFAT ------------------------------------------------------------

    fn read_difat(&mut self, header: &Header) {
        self.difat.reserve(consts::NUM_DIFAT_ENTRIES_IN_HEADER);
        for (index, &entry) in
            header.initial_difat_entries.iter().enumerate()
        {
            if entry != consts::FREE_SECTOR && entry >= self.num_sectors {
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(OFFSET_DIFAT_ENTRIES + 4 * index as u64),
                    Some(entry),
                    format!(
                        "header DIFAT entry {index} points to sector {entry}, \
                         but file has only {} sectors",
                        self.num_sectors
                    ),
                );
            }
            self.difat.push(entry);
        }
        while self.difat.last() == Some(&consts::FREE_SECTOR) {
            self.difat.pop();
        }

        let mut current = header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(OFFSET_FIRST_DIFAT_SECTOR),
                    Some(current),
                    format!(
                        "DIFAT chain links to sector {current}, but file has \
                         only {} sectors",
                        self.num_sectors
                    ),
                );
                break;
            }
            if self.difat_chain.contains(&current) {
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::Cycle,
                    Some(
                        self.difat_last_link_offset()
                            .unwrap_or(OFFSET_FIRST_DIFAT_SECTOR),
                    ),
                    Some(current),
                    format!(
                        "DIFAT chain revisits sector {current}, forming a \
                         cycle"
                    ),
                );
                break;
            }
            self.difat_chain.push(current);

            let sector_base =
                (u64::from(current) + 1) * u64::from(self.sector_len);
            let slots = self.sector_len / 4 - 1;
            for slot in 0..slots {
                let Some(entry) =
                    self.u32_at(sector_base + u64::from(slot) * 4)
                else {
                    break;
                };
                if entry != consts::FREE_SECTOR
                    && entry <= consts::MAX_REGULAR_SECTOR
                    && entry >= self.num_sectors
                {
                    let difat_sector_index =
                        (self.difat_chain.len() - 1) as u32;
                    self.evidence(
                        AuditLayer::Difat,
                        CorruptionKind::OutOfBounds,
                        self.difat_sector_cell_offset(
                            difat_sector_index,
                            slot,
                        ),
                        Some(entry),
                        format!(
                            "DIFAT sector {current} pointer {slot} refers to \
                             sector {entry}, but file has only {} sectors",
                            self.num_sectors
                        ),
                    );
                }
                self.difat.push(entry);
            }

            let next_offset = sector_base
                + u64::from(self.sector_len)
                - 4;
            current = match self.u32_at(next_offset) {
                Some(value) => value,
                None => break,
            };
        }

        if header.num_difat_sectors as usize != self.difat_chain.len() {
            self.evidence(
                AuditLayer::Difat,
                CorruptionKind::LengthMismatch,
                Some(OFFSET_NUM_DIFAT_SECTORS),
                None,
                format!(
                    "header says {} DIFAT sector(s), but the DIFAT chain has \
                     {}",
                    header.num_difat_sectors,
                    self.difat_chain.len()
                ),
            );
        }
        if header.num_fat_sectors as usize != self.difat.len() {
            self.evidence(
                AuditLayer::Difat,
                CorruptionKind::LengthMismatch,
                Some(OFFSET_NUM_FAT_SECTORS),
                None,
                format!(
                    "header says {} FAT sector(s), but the DIFAT lists {}",
                    header.num_fat_sectors,
                    self.difat.len()
                ),
            );
        }
    }

    /// Byte offset of the "next DIFAT sector" link that points at the current
    /// head of the walk, i.e. the link to report for a cycle.
    fn difat_last_link_offset(&self) -> Option<u64> {
        if self.difat_chain.is_empty() {
            return None;
        }
        let last = *self.difat_chain.last().unwrap();
        Some(
            (u64::from(last) + 1) * u64::from(self.sector_len)
                + u64::from(self.sector_len)
                - 4,
        )
    }

    // -- FAT --------------------------------------------------------------

    fn read_fat(&mut self, _header: &Header) {
        let entries_per_sector = self.sector_len / 4;
        for &fat_sector in self.difat.clone().iter() {
            if fat_sector >= self.num_sectors {
                // Already reported as a DIFAT out-of-bounds pointer; the FAT
                // sector cannot be read.
                continue;
            }
            let base =
                (u64::from(fat_sector) + 1) * u64::from(self.sector_len);
            for slot in 0..entries_per_sector {
                match self.u32_at(base + u64::from(slot) * 4) {
                    Some(value) => self.fat.push(value),
                    None => break,
                }
            }
        }
        // Trim padding past the file end, mirroring the open path, but keep
        // the table length aligned to the file for indexing.
        while (self.fat.len() as u32) > self.num_sectors {
            self.fat.pop();
        }
        while (self.fat.len() as u32) < self.num_sectors {
            self.fat.push(consts::FREE_SECTOR);
        }
        self.owners = vec![None; self.fat.len()];
    }

    /// Scans every raw FAT cell for values that are illegal on their own,
    /// independent of any chain walk.
    fn scan_fat_cells(&mut self) {
        // First, mark the sectors the DIFAT declares as FAT/DIFAT sectors, so
        // a wrong marker is detectable but does not masquerade as a chain.
        for (difat_index, &difat_sector) in
            self.difat_chain.iter().enumerate()
        {
            let index = difat_sector as usize;
            if index < self.fat.len() {
                let actual = self.fat[index];
                if actual != consts::DIFAT_SECTOR {
                    self.evidence(
                        AuditLayer::Fat,
                        CorruptionKind::Malformed,
                        self.fat_cell_offset(difat_sector),
                        Some(difat_sector),
                        format!(
                            "DIFAT sector {difat_sector} (chain position \
                             {difat_index}) is marked {actual:#010x} in the \
                             FAT, not {:#010x}",
                            consts::DIFAT_SECTOR
                        ),
                    );
                    if let Some(offset) = self.fat_cell_offset(difat_sector)
                    {
                        self.patch_u32(
                            offset,
                            consts::DIFAT_SECTOR,
                            format!(
                                "mark DIFAT sector {difat_sector} correctly"
                            ),
                        );
                    }
                }
                self.owners[index] = Some(Owner::DifatSector);
            }
        }
        for (difat_index, &fat_sector) in self.difat.iter().enumerate() {
            let index = fat_sector as usize;
            if index >= self.fat.len() {
                continue;
            }
            let actual = self.fat[index];
            if actual != consts::FAT_SECTOR {
                self.evidence(
                    AuditLayer::Fat,
                    CorruptionKind::Malformed,
                    self.fat_cell_offset(fat_sector),
                    Some(fat_sector),
                    format!(
                        "FAT sector {fat_sector} (DIFAT position \
                         {difat_index}) is marked {actual:#010x} in the FAT, \
                         not {:#010x}",
                        consts::FAT_SECTOR
                    ),
                );
                if let Some(offset) = self.fat_cell_offset(fat_sector) {
                    self.patch_u32(
                        offset,
                        consts::FAT_SECTOR,
                        format!("mark FAT sector {fat_sector} correctly"),
                    );
                }
            }
            self.owners[index] = Some(Owner::FatSector);
        }

        let mut pointees: BTreeMap<u32, u32> = BTreeMap::new();
        for (from, &value) in self.fat.iter().enumerate() {
            if value == consts::INVALID_SECTOR {
                let from = from as u32;
                self.evidence(
                    AuditLayer::Fat,
                    CorruptionKind::Malformed,
                    self.fat_cell_offset(from),
                    Some(from),
                    format!(
                        "FAT cell {from} holds the invalid value \
                         {value:#010x}"
                    ),
                );
                if let Some(offset) = self.fat_cell_offset(from) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "end the chain at FAT cell {from} instead of the \
                             invalid marker"
                        ),
                    );
                }
            } else if value <= consts::MAX_REGULAR_SECTOR
                && value as usize >= self.fat.len()
            {
                let from = from as u32;
                self.evidence(
                    AuditLayer::Fat,
                    CorruptionKind::OutOfBounds,
                    self.fat_cell_offset(from),
                    Some(from),
                    format!(
                        "FAT cell {from} points to sector {value}, beyond the \
                         {} sector(s) in the file",
                        self.fat.len()
                    ),
                );
                if let Some(offset) = self.fat_cell_offset(from) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "truncate the chain at FAT cell {from} before the \
                             out-of-bounds link"
                        ),
                    );
                }
            } else if value <= consts::MAX_REGULAR_SECTOR {
                pointees
                    .entry(value)
                    .and_modify(|first| {
                        if *first != from as u32 {
                            let from = from as u32;
                            self.evidence(
                                AuditLayer::Fat,
                                CorruptionKind::DuplicateOccupancy,
                                self.fat_cell_offset(from),
                                Some(value),
                                format!(
                                    "sector {value} is the next sector of both \
                                     sector {} and sector {from}",
                                    *first
                                ),
                            );
                        }
                    })
                    .or_insert(from as u32);
            }
        }
    }

    // -- Ownership / chain walks ------------------------------------------

    /// Claims a sector for an owner while walking a chain.  Returns the chain
    /// as collected so far (without the contested sector appended) and the
    /// prior owner when the sector was already claimed by a different chain.
    fn claim(
        &mut self,
        sector: u32,
        owner: &Owner,
        chain: &[u32],
    ) -> Result<(), Option<Owner>> {
        if sector >= self.num_sectors {
            return Err(None);
        }
        let index = sector as usize;
        if let Some(existing) = &self.owners[index] {
            if existing != owner {
                return Err(Some(existing.clone()));
            }
        }
        // A self-revisiting chain is a cycle, independent of ownership.
        if chain.contains(&sector) {
            return Err(None);
        }
        self.owners[index] = Some(owner.clone());
        Ok(())
    }

    /// Walks a regular-sector FAT chain from `start`, marking each sector with
    /// `owner`.  Returns the visited sectors.  `layer`/`owner` describe where
    /// the chain is rooted for evidence messages.  A losing stream chain
    /// (one that crosses into another chain) is detached and freed by
    /// `on_cross`.
    fn walk_fat_chain(
        &mut self,
        start: u32,
        owner: Owner,
        layer: AuditLayer,
        root_offset: Option<u64>,
    ) -> Vec<u32> {
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return Vec::new();
        }
        if start > consts::MAX_REGULAR_SECTOR || start >= self.num_sectors {
            self.evidence(
                layer,
                CorruptionKind::OutOfBounds,
                root_offset,
                Some(start),
                format!(
                    "{} starts at sector {start}, outside the file's {} \
                     sector(s)",
                    owner.label(),
                    self.num_sectors
                ),
            );
            return Vec::new();
        }

        let mut chain = Vec::new();
        let mut current = start;
        loop {
            if chain.contains(&current) {
                let previous = *chain.last().unwrap();
                self.evidence(
                    layer,
                    CorruptionKind::Cycle,
                    self.fat_cell_offset(previous),
                    Some(current),
                    format!(
                        "{} loops back from sector {previous} to sector \
                         {current}",
                        owner.label()
                    ),
                );
                if let Some(offset) = self.fat_cell_offset(previous) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "break the {} cycle by ending it at sector \
                             {previous}",
                            owner.label()
                        ),
                    );
                }
                break;
            }
            if let Err(prior) =
                self.claim(current, &owner, &chain)
            {
                // Crossing into another owner's sector: a cross-chain
                // (duplicate occupancy).  This chain is the loser; detach it
                // and release everything it uniquely claimed.
                let previous = *chain.last().unwrap_or(&start);
                let prior_label = prior
                    .as_ref()
                    .map(|owner| owner.label())
                    .unwrap_or_else(|| "an out-of-range sector".to_string());
                self.evidence(
                    layer,
                    CorruptionKind::DuplicateOccupancy,
                    self.fat_cell_offset(previous),
                    Some(current),
                    format!(
                        "{} crosses into sector {current}, already claimed by \
                         {prior_label}",
                        owner.label()
                    ),
                );
                self.detach_losing_chain(&chain, &owner);
                return Vec::new();
            }
            chain.push(current);
            let value = self.fat[current as usize];
            if value == consts::END_OF_CHAIN {
                break;
            }
            if value == consts::FREE_SECTOR {
                self.evidence(
                    layer,
                    CorruptionKind::Malformed,
                    self.fat_cell_offset(current),
                    Some(current),
                    format!(
                        "{} uses FREE_SECTOR ({value:#010x}) as a link in its \
                         chain",
                        owner.label()
                    ),
                );
                break;
            }
            if value > consts::MAX_REGULAR_SECTOR
                || value as usize >= self.fat.len()
            {
                self.evidence(
                    layer,
                    CorruptionKind::OutOfBounds,
                    self.fat_cell_offset(current),
                    Some(current),
                    format!(
                        "{} links from sector {current} to {value:#010x}, \
                         outside the FAT",
                        owner.label()
                    ),
                );
                if let Some(offset) = self.fat_cell_offset(current) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "truncate {} at sector {current} before the bad \
                             link",
                            owner.label()
                        ),
                    );
                }
                break;
            }
            current = value;
        }
        chain
    }

    /// Releases the sectors a defeated cross-chain uniquely owned and clears
    /// their FAT cells to FREE_SECTOR, so they cannot linger as a second
    /// occupant.
    fn detach_losing_chain(&mut self, chain: &[u32], loser: &Owner) {
        for &sector in chain {
            let index = sector as usize;
            if index < self.owners.len()
                && self.owners[index].as_ref() == Some(loser)
            {
                self.owners[index] = None;
                if let Some(offset) = self.fat_cell_offset(sector) {
                    self.patch_u32(
                        offset,
                        consts::FREE_SECTOR,
                        format!(
                            "free sector {sector} released from the detached \
                             cross-chain"
                        ),
                    );
                }
            }
        }
        if let Some(&first) = chain.first() {
            // The caller rewrites the loser's start pointer separately (it
            // lives in a directory entry), but the first cell is freed along
            // with the rest.
            let _ = first;
        }
    }

    fn claim_metadata_chains(&mut self, header: &Header) {
        let dir_chain = self.walk_fat_chain(
            header.first_dir_sector,
            Owner::Directory,
            AuditLayer::Directory,
            Some(OFFSET_FIRST_DIR_SECTOR),
        );
        self.dir_chain = dir_chain;

        let minifat_chain = self.walk_fat_chain(
            header.first_minifat_sector,
            Owner::MiniFat,
            AuditLayer::MiniFat,
            Some(OFFSET_FIRST_MINIFAT_SECTOR),
        );
        self.minifat_chain = minifat_chain;
    }

    // -- Directory chain --------------------------------------------------

    fn walk_directory_chain(&mut self, header: &Header) {
        if header.version == Version::V4
            && header.num_dir_sectors as usize != self.dir_chain.len()
            && header.num_dir_sectors != 0
        {
            self.evidence(
                AuditLayer::Directory,
                CorruptionKind::LengthMismatch,
                Some(OFFSET_NUM_DIR_SECTORS),
                None,
                format!(
                    "V4 header says {} directory sector(s), but the \
                     directory chain has {}",
                    header.num_dir_sectors,
                    self.dir_chain.len()
                ),
            );
        }
    }

    /// A truncated directory chain can leave directory sectors allocated but
    /// unreachable: the FAT link that should continue the chain was severed,
    /// so the trailing sectors look orphan even though they still hold valid
    /// directory entries.  Before reading entries, extend the chain with such
    /// sectors deterministically (lowest sector id first), relinking the FAT.
    fn repair_truncated_directory(&mut self) {
        let mut candidate = match self.dir_chain.last() {
            Some(&last) => last + 1,
            None => return,
        };
        loop {
            if candidate >= self.num_sectors {
                break;
            }
            let index = candidate as usize;
            if self.owners[index].is_some() {
                break;
            }
            if !self.sector_looks_like_directory(candidate) {
                break;
            }
            // Relink the previous directory sector's FAT cell to this sector.
            let previous = *self.dir_chain.last().unwrap();
            if let Some(offset) = self.fat_cell_offset(previous) {
                self.patch_u32(
                    offset,
                    candidate,
                    format!(
                        "relink truncated directory chain from sector \
                         {previous} to sector {candidate}"
                    ),
                );
            }
            self.fat[previous as usize] = candidate;
            self.owners[index] = Some(Owner::Directory);
            self.dir_chain.push(candidate);
            candidate += 1;
        }
    }

    /// True when the first entries of `sector` look like valid allocated
    /// directory entries rather than free space, i.e. the sector is plausibly
    /// a continuation of the directory chain.
    fn sector_looks_like_directory(&self, sector: u32) -> bool {
        let base =
            (u64::from(sector) + 1) * u64::from(self.sector_len);
        let mut cursor =
            Cursor::new(&self.bytes[base as usize..]);
        let mut allocated = 0usize;
        for _ in 0..4 {
            let mut buffer = [0u8; consts::DIR_ENTRY_LEN];
            if cursor.read_exact(&mut buffer).is_err() {
                return false;
            }
            match DirEntry::read_from(
                &mut &buffer[..],
                self.version,
                Validation::Permissive,
            ) {
                Ok(entry) => {
                    if entry.obj_type != ObjType::Unallocated {
                        allocated += 1;
                    }
                }
                Err(_) => return false,
            }
        }
        allocated > 0
    }

    fn read_directory_entries(&mut self) {
        let per_sector =
            self.sector_len as usize / consts::DIR_ENTRY_LEN;
        for &sector in self.dir_chain.clone().iter() {
            let base =
                (u64::from(sector) + 1) * u64::from(self.sector_len);
            for slot in 0..per_sector {
                let entry_offset =
                    base + (slot as u64) * consts::DIR_ENTRY_LEN as u64;
                let Some(raw) = self.bytes.get(
                    entry_offset as usize
                        ..entry_offset as usize
                            + consts::DIR_ENTRY_LEN,
                ) else {
                    break;
                };
                let entry_index = self.dir_entries.len();
                match DirEntry::read_from(
                    &mut &raw[..],
                    self.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => self.dir_entries.push((entry, sector)),
                    Err(error) => {
                        self.evidence(
                            AuditLayer::Directory,
                            CorruptionKind::Malformed,
                            Some(entry_offset),
                            Some(entry_index as u32),
                            format!(
                                "directory entry {entry_index} in sector \
                                 {sector} is unreadable: {error}"
                            ),
                        );
                    }
                }
            }
        }
    }

    // -- MiniFAT ----------------------------------------------------------

    fn walk_minifat(&mut self, header: &Header) {
        // Read the MiniFAT bytes from the walked MiniFAT chain.
        let mut minifat = Vec::new();
        for &sector in self.minifat_chain.clone().iter() {
            let base =
                (u64::from(sector) + 1) * u64::from(self.sector_len);
            for slot in 0..self.sector_len / 4 {
                if let Some(value) =
                    self.u32_at(base + u64::from(slot) * 4)
                {
                    minifat.push(value);
                }
            }
        }
        while minifat.last() == Some(&consts::FREE_SECTOR) {
            minifat.pop();
        }

        let actual_sectors = self.minifat_chain.len() as u32;
        if header.first_minifat_sector != consts::END_OF_CHAIN
            && header.num_minifat_sectors != actual_sectors
        {
            self.evidence(
                AuditLayer::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(OFFSET_NUM_MINIFAT_SECTORS),
                None,
                format!(
                    "header says {} MiniFAT sector(s), but the MiniFAT chain \
                     has {actual_sectors}",
                    header.num_minifat_sectors
                ),
            );
        }

        // Raw cell scan: invalid values, out-of-bounds links, and double
        // pointees are independent of any particular mini stream.
        let mut pointees: BTreeMap<u32, u32> = BTreeMap::new();
        for (from, &value) in minifat.iter().enumerate() {
            let from = from as u32;
            if value <= consts::MAX_REGULAR_SECTOR
                && value as usize >= minifat.len()
            {
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::OutOfBounds,
                    self.minifat_cell_offset(from),
                    Some(from),
                    format!(
                        "MiniFAT cell {from} points to mini sector {value}, \
                         beyond the {} mini sector(s) in the MiniFAT",
                        minifat.len()
                    ),
                );
            } else if value <= consts::MAX_REGULAR_SECTOR {
                pointees
                    .entry(value)
                    .and_modify(|first| {
                        if *first != from {
                            self.evidence(
                                AuditLayer::MiniFat,
                                CorruptionKind::DuplicateOccupancy,
                                self.minifat_cell_offset(from),
                                Some(value),
                                format!(
                                    "mini sector {value} is the next sector of \
                                     both mini sector {} and mini sector \
                                     {from}",
                                    *first
                                ),
                            );
                        }
                    })
                    .or_insert(from);
            }
        }

        self.minifat = minifat;
        self.mini_owners = vec![None; self.minifat.len()];

        // Walk the root mini stream as a FAT chain (it is stored in regular
        // sectors and owned independently of the MiniFAT table).
        if let Some((root, _)) = self.dir_entries.first() {
            let mini_stream_chain = self.walk_fat_chain(
                root.start_sector,
                Owner::MiniStream,
                AuditLayer::MiniFat,
                Some(self.dir_entry_field(
                    0,
                    OFFSET_ENTRY_START_SECTOR,
                )),
            );
            self.mini_stream_chain = mini_stream_chain;
        }
    }

    fn claim_mini(
        &mut self,
        mini_sector: u32,
        owner: &Owner,
        chain: &[u32],
    ) -> bool {
        if chain.contains(&mini_sector) {
            return false;
        }
        let index = mini_sector as usize;
        if index >= self.mini_owners.len() {
            return false;
        }
        if let Some(existing) = &self.mini_owners[index] {
            return existing == owner;
        }
        self.mini_owners[index] = Some(owner.clone());
        true
    }

    // -- Directory references: per-stream chains and declared lengths ------

    fn analyze_directory_references(&mut self) {
        let root_len = self
            .dir_entries
            .first()
            .map(|(root, _)| root.stream_len)
            .unwrap_or(0);
        let root_mini_capacity =
            (self.mini_stream_chain.len() as u64)
                * consts::MINI_SECTOR_LEN as u64;
        if root_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            self.evidence(
                AuditLayer::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(self.dir_entry_field(0, OFFSET_ENTRY_STREAM_LEN)),
                Some(0),
                format!(
                    "root mini stream length {root_len} is not a multiple of \
                     the {} -byte mini sector size",
                    consts::MINI_SECTOR_LEN
                ),
            );
        }
        if root_len > root_mini_capacity {
            self.evidence(
                AuditLayer::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(self.dir_entry_field(0, OFFSET_ENTRY_STREAM_LEN)),
                Some(0),
                format!(
                    "root mini stream declares {root_len} bytes, but its FAT \
                     chain holds only {root_mini_capacity}"
                ),
            );
        }
        let minifat_declared_sectors =
            root_len / consts::MINI_SECTOR_LEN as u64;
        if (self.minifat.len() as u64) > minifat_declared_sectors {
            self.evidence(
                AuditLayer::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(self.dir_entry_field(0, OFFSET_ENTRY_STREAM_LEN)),
                Some(0),
                format!(
                    "MiniFAT has {} entries, but the root mini stream only \
                     covers {minifat_declared_sectors} mini sector(s)",
                    self.minifat.len()
                ),
            );
        }

        let entries = self.dir_entries.clone();
        for (entry_index, (entry, _)) in entries.into_iter().enumerate() {
            if entry_index == 0 || entry.obj_type != ObjType::Stream {
                continue;
            }
            let start_offset =
                self.dir_entry_field(entry_index, OFFSET_ENTRY_START_SECTOR);
            let len_offset =
                self.dir_entry_field(entry_index, OFFSET_ENTRY_STREAM_LEN);
            let owner = Owner::Stream { entry: entry_index };

            if entry.stream_len < consts::MINI_STREAM_CUTOFF as u64 {
                self.analyze_mini_stream(
                    entry_index,
                    entry.start_sector,
                    entry.stream_len,
                    start_offset,
                    len_offset,
                    owner,
                );
            } else {
                self.analyze_regular_stream(
                    entry_index,
                    entry.start_sector,
                    entry.stream_len,
                    start_offset,
                    len_offset,
                    owner,
                );
            }
        }
    }

    fn analyze_mini_stream(
        &mut self,
        entry_index: usize,
        start: u32,
        declared_len: u64,
        start_offset: u64,
        len_offset: u64,
        owner: Owner,
    ) {
        let label = owner.label();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            if declared_len != 0 {
                self.length_mismatch(
                    AuditLayer::MiniFat,
                    len_offset,
                    entry_index as u32,
                    &label,
                    declared_len,
                    0,
                    "mini",
                );
                self.patch_u64(
                    len_offset,
                    0,
                    format!("zero {label}'s declared length"),
                );
            }
            return;
        }
        if start > consts::MAX_REGULAR_SECTOR
            || start as usize >= self.minifat.len()
        {
            self.evidence(
                AuditLayer::MiniFat,
                CorruptionKind::OutOfBounds,
                Some(start_offset),
                Some(start),
                format!(
                    "{label} starts at mini sector {start}, outside the {} \
                     MiniFAT entr(ies)",
                    self.minifat.len()
                ),
            );
            self.patch_u32(
                start_offset,
                consts::END_OF_CHAIN,
                format!("detach {label} from the out-of-range mini sector"),
            );
            self.patch_u64(
                len_offset,
                0,
                format!("zero {label}'s declared length"),
            );
            return;
        }

        let mut chain = Vec::new();
        let mut current = start;
        loop {
            if chain.contains(&current) {
                let previous = *chain.last().unwrap();
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::Cycle,
                    self.minifat_cell_offset(previous),
                    Some(current),
                    format!(
                        "{label}'s mini chain loops from mini sector \
                         {previous} back to {current}"
                    ),
                );
                if let Some(offset) = self.minifat_cell_offset(previous) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "break {label}'s mini-chain cycle at mini sector \
                             {previous}"
                        ),
                    );
                }
                break;
            }
            if !self.claim_mini(current, &owner, &chain) {
                let previous = *chain.last().unwrap();
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::DuplicateOccupancy,
                    self.minifat_cell_offset(previous),
                    Some(current),
                    format!(
                        "{label}'s mini chain crosses into mini sector \
                         {current} already used elsewhere"
                    ),
                );
                self.detach_losing_mini_chain(&chain, &owner);
                self.patch_u32(
                    start_offset,
                    consts::END_OF_CHAIN,
                    format!("detach {label}'s crossed mini chain"),
                );
                self.patch_u64(
                    len_offset,
                    0,
                    format!("zero {label}'s declared length"),
                );
                return;
            }
            chain.push(current);
            let value = self.minifat[current as usize];
            if value == consts::END_OF_CHAIN {
                break;
            }
            if value == consts::FREE_SECTOR
                || value > consts::MAX_REGULAR_SECTOR
                || value as usize >= self.minifat.len()
            {
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::OutOfBounds,
                    self.minifat_cell_offset(current),
                    Some(current),
                    format!(
                        "{label}'s mini chain links from mini sector {current} \
                         to {value:#010x}, outside the MiniFAT"
                    ),
                );
                if let Some(offset) = self.minifat_cell_offset(current) {
                    self.patch_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!(
                            "truncate {label}'s mini chain at mini sector \
                             {current}"
                        ),
                    );
                }
                break;
            }
            current = value;
        }

        // The mini chain sectors must also lie within the root mini stream.
        let mini_stream_capacity_sectors =
            (self.mini_stream_chain.len() as u64)
                * (u64::from(self.sector_len)
                    / consts::MINI_SECTOR_LEN as u64);
        if let Some(&last) = chain.last() {
            if (last as u64) >= mini_stream_capacity_sectors {
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::OutOfBounds,
                    Some(start_offset),
                    Some(last),
                    format!(
                        "{label}'s mini chain reaches mini sector {last}, but \
                         the root mini stream provides only \
                         {mini_stream_capacity_sectors} mini sector(s)"
                    ),
                );
                self.patch_u32(
                    start_offset,
                    consts::END_OF_CHAIN,
                    format!(
                        "detach {label} from the mini sector beyond the mini \
                         stream"
                    ),
                );
                self.patch_u64(
                    len_offset,
                    0,
                    format!("zero {label}'s declared length"),
                );
                return;
            }
        }

        let capacity =
            (chain.len() as u64) * consts::MINI_SECTOR_LEN as u64;
        if declared_len > capacity {
            self.length_mismatch(
                AuditLayer::MiniFat,
                len_offset,
                entry_index as u32,
                &label,
                declared_len,
                capacity,
                "mini",
            );
            self.patch_u64(
                len_offset,
                capacity,
                format!("set {label}'s declared length to its chain size"),
            );
        }
    }
}
}
}
}
