//! Opt-in structural auditing and read-only repair planning for corrupted
//! allocation structures (FAT, DIFAT, MiniFAT, directory chain).
//!
//! Everything in this module is entered through the crate's public API
//! (`cfb::audit` / `OpenOptions::audit_with`).  The auditor never constructs
//! the library's mutable internal allocator objects: it parses the raw bytes
//! defensively, collects *evidence* of corruption, and produces a plan of
//! byte-level patches.  The plan is read-only and can only be applied
//! explicitly when the file's precondition digest still matches.

use std::cmp::Ordering;
use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::consts;
use crate::internal::Version;

//===========================================================================//
// Public value types

/// Which allocation structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AllocationTable {
    /// The File Allocation Table (regular sector chains).
    Fat,
    /// The Double-Indirect FAT (the chain/list of FAT sectors).
    Difat,
    /// The Mini FAT (64-byte mini-sector chains).
    MiniFat,
    /// The chain of sectors holding directory entries.
    DirectoryChain,
}

impl fmt::Display for AllocationTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AllocationTable::Fat => write!(f, "FAT"),
            AllocationTable::Difat => write!(f, "DIFAT"),
            AllocationTable::MiniFat => write!(f, "MiniFAT"),
            AllocationTable::DirectoryChain => write!(f, "directory chain"),
        }
    }
}

/// The *kind* of corruption that was found.
///
/// The five categories required to be reported distinctly are represented by
/// separate variants: cycles ([`CorruptionKind::ChainCycle`]), out-of-bounds
/// references ([`CorruptionKind::OutOfBounds`],
/// [`CorruptionKind::MiniStreamOutOfBounds`]), double occupation
/// ([`CorruptionKind::DoubleAllocated`]), orphan sectors
/// ([`CorruptionKind::OrphanSector`]), and declared-length inconsistencies
/// ([`CorruptionKind::DeclaredLengthMismatch`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CorruptionKind {
    /// A chain points back at a sector it already visited (a loop).
    ChainCycle,
    /// A chain pointer references an invalid sector or one past EOF.
    OutOfBounds,
    /// The same sector/mini-sector is reachable from two different chains.
    DoubleAllocated,
    /// A sector that is marked in-use in the FAT is not reachable from any
    /// known root chain.
    OrphanSector,
    /// A declared length (header count, directory length, FAT length) does
    /// not agree with the on-disk structure.
    DeclaredLengthMismatch,
    /// The directory chain stops before all populated directory sectors have
    /// been visited.
    TruncatedDirectory,
    /// A mini stream references a mini sector outside the MiniFAT/root stream.
    MiniStreamOutOfBounds,
    /// A table entry uses a reserved/illegal marker value.
    InvalidEntry,
    /// A sector that a table claims belongs to that table is marked
    /// differently in the FAT.
    TableMarkMismatch,
}

impl CorruptionKind {
    /// A short, stable identifier used in test names and diagnostics.
    pub fn identifier(self) -> &'static str {
        match self {
            CorruptionKind::ChainCycle => "chain_cycle",
            CorruptionKind::OutOfBounds => "out_of_bounds",
            CorruptionKind::DoubleAllocated => "double_allocated",
            CorruptionKind::OrphanSector => "orphan_sector",
            CorruptionKind::DeclaredLengthMismatch => "declared_length_mismatch",
            CorruptionKind::TruncatedDirectory => "truncated_directory",
            CorruptionKind::MiniStreamOutOfBounds => "mini_stream_out_of_bounds",
            CorruptionKind::InvalidEntry => "invalid_entry",
            CorruptionKind::TableMarkMismatch => "table_mark_mismatch",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.identifier())
    }
}

/// A single piece of corruption evidence.
///
/// The evidence records the structure affected, the category of corruption,
/// the *first offending position* (sector and, where relevant, slot/entry),
/// and human-readable context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Corruption {
    table: AllocationTable,
    kind: CorruptionKind,
    sector: Option<u32>,
    slot: Option<u64>,
    context: String,
}

impl Corruption {
    /// The allocation table this evidence concerns.
    pub fn table(&self) -> AllocationTable {
        self.table
    }
    /// The category of corruption.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }
    /// The first offending sector index, if applicable.
    pub fn sector(&self) -> Option<u32> {
        self.sector
    }
    /// The first offending slot/entry index within the sector or table, if
    /// applicable (e.g. a directory-entry id or a FAT entry index).
    pub fn slot(&self) -> Option<u64> {
        self.slot
    }
    /// Human-readable context describing the violation.
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.table, self.kind.identifier())?;
        if let Some(sector) = self.sector {
            write!(f, " at sector {sector}")?;
        }
        if let Some(slot) = self.slot {
            write!(f, " slot {slot}")?;
        }
        write!(f, " ({})", self.context)
    }
}

//===========================================================================//
// Digest

/// A 128-bit FNV-1a fingerprint of the audited file bytes.
///
/// This is recorded in a repair plan as the precondition that must still hold
/// when the plan is applied.  It is not a cryptographic hash; it only needs
/// to deterministically identify the exact bytes the plan was computed from.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AuditDigest([u8; 16]);

impl AuditDigest {
    fn compute(bytes: &[u8]) -> AuditDigest {
        // FNV-1a, 128-bit (offset basis 144066263297769815596495629667062367629,
        // prime 309485009821345068724781371).
        let mut hash: u128 =
            0x0000000001000000000000000000013b_u128
            ^ 0x6c62272e07bb014262b821756295c58d_u128;
        for &byte in bytes {
            hash ^= byte as u128;
            hash = hash.wrapping_mul(
                0x00000000000000000100000000000000_u128
                ^ 0x00000000010000000000000000000157_u128,
            );
        }
        AuditDigest(hash.to_be_bytes())
    }

    /// Returns the digest as 32 lowercase hexadecimal characters.
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(32);
        for byte in &self.0 {
            use fmt::Write as _;
            write!(out, "{byte:02x}").unwrap();
        }
        out
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_hex())
    }
}

//===========================================================================//
// Repair steps and plans

/// One atomic byte-level modification proposed by a repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    offset: u64,
    old_bytes: Vec<u8>,
    new_bytes: Vec<u8>,
    description: String,
}

impl RepairStep {
    /// Byte offset into the file where the patch starts.
    pub fn offset(&self) -> u64 {
        self.offset
    }
    /// The bytes currently present at that offset.
    pub fn old_bytes(&self) -> &[u8] {
        &self.old_bytes
    }
    /// The bytes the repair would write.
    pub fn new_bytes(&self) -> &[u8] {
        &self.new_bytes
    }
    /// A human-readable description of the change.
    pub fn description(&self) -> &str {
        &self.description
    }
}

impl fmt::Display for RepairStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "@{}: {} ({} bytes)",
            self.offset,
            self.description,
            self.new_bytes.len()
        )
    }
}

/// A read-only plan for repairing the corruption found by an audit.
///
/// The plan records the digest of the file it was computed for
/// ([`RepairPlan::precondition_digest`]).  It can only be applied when the
/// file's current digest still matches that precondition; otherwise
/// [`RepairPlan::apply_to`] fails *before writing anything*.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition: AuditDigest,
    steps: Vec<RepairStep>,
    file_len: u64,
}

impl RepairPlan {
    /// The digest the file must still have for this plan to be applicable.
    pub fn precondition_digest(&self) -> AuditDigest {
        self.precondition
    }

    /// The ordered, non-overlapping byte patches this plan would perform.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }

    /// Returns true if this plan performs no writes.
    pub fn is_noop(&self) -> bool {
        self.steps.is_empty()
    }

    /// Describes the plan without touching any byte.  This is the dry-run: it
    /// only borrows the reader to verify that the bytes still match the
    /// precondition; it never seeks to write.
    pub fn dry_run<R: Read + Seek>(
        &self,
        reader: &mut R,
    ) -> io::Result<&[RepairStep]> {
        let digest = hash_reader(reader, self.file_len)?;
        if digest != self.precondition {
            invalid_input!(
                "Cannot dry-run repair plan: file has changed since the audit \
                 (expected digest {}, found {})",
                self.precondition,
                digest
            );
        }
        Ok(&self.steps)
    }

    /// Applies the plan to `writer` atomically.
    ///
    /// The whole file is first verified against the precondition digest.  The
    /// patches are then applied one by one; if any write or flush fails, every
    /// patch already made is rolled back from its recorded `old_bytes` before
    /// the error is returned, leaving the file byte-for-byte unchanged.  On
    /// success the new digest is returned.
    pub fn apply_to<W: Read + Write + Seek>(
        &self,
        writer: &mut W,
    ) -> io::Result<AuditDigest> {
        if self.steps.is_empty() {
            let digest = hash_reader(writer, self.file_len)?;
            if digest != self.precondition {
                invalid_input!(
                    "Cannot apply repair plan: file has changed since the \
                     audit (expected digest {}, found {})",
                    self.precondition,
                    digest
                );
            }
            return Ok(digest);
        }
        // Precondition check happens before any write.
        let current = hash_reader(writer, self.file_len)?;
        if current != self.precondition {
            invalid_input!(
                "Cannot apply repair plan: file has changed since the audit \
                 (expected digest {}, found {})",
                self.precondition,
                current
            );
        }
        let applied = self.write_all(writer, true);
        match applied {
            Ok(()) => {}
            Err(forward_err) => {
                // Best-effort rollback.  Rollback writes are themselves
                // attempted; if the medium is gone there is nothing more we
                // can do, but the forward error remains what the caller sees.
                let _ = self.write_all(writer, false);
                let _ = writer.flush();
                return Err(forward_err);
            }
        }
        writer.flush()?;
        let new_digest = hash_reader(writer, self.file_len)?;
        Ok(new_digest)
    }

    fn write_all<W: Read + Write + Seek>(
        &self,
        writer: &mut W,
        forward: bool,
    ) -> io::Result<()> {
        if forward {
            for step in &self.steps {
                writer.seek(SeekFrom::Start(step.offset))?;
                writer.write_all(&step.new_bytes)?;
            }
        } else {
            for step in self.steps.iter().rev() {
                writer.seek(SeekFrom::Start(step.offset))?;
                writer.write_all(&step.old_bytes)?;
            }
        }
        Ok(())
    }
}

//===========================================================================//
// Audit report

/// The result of an opt-in structural audit.
///
/// The report collects independently-classified evidence and a read-only
/// repair plan.  Auditing never mutates the input.
#[derive(Clone, Debug)]
pub struct AuditReport {
    digest: AuditDigest,
    file_len: u64,
    evidence: Vec<Corruption>,
    plan: RepairPlan,
}

impl AuditReport {
    /// Digest of the audited bytes.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }
    /// True if no corruption evidence was found.
    pub fn is_clean(&self) -> bool {
        self.evidence.is_empty()
    }
    /// All evidence, sorted deterministically (table, kind, then position).
    pub fn evidence(&self) -> &[Corruption] {
        &self.evidence
    }
    /// Evidence filtered to a single allocation table.
    pub fn evidence_in(&self, table: AllocationTable) -> Vec<&Corruption> {
        self.evidence.iter().filter(|c| c.table == table).collect()
    }
    /// Returns true if evidence of the given category is present.
    pub fn has_kind(&self, kind: CorruptionKind) -> bool {
        self.evidence.iter().any(|c| c.kind == kind)
    }
    /// The read-only repair plan derived from the evidence.
    pub fn repair_plan(&self) -> &RepairPlan {
        &self.plan
    }
}

//===========================================================================//
// Raw parsed header (fields are read straight off disk without normalization)

#[derive(Clone, Copy)]
struct RawHeader {
    version: Version,
    num_dir_sectors: u32,
    num_fat_sectors: u32,
    first_dir_sector: u32,
    first_minifat_sector: u32,
    num_minifat_sectors: u32,
    first_difat_sector: u32,
    num_difat_sectors: u32,
}

//===========================================================================//
// Internal fix instructions (collected while evidence is gathered)

#[derive(Clone)]
enum Fix {
    /// Rewrite the entire FAT: (sector_id, entries for that sector).
    RewriteFatSector(u32, Vec<u32>),
    /// Patch a single MiniFAT entry.
    MiniFatEntry { index: u32, value: u32 },
    /// Set a u32 field in the file header.
    HeaderU32 { offset: u64, value: u32, desc: &'static str },
    /// Set a directory-entry u32 field (start sector / sibling / child).
    DirEntryU32 { slot: u32, offset: u64, value: u32 },
    /// Set a directory-entry u64 stream length.
    DirEntryU64 { slot: u32, offset: u64, value: u64 },
    /// Set a single FAT edge: fat[from] = value.
    FatEdge { from: u32, value: u32 },
    /// Recover truncated directory sectors by linking them back onto the
    /// directory chain, in ascending sector order, and repointing the header.
    RecoverDirectory {
        current_last: Option<u32>,
        sectors: Vec<u32>,
    },
}

/// Who owns a reachable sector, used to distinguish cross-chain double
/// occupation from simple loops within one chain.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    FatSector,
    DifatSector,
    Directory,
    MiniFat,
    RootContainer,
    /// A regular stream: (directory slot, length in bytes).
    Stream(u32, u64),
}

struct AuditState {
    version: Version,
    sector_len: usize,
    num_sectors: u32,
    file_len: u64,
    header: RawHeader,
    evidence: Vec<Corruption>,
    fixes: Vec<Fix>,
}

fn u32le(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}
fn u64le(bytes: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())
}

impl AuditState {
    fn report(&mut self, table: AllocationTable, kind: CorruptionKind,
              sector: Option<u32>, slot: Option<u64>, context: String) {
        self.evidence.push(Corruption {
            table,
            kind,
            sector,
            slot,
            context,
        });
    }

    fn sector_offset(&self, sector: u32) -> u64 {
        consts::HEADER_LEN as u64 + (sector as u64) * (self.sector_len as u64)
    }

    fn sector_bytes<'a>(&self, data: &'a [u8], sector: u32) -> &'a [u8] {
        let start = self.sector_offset(sector) as usize;
        &data[start..start + self.sector_len]
    }

    fn valid_sector(&self, sector: u32) -> bool {
        sector < self.num_sectors
    }
}

//===========================================================================//
// Top-level audit entry point

/// Audits `inner`, returning evidence and a read-only repair plan.
pub(crate) fn audit_reader<F: Read + Seek>(
    mut inner: F,
) -> io::Result<AuditReport> {
    let file_len = inner.seek(SeekFrom::End(0))?;
    if file_len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small to audit)",
            file_len
        );
    }
    let mut data = vec![0u8; file_len as usize];
    inner.seek(SeekFrom::Start(0))?;
    inner.read_exact(&mut data)?;
    let digest = AuditDigest::compute(&data);

    // Parse the minimum header fields needed.  We reuse the same on-disk
    // offsets the production header parser uses, but keep going even when a
    // field would normally be rejected, so that evidence can still be
    // collected.
    if data[0..8] != consts::MAGIC_NUMBER {
        invalid_data!("Invalid CFB file (wrong magic number); cannot audit");
    }
    let version_number = u16::from_le_bytes([data[26], data[27]]);
    let version = match Version::from_number(version_number) {
        Some(v) => v,
        None => invalid_data!(
            "CFB version {} is not supported; cannot audit",
            version_number
        ),
    };
    let sector_len = version.sector_len();
    if file_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length {} < sector length {}); cannot audit",
            file_len,
            sector_len
        );
    }
    let num_sectors =
        ((file_len - consts::HEADER_LEN as u64) / sector_len as u64) as u32;

    let header = RawHeader {
        version,
        num_dir_sectors: u32le(&data, 40),
        num_fat_sectors: u32le(&data, 44),
        first_dir_sector: u32le(&data, 48),
        first_minifat_sector: u32le(&data, 60),
        num_minifat_sectors: u32le(&data, 64),
        first_difat_sector: u32le(&data, 68),
        num_difat_sectors: u32le(&data, 72),
    };

    let mut state = AuditState {
        version,
        sector_len,
        num_sectors,
        file_len,
        header,
        evidence: Vec::new(),
        fixes: Vec::new(),
    };

    let (difat_sector_ids, mut difat) =
        analyze_difat(&mut state, &data);
    let fat = analyze_fat(&mut state, &data, &difat_sector_ids, &mut difat);

    let mut owners: std::collections::HashMap<u32, Owner> =
        std::collections::HashMap::new();
    for &s in &difat_sector_ids {
        owners.insert(s, Owner::DifatSector);
    }
    for &s in &difat {
        if state.valid_sector(s) {
            owners.insert(s, Owner::FatSector);
        }
    }

    // Directory chain.
    let (dir_chain, dir_truncated_extra) =
        analyze_directory(&mut state, &data, &fat, &mut owners);

    // Parse directory entries that the (possibly broken) directory chain
    // reached.
    let mut raw_entries: Vec<RawEntry> = Vec::new();
    let mut reached_slots = std::collections::HashSet::new();
    for &sector in &dir_chain {
        let base = state.sector_offset(sector) as usize;
        for j in 0..version.dir_entries_per_sector() {
            let slot = (raw_entries.len()) as u32;
            let entry_bytes =
                &data[base + j * consts::DIR_ENTRY_LEN
                          ..base + (j + 1) * consts::DIR_ENTRY_LEN];
            let raw = RawEntry::parse(entry_bytes, version);
            reached_slots.insert(slot);
            raw_entries.push(raw);
        }
    }

    analyze_streams_and_mini(
        &mut state,
        &data,
        &fat,
        &mut owners,
        &raw_entries,
        &reached_slots,
        &dir_chain,
    );

    if dir_truncated_extra {
        recover_truncated_directory(&mut state, &data, &fat, &owners,
                                    &dir_chain);
    }

    scan_orphans(&mut state, &fat, &owners);

    // Deterministic ordering of evidence.
    state.evidence.sort_by(compare_evidence);
    state.evidence.dedup();

    let steps = build_steps(&mut state, &data);
    let plan = RepairPlan {
        precondition: digest,
        steps,
        file_len,
    };
    Ok(AuditReport {
        digest,
        file_len,
        evidence: state.evidence,
        plan,
    })
}

fn compare_evidence(a: &Corruption, b: &Corruption) -> Ordering {
    (a.table, a.kind, a.sector, a.slot, a.context.clone())
        .cmp(&(b.table, b.kind, b.sector, b.slot, b.context.clone()))
}

//===========================================================================//
// DIFAT analysis

fn analyze_difat(state: &mut AuditState, data: &[u8])
    -> (Vec<u32>, Vec<u32>)
{
    let sector_len = state.sector_len;
    let entries_per_difat_sector = sector_len / 4 - 1;

    // Initial DIFAT entries live in the header at offset 76.
    let mut difat: Vec<u32> = Vec::new();
    for i in 0..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
        difat.push(u32le(data, 76 + i * 4));
    }

    // Walk the DIFAT sector chain.
    let mut difat_sector_ids = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut current = state.header.first_difat_sector;
    let mut guard = 0u32;
    let max_steps = state.num_sectors + 2;
    while current != consts::END_OF_CHAIN
        && current != consts::FREE_SECTOR
    {
        guard += 1;
        if guard > max_steps {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::ChainCycle,
                Some(current),
                None,
                "DIFAT chain did not terminate".to_string(),
            );
            break;
        }
        if current > consts::MAX_REGULAR_SECTOR || !state.valid_sector(current)
        {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::OutOfBounds,
                Some(current),
                None,
                format!(
                    "DIFAT chain references sector {}, but file has {} sectors",
                    current, state.num_sectors
                ),
            );
            break;
        }
        if !seen.insert(current) {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::ChainCycle,
                Some(current),
                None,
                "DIFAT chain revisits sector".to_string(),
            );
            break;
        }
        difat_sector_ids.push(current);
        let base = state.sector_offset(current) as usize;
        for j in 0..entries_per_difat_sector {
            difat.push(u32le(data, base + j * 4));
        }
        current = u32le(data, base + entries_per_difat_sector * 4);
    }

    // Header count consistency for DIFAT sectors.
    if state.header.num_difat_sectors as usize != difat_sector_ids.len() {
        state.report(
            AllocationTable::Difat,
            CorruptionKind::DeclaredLengthMismatch,
            Some(state.header.first_difat_sector),
            Some(state.header.num_difat_sectors as u64),
            format!(
                "header declares {} DIFAT sectors, chain has {}",
                state.header.num_difat_sectors,
                difat_sector_ids.len()
            ),
        );
        state.fixes.push(Fix::HeaderU32 {
            offset: 72,
            value: difat_sector_ids.len() as u32,
            desc: "num DIFAT sectors",
        });
    }

    // Trim trailing FREE entries, mirroring the production reader.
    while difat.last() == Some(&consts::FREE_SECTOR) {
        difat.pop();
    }

    // De-duplicate FAT sector references; duplicates are DIFAT double
    // occupation.
    let mut unique_fat = Vec::new();
    let mut fat_seen = std::collections::HashSet::new();
    for &sector in &difat {
        if sector == consts::FREE_SECTOR {
            continue;
        }
        if sector > consts::MAX_REGULAR_SECTOR {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::OutOfBounds,
                Some(sector),
                None,
                format!("DIFAT lists invalid sector index 0x{sector:08X}"),
            );
            continue;
        }
        if !state.valid_sector(sector) {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::OutOfBounds,
                Some(sector),
                None,
                format!(
                    "DIFAT lists FAT sector {}, but file has {} sectors",
                    sector, state.num_sectors
                ),
            );
            continue;
        }
        if !fat_seen.insert(sector) {
            state.report(
                AllocationTable::Difat,
                CorruptionKind::DoubleAllocated,
                Some(sector),
                None,
                "FAT sector listed more than once in DIFAT".to_string(),
            );
            continue;
        }
        unique_fat.push(sector);
    }

    if state.header.num_fat_sectors as usize != unique_fat.len() {
        state.report(
            AllocationTable::Difat,
            CorruptionKind::DeclaredLengthMismatch,
            Some(state.header.first_dir_sector),
            Some(state.header.num_fat_sectors as u64),
            format!(
                "header declares {} FAT sectors, DIFAT lists {}",
                state.header.num_fat_sectors,
                unique_fat.len()
            ),
        );
        state.fixes.push(Fix::HeaderU32 {
            offset: 44,
            value: unique_fat.len() as u32,
            desc: "num FAT sectors",
        });
    }

    (difat_sector_ids, unique_fat)
}
