//! Opt-in structural auditing of Compound File Binary files.
//!
//! This module is a read-only, non-destructive counterpart to the normal
//! open/create entry points: [`audit`](crate::audit) (and
//! [`OpenOptions::audit_with`](crate::OpenOptions::audit_with)) parse a file
//! that may be corrupt, collect *evidence* of damage to the allocation
//! structures (the FAT, DIFAT, MiniFAT, and directory chain) without stopping
//! at the first problem, and produce a [`RepairPlan`].
//!
//! The plan never touches the input on its own: [`StructureAudit::dry_run`]
//! cannot write (its type does not borrow a writer), while
//! [`StructureAudit::apply_plan`] only writes when the file still matches the
//! plan's precondition [`FileDigest`].  Every audit is independent: the
//! analysis holds only local state identified by that digest, so no cache,
//! counter, or temporary data from one call can leak into the next.
//!
//! The auditor reuses the production parsing primitives
//! ([`Header::read_from`](crate::internal::Header::read_from),
//! [`DirEntry::read_from`](crate::internal::DirEntry::read_from),
//! [`Sectors`](crate::internal::Sectors), and the shared FAT-entry
//! classifier) rather than a second, test-only copy of the format logic.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Sectors, Validation, Version};
use crate::ReadLeNumber;

//===========================================================================//

/// Which CFB allocation structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum AuditTable {
    /// The file header and the double-indirect FAT (DIFAT) chain it roots.
    Difat,
    /// The file allocation table chain.
    Fat,
    /// The directory sector chain.
    Directory,
    /// The mini FAT chain and the mini stream it addresses.
    MiniFat,
}

/// The category of damage found.
///
/// Cycles, out-of-bounds references, doubly occupied sectors, orphan sectors,
/// and declared-length mismatches are always reported as distinct codes, even
/// when one corruption triggers more than one of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum FindingCode {
    /// A chain loops back to a sector it already visited.
    Cycle,
    /// A reference points past the end of the file or table it indexes.
    OutOfBounds,
    /// The same sector is reachable through two different owners/chains.
    DoubleOccupancy,
    /// A sector is allocated in its table but owned by no chain or table.
    OrphanSector,
    /// A length or count declared by a header field or directory entry does
    /// not match what the allocation chains actually provide.
    DeclaredLength,
    /// An entry that cannot be parsed or repaired safely.
    MalformedEntry,
}

/// Where a [`Finding`] occurs: the first violating position, with enough
/// context to locate it in the file.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum FindingLocation {
    /// A field of the 512-byte CFB header, at this byte offset.
    Header(u64),
    /// An individual FAT entry at this sector index.
    FatEntry { sector: u32 },
    /// A chain followed from `chain_start`; `sector` is the first sector at
    /// which the violation is visible.
    Chain { table: AuditTable, chain_start: u32, sector: u32 },
    /// A directory entry (by stream ID) inside the directory chain.
    DirectoryEntry { stream_id: u32 },
    /// An individual MiniFAT entry at this mini sector index.
    MiniFatEntry { mini_sector: u32 },
}

/// One piece of damage evidence: what is wrong, where, and a human-readable
/// description of the necessary context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Finding {
    code: FindingCode,
    table: AuditTable,
    location: FindingLocation,
    detail: String,
    repairable: bool,
}

impl Finding {
    /// The damage category.
    pub fn code(&self) -> FindingCode {
        self.code
    }
    /// The allocation structure concerned.
    pub fn table(&self) -> AuditTable {
        self.table
    }
    /// The first violating position.
    pub fn location(&self) -> &FindingLocation {
        &self.location
    }
    /// A human-readable description including the necessary context.
    pub fn detail(&self) -> &str {
        &self.detail
    }
    /// Whether the generated repair plan can safely address this finding.
    /// Unrepairable findings make the whole plan blocked.
    pub fn is_repairable(&self) -> bool {
        self.repairable
    }

    fn ordering_key(&self) -> (AuditTable, FindingCode, u64, u64, &str) {
        let (loc_a, loc_b) = match &self.location {
            FindingLocation::Header(offset) => (0, *offset),
            FindingLocation::FatEntry { sector } => (1, u64::from(*sector)),
            FindingLocation::Chain { chain_start, sector, .. } => {
                (2, (u64::from(*chain_start) << 32) | u64::from(*sector))
            }
            FindingLocation::DirectoryEntry { stream_id } => {
                (3, u64::from(*stream_id))
            }
            FindingLocation::MiniFatEntry { mini_sector } => {
                (4, u64::from(*mini_sector))
            }
        };
        (self.table, self.code, loc_a, loc_b, &self.detail)
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} in {:?} at {:?}: {}",
            self.code, self.table, self.location, self.detail
        )
    }
}

//===========================================================================//

/// A non-cryptographic identity of the audited file's contents: its length
/// and an FNV-1a 64-bit hash of every byte.  A [`RepairPlan`] is bound to
/// the digest captured at audit time; applying it first recomputes the digest
/// and refuses to write anything when the file has changed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileDigest {
    len: u64,
    hash: u64,
}

impl FileDigest {
    /// The audited file length in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }
    /// Whether the audited file was empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl fmt::Display for FileDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:0x{:016x}", self.len, self.hash)
    }
}

const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

fn fnv1a64(reader: &mut (impl Read + Seek)) -> io::Result<FileDigest> {
    reader.seek(SeekFrom::Start(0))?;
    let mut hash = FNV_OFFSET_BASIS;
    let mut len: u64 = 0;
    let mut buffer = [0u8; 1 << 16];
    loop {
        let n = reader.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        for &byte in &buffer[..n] {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        len += n as u64;
    }
    Ok(FileDigest { len, hash })
}

//===========================================================================//

/// One fixed-length, in-place byte replacement proposed by a repair plan.
/// Repair never changes file size; ambiguous damage is instead left for
/// manual recovery and blocks the plan.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RepairStep {
    offset: u64,
    expected: Vec<u8>,
    replacement: Vec<u8>,
    description: String,
}

impl RepairStep {
    /// Byte offset at which the replacement is made.
    pub fn offset(&self) -> u64 {
        self.offset
    }
    /// The bytes expected to be present there before applying.
    pub fn expected_bytes(&self) -> &[u8] {
        &self.expected
    }
    /// The bytes to write.
    pub fn replacement_bytes(&self) -> &[u8] {
        &self.replacement
    }
    /// Describes the repair in CFB terms.
    pub fn description(&self) -> &str {
        &self.description
    }
}

impl fmt::Display for RepairStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "@{}: replace {} byte(s) ({})",
            self.offset,
            self.replacement.len(),
            self.description
        )
    }
}

//===========================================================================//

/// The result of preparing a [`RepairPlan`]: either a plan that may be
/// applied, or an explanation of why the damage cannot be repaired safely.
#[derive(Clone, Debug)]
pub enum PreparedPlan {
    /// Every finding has a safe repair; the plan may be applied.
    Repairable(RepairPlan),
    /// At least one finding is ambiguous or unsafe to repair automatically;
    /// applying such a plan is refused and writes nothing.
    Blocked {
        /// The unrepairable findings that force the block.
        reasons: Vec<Finding>,
    },
}

/// A read-only repair plan bound to a precondition [`FileDigest`].
#[derive(Clone, Debug)]
pub struct RepairPlan {
    digest: FileDigest,
    steps: Vec<RepairStep>,
}

impl RepairPlan {
    /// The digest the input must still match for the plan to be applied.
    pub fn precondition_digest(&self) -> FileDigest {
        self.digest
    }
    /// The ordered, deduplicated byte replacements the plan would make.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }
}

impl fmt::Display for RepairPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "RepairPlan precondition {}",
            self.digest
        )?;
        for step in &self.steps {
            writeln!(f, "  {step}")?;
        }
        Ok(())
    }
}

//===========================================================================//

/// The outcome of an opt-in structural audit: damage evidence plus, on
/// request, a read-only repair plan.
///
/// The audit borrows the underlying reader for its whole lifetime; the input
/// bytes are never modified.  Construction only ever happens through
/// [`audit`], [`OpenOptions::audit_with`](crate::OpenOptions::audit_with),
/// or [`CompoundFileAudit::open`](crate::CompoundFileAudit::open).
pub struct StructureAudit<F> {
    inner: F,
    version: Version,
    digest: FileDigest,
    findings: Vec<Finding>,
    steps: Vec<RepairStep>,
}

impl<F> StructureAudit<F> {
    /// The CFB version recorded in the file header.
    pub fn version(&self) -> Version {
        self.version
    }
    /// The identity of the audited file's bytes; the repair plan is bound to
    /// it.
    pub fn digest(&self) -> FileDigest {
        self.digest
    }
    /// All findings, in a deterministic order independent of collection
    /// order or scheduling.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }
    /// Returns true if no damage was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
    /// The collected, deduplicated repair steps so far (exposed without
    /// consuming the audit).
    pub fn proposed_steps(&self) -> &[RepairStep] {
        &self.steps
    }

    fn findings_by(&self, code: FindingCode) -> Vec<&Finding> {
        let mut matches: Vec<&Finding> =
            self.findings.iter().filter(|f| f.code == code).collect();
        matches.sort_by(|a, b| a.ordering_key().cmp(&b.ordering_key()));
        matches
    }

    /// All findings reporting cycles.
    pub fn cycles(&self) -> Vec<&Finding> {
        self.findings_by(FindingCode::Cycle)
    }
    /// All findings reporting out-of-bounds references.
    pub fn out_of_bounds(&self) -> Vec<&Finding> {
        self.findings_by(FindingCode::OutOfBounds)
    }
    /// All findings reporting sectors occupied by two owners.
    pub fn double_occupancy(&self) -> Vec<&Finding> {
        self.findings_by(FindingCode::DoubleOccupancy)
    }
    /// All findings reporting allocated but unreachable sectors.
    pub fn orphan_sectors(&self) -> Vec<&Finding> {
        self.findings_by(FindingCode::OrphanSector)
    }
    /// All findings reporting declared-length or count mismatches.
    pub fn declared_length_mismatches(&self) -> Vec<&Finding> {
        self.findings_by(FindingCode::DeclaredLength)
    }

    /// Consumes the audit, returning the underlying reader (unmodified).
    pub fn into_inner(self) -> F {
        self.inner
    }

    /// Builds the read-only repair plan from the current findings.  The plan
    /// is [`PreparedPlan::Blocked`] if any finding is not safely repairable;
    /// in that case applying it is impossible and would never write bytes.
    pub fn prepare_plan(&self) -> PreparedPlan {
        let blocked: Vec<Finding> =
            self.findings.iter().filter(|f| !f.repairable).cloned().collect();
        if !blocked.is_empty() {
            return PreparedPlan::Blocked { reasons: blocked };
        }
        PreparedPlan::Repairable(RepairPlan {
            digest: self.digest,
            steps: self.steps.clone(),
        })
    }
}

impl<F: Read + Seek> StructureAudit<F> {
    /// Checks, without writing, whether `plan` could be applied: the file
    /// must still match the plan's precondition digest and every step's
    /// expected bytes must still be present.
    ///
    /// This method cannot modify the input (it takes `&mut self` over a
    /// read-only reader), which is the type-level guarantee behind the
    /// dry-run contract.
    pub fn dry_run(&mut self, plan: &RepairPlan) -> io::Result<()> {
        let current = fnv1a64(&mut self.inner)?;
        if current != plan.digest {
            return Err(stale_plan_error(plan.digest, current));
        }
        for step in &plan.steps {
            let mut buffer = vec![0u8; step.expected.len()];
            self.inner.seek(SeekFrom::Start(step.offset))?;
            self.inner.read_exact(&mut buffer)?;
            if buffer != step.expected {
                invalid_data!(
                    "Repair step at offset {} no longer matches the file \
                     (the file changed since the plan was prepared)",
                    step.offset
                );
            }
        }
        Ok(())
    }
}

impl<F: Read + Write + Seek> StructureAudit<F> {
    /// Applies a previously prepared plan, but only if the file still matches
    /// the plan's precondition digest.  On success the audit is refreshed by
    /// re-analysing the same input and returns the new digest; on failure no
    /// byte is left modified: any writes already made are rolled back before
    /// the error is returned, leaving the file exactly as it was.
    pub fn apply_plan(&mut self, plan: &RepairPlan) -> io::Result<FileDigest> {
        // Re-check the whole-file identity first; nothing is written on
        // mismatch.
        let current = fnv1a64(&mut self.inner)?;
        if current != plan.digest {
            return Err(stale_plan_error(plan.digest, current));
        }
        // Snapshot the bytes every step will touch, then verify expected
        // contents before the first write.
        let mut snapshots: Vec<(u64, Vec<u8>)> = Vec::new();
        for step in &plan.steps {
            let mut buffer = vec![0u8; step.expected.len()];
            self.inner.seek(SeekFrom::Start(step.offset))?;
            self.inner.read_exact(&mut buffer)?;
            if buffer != step.expected {
                invalid_data!(
                    "Repair step at offset {} no longer matches the file \
                     (the file changed since the plan was prepared)",
                    step.offset
                );
            }
            snapshots.push((step.offset, buffer));
        }
        let mut applied = 0usize;
        let outcome = (|| -> io::Result<()> {
            for step in &plan.steps {
                self.inner.seek(SeekFrom::Start(step.offset))?;
                self.inner.write_all(&step.replacement)?;
                applied += 1;
            }
            self.inner.flush()?;
            Ok(())
        })();
        if let Err(error) = outcome {
            // Best-effort rollback of every step already written.
            for (offset, bytes) in snapshots.iter().take(applied).rev() {
                let rollback = (|| -> io::Result<()> {
                    self.inner.seek(SeekFrom::Start(*offset))?;
                    self.inner.write_all(bytes)?;
                    self.inner.flush()?;
                    Ok(())
                })();
                if let Err(rollback_error) = rollback {
                    return Err(io::Error::other(format!(
                        "Repair failed at {error}; rollback also failed: \
                         {rollback_error}"
                    )));
                }
            }
            return Err(error);
        }
        // Refresh all evidence from the repaired file.
        self.reanalyze()
    }
}

fn stale_plan_error(expected: FileDigest, actual: FileDigest) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "Cannot apply repair plan: file changed since the plan was \
             prepared (precondition {expected}, current {actual})"
        ),
    )
}

/// Opt-in entry point: analyses `inner` structurally without modifying it.
pub fn audit<F: Read + Seek>(inner: F) -> io::Result<StructureAudit<F>> {
    analyze(inner)
}

//===========================================================================//
// Internal analysis
//===========================================================================//

#[derive(Clone, Copy, PartialEq, Eq)]
enum DataOwner {
    Directory,
    MiniFat,
    MiniStream,
    Stream(u32),
}

impl DataOwner {
    fn label(self) -> String {
        match self {
            DataOwner::Directory => "directory chain".to_string(),
            DataOwner::MiniFat => "MiniFAT chain".to_string(),
            DataOwner::MiniStream => "mini stream".to_string(),
            DataOwner::Stream(id) => format!("stream entry {id}"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum MetaRole {
    Fat,
    Difat,
}

/// The outcome of walking one FAT chain.
#[derive(Default)]
struct ChainWalk {
    sectors: Vec<u32>,
    /// True when the start sector itself could not be followed at all.
    start_unusable: bool,
}

struct Analyzer {
    version: Version,
    sector_len: u64,
    num_sectors: u32,
    difat_fat_sectors: Vec<u32>,
    fat: Vec<u32>,
    findings: Vec<Finding>,
    steps: BTreeMap<u64, RepairStep>,
}

fn new_finding(
    code: FindingCode,
    table: AuditTable,
    location: FindingLocation,
    detail: impl Into<String>,
    repairable: bool,
) -> Finding {
    Finding {
        code,
        table,
        location,
        detail: detail.into(),
        repairable,
    }
}

impl Analyzer {
    fn step(
        &mut self,
        offset: u64,
        expected: Vec<u8>,
        replacement: Vec<u8>,
        description: impl Into<String>,
    ) {
        let new_step = RepairStep {
            offset,
            expected,
            replacement,
            description: description.into(),
        };
        let _ = self.steps.try_insert(offset, new_step);
    }

    fn step_u32(
        &mut self,
        offset: u64,
        expected: u32,
        replacement: u32,
        description: impl Into<String>,
    ) {
        self.step(
            offset,
            expected.to_le_bytes().to_vec(),
            replacement.to_le_bytes().to_vec(),
            description,
        );
    }

    fn add(&mut self, item: Finding) {
        self.findings.push(item);
    }

    /// Byte offset of FAT entry `sector`, if it lives inside a reachable FAT
    /// sector.  Uses the same arithmetic as the production `Sectors` type.
    fn fat_entry_offset(&self, sector: u32) -> Option<u64> {
        let per_sector = (self.sector_len / 4) as u32;
        let fat_sector_index = sector / per_sector;
        let within = sector % per_sector;
        let fat_sector =
            *self.difat_fat_sectors.get(fat_sector_index as usize)?;
        if fat_sector >= self.num_sectors {
            return None;
        }
        Some(
            consts::HEADER_LEN as u64
                + u64::from(fat_sector) * self.sector_len
                + u64::from(within) * 4,
        )
    }

    fn repair_fat_entry(&mut self, sector: u32, value: u32, why: &str) {
        if let Some(offset) = self.fat_entry_offset(sector) {
            let current =
                self.fat.get(sector as usize).copied().unwrap_or(value);
            self.step_u32(offset, current, value, why);
        }
    }

    /// Follows one chain in the FAT from `start`, bounded by the file size
    /// and a per-walk visited set so a cycle terminates the traversal.
    /// Every violation is recorded as evidence rather than aborting.
    fn walk_fat_chain(
        &mut self,
        start: u32,
        table: AuditTable,
        owner: DataOwner,
        roles: &[Option<MetaRole>],
        owners: &mut [Option<DataOwner>],
    ) -> ChainWalk {
        let mut walk = ChainWalk::default();
        let loc = |sector: u32| FindingLocation::Chain {
            table,
            chain_start: start,
            sector,
        };
        if start == consts::END_OF_CHAIN {
            return walk;
        }
        if start == consts::FREE_SECTOR {
            self.add(new_finding(
                FindingCode::MalformedEntry,
                table,
                loc(start),
                format!(
                    "{} starts at FREE_SECTOR instead of END_OF_CHAIN",
                    owner.label()
                ),
                false,
            ));
            walk.start_unusable = true;
            return walk;
        }
        if start > consts::MAX_REGULAR_SECTOR || start >= self.num_sectors {
            self.add(new_finding(
                FindingCode::OutOfBounds,
                table,
                loc(start),
                format!(
                    "{} starts at sector {}, but the file has only {} sectors",
                    owner.label(),
                    start, self.num_sectors
                ),
                false,
            ));
            walk.start_unusable = true;
            return walk;
        }
        if roles[start as usize].is_some() {
            self.add(new_finding(
                FindingCode::DoubleOccupancy,
                table,
                loc(start),
                format!(
                    "{} starts in metadata sector {}",
                    owner.label(),
                    start
                ),
                false,
            ));
            walk.start_unusable = true;
            return walk;
        }
        let mut current = start;
        let mut visited = std::collections::BTreeSet::new();
        loop {
            if !visited.insert(current) {
                self.add(new_finding(
                    FindingCode::Cycle,
                    table,
                    loc(current),
                    format!("{} loops back on sector {}", owner.label(), current),
                    false,
                ));
                return walk;
            }
            walk.sectors.push(current);
            match owners[current as usize] {
                None => owners[current as usize] = Some(owner),
                Some(existing) if existing == owner => {}
                Some(existing) => self.add(new_finding(
                    FindingCode::DoubleOccupancy,
                    table,
                    loc(current),
                    format!(
                        "sector {} is shared by {} and {}",
                        current,
                        existing.label(),
                        owner.label()
                    ),
                    false,
                )),
            }
            let entry = self
                .fat
                .get(current as usize)
                .copied()
                .unwrap_or(consts::FREE_SECTOR);
            match consts::classify_fat_entry(entry) {
                consts::FatEntryKind::Pointer(next) => {
                    if next >= self.num_sectors {
                        self.add(new_finding(
                            FindingCode::OutOfBounds,
                            table,
                            loc(next),
                            format!(
                                "FAT entry of sector {} points past the file \
                                 to sector {} (sector count {})",
                                current, next, self.num_sectors
                            ),
                            true,
                        ));
                        self.repair_fat_entry(
                            current,
                            consts::END_OF_CHAIN,
                            "terminate chain at out-of-bounds pointer",
                        );
                        return walk;
                    }
                    if roles[next as usize].is_some() {
                        self.add(new_finding(
                            FindingCode::DoubleOccupancy,
                            table,
                            loc(next),
                            format!(
                                "{} enters metadata sector {} through the FAT",
                                owner.label(),
                                next
                            ),
                            false,
                        ));
                        return walk;
                    }
                    current = next;
                }
                consts::FatEntryKind::EndOfChain => return walk,
                consts::FatEntryKind::Free => {
                    self.add(new_finding(
                        FindingCode::DeclaredLength,
                        table,
                        loc(current),
                        format!(
                            "{} sector {} has a FREE_SECTOR FAT entry instead \
                             of END_OF_CHAIN",
                            owner.label(),
                            current
                        ),
                        true,
                    ));
                    self.repair_fat_entry(
                        current,
                        consts::END_OF_CHAIN,
                        "terminate chain with END_OF_CHAIN marker",
                    );
                    return walk;
                }
                consts::FatEntryKind::Invalid => {
                    self.add(new_finding(
                        FindingCode::OutOfBounds,
                        table,
                        loc(current),
                        format!(
                            "FAT entry of sector {} is the invalid marker \
                             0x{:08X}",
                            current,
                            consts::INVALID_SECTOR
                        ),
                        true,
                    ));
                    self.repair_fat_entry(
                        current,
                        consts::END_OF_CHAIN,
                        "replace invalid FAT entry with END_OF_CHAIN",
                    );
                    return walk;
                }
                consts::FatEntryKind::Fat | consts::FatEntryKind::Difat => {
                    self.add(new_finding(
                        FindingCode::MalformedEntry,
                        table,
                        loc(current),
                        format!(
                            "{} runs through metadata-marked sector {}",
                            owner.label(),
                            current
                        ),
                        true,
                    ));
                    self.repair_fat_entry(
                        current,
                        consts::END_OF_CHAIN,
                        "terminate data chain at metadata marker",
                    );
                    return walk;
                }
            }
        }
    }
}

//===========================================================================//

/// Header byte offsets for the declared counts the audit cross-checks.
const OFFSET_NUM_DIR_SECTORS: u64 = 40;
const OFFSET_NUM_FAT_SECTORS: u64 = 44;
const OFFSET_FIRST_DIR_SECTOR: u64 = 48;
const OFFSET_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const OFFSET_FIRST_DIFAT_SECTOR: u64 = 68;
const OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
const OFFSET_INITIAL_DIFAT: u64 = 76;

fn analyze<F: Read + Seek>(inner: F) -> io::Result<StructureAudit<F>> {
    let mut audit = StructureAudit {
        inner,
        version: Version::V3,
        digest: FileDigest { len: 0, hash: 0 },
        findings: Vec::new(),
        steps: Vec::new(),
    };
    let digest = fnv1a64(&mut audit.inner)?;
    if digest.len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            digest.len
        );
    }

    // Read the header with the same production parser, first directly; if
    // only its initial DIFAT array is invalid, neutralize those entries and
    // retry, recording each as evidence.
    audit.inner.seek(SeekFrom::Start(0))?;
    let mut header_bytes = [0u8; consts::HEADER_LEN];
    audit.inner.read_exact(&mut header_bytes)?;
    let header = match Header::read_from(
        &mut &header_bytes[..],
        Validation::Permissive,
    ) {
        Ok(header) => header,
        Err(error) => {
            // Initial DIFAT entries holding regular-sector range values are
            // rejected by the parser; treat them as evidence and retry.
            let mut repaired = header_bytes;
            let mut patched = 0u32;
            for index in 0..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
                let offset = OFFSET_INITIAL_DIFAT as usize + 4 * index;
                let value = u32::from_le_bytes([
                    repaired[offset],
                    repaired[offset + 1],
                    repaired[offset + 2],
                    repaired[offset + 3],
                ]);
                if value != consts::FREE_SECTOR
                    && value > consts::MAX_REGULAR_SECTOR
                {
                    repaired[offset..offset + 4]
                        .copy_from_slice(&consts::FREE_SECTOR.to_le_bytes());
                    patched += 1;
                }
            }
            if patched == 0 {
                return Err(error);
            }
            let header = Header::read_from(
                &mut &repaired[..],
                Validation::Permissive,
            )?;
            analyzer.add(new_finding(
                FindingCode::OutOfBounds,
                AuditTable::Difat,
                FindingLocation::Header(OFFSET_INITIAL_DIFAT),
                format!(
                    "initial DIFAT array contains {} entry value(s) outside \
                     the regular-sector range",
                    patched
                ),
                true,
            ));
            header
        }
    };
    audit.version = header.version;
    let sector_len = header.version.sector_len() as u64;
    if digest.len < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            digest.len,
            sector_len
        );
    }
    let num_sectors =
        ((digest.len / sector_len).saturating_sub(1)) as u32;

    let mut analyzer = Analyzer {
        version: header.version,
        sector_len,
        num_sectors,
        difat_fat_sectors: Vec::new(),
        fat: Vec::new(),
        findings: Vec::new(),
        steps: BTreeMap::new(),
    };

    // Read the DIFAT chain (including its chain-pointer entries), mirroring
    // the traversal performed while opening a file.
    let mut sectors = Sectors::new(header.version, digest.len, &mut audit.inner);
    let mut difat: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();
    let mut difat_sector_ids: Vec<u32> = Vec::new();
    let mut current_difat = header.first_difat_sector;
    let mut seen_difat = std::collections::BTreeSet::new();
    while current_difat != consts::END_OF_CHAIN
        && current_difat != consts::FREE_SECTOR
    {
        if current_difat > consts::MAX_REGULAR_SECTOR
            || current_difat >= num_sectors
        {
            analyzer.add(new_finding(
                FindingCode::OutOfBounds,
                AuditTable::Difat,
                FindingLocation::Chain {
                    table: AuditTable::Difat,
                    chain_start: header.first_difat_sector,
                    sector: current_difat,
                },
                format!(
                    "DIFAT chain references sector {}, but sector count is \
                     {}",
                    current_difat, num_sectors
                ),
                false,
            ));
            break;
        }
        if !seen_difat.insert(current_difat) {
            analyzer.add(new_finding(
                FindingCode::Cycle,
                AuditTable::Difat,
                FindingLocation::Chain {
                    table: AuditTable::Difat,
                    chain_start: header.first_difat_sector,
                    sector: current_difat,
                },
                format!(
                    "DIFAT chain loops back on sector {}",
                    current_difat
                ),
                false,
            ));
            break;
        }
        difat_sector_ids.push(current_difat);
        let mut sector_data = vec![0u8; sector_len as usize];
        sectors.seek_to_sector(current_difat)?.read_exact(&mut sector_data)?;
        let entries_per_sector = (sector_len / 4) as usize;
        let mut cursor = &sector_data[..];
        for _ in 0..entries_per_sector - 1 {
            let next = cursor.read_le_u32()?;
            difat.push(next);
        }
        current_difat = cursor.read_le_u32()?;
    }
    while difat.last() == Some(&consts::FREE_SECTOR) {
        difat.pop();
    }
    let difat_fat_sectors: Vec<u32> = difat
        .iter()
        .copied()
        .filter(|&entry| entry <= consts::MAX_REGULAR_SECTOR)
        .collect();
    analyzer.difat_fat_sectors = difat_fat_sectors.clone();

    // Read the complete FAT, one sector per DIFAT pointer.
    let entries_per_sector = (sector_len / 4) as usize;
    let mut fat: Vec<u32> = Vec::new();
    for &fat_sector in &difat_fat_sectors {
        if fat_sector >= num_sectors {
            analyzer.add(new_finding(
                FindingCode::OutOfBounds,
                AuditTable::Difat,
                FindingLocation::FatEntry { sector: fat_sector },
                format!(
                    "DIFAT lists FAT sector {}, but sector count is {}",
                    fat_sector, num_sectors
                ),
                false,
            ));
            fat.extend(
                std::iter::repeat(consts::FREE_SECTOR).take(entries_per_sector),
            );
            continue;
        }
        let mut sector_data = vec![0u8; sector_len as usize];
        sectors.seek_to_sector(fat_sector)?.read_exact(&mut sector_data)?;
        let mut cursor = &sector_data[..];
        for _ in 0..entries_per_sector {
            fat.push(cursor.read_le_u32()?);
        }
    }


    // Normalize the FAT to exactly one entry per sector, recording evidence
    // for meaningless entries past end-of-file (the permissive open path
    // strips exactly these).
    while analyzer.fat.len() < num_sectors as usize {
        let index = analyzer.fat.len();
        let entry = fat.get(index).copied().unwrap_or(consts::FREE_SECTOR);
        analyzer.fat.push(entry);
    }
    for (index, &entry) in fat.iter().enumerate().skip(num_sectors as usize) {
        if !matches!(
            consts::classify_fat_entry(entry),
            consts::FatEntryKind::Free
                | consts::FatEntryKind::Fat
                | consts::FatEntryKind::Difat
        ) && entry != 0
        {
            analyzer.add(new_finding(
                FindingCode::OutOfBounds,
                AuditTable::Fat,
                FindingLocation::FatEntry { sector: index as u32 },
                format!(
                    "FAT entry at index {} exists past end of file (sector \
                     count {})",
                    index, num_sectors
                ),
                false,
            ));
        }
    }

    // Classify metadata sectors from the DIFAT and check that the FAT marks
    // them consistently with their roles (a mismatch is repairable).
    let mut roles: Vec<Option<MetaRole>> = vec![None; num_sectors as usize];
    let mut owners: Vec<Option<DataOwner>> =
        vec![None; num_sectors as usize];

    for &sector_id in &difat_sector_ids {
        let index = sector_id as usize;
        if index >= num_sectors as usize {
            continue;
        }
        match consts::classify_fat_entry(analyzer.fat[index]) {
            consts::FatEntryKind::Difat => {}
            consts::FatEntryKind::Fat => {
                analyzer.add(new_finding(
                    FindingCode::DeclaredLength,
                    AuditTable::Difat,
                    FindingLocation::FatEntry { sector: sector_id },
                    format!(
                        "DIFAT sector {} is marked as a FAT sector in the FAT",
                        sector_id
                    ),
                    true,
                ));
                analyzer.repair_fat_entry(
                    sector_id,
                    consts::DIFAT_SECTOR,
                    "mark DIFAT sector with DIFAT_SECTOR",
                );
            }
            _ => {
                analyzer.add(new_finding(
                    FindingCode::DeclaredLength,
                    AuditTable::Difat,
                    FindingLocation::FatEntry { sector: sector_id },
                    format!(
                        "sector {} is part of the DIFAT chain but is not \
                         marked DIFAT_SECTOR in the FAT",
                        sector_id
                    ),
                    true,
                ));
                analyzer.repair_fat_entry(
                    sector_id,
                    consts::DIFAT_SECTOR,
                    "mark DIFAT chain sector with DIFAT_SECTOR",
                );
            }
        }
        roles[index] = Some(MetaRole::Difat);
    }
    for &sector_id in &difat_fat_sectors {
        let index = sector_id as usize;
        if index >= num_sectors as usize {
            continue;
        }
        match consts::classify_fat_entry(analyzer.fat[index]) {
            consts::FatEntryKind::Fat => {}
            consts::FatEntryKind::Difat => {
                analyzer.add(new_finding(
                    FindingCode::DeclaredLength,
                    AuditTable::Fat,
                    FindingLocation::FatEntry { sector: sector_id },
                    format!(
                        "FAT sector {} is marked as a DIFAT sector in the FAT",
                        sector_id
                    ),
                    true,
                ));
                analyzer.repair_fat_entry(
                    sector_id,
                    consts::FAT_SECTOR,
                    "mark FAT sector with FAT_SECTOR",
                );
            }
            _ => {
                analyzer.add(new_finding(
                    FindingCode::DeclaredLength,
                    AuditTable::Fat,
                    FindingLocation::FatEntry { sector: sector_id },
                    format!(
                        "sector {} is part of a FAT chain but is not marked \
                         FAT_SECTOR in the FAT",
                        sector_id
                    ),
                    true,
                ));
                analyzer.repair_fat_entry(
                    sector_id,
                    consts::FAT_SECTOR,
                    "mark FAT chain sector with FAT_SECTOR",
                );
            }
        }
        roles[index] = Some(MetaRole::Fat);
    }

    // Directory chain.
    let dir_walk = analyzer.walk_fat_chain(
        header.first_dir_sector,
        AuditTable::Directory,
        DataOwner::Directory,
        &roles,
        &mut owners,
    );
    if header.version == Version::V4 && !dir_walk.start_unusable {
        let actual = dir_walk.sectors.len() as u32;
        if header.num_dir_sectors != actual {
            analyzer.add(new_finding(
                FindingCode::DeclaredLength,
                AuditTable::Directory,
                FindingLocation::Header(OFFSET_NUM_DIR_SECTORS),
                format!(
                    "header declares {} directory sectors, but the directory \
                     chain has {}",
                    header.num_dir_sectors, actual
                ),
                true,
            ));
            analyzer.step_u32(
                OFFSET_NUM_DIR_SECTORS,
                header.num_dir_sectors,
                actual,
                "set header directory sector count to actual chain length",
            );
        }
    }

    // Parse directory entries with the production parser, tolerantly, in
    // chain order, recording the file offset of every slot.
    let entries_per_dir_sector =
        header.version.dir_entries_per_sector();
    let mut dir_entries: Vec<Option<(DirEntry, u64)>> = Vec::new();
    for (chain_index, &sector_id) in dir_walk.sectors.iter().enumerate() {
        let sector_base = consts::HEADER_LEN as u64
            + u64::from(sector_id) * sector_len;
        let mut sector_data = vec![0u8; sector_len as usize];
        sectors.seek_to_sector(sector_id)?.read_exact(&mut sector_data)?;
        for slot in 0..entries_per_dir_sector {
            let offset = sector_base + (slot as u64) * consts::DIR_ENTRY_LEN as u64;
            let mut cursor = &sector_data[slot * consts::DIR_ENTRY_LEN
                ..(slot + 1) * consts::DIR_ENTRY_LEN];
            let stream_id =
                (chain_index * entries_per_dir_sector + slot) as u32;
            match DirEntry::read_from(
                &mut cursor,
                header.version,
                Validation::Permissive,
            ) {
                Ok(entry) => dir_entries.push(Some((entry, offset))),
                Err(error) => {
                    dir_entries.push(None);
                    analyzer.add(new_finding(
                        FindingCode::MalformedEntry,
                        AuditTable::Directory,
                        FindingLocation::DirectoryEntry { stream_id },
                        format!("directory entry cannot be parsed: {error}"),
                        false,
                    ));
                }
            }
        }
    }
