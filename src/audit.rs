//! Structural auditing of compound files and read-only repair plans.
//!
//! This module implements the opt-in structural audit offered through
//! [`OpenOptions::audit`](crate::OpenOptions::audit) (and the
//! [`crate::audit`](crate::audit) / [`crate::audit_path`](crate::audit_path)
//! convenience functions).  Auditing a compound file never modifies the
//! input: the whole input is snapshotted, and all analysis runs against that
//! snapshot.  The result is an [`AuditReport`] containing independently
//! classified [`Finding`]s for the DIFAT, the FAT, the MiniFAT and the
//! directory chain, together with a read-only [`RepairPlan`].
//!
//! The five corruption classes requested by callers -- cycles,
//! out-of-range references, duplicate sector allocation, orphan sectors and
//! declared-length mismatches -- are always reported as separate findings,
//! each carrying the first offending location plus enough context (chain
//! owner, sector counts) to explain it.
//!
//! A repair plan is bound to the exact input it was planned for by a
//! [`PreconditionDigest`].  [`RepairPlan::apply`] recomputes the digest and
//! refuses to write anything unless it still matches, so a file that changed
//! after planning cannot be half-updated.  All repaired bytes are computed
//! in memory before the single write-back pass.  [`RepairPlan::dry_run`]
//! performs exactly the same checks but takes a read-only source and never
//! writes.  Because every audit starts from a fresh snapshot, no cache,
//! counter or other state leaks between calls.
//!
//! The auditor deliberately shares its low-level parsing with the normal
//! open path: it reuses [`Header::read_from`], [`DirEntry::read_from`],
//! [`Version`] and the FAT entry constants from [`crate::internal`], so the
//! bytes it reasons about are parsed exactly as they are when a compound
//! file is opened.  Only the chain traversal differs: the open path fails at
//! the first problem, whereas the auditor tolerates corruption, records it
//! and keeps walking.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};

// Field offsets within the 512-byte CFB header (MS-CFB 2.2).
const OFFSET_NUM_DIR_SECTORS: u64 = 40;
const OFFSET_NUM_FAT_SECTORS: u64 = 44;
const OFFSET_FIRST_DIR_SECTOR: u64 = 48;
const OFFSET_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
const HEADER_DIFAT_START: u64 = 76;

// Field offsets within a 128-byte directory entry (MS-CFB 2.6).
const ENTRY_LEFT_SIBLING: u64 = 68;
const ENTRY_RIGHT_SIBLING: u64 = 72;
const ENTRY_CHILD: u64 = 76;
const ENTRY_START_SECTOR: u64 = 116;
const ENTRY_STREAM_LEN: u64 = 120;

//===========================================================================//
// Precondition digest

/// A fingerprint of the exact input a [`RepairPlan`] was made for.
///
/// The digest combines the input length with two FNV-1/FNV-1a 64-bit hashes
/// of the input bytes.  It is cheap and dependency-free, and it serves as
/// the version identity of a plan: applying the plan is only allowed while
/// the current input still has this digest.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PreconditionDigest {
    len: u64,
    fnv1: u64,
    fnv1a: u64,
}

impl PreconditionDigest {
    fn of(data: &[u8]) -> PreconditionDigest {
        const PRIME: u64 = 0x100000001b3;
        let mut fnv1 = 0xcbf29ce484222325;
        let mut fnv1a = 0x84222325cbf29ce4;
        for &byte in data.iter() {
            // FNV-1: multiply first, then xor.
            fnv1 = fnv1.wrapping_mul(PRIME) ^ byte as u64;
            // FNV-1a: xor first, then multiply.
            fnv1a = fnv1a.wrapping_mul(PRIME) ^ byte as u64;
        }
        PreconditionDigest { len: data.len() as u64, fnv1, fnv1a }
    }

    /// The length, in bytes, of the input this digest describes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns true if the input is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl fmt::Debug for PreconditionDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl fmt::Display for PreconditionDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "len={:016x}/fnv1={:016x}/fnv1a={:016x}",
            self.len, self.fnv1, self.fnv1a
        )
    }
}

//===========================================================================//
// Findings

/// The part of a compound file a [`Finding`] refers to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Structure {
    /// The file header and its declared sector counts.
    Header,
    /// The Double-Indirect FAT (header array and DIFAT sector chain).
    Difat,
    /// The File Allocation Table and the sector chains it describes.
    Fat,
    /// The MiniFAT and the mini-sector chains it describes.
    MiniFat,
    /// The chain of directory sectors.
    DirectoryChain,
    /// A single directory entry.
    DirectoryEntry,
}

/// The class of corruption recorded by a [`Finding`].
///
/// Cycles, out-of-range references, duplicate allocation, orphan sectors and
/// declared-length mismatches are always classified separately, so callers
/// can react to each condition independently.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorruptionCategory {
    /// A chain revisits a sector it already contains.
    Loop,
    /// A reference points past the end of the table that should contain it,
    /// or at a reserved/free sector id used as a pointer.
    OutOfBounds,
    /// Two chains (or DIFAT entries) claim the same sector.
    DuplicateAllocation,
    /// A sector is marked allocated but no chain reaches it.
    OrphanSector,
    /// A declared length or sector count disagrees with what is present.
    LengthMismatch,
    /// Any other spec violation that does not fit the classes above.
    Malformed,
}

/// A single piece of corruption evidence produced by an audit.
///
/// Findings are reported in a canonical order that depends only on the
/// audited bytes: chains are walked in a fixed sequence and sector ids are
/// scanned in ascending order, so two audits of the same input always
/// produce identical findings regardless of thread or timing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    category: CorruptionCategory,
    structure: Structure,
    location: Option<u32>,
    message: String,
}

impl Finding {
    /// The class of corruption.
    pub fn category(&self) -> CorruptionCategory {
        self.category
    }

    /// The structure the corruption was found in.
    pub fn structure(&self) -> Structure {
        self.structure
    }

    /// The sector id, mini-sector id or directory-entry index at which the
    /// corruption was first observed, if a single id identifies it.
    pub fn location(&self) -> Option<u32> {
        self.location
    }

    /// A human-readable description with the context of the violation.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.location {
            Some(location) => write!(
                f,
                "{:?} in {:?} at {}: {}",
                self.category, self.structure, location, self.message
            ),
            None => write!(
                f,
                "{:?} in {:?}: {}",
                self.category, self.structure, self.message
            ),
        }
    }
}

//===========================================================================//
// Repair plan

/// One byte-level change proposed by a [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairAction {
    description: String,
    offset: u64,
    expect: Vec<u8>,
    patch: Vec<u8>,
}

impl RepairAction {
    /// A human-readable description of what this action changes and why.
    pub fn description(&self) -> &str {
        &self.description
    }

    /// The byte offset in the file at which the patch is applied.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// The bytes expected at `offset` before patching.  Application checks
    /// these as a second line of defense behind the plan digest.
    pub fn expected_bytes(&self) -> &[u8] {
        &self.expect
    }

    /// The bytes that replace the expected ones.
    pub fn patched_bytes(&self) -> &[u8] {
        &self.patch
    }
}

/// The result of [`RepairPlan::dry_run`]: the actions that would be applied
/// and the digest the input would have afterwards, computed without writing
/// anything.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPreview {
    actions: Vec<RepairAction>,
    resulting_digest: PreconditionDigest,
}

impl RepairPreview {
    /// The actions a real apply would perform.
    pub fn actions(&self) -> &[RepairAction] {
        &self.actions
    }

    /// The digest the input would have if the plan were applied.
    pub fn resulting_digest(&self) -> PreconditionDigest {
        self.resulting_digest
    }
}

/// A read-only plan for repairing the corruptions found by an audit.
///
/// A plan is a plain value: it holds no I/O handle, cache or mutable state,
/// so it can be cloned, shared between threads and reused freely.  What ties
/// it to a particular input is its [`PreconditionDigest`]; both
/// [`dry_run`](RepairPlan::dry_run) and [`apply`](RepairPlan::apply) recompute
/// the digest of the current input and refuse to proceed if it no longer
/// matches.  Application is atomic with respect to verification failures:
/// every check runs against an in-memory snapshot and the repaired image is
/// fully built before the single write-back pass, so a failed apply leaves
/// the input untouched.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPlan {
    digest: PreconditionDigest,
    actions: Vec<RepairAction>,
}

impl RepairPlan {
    /// The digest of the input this plan was made for.  The plan can only be
    /// applied while the input still has this digest.
    pub fn precondition_digest(&self) -> PreconditionDigest {
        self.digest
    }

    /// The byte-level actions of the plan, in the order they are applied.
    pub fn actions(&self) -> &[RepairAction] {
        &self.actions
    }

    /// Returns true if the plan changes nothing (the input was healthy).
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }

    /// Verifies the plan against `inner` and reports what would change,
    /// without writing any bytes.  The input only needs to be readable.
    pub fn dry_run<F: Read + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<RepairPreview> {
        let snapshot = read_snapshot(inner)?;
        self.check_precondition(&snapshot)?;
        let patched = render_patched(&snapshot, &self.actions)?;
        Ok(RepairPreview {
            actions: self.actions.clone(),
            resulting_digest: PreconditionDigest::of(&patched),
        })
    }

    /// Applies the plan to `inner`, provided the input still matches the
    /// plan's precondition digest.
    ///
    /// The input is fully re-read and verified first, and the complete
    /// repaired image is computed in memory; only then is it written back in
    /// one pass.  If verification fails, no byte is written.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<()> {
        let snapshot = read_snapshot(inner)?;
        self.check_precondition(&snapshot)?;
        if self.actions.is_empty() {
            return Ok(());
        }
        let patched = render_patched(&snapshot, &self.actions)?;
        inner.seek(SeekFrom::Start(0))?;
        inner.write_all(&patched)?;
        inner.flush()
    }

    fn check_precondition(&self, snapshot: &[u8]) -> io::Result<()> {
        let current = PreconditionDigest::of(snapshot);
        if current != self.digest {
            invalid_data!(
                "Repair plan precondition mismatch: plan was made for input \
                 {}, but the current input is {}",
                self.digest,
                current
            );
        }
        Ok(())
    }
}

/// Builds the repaired image in memory.  Every action's expected bytes are
/// checked, so a mismatch anywhere aborts before anything is written.
fn render_patched(
    snapshot: &[u8],
    actions: &[RepairAction],
) -> io::Result<Vec<u8>> {
    let mut image = snapshot.to_vec();
    for action in actions {
        let start = action.offset as usize;
        let end = start + action.patch.len();
        if end > image.len() {
            invalid_data!(
                "Repair action at offset {} extends past end of input ({} \
                 bytes)",
                action.offset,
                image.len()
            );
        }
        if image[start..end] != action.expect[..] {
            invalid_data!(
                "Repair action at offset {} ({}) does not match the input",
                action.offset,
                action.description
            );
        }
        image[start..end].copy_from_slice(&action.patch);
    }
    Ok(image)
}

//===========================================================================//
// Audit report

/// The result of a structural audit: classified corruption evidence plus a
/// read-only repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuditReport {
    findings: Vec<Finding>,
    plan: RepairPlan,
}

impl AuditReport {
    /// All findings, in canonical order.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// The first finding, if any.  Because findings are ordered, this is the
    /// earliest violation in the auditor's traversal of the file.
    pub fn first_finding(&self) -> Option<&Finding> {
        self.findings.first()
    }

    /// Returns true if no corruption was found.
    pub fn is_healthy(&self) -> bool {
        self.findings.is_empty()
    }

    /// The read-only repair plan derived from the findings.
    pub fn repair_plan(&self) -> &RepairPlan {
        &self.plan
    }
}

//===========================================================================//
// Entry point

/// Audits the compound file readable from `inner`, without modifying it.
///
/// This is the implementation behind `cfb::audit` and
/// `OpenOptions::audit_with`.  Inputs whose header cannot be parsed at all
/// are rejected with the same `InvalidData` errors the normal open path
/// produces.
pub(crate) fn audit_reader<F: Read + Seek>(inner: F) -> io::Result<AuditReport> {
    let mut inner = inner;
    let snapshot = read_snapshot(&mut inner)?;
    analyze(&snapshot)
}

fn read_snapshot<F: Read + Seek>(inner: &mut F) -> io::Result<Vec<u8>> {
    inner.seek(SeekFrom::Start(0))?;
    let mut data = Vec::new();
    inner.read_to_end(&mut data)?;
    Ok(data)
}

fn read_u32_at(data: &[u8], offset: u64) -> u32 {
    let start = offset as usize;
    u32::from_le_bytes([
        data[start],
        data[start + 1],
        data[start + 2],
        data[start + 3],
    ])
}

//===========================================================================//
// Auditor

/// Where the on-disk pointer to the start of a chain lives, so that a chain
/// whose very first link is broken can be repaired at that pointer.
#[derive(Clone, Copy)]
enum StartRef {
    /// A u32 field in the header, at the given byte offset.
    HeaderField(u64),
    /// The start-sector field of the given directory entry.
    DirEntryStart(u32),
}

struct Auditor<'a> {
    data: &'a [u8],
    header: Header,
    sector_len: usize,
    num_sectors: u32,
    /// Valid FAT sector ids collected from the DIFAT, in order.
    difat: Vec<u32>,
    /// Valid DIFAT chain sector ids, in chain order.
    difat_sectors: Vec<u32>,
    /// The FAT, trimmed/padded to `num_sectors` entries like the open path.
    fat: Vec<u32>,
    /// A working copy of the FAT with every planned repair applied.
    repaired_fat: Vec<u32>,
    /// Sector id -> owner description, for every reachable regular sector.
    claimed: BTreeMap<u32, String>,
    /// File offset of each loaded directory entry.
    dir_entry_offsets: Vec<u64>,
    /// The directory entries loaded from the directory chain.
    dir_entries: Vec<DirEntry>,
    /// The directory chain's sector ids (post-repair).
    dir_chain: Vec<u32>,
    /// The MiniFAT chain's sector ids (post-repair).
    minifat_chain: Vec<u32>,
    /// The MiniFAT entries (trailing FREE entries stripped), and its
    /// repaired working copy.
    minifat: Vec<u32>,
    repaired_minifat: Vec<u32>,
    /// Mini-sector id -> owner description, for reachable mini sectors.
    claimed_minis: BTreeMap<u32, String>,
    findings: Vec<Finding>,
    actions: Vec<RepairAction>,
}

impl<'a> Auditor<'a> {
    fn finding(
        &mut self,
        category: CorruptionCategory,
        structure: Structure,
        location: Option<u32>,
        message: String,
    ) {
        self.findings.push(Finding { category, structure, location, message });
    }

    fn action_u32(&mut self, description: String, offset: u64, value: u32) {
        let start = offset as usize;
        let expect = self.data[start..start + 4].to_vec();
        self.actions.push(RepairAction {
            description,
            offset,
            expect,
            patch: value.to_le_bytes().to_vec(),
        });
    }

    fn action_u64(&mut self, description: String, offset: u64, value: u64) {
        let start = offset as usize;
        let expect = self.data[start..start + 8].to_vec();
        self.actions.push(RepairAction {
            description,
            offset,
            expect,
            patch: value.to_le_bytes().to_vec(),
        });
    }

    /// File offset of the first byte of the given sector.
    fn sector_offset(&self, sector_id: u32) -> u64 {
        (sector_id as u64 + 1) * self.sector_len as u64
    }

    /// File offset of the FAT entry for `sector_id`, if that entry is backed
    /// by a FAT sector listed in the (valid part of the) DIFAT.
    fn fat_entry_offset(&self, sector_id: u32) -> Option<u64> {
        let per_sector = self.sector_len / 4;
        let index = sector_id as usize / per_sector;
        let &fat_sector = self.difat.get(index)?;
        Some(
            self.sector_offset(fat_sector)
                + (sector_id as usize % per_sector) as u64 * 4,
        )
    }

    /// File offset of the MiniFAT entry for `mini_sector`, if it is backed
    /// by a sector of the (post-repair) MiniFAT chain.
    fn minifat_entry_offset(&self, mini_sector: u32) -> Option<u64> {
        let per_sector = self.sector_len / 4;
        let index = mini_sector as usize / per_sector;
        let &sector = self.minifat_chain.get(index)?;
        Some(
            self.sector_offset(sector)
                + (mini_sector as usize % per_sector) as u64 * 4,
        )
    }

    /// File offset of a field within the given directory entry.
    fn dir_entry_field_offset(
        &self,
        stream_id: u32,
        field: u64,
    ) -> Option<u64> {
        self.dir_entry_offsets
            .get(stream_id as usize)
            .map(|&base| base + field)
    }
}

fn analyze(data: &[u8]) -> io::Result<AuditReport> {
    // Mirror the size checks of the normal open path so that inputs which
    // cannot be compound files at all are rejected with the same errors.
    if data.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            data.len()
        );
    }
    let header = Header::read_from(&mut &data[..], Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len();
    if data.len() as u64
        > (consts::MAX_REGULAR_SECTOR as u64 + 1) * sector_len as u64
    {
        invalid_data!(
            "Invalid CFB file ({} bytes is too large)",
            data.len()
        );
    }
    if data.len() < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            data.len(),
            sector_len
        );
    }
    // Same sector count computation as `Sectors::new`.
    let num_sectors =
        (data.len() as u64).div_ceil(sector_len as u64) as u32 - 1;

    let mut auditor = Auditor {
        data,
        header,
        sector_len,
        num_sectors,
        difat: Vec::new(),
        difat_sectors: Vec::new(),
        fat: Vec::new(),
        repaired_fat: Vec::new(),
        claimed: BTreeMap::new(),
        dir_entry_offsets: Vec::new(),
        dir_entries: Vec::new(),
        dir_chain: Vec::new(),
        minifat_chain: Vec::new(),
        minifat: Vec::new(),
        repaired_minifat: Vec::new(),
        claimed_minis: BTreeMap::new(),
        findings: Vec::new(),
        actions: Vec::new(),
    };
    auditor.run();
    let plan = RepairPlan {
        digest: PreconditionDigest::of(data),
        actions: auditor.actions,
    };
    Ok(AuditReport { findings: auditor.findings, plan })
}

impl<'a> Auditor<'a> {
    /// Runs the full audit in a fixed phase order, so findings are always
    /// produced in the same sequence for the same input.
    fn run(&mut self) {
        self.audit_difat();
        self.load_fat();
        self.repaired_fat = self.fat.clone();
        self.claim_special_sectors();
        self.audit_directory_chain();
        self.audit_minifat();
        self.audit_mini_stream_container();
        self.audit_streams();
        self.audit_mini_orphans();
        self.audit_orphans();
    }

    //=== DIFAT ===//

    fn audit_difat(&mut self) {
        let mut seen = Vec::<u32>::new();
        // FAT sector ids listed in the header's DIFAT array.  The production
        // header parser has already rejected reserved ids here.
        for index in 0..consts::NUM_DIFAT_ENTRIES_IN_HEADER {
            let entry = self.header.initial_difat_entries[index];
            if entry == consts::FREE_SECTOR {
                continue;
            }
            self.check_difat_entry(entry, &mut seen);
        }
        // Walk the DIFAT sector chain.
        let entries_per_sector = self.sector_len / 4 - 1;
        let mut current = self.header.first_difat_sector;
        while current != consts::END_OF_CHAIN {
            if current > consts::MAX_REGULAR_SECTOR {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    Structure::Difat,
                    Some(current),
                    format!(
                        "DIFAT chain includes reserved sector id 0x{current:08X}"
                    ),
                );
                break;
            }
            if current >= self.num_sectors {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    Structure::Difat,
                    Some(current),
                    format!(
                        "DIFAT chain includes sector {current}, but sector \
                         count is only {}",
                        self.num_sectors
                    ),
                );
                break;
            }
            if self.difat_sectors.contains(&current) {
                self.finding(
                    CorruptionCategory::Loop,
                    Structure::Difat,
                    Some(current),
                    format!("DIFAT chain loops back to sector {current}"),
                );
                break;
            }
            self.difat_sectors.push(current);
            let base = self.sector_offset(current);
            for index in 0..entries_per_sector {
                let entry = read_u32_at(self.data, base + 4 * index as u64);
                if entry == consts::FREE_SECTOR {
                    continue;
                }
                if entry > consts::MAX_REGULAR_SECTOR {
                    self.finding(
                        CorruptionCategory::OutOfBounds,
                        Structure::Difat,
                        Some(entry),
                        format!(
                            "DIFAT sector {current} lists reserved sector id \
                             0x{entry:08X}"
                        ),
                    );
                    continue;
                }
                self.check_difat_entry(entry, &mut seen);
            }
            current =
                read_u32_at(self.data, base + 4 * entries_per_sector as u64);
            if current == consts::FREE_SECTOR {
                // The strict open path rejects this; the permissive one
                // treats it as the end of the chain.  Report it, then stop.
                self.finding(
                    CorruptionCategory::Malformed,
                    Structure::Difat,
                    None,
                    "DIFAT chain terminates with FREE_SECTOR instead of \
                     END_OF_CHAIN"
                        .to_string(),
                );
                break;
            }
        }
        if self.header.num_difat_sectors as usize != self.difat_sectors.len() {
            let declared = self.header.num_difat_sectors;
            let actual = self.difat_sectors.len();
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::Difat,
                None,
                format!(
                    "header declares {declared} DIFAT sectors, but the DIFAT \
                     chain contains {actual}"
                ),
            );
            let description = format!(
                "set header DIFAT sector count to the actual {actual}"
            );
            self.action_u32(
                description,
                OFFSET_NUM_DIFAT_SECTORS,
                actual as u32,
            );
        }
    }

    fn check_difat_entry(&mut self, entry: u32, seen: &mut Vec<u32>) {
        if entry >= self.num_sectors {
            self.finding(
                CorruptionCategory::OutOfBounds,
                Structure::Difat,
                Some(entry),
                format!(
                    "DIFAT refers to sector {entry}, but sector count is \
                     only {}",
                    self.num_sectors
                ),
            );
            return;
        }
        if seen.contains(&entry) {
            self.finding(
                CorruptionCategory::DuplicateAllocation,
                Structure::Difat,
                Some(entry),
                format!("sector {entry} is listed in the DIFAT twice"),
            );
            return;
        }
        seen.push(entry);
        self.difat.push(entry);
    }

    //=== FAT loading ===//

    fn load_fat(&mut self) {
        let entries_per_sector = self.sector_len / 4;
        for &fat_sector in self.difat.clone().iter() {
            let base = self.sector_offset(fat_sector);
            for index in 0..entries_per_sector {
                self.fat.push(read_u32_at(self.data, base + 4 * index as u64));
            }
        }
        // Mirror the permissive open path: strip trailing zero/FAT/DIFAT/FREE
        // padding beyond the sector count, then trailing FREE entries.
        while self.fat.len() > self.num_sectors as usize {
            match self.fat.last() {
                Some(&entry)
                    if entry == 0
                        || entry == consts::DIFAT_SECTOR
                        || entry == consts::FAT_SECTOR
                        || entry == consts::FREE_SECTOR =>
                {
                    self.fat.pop();
                }
                _ => break,
            }
        }
        while self.fat.len() > self.num_sectors as usize
            && self.fat.last() == Some(&consts::FREE_SECTOR)
        {
            self.fat.pop();
        }
        if self.fat.len() > self.num_sectors as usize {
            self.finding(
                CorruptionCategory::Malformed,
                Structure::Fat,
                None,
                format!(
                    "FAT has {} entries, but file has only {} sectors",
                    self.fat.len(),
                    self.num_sectors
                ),
            );
            // Continue the audit with the entries that exist on disk.
            self.fat.truncate(self.num_sectors as usize);
        }
        while self.fat.len() < self.num_sectors as usize {
            self.fat.push(consts::FREE_SECTOR);
        }
        if self.header.num_fat_sectors as usize != self.difat.len() {
            let declared = self.header.num_fat_sectors;
            let actual = self.difat.len();
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::Difat,
                None,
                format!(
                    "header declares {declared} FAT sectors, but the DIFAT \
                     lists {actual}"
                ),
            );
            let description = format!(
                "set header FAT sector count to the actual {actual}"
            );
            self.action_u32(description, OFFSET_NUM_FAT_SECTORS, actual as u32);
        }
    }

    /// Marks the FAT and DIFAT sectors themselves as claimed, and plans
    /// repairs for sectors whose FAT entries do not mark them correctly
    /// (mirroring what `Allocator::validate` fixes in memory).
    fn claim_special_sectors(&mut self) {
        for &sector in self.difat_sectors.clone().iter() {
            self.claimed.insert(sector, "DIFAT chain".to_string());
            if self.repaired_fat[sector as usize] != consts::DIFAT_SECTOR {
                self.finding(
                    CorruptionCategory::Malformed,
                    Structure::Fat,
                    Some(sector),
                    format!(
                        "DIFAT sector {sector} is not marked as such in the \
                         FAT"
                    ),
                );
                self.repaired_fat[sector as usize] = consts::DIFAT_SECTOR;
                if let Some(offset) = self.fat_entry_offset(sector) {
                    let description =
                        format!("mark DIFAT sector {sector} as such in the FAT");
                    self.action_u32(description, offset, consts::DIFAT_SECTOR);
                }
            }
        }
        for &sector in self.difat.clone().iter() {
            self.claimed.insert(sector, "FAT".to_string());
            if self.repaired_fat[sector as usize] != consts::FAT_SECTOR {
                self.finding(
                    CorruptionCategory::Malformed,
                    Structure::Fat,
                    Some(sector),
                    format!(
                        "FAT sector {sector} is not marked as such in the FAT"
                    ),
                );
                self.repaired_fat[sector as usize] = consts::FAT_SECTOR;
                if let Some(offset) = self.fat_entry_offset(sector) {
                    let description =
                        format!("mark FAT sector {sector} as such in the FAT");
                    self.action_u32(description, offset, consts::FAT_SECTOR);
                }
            }
        }
    }

    //=== Chain walking ===//

    /// Walks the regular-sector chain starting at `start` over the repaired
    /// FAT, recording a finding and planning a truncation repair for every
    /// loop, out-of-range pointer or crossed chain encountered.  Returns the
    /// sector ids of the (possibly truncated) chain.
    fn walk_fat_chain(
        &mut self,
        start: u32,
        owner: &str,
        structure: Structure,
        start_ref: StartRef,
    ) -> Vec<u32> {
        let mut chain = Vec::<u32>::new();
        let mut current = start;
        let mut previous: Option<u32> = None;
        loop {
            if current == consts::END_OF_CHAIN {
                break;
            }
            if current > consts::MAX_REGULAR_SECTOR {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    structure,
                    previous.or(Some(current)),
                    format!(
                        "chain for {owner} references reserved sector id \
                         0x{current:08X}"
                    ),
                );
                self.truncate_fat_chain(previous, start_ref, owner);
                break;
            }
            if current >= self.num_sectors {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    structure,
                    Some(current),
                    format!(
                        "chain for {owner} references sector {current}, but \
                         sector count is only {}",
                        self.num_sectors
                    ),
                );
                self.truncate_fat_chain(previous, start_ref, owner);
                break;
            }
            if chain.contains(&current) {
                self.finding(
                    CorruptionCategory::Loop,
                    structure,
                    Some(current),
                    format!("chain for {owner} loops back to sector {current}"),
                );
                self.truncate_fat_chain(previous, start_ref, owner);
                break;
            }
            if let Some(other) = self.claimed.get(&current) {
                let other = other.clone();
                self.finding(
                    CorruptionCategory::DuplicateAllocation,
                    structure,
                    Some(current),
                    format!(
                        "sector {current} is allocated to both {other} and \
                         {owner}"
                    ),
                );
                self.truncate_fat_chain(previous, start_ref, owner);
                break;
            }
            self.claimed.insert(current, owner.to_string());
            chain.push(current);
            previous = Some(current);
            current = self.repaired_fat[current as usize];
        }
        chain
    }

    /// Ends a damaged chain just before its first bad link: either by
    /// terminating the FAT entry of the last good sector, or, when the very
    /// first link is bad, by clearing the pointer to the chain's start.
    fn truncate_fat_chain(
        &mut self,
        previous: Option<u32>,
        start_ref: StartRef,
        owner: &str,
    ) {
        match previous {
            Some(sector) => {
                self.repaired_fat[sector as usize] = consts::END_OF_CHAIN;
                if let Some(offset) = self.fat_entry_offset(sector) {
                    let description = format!(
                        "truncate the chain for {owner} after sector {sector}"
                    );
                    self.action_u32(description, offset, consts::END_OF_CHAIN);
                }
            }
            None => match start_ref {
                StartRef::HeaderField(offset) => {
                    let description = format!(
                        "clear the header start sector of the chain for \
                         {owner}"
                    );
                    self.action_u32(description, offset, consts::END_OF_CHAIN);
                }
                StartRef::DirEntryStart(stream_id) => {
                    if let Some(offset) = self.dir_entry_field_offset(
                        stream_id,
                        ENTRY_START_SECTOR,
                    ) {
                        let description = format!(
                            "clear the start sector of directory entry \
                             {stream_id} ({owner})"
                        );
                        self.action_u32(
                            description,
                            offset,
                            consts::END_OF_CHAIN,
                        );
                    }
                }
            },
        }
    }

    //=== Directory ===//

    fn audit_directory_chain(&mut self) {
        self.dir_chain = self.walk_fat_chain(
            self.header.first_dir_sector,
            "directory chain",
            Structure::DirectoryChain,
            StartRef::HeaderField(OFFSET_FIRST_DIR_SECTOR),
        );
        if self.header.version == Version::V4
            && self.header.num_dir_sectors as usize != self.dir_chain.len()
        {
            let declared = self.header.num_dir_sectors;
            let actual = self.dir_chain.len();
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::DirectoryChain,
                None,
                format!(
                    "header declares {declared} directory sectors, but the \
                     directory chain contains {actual}"
                ),
            );
            let description = format!(
                "set header directory sector count to the actual {actual}"
            );
            self.action_u32(description, OFFSET_NUM_DIR_SECTORS, actual as u32);
        }
        if self.dir_chain.is_empty() {
            self.finding(
                CorruptionCategory::Malformed,
                Structure::DirectoryChain,
                None,
                "directory chain is empty; the root entry is missing"
                    .to_string(),
            );
            return;
        }
        // Parse the directory entries with the production parser.
        let entries_per_sector = self.header.version.dir_entries_per_sector();
        let dir_chain = self.dir_chain.clone();
        for &sector in dir_chain.iter() {
            let base = self.sector_offset(sector);
            for index in 0..entries_per_sector {
                let offset = base + (index * consts::DIR_ENTRY_LEN) as u64;
                let start = offset as usize;
                let end = start + consts::DIR_ENTRY_LEN;
                let mut bytes = &self.data[start..end];
                match DirEntry::read_from(
                    &mut bytes,
                    self.header.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => {
                        self.dir_entry_offsets.push(offset);
                        self.dir_entries.push(entry);
                    }
                    Err(err) => {
                        let stream_id = self.dir_entries.len() as u32;
                        self.finding(
                            CorruptionCategory::Malformed,
                            Structure::DirectoryEntry,
                            Some(stream_id),
                            format!(
                                "directory entry {stream_id} could not be \
                                 parsed: {err}"
                            ),
                        );
                        self.dir_entry_offsets.push(offset);
                        self.dir_entries.push(DirEntry::unallocated());
                    }
                }
            }
        }
        // Check sibling/child references against the entries actually loaded;
        // a reference past the last entry means the directory chain was
        // truncated (or the reference is garbage).
        let entry_count = self.dir_entries.len() as u32;
        for stream_id in 0..entry_count {
            let entry = &self.dir_entries[stream_id as usize];
            if entry.obj_type == ObjType::Unallocated {
                continue;
            }
            let references = [
                ("left sibling", entry.left_sibling, ENTRY_LEFT_SIBLING),
                ("right sibling", entry.right_sibling, ENTRY_RIGHT_SIBLING),
                ("child", entry.child, ENTRY_CHILD),
            ];
            for (kind, reference, field) in references {
                if reference != consts::NO_STREAM && reference >= entry_count {
                    let name = entry.name.clone();
                    self.finding(
                        CorruptionCategory::OutOfBounds,
                        Structure::DirectoryEntry,
                        Some(stream_id),
                        format!(
                            "directory entry {stream_id} ({name:?}) refers \
                             to {kind} entry {reference}, but only \
                             {entry_count} entries are present"
                        ),
                    );
                    if let Some(offset) =
                        self.dir_entry_field_offset(stream_id, field)
                    {
                        let description = format!(
                            "clear the dangling {kind} reference of directory \
                             entry {stream_id}"
                        );
                        self.action_u32(description, offset, consts::NO_STREAM);
                    }
                }
            }
        }
    }

    //=== MiniFAT ===//

    fn audit_minifat(&mut self) {
        self.minifat_chain = self.walk_fat_chain(
            self.header.first_minifat_sector,
            "MiniFAT chain",
            Structure::MiniFat,
            StartRef::HeaderField(OFFSET_FIRST_MINIFAT_SECTOR),
        );
        if self.header.num_minifat_sectors as usize != self.minifat_chain.len()
        {
            let declared = self.header.num_minifat_sectors;
            let actual = self.minifat_chain.len();
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::MiniFat,
                None,
                format!(
                    "header declares {declared} MiniFAT sectors, but the \
                     MiniFAT chain contains {actual}"
                ),
            );
            let description = format!(
                "set header MiniFAT sector count to the actual {actual}"
            );
            self.action_u32(
                description,
                OFFSET_NUM_MINIFAT_SECTORS,
                actual as u32,
            );
        }
        // Read the MiniFAT entries from the chain's sectors, stripping
        // trailing FREE entries like the open path does.
        let entries_per_sector = self.sector_len / 4;
        let minifat_chain = self.minifat_chain.clone();
        for &sector in minifat_chain.iter() {
            let base = self.sector_offset(sector);
            for index in 0..entries_per_sector {
                self.minifat
                    .push(read_u32_at(self.data, base + 4 * index as u64));
            }
        }
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            self.minifat.pop();
        }
        self.repaired_minifat = self.minifat.clone();
    }

    //=== Mini stream container (the root entry's stream) ===//

    fn audit_mini_stream_container(&mut self) {
        let Some(root) = self.dir_entries.first() else {
            return;
        };
        if root.obj_type != ObjType::Root {
            return;
        }
        let root_start = root.start_sector;
        let root_len = root.stream_len;
        let container = self.walk_fat_chain(
            root_start,
            "mini stream",
            Structure::Fat,
            StartRef::DirEntryStart(consts::ROOT_STREAM_ID),
        );
        let capacity = (container.len() * self.sector_len) as u64;
        let mini_sector_len = consts::MINI_SECTOR_LEN as u64;
        let mut repaired_root_len = root_len;
        if root_len % mini_sector_len != 0 {
            repaired_root_len = root_len / mini_sector_len * mini_sector_len;
            self.finding(
                CorruptionCategory::Malformed,
                Structure::DirectoryEntry,
                Some(consts::ROOT_STREAM_ID),
                format!(
                    "mini stream length {root_len} is not a multiple of the \
                     mini sector size {mini_sector_len}"
                ),
            );
        }
        if repaired_root_len > capacity {
            repaired_root_len = capacity / mini_sector_len * mini_sector_len;
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::DirectoryEntry,
                Some(consts::ROOT_STREAM_ID),
                format!(
                    "mini stream declares length {root_len}, but its chain \
                     holds only {capacity} bytes"
                ),
            );
        }
        if repaired_root_len != root_len {
            if let Some(offset) = self.dir_entry_field_offset(
                consts::ROOT_STREAM_ID,
                ENTRY_STREAM_LEN,
            ) {
                let description = format!(
                    "set the mini stream length to {repaired_root_len}"
                );
                self.action_u64(description, offset, repaired_root_len);
            }
        }
        // The MiniFAT must not hold more entries than the mini stream has
        // mini sectors; the permissive open path truncates the excess, so
        // plan to free it.
        let mini_sectors = repaired_root_len / mini_sector_len;
        if self.repaired_minifat.len() as u64 > mini_sectors {
            self.finding(
                CorruptionCategory::LengthMismatch,
                Structure::MiniFat,
                Some(mini_sectors as u32),
                format!(
                    "MiniFAT has {} entries, but the mini stream holds only \
                     {mini_sectors} mini sectors",
                    self.repaired_minifat.len()
                ),
            );
            for index in mini_sectors..self.repaired_minifat.len() as u64 {
                self.repaired_minifat[index as usize] = consts::FREE_SECTOR;
                if let Some(offset) =
                    self.minifat_entry_offset(index as u32)
                {
                    let description = format!(
                        "free MiniFAT entry {index} beyond the mini stream"
                    );
                    self.action_u32(description, offset, consts::FREE_SECTOR);
                }
            }
        }
    }

    //=== Streams ===//

    fn audit_streams(&mut self) {
        for stream_id in 0..self.dir_entries.len() as u32 {
            let entry = &self.dir_entries[stream_id as usize];
            if entry.obj_type != ObjType::Stream {
                continue;
            }
            let (name, start, declared) =
                (entry.name.clone(), entry.start_sector, entry.stream_len);
            let owner = format!("stream {name:?} (entry {stream_id})");
            if declared == 0 {
                if start != consts::END_OF_CHAIN {
                    self.finding(
                        CorruptionCategory::Malformed,
                        Structure::DirectoryEntry,
                        Some(stream_id),
                        format!(
                            "{owner} has zero length but starts at sector \
                             {start}"
                        ),
                    );
                    if let Some(offset) = self
                        .dir_entry_field_offset(stream_id, ENTRY_START_SECTOR)
                    {
                        let description = format!(
                            "clear the start sector of empty {owner}"
                        );
                        self.action_u32(
                            description,
                            offset,
                            consts::END_OF_CHAIN,
                        );
                    }
                }
                continue;
            }
            if declared >= consts::MINI_STREAM_CUTOFF as u64 {
                // Regular-sector chain.
                let chain = self.walk_fat_chain(
                    start,
                    &owner,
                    Structure::Fat,
                    StartRef::DirEntryStart(stream_id),
                );
                let capacity = (chain.len() * self.sector_len) as u64;
                if declared > capacity {
                    self.finding(
                        CorruptionCategory::LengthMismatch,
                        Structure::DirectoryEntry,
                        Some(stream_id),
                        format!(
                            "{owner} declares length {declared}, but its \
                             chain holds only {capacity} bytes"
                        ),
                    );
                    if let Some(offset) = self
                        .dir_entry_field_offset(stream_id, ENTRY_STREAM_LEN)
                    {
                        let description = format!(
                            "set the length of {owner} to its chain \
                             capacity {capacity}"
                        );
                        self.action_u64(description, offset, capacity);
                    }
                }
            } else {
                // Mini-sector chain.
                let chain = self.walk_mini_chain(start, &owner, stream_id);
                let capacity =
                    (chain.len() * consts::MINI_SECTOR_LEN) as u64;
                if declared > capacity {
                    self.finding(
                        CorruptionCategory::LengthMismatch,
                        Structure::DirectoryEntry,
                        Some(stream_id),
                        format!(
                            "{owner} declares length {declared}, but its \
                             mini chain holds only {capacity} bytes"
                        ),
                    );
                    if let Some(offset) = self
                        .dir_entry_field_offset(stream_id, ENTRY_STREAM_LEN)
                    {
                        let description = format!(
                            "set the length of {owner} to its mini chain \
                             capacity {capacity}"
                        );
                        self.action_u64(description, offset, capacity);
                    }
                }
            }
        }
    }

    /// Walks a mini-sector chain over the repaired MiniFAT, mirroring
    /// `walk_fat_chain` at mini-sector granularity.
    fn walk_mini_chain(
        &mut self,
        start: u32,
        owner: &str,
        stream_id: u32,
    ) -> Vec<u32> {
        let mut chain = Vec::<u32>::new();
        let mut current = start;
        let mut previous: Option<u32> = None;
        loop {
            if current == consts::END_OF_CHAIN {
                break;
            }
            if current > consts::MAX_REGULAR_SECTOR {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    Structure::MiniFat,
                    previous.or(Some(current)),
                    format!(
                        "mini chain for {owner} references reserved mini \
                         sector id 0x{current:08X}"
                    ),
                );
                self.truncate_mini_chain(previous, stream_id, owner);
                break;
            }
            if current as usize >= self.repaired_minifat.len() {
                self.finding(
                    CorruptionCategory::OutOfBounds,
                    Structure::MiniFat,
                    Some(current),
                    format!(
                        "mini chain for {owner} references mini sector \
                         {current}, but the MiniFAT has only {} entries",
                        self.repaired_minifat.len()
                    ),
                );
                self.truncate_mini_chain(previous, stream_id, owner);
                break;
            }
            if chain.contains(&current) {
                self.finding(
                    CorruptionCategory::Loop,
                    Structure::MiniFat,
                    Some(current),
                    format!(
                        "mini chain for {owner} loops back to mini sector \
                         {current}"
                    ),
                );
                self.truncate_mini_chain(previous, stream_id, owner);
                break;
            }
            if let Some(other) = self.claimed_minis.get(&current) {
                let other = other.clone();
                self.finding(
                    CorruptionCategory::DuplicateAllocation,
                    Structure::MiniFat,
                    Some(current),
                    format!(
                        "mini sector {current} is allocated to both {other} \
                         and {owner}"
                    ),
                );
                self.truncate_mini_chain(previous, stream_id, owner);
                break;
            }
            self.claimed_minis.insert(current, owner.to_string());
            chain.push(current);
            previous = Some(current);
            current = self.repaired_minifat[current as usize];
        }
        chain
    }

    fn truncate_mini_chain(
        &mut self,
        previous: Option<u32>,
        stream_id: u32,
        owner: &str,
    ) {
        match previous {
            Some(mini_sector) => {
                self.repaired_minifat[mini_sector as usize] =
                    consts::END_OF_CHAIN;
                if let Some(offset) = self.minifat_entry_offset(mini_sector) {
                    let description = format!(
                        "truncate the mini chain for {owner} after mini \
                         sector {mini_sector}"
                    );
                    self.action_u32(description, offset, consts::END_OF_CHAIN);
                }
            }
            None => {
                if let Some(offset) =
                    self.dir_entry_field_offset(stream_id, ENTRY_START_SECTOR)
                {
                    let description = format!(
                        "clear the start mini sector of directory entry \
                         {stream_id} ({owner})"
                    );
                    self.action_u32(description, offset, consts::END_OF_CHAIN);
                }
            }
        }
    }

    //=== Orphans ===//

    /// Mini sectors that are allocated in the MiniFAT but unreachable from
    /// any mini chain are orphans; plan to free them.
    fn audit_mini_orphans(&mut self) {
        for mini_sector in 0..self.repaired_minifat.len() as u32 {
            if self.repaired_minifat[mini_sector as usize]
                == consts::FREE_SECTOR
                || self.claimed_minis.contains_key(&mini_sector)
            {
                continue;
            }
            self.finding(
                CorruptionCategory::OrphanSector,
                Structure::MiniFat,
                Some(mini_sector),
                format!(
                    "mini sector {mini_sector} is allocated but not \
                     reachable from any mini chain"
                ),
            );
            self.repaired_minifat[mini_sector as usize] = consts::FREE_SECTOR;
            if let Some(offset) = self.minifat_entry_offset(mini_sector) {
                let description =
                    format!("free orphan mini sector {mini_sector}");
                self.action_u32(description, offset, consts::FREE_SECTOR);
            }
        }
    }

    /// Sectors that are allocated in the FAT but unreachable from any chain
    /// are orphans; plan to free them.
    fn audit_orphans(&mut self) {
        for sector in 0..self.num_sectors {
            if self.repaired_fat[sector as usize] == consts::FREE_SECTOR
                || self.claimed.contains_key(&sector)
            {
                continue;
            }
            self.finding(
                CorruptionCategory::OrphanSector,
                Structure::Fat,
                Some(sector),
                format!(
                    "sector {sector} is allocated but not reachable from \
                     any chain"
                ),
            );
            self.repaired_fat[sector as usize] = consts::FREE_SECTOR;
            if let Some(offset) = self.fat_entry_offset(sector) {
                let description = format!("free orphan sector {sector}");
                self.action_u32(description, offset, consts::FREE_SECTOR);
            }
        }
    }
}

//===========================================================================//
