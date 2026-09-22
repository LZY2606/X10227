//! Opt-in structural auditing of compound files.
//!
//! This module is entered the same way a compound file is normally opened:
//! [`audit_reader`] / [`audit_path`] take the exact same input as
//! [`crate::CompoundFile::open`], but instead of interpreting the file they
//! collect *evidence* of structural damage in the FAT, DIFAT, MiniFAT, and
//! directory chains, and produce a read-only [`RepairPlan`].  Auditing never
//! mutates the input (it only requires [`Read`] + [`Seek`]).
//!
//! The audit deliberately reuses the production parsing code
//! ([`Header::read_from`](crate::internal::Header::read_from),
//! [`Sectors`](crate::internal::Sectors),
//! [`DirEntry::read_from`](crate::internal::DirEntry::read_from)): it is a
//! tolerant, non-aborting front end over the same format primitives that the
//! normal open path uses, not a second parser kept only for the tests.
//!
//! Damage is reported as distinct [`FindingKind`]s: a loop, an
//! out-of-bounds reference, a cross-linked (doubly occupied) sector, an
//! orphan sector, or a declared-vs-actual length mismatch are never folded
//! into a single boolean.  Every finding records the first offending sector
//! and a human-readable message with the surrounding context.
//!
//! The returned [`RepairPlan`] carries the [`Summary`] (a digest of the
//! exact audited bytes).  That summary is the plan's *version identity*:
//! [`RepairPlan::dry_run`] and [`RepairPlan::apply`] recompute it and refuse
//! to touch the file if the bytes have changed since the plan was built.
//! `dry_run` cannot write at all (its argument is not writable).  `apply`
//! stages every edit and rolls all completed writes back if any write (or
//! the summary check) fails, so a failed apply never leaves a half-written
//! file.
//!
//! Nothing in this module keeps state between calls: each audit starts from
//! the input bytes and owns all of its working sets, so a failed or aborted
//! audit cannot leak caches, counters, or temporary state into a later call.

use std::fmt;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

use fnv::{FnvHashMap, FnvHashSet};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Sectors, Validation, Version};
use crate::ReadLeNumber;

// Byte offsets of fixed-size header fields (MS-CFB section 2.2).
const HEADER_OFFSET_NUM_DIR_SECTORS: u64 = 40;
const HEADER_OFFSET_NUM_FAT_SECTORS: u64 = 44;
const HEADER_OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const HEADER_OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
/// Byte offset of the starting-sector field within a 128-byte directory
/// entry (MS-CFB section 2.6.3).
const DIR_ENTRY_START_SECTOR_OFFSET: u64 = 116;

// FNV-1a (128-bit) constants; no crypto dependency is needed for detecting
// that the input bytes have changed since the plan was built.
const FNV128_OFFSET_BASIS: u128 = 0x6c62272e07bb014262b821756295c58d;
const FNV128_PRIME: u128 = 0x0000_0000_0000_0001_0000_0000_0000_013b;

// ===========================================================================
// Public types
// ===========================================================================

/// Which CFB allocation structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Structure {
    /// The file allocation table (MS-CFB section 2.3).
    Fat,
    /// The double-indirect FAT (header array plus DIFAT sectors).
    Difat,
    /// The mini stream allocation table.
    MiniFat,
    /// The chain of sectors holding directory entries.
    DirectoryChain,
}

impl fmt::Display for Structure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Structure::Fat => f.write_str("FAT"),
            Structure::Difat => f.write_str("DIFAT"),
            Structure::MiniFat => f.write_str("MiniFAT"),
            Structure::DirectoryChain => f.write_str("directory chain"),
        }
    }
}

/// The category of structural damage found by an audit.  These categories are
/// reported separately even when a single corruption causes more than one
/// (e.g. a FAT loop also makes one sector pointed to twice).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FindingKind {
    /// A chain reaches a sector already seen on that same chain.
    Loop,
    /// A chain or table entry refers to a sector or mini sector that does
    /// not exist.
    OutOfBounds,
    /// Two chains occupy the same sector (a cross-linked chain).
    DuplicateOccupancy,
    /// A sector is marked allocated but cannot be reached from any header
    /// pointer or directory entry.
    OrphanSector,
    /// A header-declared length does not match what is actually present.
    DeclaredLengthMismatch,
}

impl fmt::Display for FindingKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FindingKind::Loop => f.write_str("chain loop"),
            FindingKind::OutOfBounds => f.write_str("out-of-bounds reference"),
            FindingKind::DuplicateOccupancy => {
                f.write_str("duplicate sector occupancy (cross-linked chain)")
            }
            FindingKind::OrphanSector => f.write_str("orphan sector"),
            FindingKind::DeclaredLengthMismatch => {
                f.write_str("declared length mismatch")
            }
        }
    }
}

/// A single piece of corruption evidence produced by an audit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// The category of damage.
    pub kind: FindingKind,
    /// Which allocation structure contains it.
    pub structure: Structure,
    /// The first offending sector (or mini sector / FAT entry index).  `None`
    /// for whole-structure findings such as a declared-length mismatch.
    pub sector: Option<u32>,
    /// What is wrong, including the surrounding context (actual vs. expected
    /// counts, the two conflicting chain entries, etc.).
    pub message: String,
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} in the {}", self.kind, self.structure)?;
        if let Some(sector) = self.sector {
            write!(f, " at sector {sector}")?;
        }
        write!(f, ": {}", self.message)
    }
}

/// A content-addressed summary of the bytes a plan (or report) was computed
/// from.  It acts as a version identity: a plan only applies to bytes whose
/// summary is still exactly the one recorded here.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Summary {
    /// Length of the input in bytes.
    pub len: u64,
    /// 128-bit FNV-1a digest of the input bytes (hexadecimal in messages).
    pub digest: u128,
}

impl fmt::Display for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} bytes digest {:032x}", self.len, self.digest)
    }
}

impl Summary {
    /// Streams the whole input once and computes its length and digest,
    /// leaving the reader positioned at the start of the file.
    fn compute<F: Read + Seek>(inner: &mut F) -> io::Result<Summary> {
        inner.seek(SeekFrom::Start(0))?;
        let mut hash = FNV128_OFFSET_BASIS;
        let mut len: u64 = 0;
        let mut buffer = [0u8; 64 * 1024];
        loop {
            match inner.read(&mut buffer) {
                Ok(0) => break,
                Ok(n) => {
                    for &byte in &buffer[..n] {
                        hash ^= byte as u128;
                        hash = hash.wrapping_mul(FNV128_PRIME);
                    }
                    len += n as u64;
                }
                Err(ref err) if err.kind() == io::ErrorKind::Interrupted => {
                    continue
                }
                Err(err) => return Err(err),
            }
        }
        hash ^= len as u128;
        hash = hash.wrapping_mul(FNV128_PRIME);
        inner.seek(SeekFrom::Start(0))?;
        Ok(Summary { len, digest: hash })
    }
}

/// One planned four-byte write at an absolute file offset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PlannedEdit {
    /// Absolute byte offset within the file.
    pub offset: u64,
    /// The little-endian 32-bit value to write.
    pub value: u32,
}

/// A read-only proposal to repair one [`Finding`].  All edits are 32-bit
/// field/FAT-entry rewrites; the plan never needs to relocate or resize the
/// file.  An action whose edits are empty describes damage that requires
/// manual intervention (no deterministic value to write).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairAction {
    /// Category of damage this action addresses.
    pub kind: FindingKind,
    /// Allocation structure this action addresses.
    pub structure: Structure,
    /// First offending sector, copied from the finding.
    pub sector: Option<u32>,
    /// Human-readable description of what the action does.
    pub description: String,
    /// The writes the action consists of.
    pub edits: Vec<PlannedEdit>,
}

/// What a dry run found.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DryRunReport {
    /// Summary of the bytes the dry run actually saw.
    pub current_summary: Summary,
    /// Exactly the edits that a matching [`RepairPlan::apply`] would write,
    /// de-duplicated and sorted by offset.
    pub edits: Vec<PlannedEdit>,
}

/// A read-only repair plan produced by an audit.
///
/// The plan carries the [`Summary`] of the exact bytes it was computed from
/// as its version identity.  Neither [`RepairPlan::dry_run`] nor
/// [`RepairPlan::apply`] will touch a file whose current summary differs;
/// re-audit the changed input and build a fresh plan instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPlan {
    /// Summary of the bytes the plan was built from.
    pub pre_summary: Summary,
    /// One action per finding, in the same order.
    pub actions: Vec<RepairAction>,
}

impl RepairPlan {
    /// Returns true when the plan contains no writes.
    pub fn is_noop(&self) -> bool {
        self.actions.iter().all(|action| action.edits.is_empty())
    }

    /// The distinct edits the plan performs, de-duplicated by offset and
    /// sorted by offset.  Two findings that resolve to the same field
    /// collapse to one write.
    pub fn edits(&self) -> Vec<PlannedEdit> {
        let mut seen_offsets = FnvHashSet::default();
        let mut edits = Vec::new();
        for action in &self.actions {
            for edit in &action.edits {
                if seen_offsets.insert(edit.offset) {
                    edits.push(*edit);
                }
            }
        }
        edits.sort_by_key(|edit| edit.offset);
        edits
    }

    /// Verifies that the input still matches the plan's pre-image summary and
    /// reports the edits that *would* be written.  This never writes any
    /// byte: its argument is only readable.
    pub fn dry_run<F: Read + Seek>(
        &self,
        mut inner: F,
    ) -> io::Result<DryRunReport> {
        let current_summary = Summary::compute(&mut inner)?;
        self.require_matching_summary(current_summary)?;
        Ok(DryRunReport {
            current_summary,
            edits: self.edits(),
        })
    }

    /// Explicitly applies the plan to `inner`.
    ///
    /// The current summary must still equal the pre-image summary recorded in
    /// the plan; otherwise this returns an
    /// [`io::ErrorKind::InvalidData`] error without writing anything.  If any
    /// write (or [`Write::flush`]) fails, every completed write is restored
    /// to its original value before the error is returned, so the file is
    /// never left half-updated.  Retrying `apply` with unchanged input then
    /// succeeds.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<()> {
        let current_summary = Summary::compute(inner)?;
        self.require_matching_summary(current_summary)?;
        let edits = self.edits();

        // Snapshot the original four bytes at every target so that any later
        // failure can be rolled back.
        let mut backups: Vec<[u8; 4]> = Vec::with_capacity(edits.len());
        for edit in &edits {
            inner.seek(SeekFrom::Start(edit.offset))?;
            let mut backup = [0u8; 4];
            inner.read_exact(&mut backup)?;
            backups.push(backup);
        }

        let result = (|| -> io::Result<()> {
            for edit in &edits {
                inner.seek(SeekFrom::Start(edit.offset))?;
                inner.write_all(&edit.value.to_le_bytes())?;
            }
            inner.flush()
        })();

        if let Err(err) = result {
            // Best-effort rollback of every write we attempted (including
            // the one that failed, in case it was partially applied).
            for (i, backup) in backups.iter().enumerate() {
                if i >= edits.len() {
                    break;
                }
                let _ = inner.seek(SeekFrom::Start(edits[i].offset));
                let _ = inner.write_all(backup);
            }
            let _ = inner.flush();
            return Err(err);
        }
        Ok(())
    }

    fn require_matching_summary(&self, current: Summary) -> io::Result<()> {
        if current == self.pre_summary {
            Ok(())
        } else {
            invalid_data!(
                "Cannot apply repair plan: input has changed since the plan \
                 was built (plan pre-image: {}; current input: {})",
                self.pre_summary,
                current
            )
        }
    }
}

/// The result of a structural audit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuditReport {
    /// CFB version declared by the audited header.
    pub version: Version,
    /// Summary of the exact audited bytes.
    pub summary: Summary,
    /// Corruption evidence, in deterministic pass/order (DIFAT, FAT,
    /// directory chain, MiniFAT, orphan scan).
    pub findings: Vec<Finding>,
    /// Read-only repair plan bound to `summary`.
    pub plan: RepairPlan,
}

impl AuditReport {
    /// Returns true when no structural damage was found.
    pub fn is_healthy(&self) -> bool {
        self.findings.is_empty()
    }
}

/// Audits the compound file readable from `inner`, which must be the exact
/// same kind of argument accepted by [`crate::CompoundFile::open`].
///
/// This is the opt-in audit performed *instead of* a normal open: it reads
/// the file, but never modifies it.
pub fn audit_reader<F: Read + Seek>(inner: F) -> io::Result<AuditReport> {
    let mut inner = inner;
    let summary = Summary::compute(&mut inner)?;
    let inner_len = inner.seek(SeekFrom::End(0))?;
    if inner_len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            inner_len
        );
    }
    inner.seek(SeekFrom::Start(0))?;

    // Same header parser as the production open path.
    let header = Header::read_from(&mut inner, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len();
    if inner_len
        > (consts::MAX_REGULAR_SECTOR as u64 + 1) * (sector_len as u64)
    {
        invalid_data!(
            "Invalid CFB file ({} bytes is too large)",
            inner_len
        );
    }
    if inner_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            inner_len,
            sector_len
        );
    }

    // Same sector access layer as the production open path.
    let mut sectors = Sectors::new(version, inner_len, inner);
    let num_sectors = sectors.num_sectors();
    let entries_per_sector = sector_len / std::mem::size_of::<u32>();
    let mut audit = Audit::new(
        version,
        sector_len,
        num_sectors,
        entries_per_sector,
        summary,
    );
    audit.run(&header, &mut sectors)?;
    Ok(audit.into_report())
}

/// Opens the file at `path` read-only and audits it.  The file itself is not
/// modified.
pub fn audit_path<P: AsRef<Path>>(path: P) -> io::Result<AuditReport> {
    audit_reader(fs::File::open(path)?)
}

// ===========================================================================
// Audit engine
// ===========================================================================

/// A single staged 32-bit write, not yet exposed publicly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Edit {
    offset: u64,
    value: u32,
}

impl Edit {
    fn public(self) -> PlannedEdit {
        PlannedEdit { offset: self.offset, value: self.value }
    }
}

/// Working state for one audit.  Every audit builds a fresh `Audit`; nothing
/// is stored after it finishes, so there is no per-call state that could leak
/// into the next audit.
struct Audit {
    version: Version,
    sector_len: usize,
    num_sectors: u32,
    entries_per_sector: usize,
    summary: Summary,
    findings: Vec<Finding>,
    actions: Vec<RepairAction>,
}

impl Audit {
    fn new(
        version: Version,
        sector_len: usize,
        num_sectors: u32,
        entries_per_sector: usize,
        summary: Summary,
    ) -> Audit {
        Audit {
            version,
            sector_len,
            num_sectors,
            entries_per_sector,
            summary,
            findings: Vec::new(),
            actions: Vec::new(),
        }
    }

    fn into_report(self) -> AuditReport {
        AuditReport {
            version: self.version,
            summary: self.summary,
            findings: self.findings,
            plan: RepairPlan {
                pre_summary: self.summary,
                actions: self.actions,
            },
        }
    }

    /// Records one finding together with the action that repairs it.
    fn report(
        &mut self,
        kind: FindingKind,
        structure: Structure,
        sector: Option<u32>,
        message: String,
        description: String,
        edits: Vec<Edit>,
    ) {
        self.findings.push(Finding { kind, structure, sector, message });
        self.actions.push(RepairAction {
            kind,
            structure,
            sector,
            description,
            edits: edits.into_iter().map(Edit::public).collect(),
        });
    }

    /// Offset of entry `index` within a table whose sectors, in order, are
    /// `table_sector_ids`.  Returns None when the index falls outside the
    /// table sectors that exist.
    fn table_entry_offset(
        &self,
        table_sector_ids: &[u32],
        index: u32,
    ) -> Option<u64> {
        let sector_id = table_sector_ids
            .get(index as usize / self.entries_per_sector)?;
        Some(
            (u64::from(*sector_id) + 1) * self.sector_len as u64
                + u64::from(index as u32 % self.entries_per_sector as u32)
                    * 4,
        )
    }

    fn fat_entry_edit(
        &self,
        fat_sector_ids: &[u32],
        index: u32,
        value: u32,
    ) -> Option<Edit> {
        Some(Edit {
            offset: self.table_entry_offset(fat_sector_ids, index)?,
            value,
        })
    }

    fn header_edit(offset: u64, value: u32) -> Edit {
        Edit { offset, value }
    }

    /// Offset/edit of MiniFAT entry `index`.
    fn minifat_entry_edit(
        &self,
        minifat_sector_ids: &[u32],
        index: usize,
    ) -> Option<Edit> {
        let sector_id = minifat_sector_ids
            .get(index / self.entries_per_sector)?;
        Some(Edit {
            offset: (u64::from(*sector_id) + 1) * self.sector_len as u64
                + (index % self.entries_per_sector) as u64 * 4,
            value: consts::END_OF_CHAIN,
        })
    }

    /// Runs all audit passes against `sectors`.  Each pass is tolerant:
    /// damage is collected as findings instead of aborting, but genuine I/O
    /// failures from the underlying reader still propagate as errors.
    fn run<F: Read + Seek>(
        &mut self,
        header: &Header,
        sectors: &mut Sectors<F>,
    ) -> io::Result<()> {
        // ---- DIFAT (header array + DIFAT sector chain) ------------------
        let (difat_sector_ids, fat_sector_ids, difat_clean) =
            self.audit_difat(header, sectors)?;

        // ---- FAT ---------------------------------------------------------
        let fat = self.read_fat(sectors, &fat_sector_ids)?;
        let fat_len = fat.len().min(self.num_sectors as usize);
        self.audit_fat(&fat_sector_ids, &fat, fat_len);

        // ---- Directory chain ---------------------------------------------
        let (dir_sector_ids, dir_clean) =
            self.audit_directory_chain(header, &fat, fat_len, sectors)?;
        let dir_entries = self.read_dir_entries(&dir_sector_ids, sectors)?;
        if self.version == Version::V4
            && dir_clean
            && header.num_dir_sectors as usize != dir_sector_ids.len()
        {
            let actual = dir_sector_ids.len() as u32;
            self.report(
                FindingKind::DeclaredLengthMismatch,
                Structure::DirectoryChain,
                None,
                format!(
                    "header declares {} directory sectors, but the \
                     directory chain contains {actual}",
                    header.num_dir_sectors
                ),
                format!(
                    "Set header num_dir_sectors field to {actual}."
                ),
                vec![Self::header_edit(
                    HEADER_OFFSET_NUM_DIR_SECTORS,
                    actual,
                )],
            );
        }

        // ---- MiniFAT -----------------------------------------------------
        let (minifat_sector_ids, minifat_clean) =
            self.audit_minifat_chain(header, &fat, fat_len, sectors)?;
        let minifat = self.read_u32_table(sectors, &minifat_sector_ids)?;
        if minifat_clean
            && header.num_minifat_sectors as usize
                != minifat_sector_ids.len()
        {
            let actual = minifat_sector_ids.len() as u32;
            self.report(
                FindingKind::DeclaredLengthMismatch,
                Structure::MiniFat,
                None,
                format!(
                    "header declares {} MiniFAT sectors, but the MiniFAT \
                     chain contains {actual}",
                    header.num_minifat_sectors
                ),
                format!(
                    "Set header num_minifat_sectors field to {actual}."
                ),
                vec![Self::header_edit(
                    HEADER_OFFSET_NUM_MINIFAT_SECTORS,
                    actual,
                )],
            );
        }
        self.audit_minifat(&minifat_sector_ids, &minifat, &dir_entries);

        // ---- Orphan sectors ----------------------------------------------
        self.audit_orphans(
            &fat_sector_ids,
            &difat_sector_ids,
            &dir_sector_ids,
            &minifat_sector_ids,
            &fat,
            fat_len,
            &dir_entries,
        );
        Ok(())
    }
}

impl Audit {
    /// Reads all 32-bit entries from the given ordered list of sectors.
    fn read_u32_table<F: Read + Seek>(
        &mut self,
        sectors: &mut Sectors<F>,
        table_sector_ids: &[u32],
    ) -> io::Result<Vec<u32>> {
        let mut entries = Vec::new();
        for &sector_id in table_sector_ids {
            let mut sector = sectors.seek_to_sector(sector_id)?;
            for _ in 0..self.entries_per_sector {
                entries.push(sector.read_le_u32()?);
            }
        }
        Ok(entries)
    }

    fn audit_difat<F: Read + Seek>(
        &mut self,
        header: &Header,
        sectors: &mut Sectors<F>,
    ) -> io::Result<(Vec<u32>, Vec<u32>, bool)> {
        let mut fat_sector_ids = Vec::<u32>::new();
        let mut seen_fat_sector_ids = FnvHashSet::default();
        let mut clean = true;

        // FAT sectors listed in the header's initial DIFAT array.
        for &sector_id in header.initial_difat_entries.iter() {
            if sector_id == consts::FREE_SECTOR {
                continue;
            }
            // Header::read_from already guarantees sector_id <=
            // MAX_REGULAR_SECTOR.
            if sector_id >= self.num_sectors {
                clean = false;
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::Difat,
                    Some(sector_id),
                    format!(
                        "initial DIFAT array refers to sector {sector_id}, \
                         but sector count is only {}",
                        self.num_sectors
                    ),
                    format!(
                        "Remove the out-of-bounds FAT sector reference \
                         {sector_id} from the initial DIFAT array."
                    ),
                    Vec::new(),
                );
                continue;
            }
            if !seen_fat_sector_ids.insert(sector_id) {
                clean = false;
                self.report(
                    FindingKind::DuplicateOccupancy,
                    Structure::Difat,
                    Some(sector_id),
                    format!(
                        "sector {sector_id} is listed as a FAT sector more \
                         than once in the initial DIFAT array"
                    ),
                    format!(
                        "Remove the duplicate FAT sector listing {sector_id}."
                    ),
                    Vec::new(),
                );
                continue;
            }
            fat_sector_ids.push(sector_id);
        }

        // DIFAT sector chain (starting in the header).
        let mut difat_sector_ids = Vec::<u32>::new();
        let mut seen_difat_sector_ids = FnvHashSet::default();
        let mut current = header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                clean = false;
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::Difat,
                    Some(current),
                    format!(
                        "DIFAT chain includes sector {current}, but sector \
                         count is only {}",
                        self.num_sectors
                    ),
                    format!(
                        "Terminate the DIFAT chain at its last valid sector."
                    ),
                    Vec::new(),
                );
                break;
            }
            if !seen_difat_sector_ids.insert(current) {
                clean = false;
                self.report(
                    FindingKind::Loop,
                    Structure::Difat,
                    Some(current),
                    format!(
                        "DIFAT chain loops back to sector {current}"
                    ),
                    format!(
                        "Terminate the DIFAT chain at its last non-repeated \
                         sector."
                    ),
                    Vec::new(),
                );
                break;
            }
            difat_sector_ids.push(current);
            let entries =
                self.read_u32_table(sectors, std::slice::from_ref(&current))?;
            for &sector_id in entries[..self.entries_per_sector - 1].iter() {
                if sector_id == consts::FREE_SECTOR {
                    continue;
                }
                if sector_id > consts::MAX_REGULAR_SECTOR
                    || sector_id >= self.num_sectors
                {
                    clean = false;
                    self.report(
                        FindingKind::OutOfBounds,
                        Structure::Difat,
                        Some(sector_id),
                        format!(
                            "DIFAT sector {current} refers to sector \
                             {sector_id}, but sector count is only {}",
                            self.num_sectors
                        ),
                        format!(
                            "Remove the out-of-bounds FAT sector reference \
                             {sector_id} from DIFAT sector {current}."
                        ),
                        Vec::new(),
                    );
                    continue;
                }
                if !seen_fat_sector_ids.insert(sector_id) {
                    clean = false;
                    self.report(
                        FindingKind::DuplicateOccupancy,
                        Structure::Difat,
                        Some(sector_id),
                        format!(
                            "sector {sector_id} is listed as a FAT sector \
                             more than once in the DIFAT"
                        ),
                        format!(
                            "Remove the duplicate FAT sector listing \
                             {sector_id}."
                        ),
                        Vec::new(),
                    );
                    continue;
                }
                fat_sector_ids.push(sector_id);
            }
            current = *entries.last().unwrap();
        }

        // Declared-length checks are only meaningful when the chains walked
        // cleanly; otherwise the discrepancy is just a consequence of the
        // earlier damage and gets covered by that finding.
        if clean
            && header.num_difat_sectors as usize != difat_sector_ids.len()
        {
            let actual = difat_sector_ids.len() as u32;
            self.report(
                FindingKind::DeclaredLengthMismatch,
                Structure::Difat,
                None,
                format!(
                    "header declares {} DIFAT sectors, but the DIFAT chain \
                     contains {actual}",
                    header.num_difat_sectors
                ),
                format!(
                    "Set header num_difat_sectors field to {actual}."
                ),
                vec![Self::header_edit(
                    HEADER_OFFSET_NUM_DIFAT_SECTORS,
                    actual,
                )],
            );
        }
        if clean && header.num_fat_sectors as usize != fat_sector_ids.len() {
            let actual = fat_sector_ids.len() as u32;
            self.report(
                FindingKind::DeclaredLengthMismatch,
                Structure::Fat,
                None,
                format!(
                    "header declares {} FAT sectors, but the DIFAT lists \
                     {actual}",
                    header.num_fat_sectors
                ),
                format!("Set header num_fat_sectors field to {actual}."),
                vec![Self::header_edit(HEADER_OFFSET_NUM_FAT_SECTORS, actual)],
            );
        }

        Ok((difat_sector_ids, fat_sector_ids, clean))
    }

    /// Reads the raw FAT, padding missing trailing entries with FREE_SECTOR
    /// exactly as the production open path does.
    fn read_fat<F: Read + Seek>(
        &mut self,
        sectors: &mut Sectors<F>,
        fat_sector_ids: &[u32],
    ) -> io::Result<Vec<u32>> {
        let mut fat = Vec::new();
        for &sector_id in fat_sector_ids {
            // All listed sectors have been bounds-checked during the DIFAT
            // pass, so any error here is a genuine I/O failure and must
            // propagate (and therefore be retriable) rather than be hidden
            // behind an empty table.
            let entries =
                self.read_u32_table(sectors, std::slice::from_ref(&sector_id))?;
            fat.extend(entries);
        }
        while fat.len() < self.num_sectors as usize {
            fat.push(consts::FREE_SECTOR);
        }
        Ok(fat)
    }
}

impl Audit {
    /// FAT-wide checks: out-of-bounds pointers, cross-linked chains
    /// (duplicate occupancy), and loops.
    fn audit_fat(&mut self, fat_sector_ids: &[u32], fat: &[u32], fat_len: usize) {
        // Out-of-bounds pointers.
        for (index, &next_sector) in fat[..fat_len].iter().enumerate() {
            if next_sector <= consts::MAX_REGULAR_SECTOR
                && next_sector >= self.num_sectors
            {
                let index = index as u32;
                let edit = self.fat_entry_edit(
                    fat_sector_ids,
                    index,
                    consts::END_OF_CHAIN,
                );
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::Fat,
                    Some(index),
                    format!(
                        "FAT entry {index} points to sector {next_sector}, \
                         but sector count is only {}",
                        self.num_sectors
                    ),
                    format!(
                        "Terminate the chain at FAT entry {index} (set it to \
                         END_OF_CHAIN)."
                    ),
                    edit.into_iter().collect(),
                );
            }
        }

        // Duplicate occupancy (cross-linked chains).  The first pointer
        // wins, in ascending FAT-entry order, so both the finding and its
        // repair are deterministic regardless of how the caller enumerates
        // or schedules the audit.
        let mut pointees = FnvHashMap::<u32, u32>::default();
        for (index, &next_sector) in fat[..fat_len].iter().enumerate() {
            if next_sector <= consts::MAX_REGULAR_SECTOR
                && next_sector < self.num_sectors
            {
                if let Some(&first_owner) = pointees.get(&next_sector) {
                    let index = index as u32;
                    let edit = self.fat_entry_edit(
                        fat_sector_ids,
                        index,
                        consts::END_OF_CHAIN,
                    );
                    self.report(
                        FindingKind::DuplicateOccupancy,
                        Structure::Fat,
                        Some(next_sector),
                        format!(
                            "sector {next_sector} is pointed to by both FAT \
                             entry {first_owner} and FAT entry {index} \
                             (cross-linked chains)"
                        ),
                        format!(
                            "Detach the later pointer: set FAT entry {index} \
                             to END_OF_CHAIN, leaving sector {next_sector} \
                             owned by entry {first_owner}."
                        ),
                        edit.into_iter().collect(),
                    );
                } else {
                    pointees.insert(next_sector, index as u32);
                }
            }
        }

        // Loops.  Each chain is walked once with an explicit per-chain
        // visited set, so a corrupt file can never make the audit spin.
        const UNVISITED: u8 = 0;
        const IN_STACK: u8 = 1;
        const DONE: u8 = 2;
        let mut state = vec![UNVISITED; fat_len];
        for start in 0..fat_len {
            if state[start] != UNVISITED {
                continue;
            }
            let mut path = Vec::new();
            let mut current = start;
            loop {
                if state[current] == DONE {
                    break;
                }
                if state[current] == IN_STACK {
                    let predecessor = *path.last().unwrap() as u32;
                    let repeated = current as u32;
                    let edit = self.fat_entry_edit(
                        fat_sector_ids,
                        predecessor,
                        consts::END_OF_CHAIN,
                    );
                    self.report(
                        FindingKind::Loop,
                        Structure::Fat,
                        Some(repeated),
                        format!(
                            "FAT entry {predecessor} points back to sector \
                             {repeated}, forming a loop"
                        ),
                        format!(
                            "Break the loop by setting FAT entry \
                             {predecessor} to END_OF_CHAIN."
                        ),
                        edit.into_iter().collect(),
                    );
                    break;
                }
                state[current] = IN_STACK;
                path.push(current);
                let next_sector = fat[current];
                if next_sector > consts::MAX_REGULAR_SECTOR
                    || next_sector as usize >= fat_len
                {
                    break;
                }
                current = next_sector as usize;
            }
            for node in path {
                state[node] = DONE;
            }
        }
    }

    /// Follows the directory chain through the FAT, recording loops and
    /// out-of-bounds (truncated) links instead of aborting.
    fn audit_directory_chain<F: Read + Seek>(
        &mut self,
        header: &Header,
        fat: &[u32],
        fat_len: usize,
        sectors: &mut Sectors<F>,
    ) -> io::Result<(Vec<u32>, bool)> {
        let _ = sectors;
        let mut sector_ids = Vec::new();
        let mut seen = FnvHashSet::default();
        let mut clean = true;
        let mut current = header.first_dir_sector;
        while current != consts::END_OF_CHAIN {
            let damage = if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                Some((
                    FindingKind::OutOfBounds,
                    format!(
                        "directory chain includes sector {current}, but \
                         sector count is only {}",
                        self.num_sectors
                    ),
                ))
            } else if !seen.insert(current) {
                Some((
                    FindingKind::Loop,
                    format!(
                        "directory chain loops back to sector {current}"
                    ),
                ))
            } else {
                None
            };
            if let Some((kind, message)) = damage {
                clean = false;
                // The FAT-level pass already records the FAT-entry edit
                // that repairs the link, so this action intentionally
                // carries no separate write (edits de-duplicate by offset
                // when the plan is applied).
                self.report(
                    kind,
                    Structure::DirectoryChain,
                    Some(current),
                    message,
                    "Directory chain damage is repaired through the FAT \
                     evidence for the same entry; no separate write is \
                     needed."
                        .to_string(),
                    Vec::new(),
                );
                break;
            }
            sector_ids.push(current);
            current = if (current as usize) < fat_len {
                fat[current as usize]
            } else {
                consts::END_OF_CHAIN
            };
        }
        Ok((sector_ids, clean))
    }

    /// Parses directory entries from the reachable directory sectors using
    /// the production [`DirEntry`] parser, and records each entry's file
    /// offset so that stream start-sector repairs are possible.
    fn read_dir_entries<F: Read + Seek>(
        &mut self,
        dir_sector_ids: &[u32],
        sectors: &mut Sectors<F>,
    ) -> io::Result<Vec<(DirEntry, u64)>> {
        let mut entries = Vec::new();
        for &sector_id in dir_sector_ids {
            let mut sector = sectors.seek_to_sector(sector_id)?;
            let mut bytes = vec![0u8; self.sector_len];
            io::Read::read_exact(&mut sector, &mut bytes)?;
            for (index, chunk) in
                bytes.chunks(consts::DIR_ENTRY_LEN).enumerate()
            {
                if let Ok(entry) = DirEntry::read_from(
                    &mut &chunk[..],
                    self.version,
                    Validation::Permissive,
                ) {
                    let offset = (u64::from(sector_id) + 1)
                        * self.sector_len as u64
                        + (index * consts::DIR_ENTRY_LEN) as u64;
                    entries.push((entry, offset));
                }
            }
        }
        Ok(entries)
    }
}

impl Audit {
    /// Follows the MiniFAT's FAT chain.
    fn audit_minifat_chain<F: Read + Seek>(
        &mut self,
        header: &Header,
        fat: &[u32],
        fat_len: usize,
        sectors: &mut Sectors<F>,
    ) -> io::Result<(Vec<u32>, bool)> {
        let _ = sectors;
        let mut sector_ids = Vec::new();
        let mut seen = FnvHashSet::default();
        let mut clean = true;
        let mut current = header.first_minifat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                clean = false;
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::MiniFat,
                    Some(current),
                    format!(
                        "MiniFAT chain includes sector {current}, but sector \
                         count is only {}",
                        self.num_sectors
                    ),
                    "Terminate the MiniFAT chain at its last valid sector."
                        .to_string(),
                    Vec::new(),
                );
                break;
            }
            if !seen.insert(current) {
                clean = false;
                self.report(
                    FindingKind::Loop,
                    Structure::MiniFat,
                    Some(current),
                    format!("MiniFAT chain loops back to sector {current}"),
                    "Terminate the MiniFAT chain before the repeated sector."
                        .to_string(),
                    Vec::new(),
                );
                break;
            }
            sector_ids.push(current);
            current = if (current as usize) < fat_len {
                fat[current as usize]
            } else {
                consts::END_OF_CHAIN
            };
        }
        Ok((sector_ids, clean))
    }

    /// MiniFAT table checks: entries beyond the table/mini stream
    /// (out of bounds), cross-linked mini sectors, and mini-chain loops.
    fn audit_minifat(
        &mut self,
        minifat_sector_ids: &[u32],
        minifat: &[u32],
        dir_entries: &[(DirEntry, u64)],
    ) {
        let table_len = minifat.len();
        let root_entry = dir_entries
            .iter()
            .find(|(entry, _)| entry.obj_type == ObjType::Root)
            .map(|(entry, _)| entry);
        let mini_stream_mini_sectors = root_entry
            .map(|entry| entry.stream_len / consts::MINI_SECTOR_LEN as u64);



        // The table itself must fit inside the mini stream.
        if let Some(mini_sector_count) = mini_stream_mini_sectors {
            if table_len as u64 > mini_sector_count {
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::MiniFat,
                    None,
                    format!(
                        "MiniFAT has {table_len} entries, but the mini stream \
                         holds only {mini_sector_count} mini sectors"
                    ),
                    "The MiniFAT is longer than the mini stream; rebuild or \
                     truncate the MiniFAT manually."
                        .to_string(),
                    Vec::new(),
                );
            }
        }

        // Per-entry out-of-bounds references.
        for (index, &next_mini_sector) in minifat.iter().enumerate() {
            if next_mini_sector > consts::MAX_REGULAR_SECTOR {
                continue;
            }
            let edit = self.minifat_entry_edit(minifat_sector_ids, index).into_iter().collect();
            if next_mini_sector as usize >= table_len {
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::MiniFat,
                    Some(index as u32),
                    format!(
                        "MiniFAT entry {index} refers to mini sector \
                         {next_mini_sector}, but the MiniFAT has only \
                         {table_len} entries"
                    ),
                    format!(
                        "Terminate the mini chain at MiniFAT entry {index} \
                         (set it to END_OF_CHAIN)."
                    ),
                    edit,
                );
            } else if let Some(mini_sector_count) = mini_stream_mini_sectors {
                if u64::from(next_mini_sector) >= mini_sector_count {
                    self.report(
                        FindingKind::OutOfBounds,
                        Structure::MiniFat,
                        Some(index as u32),
                        format!(
                            "MiniFAT entry {index} refers to mini sector \
                             {next_mini_sector}, but the mini stream holds \
                             only {mini_sector_count} mini sectors"
                        ),
                        format!(
                            "Terminate the mini chain at MiniFAT entry \
                             {index} (set it to END_OF_CHAIN)."
                        ),
                        edit,
                    );
                }
            }
        }

        // Duplicate occupancy within the MiniFAT.
        let mut pointees = FnvHashMap::<u32, u32>::default();
        for (index, &next_mini_sector) in minifat.iter().enumerate() {
            if next_mini_sector <= consts::MAX_REGULAR_SECTOR
                && next_mini_sector as usize < table_len
            {
                if let Some(&first_owner) = pointees.get(&next_mini_sector) {
                    let edit = self.minifat_entry_edit(minifat_sector_ids, index).into_iter().collect();
                    self.report(
                        FindingKind::DuplicateOccupancy,
                        Structure::MiniFat,
                        Some(next_mini_sector),
                        format!(
                            "mini sector {next_mini_sector} is pointed to by \
                             both MiniFAT entry {first_owner} and MiniFAT \
                             entry {index} (cross-linked mini chains)"
                        ),
                        format!(
                            "Detach the later mini-chain pointer: set \
                             MiniFAT entry {index} to END_OF_CHAIN."
                        ),
                        edit,
                    );
                } else {
                    pointees.insert(next_mini_sector, index as u32);
                }
            }
        }

        // Loops within the MiniFAT.
        const UNVISITED: u8 = 0;
        const IN_STACK: u8 = 1;
        const DONE: u8 = 2;
        let mut state = vec![UNVISITED; table_len];
        for start in 0..table_len {
            if state[start] != UNVISITED {
                continue;
            }
            let mut path = Vec::new();
            let mut current = start;
            loop {
                if state[current] == DONE {
                    break;
                }
                if state[current] == IN_STACK {
                    let predecessor = *path.last().unwrap();
                    let repeated = current as u32;
                    let edit =
                        self.minifat_entry_edit(minifat_sector_ids, predecessor).into_iter().collect();
                    self.report(
                        FindingKind::Loop,
                        Structure::MiniFat,
                        Some(repeated),
                        format!(
                            "MiniFAT entry {predecessor} points back to mini \
                             sector {repeated}, forming a loop"
                        ),
                        format!(
                            "Break the mini loop by setting MiniFAT entry \
                             {predecessor} to END_OF_CHAIN."
                        ),
                        edit,
                    );
                    break;
                }
                state[current] = IN_STACK;
                path.push(current);
                let next_mini_sector = minifat[current];
                if next_mini_sector > consts::MAX_REGULAR_SECTOR
                    || next_mini_sector as usize >= table_len
                {
                    break;
                }
                current = next_mini_sector as usize;
            }
            for node in path {
                state[node] = DONE;
            }
        }

        // Stream start sectors declared by directory entries.
        for (entry, dir_entry_offset) in dir_entries {
            if entry.obj_type != ObjType::Stream || entry.stream_len == 0 {
                continue;
            }
            if entry.start_sector > consts::MAX_REGULAR_SECTOR {
                continue;
            }
            if entry.stream_len < u64::from(consts::MINI_STREAM_CUTOFF) {
                let bound = mini_stream_mini_sectors
                    .filter(|_| entry.start_sector as u64 < table_len as u64);
                if entry.start_sector as usize >= table_len
                    || bound
                        .is_some_and(|count| entry.start_sector as u64 >= count)
                {
                    let edit = Edit {
                        offset: dir_entry_offset
                            + DIR_ENTRY_START_SECTOR_OFFSET,
                        value: consts::END_OF_CHAIN,
                    };
                    self.report(
                        FindingKind::OutOfBounds,
                        Structure::MiniFat,
                        Some(entry.start_sector),
                        format!(
                            "mini stream {:?} starts at mini sector {}, \
                             outside the MiniFAT/mini stream",
                            entry.name, entry.start_sector
                        ),
                        format!(
                            "Clear the starting sector of mini stream {:?} \
                             (set it to END_OF_CHAIN).",
                            entry.name
                        ),
                        vec![edit],
                    );
                }
            } else if entry.start_sector >= self.num_sectors {
                let edit = Edit {
                    offset: dir_entry_offset + DIR_ENTRY_START_SECTOR_OFFSET,
                    value: consts::END_OF_CHAIN,
                };
                self.report(
                    FindingKind::OutOfBounds,
                    Structure::Fat,
                    Some(entry.start_sector),
                    format!(
                        "regular stream {:?} starts at sector {}, but sector \
                         count is only {}",
                        entry.name, entry.start_sector, self.num_sectors
                    ),
                    format!(
                        "Clear the starting sector of stream {:?} (set it to \
                         END_OF_CHAIN).",
                        entry.name
                    ),
                    vec![edit],
                );
            }
        }
    }
}

impl Audit {
    /// Finds allocated sectors that no chain can reach.
    #[allow(clippy::too_many_arguments)]
    fn audit_orphans(
        &mut self,
        fat_sector_ids: &[u32],
        difat_sector_ids: &[u32],
        dir_sector_ids: &[u32],
        minifat_sector_ids: &[u32],
        fat: &[u32],
        fat_len: usize,
        dir_entries: &[(DirEntry, u64)],
    ) {
        let mut reachable = FnvHashSet::default();
        reachable.extend(fat_sector_ids.iter().copied());
        reachable.extend(difat_sector_ids.iter().copied());
        reachable.extend(dir_sector_ids.iter().copied());
        reachable.extend(minifat_sector_ids.iter().copied());

        // Walk a FAT chain, stopping safely on loops (a chain sector already
        // in `reachable` has already been walked).
        let walk_chain = |start_sector: u32, reachable: &mut FnvHashSet<u32>| {
            let mut current = start_sector;
            while current <= consts::MAX_REGULAR_SECTOR
                && (current as usize) < fat_len
                && reachable.insert(current)
            {
                let next_sector = fat[current as usize];
                if next_sector > consts::MAX_REGULAR_SECTOR
                    || next_sector as usize >= fat_len
                {
                    break;
                }
                current = next_sector;
            }
        };

        // The root entry's chain is the mini stream container.
        if let Some((root_entry, _)) = dir_entries
            .iter()
            .find(|(entry, _)| entry.obj_type == ObjType::Root)
        {
            walk_chain(root_entry.start_sector, &mut reachable);
        }
        // Regular stream chains.
        for (entry, _) in dir_entries {
            if entry.obj_type == ObjType::Stream
                && entry.stream_len >= u64::from(consts::MINI_STREAM_CUTOFF)
            {
                walk_chain(entry.start_sector, &mut reachable);
            }
        }

        for sector_id in 0..self.num_sectors {
            let index = sector_id as usize;
            if index >= fat_len {
                break;
            }
            let entry = fat[index];
            if entry != consts::FREE_SECTOR
                && !reachable.contains(&sector_id)
            {
                let edit = self
                    .fat_entry_edit(
                        fat_sector_ids,
                        sector_id,
                        consts::FREE_SECTOR,
                    )
                    .into_iter()
                    .collect();
                self.report(
                    FindingKind::OrphanSector,
                    Structure::Fat,
                    Some(sector_id),
                    format!(
                        "sector {sector_id} is marked allocated (FAT entry \
                         0x{entry:08X}) but cannot be reached from the \
                         DIFAT, directory chain, MiniFAT, mini stream, or \
                         any stream chain"
                    ),
                    format!(
                        "Mark orphan sector {sector_id} as FREE in the FAT."
                    ),
                    edit,
                );
            }
        }
    }
}

// ===========================================================================
