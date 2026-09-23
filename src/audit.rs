//! Opt-in structural auditing of compound files.
//!
//! Unlike the normal open path, which reports the first fatal error it finds
//! (or tolerates known spec violations under permissive validation), an audit
//! reads a compound file without mutating it and collects *every* piece of
//! allocation-table corruption it can prove, grouped by both the allocation
//! structure involved (FAT, DIFAT, MiniFAT, directory chain, mini stream) and
//! the category of corruption (loops, out-of-bounds references, duplicate
//! allocation / crossed chains, orphan sectors, and declared-length
//! mismatches).
//!
//! Along with the evidence, an audit produces a [`RepairPlan`].  The plan
//! never modifies anything by itself: it carries a digest of the input that
//! serves as the version identity of the bytes it was generated for.  Its
//! [`RepairPlan::dry_run`] method cannot write (it only accepts a
//! [`Read`](std::io::Read) plus [`Seek`](std::io::Seek)), and
//! [`RepairPlan::apply`] refuses to touch the input unless the current digest
//! still matches the recorded one.  All edits are staged on an in-memory copy
//! first, so a failed application leaves the input unchanged.
//!
//! The audit reuses the production parsing entry points ([`Header::read_from`]
//! and [`DirEntry::read_from`]) and the same sector layout constants as the
//! normal open path; only the treatment of the allocation tables is
//! intentionally more tolerant, so that one damaged chain does not hide the
//! rest of the evidence.

use std::fmt;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

use fnv::{FnvHashMap, FnvHashSet};

use crate::internal::{consts, DirEntry, Header, ObjType, Validation};

// Byte offsets of the u32 fields in the CFB header that repair plans may
// rewrite.  These are fixed by the CFB format (see MS-CFB section 2.2).
const HEADER_NUM_DIR_SECTORS_OFFSET: u64 = 40;
const HEADER_NUM_FAT_SECTORS_OFFSET: u64 = 44;
const HEADER_NUM_MINIFAT_SECTORS_OFFSET: u64 = 64;
const HEADER_NUM_DIFAT_SECTORS_OFFSET: u64 = 72;

//===========================================================================//

/// An allocation structure within a compound file that corruption evidence
/// may refer to.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AuditArea {
    /// The double-indirect FAT (the chain of DIFAT sectors and the FAT-sector
    /// pointers reachable from it).
    Difat,
    /// The regular file allocation table.
    Fat,
    /// The mini-sector allocation table.
    MiniFat,
    /// The sector chain holding the directory entries.
    DirectoryChain,
    /// The mini stream (the root entry's regular-sector chain, plus the
    /// directory entries that claim mini sectors from it).
    MiniStream,
}

impl fmt::Display for AuditArea {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            AuditArea::Difat => "DIFAT",
            AuditArea::Fat => "FAT",
            AuditArea::MiniFat => "MiniFAT",
            AuditArea::DirectoryChain => "directory chain",
            AuditArea::MiniStream => "mini stream",
        };
        f.write_str(name)
    }
}

/// The category of corruption recorded by an audit.
///
/// Loops, out-of-bounds references, duplicate allocation, orphan sectors, and
/// declared-length mismatches are always reported as separate findings, even
/// when a single damaged input triggers several of them.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorruptionKind {
    /// A chain pointer reaches a sector or mini sector already seen in the
    /// same chain (a cycle).
    Loop,
    /// A reference points past the end of the file, past the end of the
    /// allocation table, or uses a reserved invalid index.
    OutOfBounds,
    /// Two chains point into the same sector (crossed chains).
    DuplicateAllocation,
    /// A sector is marked allocated but cannot be reached from any chain root.
    OrphanSector,
    /// A count declared in the header or by the directory entries does not
    /// match what the allocation tables actually contain.
    LengthMismatch,
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            CorruptionKind::Loop => "loop",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DuplicateAllocation => {
                "duplicate allocation (crossed chains)"
            }
            CorruptionKind::OrphanSector => "orphan sector",
            CorruptionKind::LengthMismatch => "declared-length mismatch",
        };
        f.write_str(name)
    }
}

/// One piece of corruption evidence.
///
/// Each finding records the first position where the invariant fails (a
/// sector or mini-sector index) and enough surrounding context to explain it,
/// rather than merely returning success or failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Corruption {
    kind: CorruptionKind,
    area: AuditArea,
    sector: Option<u32>,
    detail: String,
}

impl Corruption {
    /// Returns the category of the corruption.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }

    /// Returns which allocation structure contains the corruption.
    pub fn area(&self) -> AuditArea {
        self.area
    }

    /// Returns the sector or mini-sector index of the first violation, if the
    /// finding is tied to one.
    pub fn sector(&self) -> Option<u32> {
        self.sector
    }

    /// Returns a human-readable description of the corruption, including the
    /// context around the first violation.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.sector {
            Some(sector) => write!(
                f,
                "{} at sector {}: {}",
                self.area, sector, self.detail
            ),
            None => write!(f, "{}: {}", self.area, self.detail),
        }
    }
}

//===========================================================================//

/// The result of auditing a compound file: the corruption evidence found,
/// together with a read-only repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuditReport {
    corruptions: Vec<Corruption>,
    plan: RepairPlan,
}

impl AuditReport {
    /// Returns true if no corruption was found and the repair plan contains
    /// no actions.
    pub fn is_clean(&self) -> bool {
        self.corruptions.is_empty() && self.plan.actions.is_empty()
    }

    /// Returns all corruption findings, in a stable, deterministic order.
    pub fn corruptions(&self) -> &[Corruption] {
        &self.corruptions
    }

    /// Returns the read-only repair plan derived from the findings.
    pub fn repair_plan(&self) -> &RepairPlan {
        &self.plan
    }
}

//===========================================================================//

/// Which on-disk structure a [`RepairAction`] rewrites.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RepairTarget {
    /// A `u32` field of the 512-byte file header.
    Header,
    /// One FAT entry.
    Fat,
    /// One MiniFAT entry.
    MiniFat,
}

/// One planned, in-place four-byte edit of the audited file image.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairAction {
    target: RepairTarget,
    offset: u64,
    value: u32,
    description: String,
}

impl RepairAction {
    /// Returns the structure this action rewrites.
    pub fn target(&self) -> RepairTarget {
        self.target
    }

    /// Returns the absolute byte offset within the file image where the
    /// little-endian `u32` value will be written.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Returns the little-endian `u32` value that would be written.
    pub fn value(&self) -> u32 {
        self.value
    }

    /// Returns a human-readable description of the action.
    pub fn description(&self) -> &str {
        &self.description
    }
}

impl fmt::Display for RepairAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.description)
    }
}

//===========================================================================//

/// A digest of the exact file bytes a [`RepairPlan`] was generated for.
///
/// This is the plan's version identity: a plan can only be applied to an
/// input whose digest is identical.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PreconditionDigest {
    len: u64,
    fnv1a_64: u64,
}

impl PreconditionDigest {
    /// Returns the length in bytes of the digested image.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns true only for a zero-length image.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the 64-bit FNV-1a hash of the digested image.
    pub fn hash(&self) -> u64 {
        self.fnv1a_64
    }
}

impl fmt::Display for PreconditionDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "len={},fnv1a={:016x}", self.len, self.fnv1a_64)
    }
}

//===========================================================================//

/// A read-only description of what applying a [`RepairPlan`] *would* do.
///
/// Computing this never writes a byte: [`RepairPlan::dry_run`] only accepts a
/// reader.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DryRunReport {
    precondition_matches: bool,
    actions: Vec<String>,
}

impl DryRunReport {
    /// Returns true if the reader currently contains exactly the bytes that
    /// the plan was generated for.
    pub fn precondition_matches(&self) -> bool {
        self.precondition_matches
    }

    /// Returns descriptions of the actions that would be applied.
    pub fn actions(&self) -> &[String] {
        &self.actions
    }
}

/// The outcome of successfully applying a [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ApplyReport {
    actions_applied: usize,
    digest_before: PreconditionDigest,
    digest_after: PreconditionDigest,
}

impl ApplyReport {
    /// Returns the number of repair actions that were written.
    pub fn actions_applied(&self) -> usize {
        self.actions_applied
    }

    /// Returns the digest of the input before the repairs were applied.
    pub fn digest_before(&self) -> PreconditionDigest {
        self.digest_before
    }

    /// Returns the digest of the image after the repairs were applied.
    pub fn digest_after(&self) -> PreconditionDigest {
        self.digest_after
    }
}

//===========================================================================//

/// A read-only repair plan for one specific input image.
///
/// The plan contains only in-place four-byte edits.  It never writes anything
/// on its own: call [`RepairPlan::dry_run`] to preview it (that function
/// cannot write at all) or [`RepairPlan::apply`] to apply it explicitly.  An
/// application refuses to start unless the current input still matches the
/// plan's [`PreconditionDigest`], and stages every edit in memory before
/// writing, so a failed application cannot half-update the input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPlan {
    digest: PreconditionDigest,
    actions: Vec<RepairAction>,
}

impl RepairPlan {
    /// Returns the digest of the exact input bytes this plan was generated
    /// for.
    pub fn precondition_digest(&self) -> PreconditionDigest {
        self.digest
    }

    /// Returns the planned actions, in application order.
    pub fn actions(&self) -> &[RepairAction] {
        &self.actions
    }

    /// Returns true if the plan contains no actions.
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }

    /// Previews the plan against `inner` without writing anything.
    ///
    /// This returns whether `inner` still matches the plan's precondition
    /// digest and which actions would run.  Because it only accepts a reader,
    /// this method is statically incapable of modifying the input.
    pub fn dry_run<F: Read + Seek>(
        &self,
        inner: F,
    ) -> io::Result<DryRunReport> {
        let image = read_image(inner)?;
        let precondition_matches = digest_image(&image) == self.digest;
        let actions =
            self.actions.iter().map(|a| a.description.clone()).collect();
        Ok(DryRunReport { precondition_matches, actions })
    }

    /// Applies the plan to `inner`, but only if its current bytes still match
    /// the plan's precondition digest.
    ///
    /// Every edit is staged on an in-memory copy before anything is written,
    /// and the digest is checked before any write occurs, so a failed
    /// application leaves the input unchanged.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        mut inner: F,
    ) -> io::Result<ApplyReport> {
        let image = read_image(&mut inner)?;
        let digest_before = digest_image(&image);
        if digest_before != self.digest {
            invalid_data!(
                "Cannot apply repair plan: input has changed since the plan \
                 was generated (expected {}, found {})",
                self.digest,
                digest_before
            );
        }
        let mut patched = image;
        for action in &self.actions {
            let start = action.offset as usize;
            let end = start.checked_add(4).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Repair action offset {} overflows", action.offset),
                )
            })?;
            if end > patched.len() {
                invalid_data!(
                    "Cannot apply repair plan: action {} targets byte {}..{}, \
                     but the file is only {} bytes long",
                    action.description,
                    start,
                    end,
                    patched.len()
                );
            }
            patched[start..end].copy_from_slice(&action.value.to_le_bytes());
        }
        inner.seek(SeekFrom::Start(0))?;
        inner.write_all(&patched)?;
        inner.flush()?;
        Ok(ApplyReport {
            actions_applied: self.actions.len(),
            digest_before,
            digest_after: digest_image(&patched),
        })
    }
}

//===========================================================================//

/// Reads the complete current image of `inner` without changing its seek
/// position relative to the returned image (the caller is responsible for any
/// further seeking).
fn read_image<F: Read + Seek>(mut inner: F) -> io::Result<Vec<u8>> {
    let len = inner.seek(SeekFrom::End(0))?;
    inner.seek(SeekFrom::Start(0))?;
    let mut image = vec![0u8; len as usize];
    inner.read_exact(&mut image)?;
    Ok(image)
}

/// Computes the FNV-1a 64-bit digest of `image`, together with its length.
///
/// FNV-1a is a fixed, dependency-free hash, so the digest is stable across
/// Rust versions and platforms (unlike `std::collections::hash_map::DefaultHasher`).
fn digest_image(image: &[u8]) -> PreconditionDigest {
    const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = FNV_OFFSET_BASIS;
    for &byte in image {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    PreconditionDigest { len: image.len() as u64, fnv1a_64: hash }
}

//===========================================================================//

/// Accumulates findings and planned actions while walking one file image.
///
/// All state is per-audit: there are no caches, counters, or temporary files
/// shared between calls, so a failed audit cannot affect a later one.
struct Auditor<'a> {
    image: &'a [u8],
    sector_len: usize,
    num_sectors: usize,
    corruptions: Vec<Corruption>,
    actions: Vec<RepairAction>,
    planned_offsets: FnvHashSet<u64>,
}

impl<'a> Auditor<'a> {
    fn new(image: &'a [u8], sector_len: usize, num_sectors: usize) -> Self {
        Auditor {
            image,
            sector_len,
            num_sectors,
            corruptions: Vec::new(),
            actions: Vec::new(),
            planned_offsets: FnvHashSet::default(),
        }
    }

    fn sector_offset(&self, sector_id: u32) -> usize {
        (sector_id as usize + 1) * self.sector_len
    }

    fn read_sector_u32s(&self, sector_id: u32) -> Vec<u32> {
        let start = self.sector_offset(sector_id);
        let count = self.sector_len / 4;
        (0..count)
            .map(|i| {
                let offset = start + 4 * i;
                u32::from_le_bytes([
                    self.image[offset],
                    self.image[offset + 1],
                    self.image[offset + 2],
                    self.image[offset + 3],
                ])
            })
            .collect()
    }

    fn report(
        &mut self,
        kind: CorruptionKind,
        area: AuditArea,
        sector: Option<u32>,
        detail: impl Into<String>,
    ) {
        self.corruptions.push(Corruption {
            kind,
            area,
            sector,
            detail: detail.into(),
        });
    }

    fn plan_action(
        &mut self,
        target: RepairTarget,
        offset: u64,
        value: u32,
        description: String,
    ) {
        // Two findings must not produce conflicting writes to the same bytes.
        if self.planned_offsets.insert(offset) {
            self.actions.push(RepairAction {
                target,
                offset,
                value,
                description,
            });
        }
    }

    fn plan_header_u32(&mut self, offset: u64, value: u32, what: &str) {
        self.plan_action(
            RepairTarget::Header,
            offset,
            value,
            format!("set header {} to {}", what, value),
        );
    }

    /// Records a planned rewrite of FAT entry `sector_id` to `value`.
    ///
    /// `fat_sector_ids` maps a FAT entry index to the on-disk FAT sector that
    /// stores it, exactly as derived from the DIFAT.
    fn plan_fat_entry(
        &mut self,
        fat_sector_ids: &[u32],
        sector_id: u32,
        value: u32,
        why: &str,
    ) {
        let entries_per_sector = (self.sector_len / 4) as u32;
        let order = sector_id / entries_per_sector;
        let within = sector_id % entries_per_sector;
        let Some(&fat_sector_id) = fat_sector_ids.get(order as usize) else {
            return;
        };
        let offset = (self.sector_offset(fat_sector_id)
            + 4 * within as usize) as u64;
        self.plan_action(
            RepairTarget::Fat,
            offset,
            value,
            format!("set FAT[{}] to 0x{:08X} ({})", sector_id, value, why),
        );
    }

    /// Records a planned rewrite of MiniFAT entry `mini_sector` to `value`.
    fn plan_minifat_entry(
        &mut self,
        minifat_sector_ids: &[u32],
        mini_sector: u32,
        value: u32,
        why: &str,
    ) {
        let entries_per_sector = (self.sector_len / 4) as u32;
        let order = mini_sector / entries_per_sector;
        let within = mini_sector % entries_per_sector;
        let Some(&minifat_sector_id) =
            minifat_sector_ids.get(order as usize)
        else {
            return;
        };
        let offset = (self.sector_offset(minifat_sector_id)
            + 4 * within as usize) as u64;
        self.plan_action(
            RepairTarget::MiniFat,
            offset,
            value,
            format!(
                "set MiniFAT[{}] to 0x{:08X} ({})",
                mini_sector, value, why
            ),
        );
    }
}

//===========================================================================//

/// Audits the compound file exposed by `inner` without modifying it,
/// returning the corruption evidence and a read-only repair plan.
pub(crate) fn audit_compound_file<F: Read + Seek>(
    inner: F,
) -> io::Result<AuditReport> {
    let image = read_image(inner)?;
    if (image.len() as u64) < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            image.len()
        );
    }
    audit_image(&image)
}

fn audit_image(image: &[u8]) -> io::Result<AuditReport> {
    // Reuse the production header parser: an audit only accepts inputs that
    // the normal open path could begin parsing as well.
    let header = Header::read_from(
        &mut Cursor::new(image),
        Validation::Permissive,
    )?;
    let sector_len = header.version.sector_len();
    if image.len() < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            image.len(),
            sector_len
        );
    }
    let num_sectors = image.len().div_ceil(sector_len) - 1;
    let mut audit = Auditor::new(image, sector_len, num_sectors);

    let (difat_sector_ids, fat_sector_ids) =
        read_difat(&mut audit, &header);
    let fat =
        read_fat(&mut audit, &difat_sector_ids, &fat_sector_ids, num_sectors);
    let dir_entries = read_directory_chain(
        &mut audit,
        &header,
        &difat_sector_ids,
        &fat_sector_ids,
        &fat,
    )?;
    let (minifat_sector_ids, minifat) =
        read_minifat(&mut audit, &header, &fat_sector_ids, &fat, &dir_entries);
    analyze_chains(
        &mut audit,
        &header,
        &fat_sector_ids,
        &fat,
        &minifat_sector_ids,
        &minifat,
        &dir_entries,
    );

    let plan = RepairPlan {
        digest: digest_image(image),
        actions: audit.actions,
    };
    Ok(AuditReport { corruptions: audit.corruptions, plan })
}

/// Walks the DIFAT, records its corruption, and returns (in deterministic
/// order) the DIFAT chain sector IDs and the FAT sector IDs listed there.
fn read_difat(
    audit: &mut Auditor,
    header: &Header,
) -> (Vec<u32>, Vec<u32>) {
    let mut fat_sector_ids: Vec<u32> =
        header.initial_difat_entries.iter().copied()
            .take_while(|&entry| entry != consts::FREE_SECTOR)
            .collect();
    // Mirror the permissive open path's tolerance of zero padding in the
    // header DIFAT entries.
    while fat_sector_ids.len()
        > consts::NUM_DIFAT_ENTRIES_IN_HEADER
        && fat_sector_ids.len() > header.num_fat_sectors as usize
        && fat_sector_ids.last() == Some(&0)
    {
        fat_sector_ids.pop();
    }

    let mut difat_sector_ids = Vec::new();
    let mut seen = FnvHashSet::default();
    let mut current = header.first_difat_sector;
    while current != consts::END_OF_CHAIN
        && current != consts::FREE_SECTOR
    {
        if current > consts::MAX_REGULAR_SECTOR {
            audit.report(
                CorruptionKind::OutOfBounds,
                AuditArea::Difat,
                Some(current),
                format!(
                    "DIFAT chain includes invalid sector index 0x{:08X}",
                    current
                ),
            );
            break;
        }
        if current as usize >= audit.num_sectors {
            audit.report(
                CorruptionKind::OutOfBounds,
                AuditArea::Difat,
                Some(current),
                format!(
                    "DIFAT chain includes sector index {}, but sector count \
                     is only {}",
                    current, audit.num_sectors
                ),
            );
            break;
        }
        if !seen.insert(current) {
            audit.report(
                CorruptionKind::Loop,
                AuditArea::Difat,
                Some(current),
                format!(
                    "DIFAT chain reaches sector {} a second time, forming a \
                     loop",
                    current
                ),
            );
            break;
        }
        difat_sector_ids.push(current);
        let entries = audit.read_sector_u32s(current);
        for &entry in entries.iter().take(entries.len() - 1) {
            if entry == consts::FREE_SECTOR {
                continue;
            }
            if entry > consts::MAX_REGULAR_SECTOR {
                audit.report(
                    CorruptionKind::OutOfBounds,
                    AuditArea::Difat,
                    Some(entry),
                    format!(
                        "DIFAT refers to invalid sector index 0x{:08X}",
                        entry
                    ),
                );
                continue;
            }
            fat_sector_ids.push(entry);
        }
        current = *entries.last().unwrap();
    }

    if difat_sector_ids.len() != header.num_difat_sectors as usize {
        audit.report(
            CorruptionKind::LengthMismatch,
            AuditArea::Difat,
            None,
            format!(
                "header declares {} DIFAT sector(s), but the DIFAT chain \
                 contains {}",
                header.num_difat_sectors,
                difat_sector_ids.len()
            ),
        );
        audit.plan_header_u32(
            HEADER_NUM_DIFAT_SECTORS_OFFSET,
            difat_sector_ids.len() as u32,
            "num DIFAT sectors",
        );
    }

    // A FAT sector listed twice in the DIFAT is a duplicate allocation of
    // the FAT-sector role; de-duplicate before reading so one bad listing
    // cannot hide other evidence.
    let mut unique = Vec::new();
    let mut seen_fat = FnvHashSet::default();
    for sector_id in fat_sector_ids {
        if !seen_fat.insert(sector_id) {
            audit.report(
                CorruptionKind::DuplicateAllocation,
                AuditArea::Difat,
                Some(sector_id),
                format!(
                    "FAT sector {} is listed more than once in the DIFAT",
                    sector_id
                ),
            );
            continue;
        }
        unique.push(sector_id);
    }
    if unique.len() != header.num_fat_sectors as usize {
        audit.report(
            CorruptionKind::LengthMismatch,
            AuditArea::Difat,
            None,
            format!(
                "header declares {} FAT sector(s), but the DIFAT lists {}",
                header.num_fat_sectors,
                unique.len()
            ),
        );
        audit.plan_header_u32(
            HEADER_NUM_FAT_SECTORS_OFFSET,
            unique.len() as u32,
            "num FAT sectors",
        );
    }
    (difat_sector_ids, unique)
}

/// Reads the FAT table pointed to by the DIFAT.
fn read_fat(
    audit: &mut Auditor,
    _difat_sector_ids: &[u32],
    fat_sector_ids: &[u32],
    num_sectors: usize,
) -> Vec<u32> {
    let mut fat = Vec::with_capacity(num_sectors);
    for &sector_id in fat_sector_ids {
        if sector_id as usize >= num_sectors {
            audit.report(
                CorruptionKind::OutOfBounds,
                AuditArea::Difat,
                Some(sector_id),
                format!(
                    "DIFAT refers to FAT sector {}, but sector count is \
                     only {}",
                    sector_id, num_sectors
                ),
            );
            continue;
        }
        fat.extend_from_slice(&audit.read_sector_u32s(sector_id));
    }
    // Tolerantly normalize the table to one entry per file sector, matching
    // the permissive open path's padding/truncation behavior.
    fat.truncate(num_sectors);
    while fat.len() < num_sectors {
        fat.push(consts::FREE_SECTOR);
    }
    fat
}

/// The outcome of tolerantly following one allocation chain.
enum TableWalk {
    /// The chain ended with END_OF_CHAIN; contains every visited sector.
    Complete(Vec<u32>),
    /// The chain starts at an invalid index; no sectors were visited.
    StartOutOfBounds(u32),
    /// The chain loops: `closer` points back at `revisited`.
    Loop {
        chain: Vec<u32>,
        closer: u32,
        revisited: u32,
    },
}

/// Follows a FAT/MiniFAT chain without panicking or looping forever.
fn walk_table(table: &[u32], limit: usize, start: u32) -> TableWalk {
    if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
        return TableWalk::Complete(Vec::new());
    }
    if start > consts::MAX_REGULAR_SECTOR || start as usize >= limit {
        return TableWalk::StartOutOfBounds(start);
    }
    let mut chain = vec![start];
    let mut seen = FnvHashSet::default();
    seen.insert(start);
    let mut current = start;
    loop {
        let next = table[current as usize];
        if next == consts::END_OF_CHAIN || next == consts::FREE_SECTOR {
            return TableWalk::Complete(chain);
        }
        // Mid-chain pointer problems (reserved values, out-of-bounds
        // pointers) are recorded by the table scans; just stop here so the
        // rest of the image can still be examined.
        if next > consts::MAX_REGULAR_SECTOR || next as usize >= limit {
            return TableWalk::Complete(chain);
        }
        if !seen.insert(next) {
            return TableWalk::Loop {
                chain,
                closer: current,
                revisited: next,
            };
        }
        chain.push(next);
        current = next;
    }
}

/// Walks the directory chain (tolerantly) and parses its directory entries
/// using the same [`DirEntry::read_from`] parser as the production open path.
fn read_directory_chain(
    audit: &mut Auditor,
    header: &Header,
    _difat_sector_ids: &[u32],
    fat_sector_ids: &[u32],
    fat: &[u32],
) -> io::Result<Vec<DirEntry>> {
    let mut dir_sectors = Vec::new();
    match walk_table(fat, audit.num_sectors, header.first_dir_sector) {
        TableWalk::Complete(chain) => dir_sectors = chain,
        TableWalk::StartOutOfBounds(sector_id) => {
            audit.report(
                CorruptionKind::OutOfBounds,
                AuditArea::DirectoryChain,
                Some(sector_id),
                format!(
                    "directory chain starts at sector {}, but the file has \
                     only {} sectors",
                    sector_id, audit.num_sectors
                ),
            );
        }
        TableWalk::Loop { chain, closer, revisited } => {
            audit.report(
                CorruptionKind::Loop,
                AuditArea::DirectoryChain,
                Some(closer),
                format!(
                    "directory chain loops: sector {} points back to {}",
                    closer, revisited
                ),
            );
            audit.plan_fat_entry(
                fat_sector_ids,
                closer,
                consts::END_OF_CHAIN,
                "break directory-chain loop",
            );
            dir_sectors = chain;
        }
    }

    // For V4 the header declares the directory-chain length; a shorter chain
    // is a truncated directory.
    if header.version == crate::internal::Version::V4
        && dir_sectors.len() != header.num_dir_sectors as usize
    {
        audit.report(
            CorruptionKind::LengthMismatch,
            AuditArea::DirectoryChain,
            None,
            format!(
                "header declares {} directory sector(s), but the directory \
                 chain contains {}",
                header.num_dir_sectors,
                dir_sectors.len()
            ),
        );
        audit.plan_header_u32(
            HEADER_NUM_DIR_SECTORS_OFFSET,
            dir_sectors.len() as u32,
            "num directory sectors",
        );
    }

    let mut dir_entries = Vec::new();
    for &sector_id in &dir_sectors {
        let start = audit.sector_offset(sector_id);
        let sector_bytes = &audit.image[start..start + audit.sector_len];
        let mut cursor = Cursor::new(sector_bytes);
        for _ in 0..header.version.dir_entries_per_sector() {
            // Deliberately propagate parser errors: a structurally invalid
            // directory entry is refused through the same io::Error layer as
            // the normal open path.
            let entry = DirEntry::read_from(
                &mut cursor,
                header.version,
                Validation::Permissive,
            )?;
            dir_entries.push(entry);
        }
    }
    Ok(dir_entries)
}

/// Walks and reads the MiniFAT chain.
fn read_minifat(
    audit: &mut Auditor,
    header: &Header,
    _difat_sector_ids: &[u32],
    fat_sector_ids: &[u32],
    fat: &[u32],
    dir_entries: &[DirEntry],
) -> (Vec<u32>, Vec<u32>) {
    let _ = dir_entries;
    let mut minifat_sector_ids = Vec::new();
    match walk_table(
        fat,
        audit.num_sectors,
        header.first_minifat_sector,
    ) {
        TableWalk::Complete(chain) => minifat_sector_ids = chain,
        TableWalk::StartOutOfBounds(sector_id) => {
            audit.report(
                CorruptionKind::OutOfBounds,
                AuditArea::MiniFat,
                Some(sector_id),
                format!(
                    "MiniFAT chain starts at sector {}, but the file has \
                     only {} sectors",
                    sector_id, audit.num_sectors
                ),
            );
        }
        TableWalk::Loop { chain, closer, revisited } => {
            audit.report(
                CorruptionKind::Loop,
                AuditArea::MiniFat,
                Some(closer),
                format!(
                    "MiniFAT chain loops: sector {} points back to {}",
                    closer, revisited
                ),
            );
            audit.plan_fat_entry(
                fat_sector_ids,
                closer,
                consts::END_OF_CHAIN,
                "break MiniFAT-chain loop",
            );
            minifat_sector_ids = chain;
        }
    }

    if minifat_sector_ids.len() != header.num_minifat_sectors as usize {
        audit.report(
            CorruptionKind::LengthMismatch,
            AuditArea::MiniFat,
            None,
            format!(
                "header declares {} MiniFAT sector(s), but the MiniFAT chain \
                 contains {}",
                header.num_minifat_sectors,
                minifat_sector_ids.len()
            ),
        );
        audit.plan_header_u32(
            HEADER_NUM_MINIFAT_SECTORS_OFFSET,
            minifat_sector_ids.len() as u32,
            "num MiniFAT sectors",
        );
    }

    let mut minifat = Vec::new();
    for &sector_id in &minifat_sector_ids {
        minifat.extend_from_slice(&audit.read_sector_u32s(sector_id));
    }
    while minifat.last() == Some(&consts::FREE_SECTOR) {
        minifat.pop();
    }
    (minifat_sector_ids, minifat)
}
