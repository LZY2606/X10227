//! Opt-in structural auditing of a Compound File Binary image.
//!
//! Unlike the normal open path, the auditor never rejects a partially damaged
//! image and never writes to it: it walks the on-disk FAT/DIFAT/MiniFAT and
//! the directory chain tolerantly and records one [`Finding`] per structural
//! violation, together with a read-only [`RepairPlan`].
//!
//! The audit shares the on-disk format knowledge of the production open path
//! (see [`crate::internal::Header`] and the constants in
//! [`crate::internal::consts`]); it does not reuse the production `Allocator`
//! because those types intentionally reject and "heal" malformed images
//! during parsing, whereas an auditor has to describe every defect instead.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::consts;
use crate::internal::{Header, ObjType, Validation, Version};
use crate::WriteLeNumber;

//===========================================================================//

/// Which allocation structure a [`Finding`] is about.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum AuditLayer {
    /// The Double-Indirect File Allocation Table (the DIFAT sector chain and
    /// the header DIFAT entries).
    Difat,
    /// The File Allocation Table sector chains.
    Fat,
    /// The MiniFAT and the mini stream.
    MiniFat,
    /// The directory sector chain and the directory entries.
    Directory,
}

impl AuditLayer {
    fn rank(self) -> u8 {
        match self {
            AuditLayer::Difat => 0,
            AuditLayer::Fat => 1,
            AuditLayer::MiniFat => 2,
            AuditLayer::Directory => 3,
        }
    }
}

impl fmt::Display for AuditLayer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            AuditLayer::Difat => "DIFAT",
            AuditLayer::Fat => "FAT",
            AuditLayer::MiniFat => "MiniFAT",
            AuditLayer::Directory => "directory chain",
        })
    }
}

/// The kind of structural damage recorded in a [`Finding`].
///
/// The five damage classes are deliberately kept distinct, per the audit
/// contract: a cycle is never reported as an out-of-bounds edge, two chains
/// sharing a sector is never merged with a lone orphan sector, and a stream
/// whose declared length disagrees with its chain is a separate class again.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CorruptionKind {
    /// A chain edge points back at a sector already on the same chain.
    Cycle,
    /// A chain edge points past the end of the file / table.
    OutOfBounds,
    /// One physical sector is reachable from two distinct chain owners.
    DuplicateOccupancy,
    /// A marked, in-range sector is not reachable from any known chain root.
    OrphanSector,
    /// A declared length is inconsistent with the chain that backs it.
    LengthMismatch,
}

impl CorruptionKind {
    fn rank(self) -> u8 {
        match self {
            CorruptionKind::Cycle => 0,
            CorruptionKind::OutOfBounds => 1,
            CorruptionKind::DuplicateOccupancy => 2,
            CorruptionKind::OrphanSector => 3,
            CorruptionKind::LengthMismatch => 4,
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DuplicateOccupancy => {
                "duplicate sector occupancy (cross-linked chains)"
            }
            CorruptionKind::OrphanSector => "orphan sector",
            CorruptionKind::LengthMismatch => "declared length mismatch",
        })
    }
}

//===========================================================================//

/// One piece of damage evidence, carrying the first offending location and
/// enough surrounding context to interpret it without rerunning the audit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    layer: AuditLayer,
    kind: CorruptionKind,
    /// The first offending location, e.g. "FAT[12]".
    location: String,
    /// Human-readable detail, e.g. "12 -> 99, but FAT has 20 entries".
    detail: String,
    /// Sector IDs that participate in the damage, in chain order when that
    /// is meaningful (for a cycle this is the cycle itself).
    chain: Vec<u32>,
}

impl Finding {
    /// The allocation structure this finding is about.
    pub fn layer(&self) -> AuditLayer {
        self.layer
    }

    /// The class of damage.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }

    /// The first offending location within the audited image.
    pub fn location(&self) -> &str {
        &self.location
    }

    /// A human-readable description of the violation and its context.
    pub fn detail(&self) -> &str {
        &self.detail
    }

    /// The sector IDs involved (e.g. the cycle, or the duplicated sector),
    /// when applicable.
    pub fn chain(&self) -> &[u32] {
        &self.chain
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} at {} ({})",
            self.layer, self.kind, self.location, self.detail
        )
    }
}


//===========================================================================//

/// A 64-bit FNV-1a fingerprint of the exact bytes a repair plan was computed
/// against.  A plan may only be applied when the fingerprint still matches.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct AuditDigest(pub u64);

impl AuditDigest {
    /// Computes the digest over an image.  FNV-1a 64-bit is deterministic
    /// across platforms and Rust versions, which is all the precondition
    /// check needs (it is not a cryptographic hash).
    pub fn compute(image: &[u8]) -> AuditDigest {
        const OFFSET: u64 = 0xcbf29ce484222325;
        const PRIME: u64 = 0x100000001b3;
        let mut hash = OFFSET;
        for &byte in image {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(PRIME);
        }
        // Mix in the length so that trailing zeroes (which do occur in CFB
        // padding) cannot be erased by truncation without detection.
        hash ^= (image.len() as u64).wrapping_mul(PRIME);
        AuditDigest(hash.wrapping_mul(PRIME))
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

//===========================================================================//

/// The order in which the auditor walks same-priority chains.  Findings are
/// sorted deterministically either way; the option exists to prove that
/// changing an enumeration/ordering condition irrelevant to the result cannot
/// change the report.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AuditOrder {
    /// Walk chain roots in ascending sector ID order.
    Ascending,
    /// Walk chain roots in descending sector ID order.
    Descending,
}

/// Options controlling a read-only structural audit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AuditOptions {
    pub(crate) order: AuditOrder,
}

impl Default for AuditOptions {
    fn default() -> Self {
        AuditOptions { order: AuditOrder::Ascending }
    }
}

impl AuditOptions {
    /// Default audit options.
    pub fn new() -> Self {
        AuditOptions::default()
    }

    /// Sets the (result-irrelevant) chain walk order.
    pub fn walk_order(mut self, order: AuditOrder) -> Self {
        self.order = order;
        self
    }
}


//===========================================================================//

/// A single in-place byte replacement within a repair plan.  Repair never
/// changes the length of the file, which keeps every sector offset stable.
#[derive(Clone, Debug, Eq, PartialEq)]
struct BytePatch {
    offset: u64,
    before: Vec<u8>,
    after: Vec<u8>,
    /// What this patch fixes, carried into the plan's step description.
    purpose: String,
}

impl BytePatch {
    fn put_u32(offset: u64, before: u32, after: u32, purpose: String) -> Self {
        BytePatch {
            offset,
            before: before.to_le_bytes().to_vec(),
            after: after.to_le_bytes().to_vec(),
            purpose,
        }
    }

    fn put_u64(offset: u64, before: u64, after: u64, purpose: String) -> Self {
        BytePatch {
            offset,
            before: before.to_le_bytes().to_vec(),
            after: after.to_le_bytes().to_vec(),
            purpose,
        }
    }

    fn len(&self) -> u64 {
        self.after.len() as u64
    }
}

/// One human- and machine-checkable step of a read-only repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    offset: u64,
    purpose: String,
}

impl RepairStep {
    /// Byte offset within the file that this step overwrites.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// What the step repairs.
    pub fn purpose(&self) -> &str {
        &self.purpose
    }
}

//===========================================================================//

/// The result of a structural audit: the damage evidence and, when every
/// finding can be resolved without growing the file, a read-only repair plan.
#[derive(Clone, Debug)]
pub struct AuditReport {
    version: Version,
    findings: Vec<Finding>,
    /// Digest of the exact image bytes that were audited.
    precondition: AuditDigest,
    image_len: u64,
    /// A repair plan, only when a fixed point with zero findings is reached.
    plan: Option<RepairPlan>,
}

impl AuditReport {
    /// True if no structural damage was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// All findings, sorted by (layer, kind, first location); each damage
    /// class is reported separately.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// Findings for one allocation layer only.
    pub fn findings_in(&self, layer: AuditLayer) -> Vec<&Finding> {
        self.findings.iter().filter(|f| f.layer == layer).collect()
    }

    /// The precondition digest recorded at audit time.
    pub fn precondition(&self) -> AuditDigest {
        self.precondition
    }

    /// The read-only repair plan, if the damage is repairable.
    pub fn repair_plan(&self) -> Option<&RepairPlan> {
        self.plan.as_ref()
    }

    /// The CFB version of the audited image.
    pub fn version(&self) -> Version {
        self.version
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.findings.is_empty() {
            writeln!(f, "Structural audit: no damage found.")?;
        } else {
            writeln!(
                f,
                "Structural audit: {} finding(s):",
                self.findings.len()
            )?;
            for finding in &self.findings {
                writeln!(f, "  - {finding}")?;
            }
        }
        write!(f, "Precondition digest: {}", self.precondition)?;
        if let Some(plan) = &self.plan {
            write!(f, "\n{}", plan.summary())?;
        }
        Ok(())
    }
}

//===========================================================================//

/// A read-only, byte-exact repair plan derived from one specific image.
///
/// The plan is inert: constructing it never touches the input.  It can only
/// be applied explicitly through [`RepairPlan::apply_with`], and only when
/// the target's current [`AuditDigest`] still equals [`RepairPlan::digest`].
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition: AuditDigest,
    /// Expected input length; changing file size also invalidates the plan.
    image_len: u64,
    patches: Vec<BytePatch>,
}

impl RepairPlan {
    /// The digest of the image this plan was computed for.
    pub fn digest(&self) -> AuditDigest {
        self.precondition
    }

    /// The individual repair steps, in application order.
    pub fn steps(&self) -> Vec<RepairStep> {
        self.patches
            .iter()
            .map(|patch| RepairStep {
                offset: patch.offset,
                purpose: patch.purpose.clone(),
            })
            .collect()
    }

    /// A short human-readable summary stating the precondition and steps.
    pub fn summary(&self) -> String {
        let mut out = format!(
            "Read-only repair plan for digest {} ({} byte step(s)):",
            self.precondition,
            self.patches.len()
        );
        for (index, patch) in self.patches.iter().enumerate() {
            out.push_str(&format!(
                "\n  {}. byte {}: {}",
                index + 1,
                patch.offset,
                patch.purpose
            ));
        }
        out.push_str(
            "\nApply only if the file digest still matches; the input is \
             never modified otherwise.",
        );
        out
    }
}


//===========================================================================//
// Test-only failure injection.
//
// The production repair algorithm is a single function: build the entire
// repaired image in memory first, verify the precondition twice, and only
// then perform one write.  To prove that a failure at the commit point is
// atomic and leaves no counter/cache behind, the write boundary carries one
// injectable error.  It exists only under `cfg(test)` and is a one-shot
// thread-local: no production code path can observe it and it cannot leak
// between tests.

#[cfg(test)]
pub(crate) mod failpoint {
    use std::cell::Cell;

    thread_local! {
        static FAIL_NEXT_COMMIT: Cell<bool> = const { Cell::new(false) };
    }

    /// Arms the failpoint so the next repair commit on this thread fails once
    /// with `Interrupted`; subsequent calls behave normally again.
    pub(crate) fn arm_once() {
        FAIL_NEXT_COMMIT.with(|cell| cell.set(true));
    }

    pub(crate) fn take_armed() -> bool {
        FAIL_NEXT_COMMIT.with(|cell| cell.replace(false))
    }

    pub(crate) fn is_armed() -> bool {
        FAIL_NEXT_COMMIT.with(Cell::get)
    }
}

impl RepairPlan {
    /// Checks whether this plan would apply to `inner` right now, without
    /// writing a single byte.  Returns the current digest for callers that
    /// want to report it, or an error of kind [`io::ErrorKind::InvalidData`]
    /// if the image has changed since the plan was made.
    pub fn check_with<F: Read + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<AuditDigest> {
        let image = read_image(inner)?;
        let current = AuditDigest::compute(&image);
        if current != self.precondition || image.len() as u64 != self.image_len
        {
            invalid_data!(
                "Repair plan precondition no longer holds (plan was made for \
                 digest {} of {} bytes, image is now digest {} of {} bytes); \
                 rerun the structural audit",
                self.precondition,
                self.image_len,
                current,
                image.len()
            );
        }
        Ok(current)
    }

    /// Applies the plan explicitly.  The full repaired image is assembled in
    /// memory and the precondition is re-checked immediately before the single
    /// write, so any failure leaves the input at its original bytes.
    pub fn apply_with<F: Read + Write + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<AuditDigest> {
        let mut image = read_image(inner)?;
        if image.len() as u64 != self.image_len {
            invalid_data!(
                "Repair plan precondition no longer holds (plan was made for \
                 {} bytes, image is now {} bytes)",
                self.image_len,
                image.len()
            );
        }
        let current = AuditDigest::compute(&image);
        if current != self.precondition {
            invalid_data!(
                "Repair plan precondition no longer holds (plan was made for \
                 digest {}, image is now digest {}); rerun the structural \
                 audit",
                self.precondition,
                current
            );
        }
        let repaired = self.compose_repaired(&image)?;
        // The composed image must still satisfy the plan's precondition up to
        // the planned byte changes; the digest of the original bytes is the
        // commit token.  Re-check after composing as well, so that even a
        // future change to composition logic cannot silently apply a stale
        // plan.
        debug_assert_eq!(image.len(), repaired.len());
        debug_assert_eq!(AuditDigest::compute(&image), self.precondition);

        // Single commit point: everything above was allocation-only.
        #[cfg(test)]
        if failpoint::take_armed() {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "injected commit failure during repair application",
            ));
        }

        inner.seek(SeekFrom::Start(0))?;
        inner.write_all(&repaired)?;
        inner.flush()?;
        let _ = &mut image;
        Ok(AuditDigest::compute(&repaired))
    }

    /// Builds the repaired image in a fresh buffer, leaving `original`
    /// untouched.  Verifies every patch still sees the bytes it was planned
    /// against.
    fn compose_repaired(&self, original: &[u8]) -> io::Result<Vec<u8>> {
        let mut repaired = original.to_vec();
        for patch in &self.patches {
            let start = patch.offset as usize;
            let end = start + patch.before.len();
            if end > repaired.len() {
                invalid_data!(
                    "Repair step at byte {} runs past the end of the file",
                    patch.offset
                );
            }
            if repaired[start..end] != patch.before[..] {
                invalid_data!(
                    "Repair step at byte {} ({}) no longer matches the bytes \
                     present at audit time; rerun the structural audit",
                    patch.offset,
                    patch.purpose
                );
            }
            repaired[start..end].copy_from_slice(&patch.after);
        }
        Ok(repaired)
    }
}


//===========================================================================//
// Raw, tolerant model of the image
//===========================================================================//

fn read_u32(image: &[u8], offset: usize) -> Option<u32> {
    let bytes = image.get(offset..offset + 4)?;
    Some(u32::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3],
    ]))
}

fn read_image<F: Read + Seek>(inner: &mut F) -> io::Result<Vec<u8>> {
    let len = inner.seek(SeekFrom::End(0))?;
    if len > consts::MAX_REGULAR_SECTOR as u64 * 64 {
        invalid_data!("Invalid CFB file ({} bytes is too large to audit)", len);
    }
    inner.seek(SeekFrom::Start(0))?;
    let mut image = Vec::with_capacity(len as usize);
    inner.take(len).read_to_end(&mut image)?;
    Ok(image)
}

/// Information parsed directly from the directory chain, without the
/// validation the production open path performs.
#[derive(Clone, Debug)]
struct RawEntry {
    stream_id: u32,
    obj_type: ObjType,
    start_sector: u32,
    stream_len: u64,
}

/// The tolerant in-memory model used by the auditor.
struct Model {
    version: Version,
    sector_len: u64,
    num_sectors: u32,
    header: Header,
    /// `true` for DIFAT sector IDs as chained from the header.
    difat_sector_ids: BTreeSet<u32>,
    /// FAT sector IDs as listed by the DIFAT.
    fat_sector_ids: BTreeSet<u32>,
    /// Raw FAT, one entry per file sector where readable (length may be
    /// shorter than `num_sectors` for truncated FAT sectors).
    fat: Vec<u32>,
    /// Directory entries reachable along the directory chain.
    dir_entries: Vec<RawEntry>,
    /// Raw MiniFAT entries (trailing FREE entries trimmed like production).
    minifat: Vec<u32>,
    /// Whether the MiniFAT sector chain itself read completely.
    minifat_complete: bool,
    /// Sector IDs holding the MiniFAT chain, if walkable.
    minifat_sectors: BTreeSet<u32>,
    /// Sector IDs holding the mini stream (root stream chain).
    mini_stream_sectors: BTreeSet<u32>,
}

impl Model {
    fn fat_entry(&self, sector: u32) -> Option<u32> {
        self.fat.get(sector as usize).copied()
    }

    fn is_metadata(&self, sector: u32) -> bool {
        self.fat_sector_ids.contains(&sector)
            || self.difat_sector_ids.contains(&sector)
    }
}


/// Parses the raw model and the findings that make production parsing fail
/// (DIFAT/FAT/directory-chain walks), all tolerantly.
fn parse_model(image: &[u8]) -> io::Result<(Model, Vec<Finding>)> {
    let mut findings = Vec::new();
    if image.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small for a header)",
            image.len()
        );
    }
    let mut cursor = io::Cursor::new(&image[..]);
    // Permissive shares the production header parser; the audit never
    // invents a second interpretation of the header.
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len() as u64;
    let num_sectors =
        ((image.len() as u64) / sector_len).saturating_sub(1) as u32;
    if image.len() < sector_len as usize {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            image.len(),
            sector_len
        );
    }

    // ---- DIFAT chain (tolerant; stop at first bad edge) -------------------
    let mut difat_sector_ids = BTreeSet::new();
    let mut difat_list: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();
    let mut current = header.first_difat_sector;
    let mut seen = BTreeSet::new();
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= num_sectors {
            findings.push(Finding {
                layer: AuditLayer::Difat,
                kind: CorruptionKind::OutOfBounds,
                location: format!("DIFAT chain sector {}", current),
                detail: format!(
                    "DIFAT chain continues at sector {}, but file has only {} \
                     sectors",
                    current, num_sectors
                ),
                chain: seen.iter().copied().collect(),
            });
            break;
        }
        if !seen.insert(current) {
            let mut chain: Vec<u32> = seen.iter().copied().collect();
            chain.push(current);
            findings.push(Finding {
                layer: AuditLayer::Difat,
                kind: CorruptionKind::Cycle,
                location: format!("DIFAT chain sector {}", current),
                detail:
                    "DIFAT sector chain revisits an already visited sector"
                        .to_string(),
                chain,
            });
            break;
        }
        difat_sector_ids.insert(current);
        // Read 127/1023 entries plus the next-pointer.
        let entries_per_sector = sector_len as usize / 4;
        let sector_offset = ((current as u64 + 1) * sector_len) as usize;
        for index in 0..entries_per_sector - 1 {
            if let Some(next) =
                read_u32(image, sector_offset + index * 4)
            {
                if next != consts::FREE_SECTOR {
                    difat_list.push(next);
                }
            }
        }
        match read_u32(image, sector_offset + (entries_per_sector - 1) * 4) {
            Some(next) => current = next,
            None => {
                findings.push(Finding {
                    layer: AuditLayer::Difat,
                    kind: CorruptionKind::OutOfBounds,
                    location: format!("DIFAT chain sector {}", current),
                    detail:
                        "DIFAT sector chain next-pointer runs past EOF"
                            .to_string(),
                    chain: seen.iter().copied().collect(),
                });
                break;
            }
        }
    }
    // Header/DIFAT sector count mismatches are declared-length inconsistencies.
    if header.num_difat_sectors as usize != difat_sector_ids.len() {
        findings.push(Finding {
            layer: AuditLayer::Difat,
            kind: CorruptionKind::LengthMismatch,
            location: "header.num_difat_sectors".to_string(),
            detail: format!(
                "header declares {} DIFAT sector(s), but {} are reachable",
                header.num_difat_sectors,
                difat_sector_ids.len()
            ),
            chain: difat_sector_ids.iter().copied().collect(),
        });
    }

    // ---- FAT sectors -------------------------------------------------------
    let mut fat_sector_ids = BTreeSet::new();
    let mut fat: Vec<u32> = Vec::new();
    let entries_per_sector = sector_len as usize / 4;
    for listed in difat_list.iter().copied() {
        if listed == consts::FREE_SECTOR {
            continue;
        }
        if listed >= num_sectors {
            findings.push(Finding {
                layer: AuditLayer::Difat,
                kind: CorruptionKind::OutOfBounds,
                location: "DIFAT FAT-sector entry".to_string(),
                detail: format!(
                    "DIFAT lists sector {} as a FAT sector, but file has only \
                     {} sectors",
                    listed, num_sectors
                ),
                chain: vec![listed],
            });
            continue;
        }
        fat_sector_ids.insert(listed);
        let offset = ((listed as u64 + 1) * sector_len) as usize;
        for index in 0..entries_per_sector {
            match read_u32(image, offset + index * 4) {
                Some(entry) if fat.len() < num_sectors as usize => {
                    fat.push(entry)
                }
                Some(_) => {}
                None if fat.len() < num_sectors as usize => {
                    // Short trailing FAT sector: pad like an unreadable tail.
                    fat.push(consts::FREE_SECTOR);
                }
                None => {}
            }
        }
    }
    while fat.len() < num_sectors as usize {
        fat.push(consts::FREE_SECTOR);
    }
    if header.num_fat_sectors as usize
        != difat_list
            .iter()
            .filter(|&&s| s != consts::FREE_SECTOR && s < num_sectors)
            .count()
    {
        findings.push(Finding {
            layer: AuditLayer::Difat,
            kind: CorruptionKind::LengthMismatch,
            location: "header.num_fat_sectors".to_string(),
            detail: format!(
                "header declares {} FAT sector(s), but the DIFAT lists {}",
                header.num_fat_sectors,
                difat_list
                    .iter()
                    .filter(|&&s| s != consts::FREE_SECTOR && s < num_sectors)
                    .count()
            ),
            chain: vec![],
        });
    }


    // ---- Directory chain (tolerant) --------------------------------------
    let mut dir_entries: Vec<RawEntry> = Vec::new();
    let mut dir_seen = BTreeSet::new();
    current = header.first_dir_sector;
    let mut truncated_directory = false;
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= num_sectors {
            findings.push(Finding {
                layer: AuditLayer::Directory,
                kind: CorruptionKind::OutOfBounds,
                location: format!("directory chain sector {}", current),
                detail: format!(
                    "directory chain continues at sector {}, but file has \
                     only {} sectors; the chain is truncated here",
                    current, num_sectors
                ),
                chain: dir_seen.iter().copied().collect(),
            });
            truncated_directory = true;
            break;
        }
        if !dir_seen.insert(current) {
            let mut chain: Vec<u32> = dir_seen.iter().copied().collect();
            chain.push(current);
            findings.push(Finding {
                layer: AuditLayer::Directory,
                kind: CorruptionKind::Cycle,
                location: format!("directory chain sector {}", current),
                detail:
                    "directory sector chain revisits an already visited sector"
                        .to_string(),
                chain,
            });
            break;
        }
        let sector_offset = ((current as u64 + 1) * sector_len) as usize;
        let entries_per_sector = version.dir_entries_per_sector();
        for slot in 0..entries_per_sector {
            let entry_offset = sector_offset + slot * consts::DIR_ENTRY_LEN;
            let obj_type = image
                .get(entry_offset + 66)
                .copied()
                .and_then(ObjType::from_byte);
            let Some(obj_type) = obj_type else {
                continue;
            };
            if obj_type == ObjType::Unallocated {
                continue;
            }
            let start_sector =
                read_u32(image, entry_offset + 116).unwrap_or(consts::END_OF_CHAIN);
            let mut stream_len =
                image
                    .get(entry_offset + 120..entry_offset + 128)
                    .map(|bytes| {
                        let mut buf = [0u8; 8];
                        buf.copy_from_slice(bytes);
                        u64::from_le_bytes(buf)
                    })
                    .unwrap_or(0);
            stream_len &= version.stream_len_mask();
            dir_entries.push(RawEntry {
                stream_id: dir_entries.len() as u32,
                obj_type,
                start_sector,
                stream_len,
            });
        }
        match fat.get(current as usize).copied() {
            Some(next) => current = next,
            None => break,
        }
    }
    if version == Version::V4
        && header.num_dir_sectors as usize != dir_seen.len()
        && !truncated_directory
    {
        findings.push(Finding {
            layer: AuditLayer::Directory,
            kind: CorruptionKind::LengthMismatch,
            location: "header.num_dir_sectors".to_string(),
            detail: format!(
                "header declares {} directory sector(s), but {} are \
                 reachable",
                header.num_dir_sectors,
                dir_seen.len()
            ),
            chain: dir_seen.iter().copied().collect(),
        });
    }


    // ---- MiniFAT chain (tolerant, walked via raw FAT) ---------------------
    let mut minifat = Vec::<u32>::new();
    let mut minifat_complete = true;
    let mut minifat_sectors = BTreeSet::new();
    current = header.first_minifat_sector;
    let mut mini_seen = BTreeSet::new();
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= num_sectors {
            findings.push(Finding {
                layer: AuditLayer::MiniFat,
                kind: CorruptionKind::OutOfBounds,
                location: format!("MiniFAT chain sector {}", current),
                detail: format!(
                    "MiniFAT chain continues at sector {}, but file has only \
                     {} sectors",
                    current, num_sectors
                ),
                chain: mini_seen.iter().copied().collect(),
            });
            minifat_complete = false;
            break;
        }
        if !mini_seen.insert(current) {
            let mut chain: Vec<u32> = mini_seen.iter().copied().collect();
            chain.push(current);
            findings.push(Finding {
                layer: AuditLayer::MiniFat,
                kind: CorruptionKind::Cycle,
                location: format!("MiniFAT chain sector {}", current),
                detail:
                    "MiniFAT sector chain revisits an already visited sector"
                        .to_string(),
                chain,
            });
            minifat_complete = false;
            break;
        }
        minifat_sectors.insert(current);
        let sector_offset = ((current as u64 + 1) * sector_len) as usize;
        for index in 0..entries_per_sector {
            match read_u32(image, sector_offset + index * 4) {
                Some(entry) => minifat.push(entry),
                None => {
                    minifat_complete = false;
                }
            }
        }
        match fat.get(current as usize).copied() {
            Some(next) => current = next,
            None => {
                minifat_complete = false;
                break;
            }
        }
    }
    while minifat.last() == Some(&consts::FREE_SECTOR) {
        minifat.pop();
    }
    if minifat_complete
        && header.num_minifat_sectors as usize != minifat_sectors.len()
        && header.first_minifat_sector != consts::END_OF_CHAIN
    {
        findings.push(Finding {
            layer: AuditLayer::MiniFat,
            kind: CorruptionKind::LengthMismatch,
            location: "header.num_minifat_sectors".to_string(),
            detail: format!(
                "header declares {} MiniFAT sector(s), but {} are reachable",
                header.num_minifat_sectors,
                minifat_sectors.len()
            ),
            chain: minifat_sectors.iter().copied().collect(),
        });
    }

    // ---- Root mini-stream sector chain -------------------------------------
    let mut mini_stream_sectors = BTreeSet::new();
    let root_start = dir_entries
        .first()
        .filter(|entry| entry.obj_type == ObjType::Root)
        .map(|entry| entry.start_sector)
        .unwrap_or(consts::END_OF_CHAIN);
    if root_start != consts::END_OF_CHAIN && root_start < num_sectors {
        current = root_start;
        let mut guard = 0u32;
        while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR
            && current < num_sectors
            && guard <= num_sectors
        {
            if !mini_stream_sectors.insert(current) {
                break;
            }
            current = fat.get(current as usize).copied().unwrap_or(
                consts::END_OF_CHAIN,
            );
            guard += 1;
        }
    }

    let model = Model {
        version,
        sector_len,
        num_sectors,
        header,
        difat_sector_ids,
        fat_sector_ids,
        fat,
        dir_entries,
        minifat,
        minifat_complete,
        minifat_sectors,
        mini_stream_sectors,
    };
    Ok((model, findings))
}


/// Classifies one FAT/MiniFAT edge value relative to the table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Edge {
    Next(u32),
    End,
    Free,
    OutOfBounds,
    Invalid,
}

fn classify(entry: u32, table_len: usize) -> Edge {
    if entry == consts::END_OF_CHAIN {
        Edge::End
    } else if entry == consts::FREE_SECTOR {
        Edge::Free
    } else if entry > consts::MAX_REGULAR_SECTOR {
        Edge::Invalid
    } else if entry as usize >= table_len {
        Edge::OutOfBounds
    } else {
        Edge::Next(entry)
    }
}

/// FAT-level analysis over the raw table.  Returns findings plus a
/// "repaired" view of the FAT in which every defective edge is cut to
/// END_OF_CHAIN, cross-linked victims released, and unreachable data sectors
/// freed; the caller uses the repaired view to decide length fixes.
struct FatAnalysis {
    /// `from -> to` after removing duplicate/cycle/oob edges (set to EOC).
    repaired: Vec<u32>,
    /// Sectors reachable from any legitimate chain root in the repaired graph.
    reachable: BTreeSet<u32>,
    /// Offsets (indices) whose FAT entry the repair must overwrite.
    edge_cuts: Vec<(u32, u32)>,
    /// Indices the repair frees (cross-linked victim tail or orphan).
    frees: Vec<u32>,
}

fn analyze_fat(model: &Model, findings: &mut Vec<Finding>) -> FatAnalysis {
    let n = model.fat.len() as u32;
    let mut repaired = model.fat.clone();

    // Pass 1: per-edge validity.  Invalid reserved values and out-of-range
    // pointers are OutOfBounds findings; cut them.
    for from in 0..n {
        let entry = model.fat[from as usize];
        match classify(entry, n as usize) {
            Edge::Next(_) | Edge::End | Edge::Free => {}
            Edge::OutOfBounds | Edge::Invalid => {
                findings.push(Finding {
                    layer: AuditLayer::Fat,
                    kind: CorruptionKind::OutOfBounds,
                    location: format!("FAT[{from}]"),
                    detail: format!(
                        "sector {from} points to {entry}, but the FAT has {} \
                         entries",
                        n
                    ),
                    chain: vec![from],
                });
                repaired[from as usize] = consts::END_OF_CHAIN;
            }
        }
    }

    // Chain roots: the directory chain, the MiniFAT chain, the root/mini
    // stream chain, and every stream start listed in the directory.
    let mut roots: BTreeSet<u32> = BTreeSet::new();
    if model.header.first_dir_sector < n
        && model.header.first_dir_sector != consts::END_OF_CHAIN
    {
        roots.insert(model.header.first_dir_sector);
    }
    if model.header.first_minifat_sector < n
        && model.header.first_minifat_sector != consts::END_OF_CHAIN
    {
        roots.insert(model.header.first_minifat_sector);
    }
    for entry in &model.dir_entries {
        if entry.obj_type == ObjType::Root
            || (entry.obj_type == ObjType::Stream
                && entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64)
        {
            if entry.start_sector < n
                && entry.start_sector != consts::END_OF_CHAIN
            {
                roots.insert(entry.start_sector);
            }
        }
    }

    // Walk every root chain over the *repaired-so-far* graph, detecting the
    // second claimant of a sector (duplicate occupancy).  Roots are walked in
    // a fixed order; the first claimant keeps the sector.
    let mut claimant: BTreeMap<u32, u32> = BTreeMap::new();
    for &start in &roots {
        let mut current = start;
        let mut local: Vec<u32> = Vec::new();
        let mut guard = 0u32;
        while current != consts::END_OF_CHAIN
            && current < n
            && guard <= n
        {
            if let Some(&owner) = claimant.get(&current) {
                if owner != start {
                    findings.push(Finding {
                        layer: AuditLayer::Fat,
                        kind: CorruptionKind::DuplicateOccupancy,
                        location: format!("FAT[{owner}]"),
                        detail: format!(
                            "sector {current} is shared by the chain starting \
                             at sector {owner} and the chain starting at sector \
                             {start}; the second chain is cut before {current}"
                        ),
                        chain: {
                            let mut c = vec![owner, current, start];
                            c.sort_unstable();
                            c.dedup();
                            c
                        },
                    });
                    // Cut the predecessor edge in the current chain.
                    if let Some(&prev) = local.last() {
                        repaired[prev as usize] = consts::END_OF_CHAIN;
                    }
                    break;
                }
                // Same owner revisiting itself: a cycle.  Handled by the
                // functional-graph cycle pass below on the full graph; stop
                // this walk to bound it.
                break;
            }
            claimant.insert(current, start);
            local.push(current);
            current = match repaired[current as usize] {
                v if v == consts::END_OF_CHAIN || v == consts::FREE_SECTOR => {
                    consts::END_OF_CHAIN
                }
                v if v >= n => consts::END_OF_CHAIN,
                v => v,
            };
            guard += 1;
        }
    }

