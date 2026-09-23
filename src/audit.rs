//! Opt-in structural auditing of compound files.
//!
//! The audit reads a compound file without mutating it and reports evidence of
//! corruption in its allocation structures: the DIFAT, the FAT, the MiniFAT,
//! and the directory chain.  Reports are deterministic and keep the first
//! offending location plus context, so different classes of corruption are
//! reported separately rather than collapsed into a single pass/fail answer.
//!
//! Every [`RepairPlan`] records a [`AuditDigest`] of the exact input bytes it
//! was derived from.  Applying a plan re-reads the file and refuses to write
//! anything unless the digest still matches, so changing the file after the
//! audit invalidates the plan.  Applying through a path is atomic: the result
//! is assembled in a temporary file and renamed into place, so a failure
//! mid-way leaves the original file byte-for-byte untouched.
//!
//! None of this changes the behavior of the usual open paths; auditing is
//! strictly opt-in.

use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};

use fnv::FnvHashMap;

use crate::internal::consts;
use crate::internal::{DirEntry, ObjType, Validation, Version};

//===========================================================================//
// Digest

const FNV_OFFSET: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

/// A compact identity for the exact bytes a report or plan was derived from.
///
/// The digest combines two independent FNV-1a hashes (one over the whole file
/// and one over the byte-reversed file) with the file length, so it is stable
/// across repeated runs while still detecting arbitrary edits.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AuditDigest {
    file_len: u64,
    forward: u64,
    backward: u64,
}

impl AuditDigest {
    fn of(bytes: &[u8]) -> AuditDigest {
        let mut forward = FNV_OFFSET;
        for &byte in bytes {
            forward ^= byte as u64;
            forward = forward.wrapping_mul(FNV_PRIME);
        }
        let mut backward = FNV_OFFSET;
        for &byte in bytes.iter().rev() {
            backward ^= byte as u64;
            backward = backward.wrapping_mul(FNV_PRIME);
        }
        AuditDigest {
            file_len: bytes.len() as u64,
            forward,
            backward,
        }
    }

    /// The file length in bytes captured by the digest.
    pub fn len(&self) -> u64 {
        self.file_len
    }

    /// Whether the digest describes an empty input.
    pub fn is_empty(&self) -> bool {
        self.file_len == 0
    }
}

impl fmt::Debug for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "AuditDigest(len={}, {:#018x}/{:#018x})",
            self.file_len, self.forward, self.backward
        )
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            fmt,
            "{:016x}:{:016x}:{:016x}",
            self.file_len, self.forward, self.backward
        )
    }
}

//===========================================================================//
// Evidence types

/// Which allocation structure an item of evidence was found in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AuditLayer {
    /// The double-indirect FAT (DIFAT) in the header and DIFAT sectors.
    Difat,
    /// The file allocation table (FAT).
    Fat,
    /// The directory sector chain.
    Directory,
    /// The mini FAT and the root-entry mini stream.
    MiniFat,
}

impl fmt::Display for AuditLayer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            AuditLayer::Difat => "DIFAT",
            AuditLayer::Fat => "FAT",
            AuditLayer::Directory => "directory chain",
            AuditLayer::MiniFat => "MiniFAT",
        })
    }
}

/// The kind of chain a piece of evidence refers to.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChainOwner {
    /// The DIFAT chain itself.
    Difat,
    /// The FAT-sector list (the DIFAT's payload).
    FatSectors,
    /// The directory chain rooted at the header's first-directory-sector
    /// field.
    Directory,
    /// The MiniFAT chain rooted at the header's first-MiniFAT-sector field.
    MiniFat,
    /// The mini stream rooted at the root directory entry's starting sector.
    MiniStream,
    /// A stream named by a directory entry (the path is included).
    Stream(String),
}

impl fmt::Display for ChainOwner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ChainOwner::Difat => f.write_str("DIFAT chain"),
            ChainOwner::FatSectors => f.write_str("FAT sector list"),
            ChainOwner::Directory => f.write_str("directory chain"),
            ChainOwner::MiniFat => f.write_str("MiniFAT chain"),
            ChainOwner::MiniStream => f.write_str("mini stream"),
            ChainOwner::Stream(path) => write!(f, "stream {path:?}"),
        }
    }
}

/// Distinct classes of allocation corruption.
///
/// The five categories the audit is required to tell apart are represented by
/// distinct variants: cycles, out-of-bounds links, repeated occupancy,
/// orphaned sectors, and declared-length mismatches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CorruptionKind {
    /// A chain points outside the file or into a special FAT value that is
    /// not valid in that position; the chain cannot be followed to its end.
    OutOfBounds,
    /// Following a chain revisits one of its own sectors without ending.
    Cycle,
    /// A sector is reachable from two different owners (or twice within one
    /// owner) instead of being exclusively owned.
    DuplicateOccupant,
    /// A sector that looks allocated in the FAT cannot be reached from any
    /// root (header pointers or directory entries).
    Orphan,
    /// A declared length or count disagrees with what the tables describe.
    DeclaredLengthMismatch,
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CorruptionKind::OutOfBounds => "out-of-bounds link",
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::DuplicateOccupant => "duplicate occupant",
            CorruptionKind::Orphan => "orphan sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared-length mismatch"
            }
        })
    }
}

/// One piece of corruption evidence: where it was found and what it means.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Corruption {
    /// The allocation structure involved.
    pub layer: AuditLayer,
    /// The class of corruption.
    pub kind: CorruptionKind,
    /// The chain that contains the offending link or length, when known.
    pub owner: Option<ChainOwner>,
    /// Byte offset of the offending field within the input file.
    pub offset: Option<u64>,
    /// The offending sector ID (or mini-sector ID in the MiniFAT layer).
    pub sector: Option<u64>,
    /// Human-readable context, including the first violation position.
    pub detail: String,
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.layer, self.kind)?;
        if let Some(owner) = &self.owner {
            write!(f, " in {owner}")?;
        }
        if let Some(sector) = self.sector {
            write!(f, " at sector {sector}")?;
        }
        if let Some(offset) = self.offset {
            write!(f, " (byte offset {offset})")?;
        }
        write!(f, ": {}", self.detail)
    }
}

//===========================================================================//
// Report

/// The result of an opt-in structural audit of a compound file.
#[derive(Clone, Debug)]
pub struct AuditReport {
    pub(crate) version: Version,
    pub(crate) file_len: u64,
    pub(crate) sector_len: u32,
    pub(crate) num_sectors: u32,
    pub(crate) digest: AuditDigest,
    pub(crate) corruptions: Vec<Corruption>,
    pub(crate) layout: Layout,
}

/// Structural layout facts gathered during an audit.
///
/// The tables are exposed read-only so callers (and tests) can reason about
/// CFB allocation semantics without reconstructing the parse; they are the
/// same tables the audit used to produce its evidence.
#[derive(Clone, Debug)]
pub struct Layout {
    /// Sector IDs holding the FAT, in DIFAT order.
    pub fat_sector_ids: Vec<u32>,
    /// Raw FAT entries, indexed by sector ID.
    pub fat: Vec<u32>,
    /// Sector IDs of the directory chain, in order.
    pub directory_chain: Vec<u32>,
    /// Raw MiniFAT entries, indexed by mini-sector ID.
    pub minifat: Vec<u32>,
    /// Parsed directory entries, including unallocated slots.
    pub entries: Vec<EntryView>,
    /// Regular-sector IDs of the MiniFAT chain, in order.
    pub minifat_chain: Vec<u32>,
    /// Regular-sector IDs of the mini stream chain, in order.
    pub mini_stream_chain: Vec<u32>,
    /// Header fields relevant to allocation.
    pub header: HeaderView,
}

/// Header allocation fields as the audit saw them.
#[derive(Clone, Copy, Debug)]
pub struct HeaderView {
    /// Declared number of FAT sectors.
    pub num_fat_sectors: u32,
    /// First sector of the directory chain.
    pub first_dir_sector: u32,
    /// Declared number of directory sectors (V4).
    pub num_dir_sectors: u32,
    /// First sector of the MiniFAT chain.
    pub first_minifat_sector: u32,
    /// Declared number of MiniFAT sectors.
    pub num_minifat_sectors: u32,
    /// First sector of the DIFAT chain.
    pub first_difat_sector: u32,
    /// Declared number of DIFAT sectors.
    pub num_difat_sectors: u32,
}

/// A directory entry as the audit saw it, even in a damaged file.
#[derive(Clone, Debug)]
pub struct EntryView {
    /// Stream ID (index within the directory chain).
    pub stream_id: u32,
    /// Entry name (empty for unparseable or unallocated entries).
    pub name: String,
    /// Raw object-type byte.
    pub obj_type_byte: u8,
    /// First sector (or first mini sector) of the entry's stream.
    pub start_sector: u32,
    /// Declared stream length in bytes.
    pub stream_len: u64,
}

impl AuditReport {
    /// Digest of the exact bytes this report describes.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// The CFB version that was audited.
    pub fn version(&self) -> Version {
        self.version
    }

    /// True if no corruption evidence was found.
    pub fn is_clean(&self) -> bool {
        self.corruptions.is_empty()
    }

    /// All evidence in a deterministic order.
    pub fn corruptions(&self) -> &[Corruption] {
        &self.corruptions
    }

    /// Evidence of one particular class, in report order.
    pub fn evidence_of_kind(
        &self,
        kind: CorruptionKind,
    ) -> impl Iterator<Item = &Corruption> {
        self.corruptions.iter().filter(move |c| c.kind == kind)
    }

    /// Structural layout tables used by the audit.
    pub fn layout(&self) -> &Layout {
        &self.layout
    }

    /// Builds a read-only repair plan from this report.  This never writes
    /// anything; the returned plan only applies when explicitly applied
    /// against bytes whose digest still matches.
    pub fn repair_plan(&self) -> RepairPlan {
        let patches = crate::internal::audit_repair::plan_patches(self);
        RepairPlan {
            precondition: self.digest,
            file_len: self.file_len,
            patches,
        }
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_clean() {
            writeln!(f, "CFB audit: clean ({} bytes)", self.file_len)?;
        } else {
            writeln!(
                f,
                "CFB audit: {} corruption(s) in {} bytes",
                self.corruptions.len(),
                self.file_len
            )?;
            for corruption in &self.corruptions {
                writeln!(f, "  - {corruption}")?;
            }
        }
        write!(f, "digest: {}", self.digest)
    }
}

//===========================================================================//
// Repair plan

/// A single byte-level replacement proposed by a repair plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BytePatch {
    /// Byte offset to overwrite.
    pub offset: u64,
    /// Bytes already present there.
    pub original: Vec<u8>,
    /// Replacement bytes (same length as `original`).
    pub replacement: Vec<u8>,
}

/// A read-only repair plan derived from one specific input.
///
/// The plan carries the [`AuditDigest`] of its input as a precondition.  It
/// can be inspected and applied repeatedly, but an application refuses to
/// write unless the target's bytes still hash to the recorded digest.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition: AuditDigest,
    file_len: u64,
    patches: Vec<BytePatch>,
}

impl RepairPlan {
    /// The digest the input must still have for application to proceed.
    pub fn precondition(&self) -> AuditDigest {
        self.precondition
    }

    /// Proposed byte patches in ascending offset order; empty for clean
    /// files or corruption that the plan does not know how to repair.
    pub fn patches(&self) -> &[BytePatch] {
        &self.patches
    }

    /// Whether applying this plan would change any bytes.
    pub fn is_noop(&self) -> bool {
        self.patches.is_empty()
    }

    fn check_precondition(&self, bytes: &[u8]) -> io::Result<()> {
        let actual = AuditDigest::of(bytes);
        if actual != self.precondition {
            invalid_data!(
                "Cannot apply repair plan: input digest {} no longer matches \
                 the plan's precondition {}",
                actual,
                self.precondition
            );
        }
        Ok(())
    }

    /// Produces the repaired image without writing anywhere.  Returns
    /// `InvalidData` if the bytes do not match the plan's precondition.
    pub fn dry_run(&self, input: &[u8]) -> io::Result<Vec<u8>> {
        self.check_precondition(input)?;
        let mut output = input.to_vec();
        for patch in &self.patches {
            let start = patch.offset as usize;
            let end = start + patch.replacement.len();
            if end > output.len()
                || output[start..end] != patch.original[..]
            {
                invalid_data!(
                    "Repair plan patch at offset {} does not match current \
                     bytes",
                    patch.offset
                );
            }
            output[start..end].copy_from_slice(&patch.replacement);
        }
        Ok(output)
    }

    /// Applies the plan to a seekable reader/writer, refusing to write unless
    /// its digest still matches.  For arbitrary writers the result is staged
    /// in memory first, so a write failure cannot leave a half-updated file.
    pub fn apply_to<W>(&self, writer: &mut W) -> io::Result<()>
    where
        W: Read + Write + Seek,
    {
        let mut input = Vec::with_capacity(self.file_len as usize);
        writer.seek(SeekFrom::Start(0))?;
        writer.read_to_end(&mut input)?;
        let output = self.dry_run(&input)?;
        with_failpoint("apply_before_commit", || {
            invalid_data!("Injected failure before committing repair plan")
        });
        writer.seek(SeekFrom::Start(0))?;
        writer.write_all(&output)?;
        writer.set_len(output.len() as u64)?;
        with_failpoint("apply_after_write", || {
            invalid_data!("Injected failure after writing repair plan")
        });
        writer.flush()
    }

    /// Atomically applies the plan to a filesystem path.  The repaired image
    /// is written to a temporary file in the same directory and renamed over
    /// the target only after a complete, successful write, so any failure
    /// leaves the original file and its bytes untouched.
    pub fn apply_path<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let path = path.as_ref();
        let input = fs::read(path)?;
        let output = self.dry_run(&input)?;
        with_failpoint("apply_path_before_tmp", || {
            invalid_data!("Injected failure before creating temp file")
        });
        let dir = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .map(|p| p.to_path_buf())
            .unwrap_or_else(|| Path::new(".").to_path_buf());
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let tmp_name = format!(
            ".{}.cfb-repair.{}.{}.tmp",
            path.file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("compound"),
            std::process::id(),
            unique
        );
        let tmp_path = dir.join(tmp_name);
        let result = (|| -> io::Result<()> {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&tmp_path)?;
            file.write_all(&output)?;
            with_failpoint("apply_path_before_rename", || {
                invalid_data!(
                    "Injected failure before atomic rename of repaired file"
                )
            });
            file.sync_all()?;
            drop(file);
            fs::rename(&tmp_path, path)?;
            Ok(())
        })();
        if result.is_err() {
            let _ = fs::remove_file(&tmp_path);
        }
        result
    }
}

//===========================================================================//
// Fault injection (test-only, process-local, never enabled in normal use)

static FAILPOINT_ENGAGED: AtomicBool = AtomicBool::new(false);

fn with_failpoint<F>(name: &str, f: F) -> io::Result<()>
where
    F: FnOnce() -> io::Error,
{
    if FAILPOINT_ENGAGED.load(Ordering::SeqCst)
        && FAILPOINT_NAME.with(|cell| cell.borrow().as_deref() == Some(name))
    {
        return Err(f());
    }
    Ok(())
}

thread_local! {
    static FAILPOINT_NAME: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

/// Engages a single named fault point on this thread for the duration of the
/// closure, then clears it even if the closure panics.  This exists solely so
/// the recovery tests can prove atomicity; it is not part of normal operation
/// and never affects other threads or persists across calls.
#[doc(hidden)]
pub fn __cfb_test_with_fault<T>(
    name: &str,
    f: impl FnOnce() -> T,
) -> T {
    FAILPOINT_NAME.with(|cell| *cell.borrow_mut() = Some(name.to_string()));
    FAILPOINT_ENGAGED.store(true, Ordering::SeqCst);
    struct Guard;
    impl Drop for Guard {
        fn drop(&mut self) {
            FAILPOINT_ENGAGED.store(false, Ordering::SeqCst);
            FAILPOINT_NAME.with(|cell| *cell.borrow_mut() = None);
        }
    }
    let _guard = Guard;
    f()
}

//===========================================================================//
// Audit engine
//
// The parser here is deliberately tolerant: malformed inputs that the normal
// open path rejects still produce an evidence-bearing report.  It reuses the
// production `Header` parser and `DirEntry` parser rather than forking the
// format interpretation.

#[derive(Clone, Copy)]
struct RawHeader {
    version: Version,
    sector_len: u32,
    num_fat_sectors: u32,
    first_dir_sector: u32,
    num_dir_sectors: u32,
    first_minifat_sector: u32,
    num_minifat_sectors: u32,
    first_difat_sector: u32,
    num_difat_sectors: u32,
    initial_difat: [u32; consts::NUM_DIFAT_ENTRIES_IN_HEADER],
}

fn le_u32(bytes: &[u8], offset: usize) -> Option<u32> {
    let slice = bytes.get(offset..offset + 4)?;
    Some(u32::from_le_bytes([
        slice[0], slice[1], slice[2], slice[3],
    ]))
}

fn le_u16(bytes: &[u8], offset: usize) -> Option<u16> {
    let slice = bytes.get(offset..offset + 2)?;
    Some(u16::from_le_bytes([slice[0], slice[1]]))
}

fn le_u64(bytes: &[u8], offset: usize) -> Option<u64> {
    let slice = bytes.get(offset..offset + 8)?;
    Some(u64::from_le_bytes([
        slice[0], slice[1], slice[2], slice[3],
        slice[4], slice[5], slice[6], slice[7],
    ]))
}

/// Parses just enough of the header to audit from raw bytes.  Returns an
/// io::Error from the existing `InvalidData` layer when the bytes are not a
/// CFB file at all.
fn parse_raw_header(bytes: &[u8]) -> io::Result<RawHeader> {
    if bytes.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            bytes.len()
        );
    }
    // Reuse the production header parser.  Permissive validation mirrors what
    // a plain `CompoundFile::open` accepts.
    let parsed = {
        let mut cursor = io::Cursor::new(bytes);
        crate::internal::Header::read_from(&mut cursor, Validation::Permissive)
    }?;
    Ok(RawHeader {
        sector_len: parsed.version.sector_len(),
        version: parsed.version,
        num_fat_sectors: parsed.num_fat_sectors,
        first_dir_sector: parsed.first_dir_sector,
        num_dir_sectors: parsed.num_dir_sectors,
        first_minifat_sector: parsed.first_minifat_sector,
        num_minifat_sectors: parsed.num_minifat_sectors,
        first_difat_sector: parsed.first_difat_sector,
        num_difat_sectors: parsed.num_difat_sectors,
        initial_difat: parsed.initial_difat_entries,
    })
}

fn sector_offset(sector_len: u32, sector_id: u32) -> usize {
    (sector_id as usize + 1) * sector_len as usize
}

/// Walks a FAT-like table starting at `start`, bounded by `table_len`.
struct WalkOutcome {
    ids: Vec<u32>,
    /// (from-index, to-value) for the first link that points out of bounds.
    out_of_bounds: Option<(usize, u32)>,
    /// Index within the walk where the chain first revisits an earlier id.
    cycle_at: Option<usize>,
}

fn walk_table(start: u32, table: &[u32]) -> WalkOutcome {
    let mut ids = Vec::new();
    if start == consts::END_OF_CHAIN {
        return WalkOutcome {
            ids,
            out_of_bounds: None,
            cycle_at: None,
        };
    }
    let mut positions: FnvHashMap<u32, usize> = FnvHashMap::default();
    let mut current = start;
    loop {
        if current == consts::END_OF_CHAIN {
            return WalkOutcome {
                ids,
                out_of_bounds: None,
                cycle_at: None,
            };
        }
        if current as usize >= table.len() || current > consts::MAX_REGULAR_SECTOR
        {
            return WalkOutcome {
                ids,
                out_of_bounds: Some((ids.len(), current)),
                cycle_at: None,
            };
        }
        if let Some(&earlier) = positions.get(&current) {
            return WalkOutcome {
                ids,
                out_of_bounds: None,
                cycle_at: Some(earlier),
            };
        }
        positions.insert(current, ids.len());
        ids.push(current);
        current = table[current as usize];
    }
}

struct Audit {
    bytes: Vec<u8>,
    header: RawHeader,
    num_sectors: u32,
    corruptions: Vec<Corruption>,
}

impl Audit {
    fn evidence(
        &mut self,
        layer: AuditLayer,
        kind: CorruptionKind,
        owner: Option<ChainOwner>,
        offset: Option<u64>,
        sector: Option<u64>,
        detail: String,
    ) {
        self.corruptions.push(Corruption {
            layer,
            kind,
            owner,
            offset,
            sector,
            detail,
        });
    }

    fn fat_entry_offset(&self, fat_sector_ids: &[u32], sector_id: u32) -> Option<u64> {
        let sector_len = self.header.sector_len as usize;
        let entries_per_sector = sector_len / 4;
        let fat_index = sector_id as usize;
        let sector_of_entry = fat_sector_ids.get(fat_index / entries_per_sector)?;
        Some(
            (sector_offset(self.header.sector_len, *sector_of_entry)
                + (fat_index % entries_per_sector) * 4) as u64,
        )
    }

    fn minifat_entry_offset(
        &self,
        minifat_chain: &[u32],
        mini_sector: u32,
    ) -> Option<u64> {
        let sector_len = self.header.sector_len as usize;
        let entries_per_sector = sector_len / 4;
        let regular =
            minifat_chain.get(mini_sector as usize / entries_per_sector)?;
        Some(
            (sector_offset(self.header.sector_len, *regular)
                + (mini_sector as usize % entries_per_sector) * 4) as u64,
        )
    }
}

/// Runs the audit over raw bytes.  Public entry points funnel here.
pub(crate) fn audit_bytes(bytes: Vec<u8>) -> io::Result<AuditReport> {
    let header = parse_raw_header(&bytes)?;
    let sector_len = header.sector_len;
    let file_len = bytes.len() as u64;
    if file_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            file_len,
            sector_len
        );
    }
    let num_sectors =
        ((file_len / sector_len as u64).saturating_sub(1)) as u32;
    let mut audit = Audit {
        bytes,
        header,
        num_sectors,
        corruptions: Vec::new(),
    };
    let (fat_sector_ids, fat, difat_chain) = audit.parse_fat();
    let (directory_chain, entries) = audit.parse_directory(&fat, &fat_sector_ids);
    let (minifat_chain, minifat) =
        audit.parse_minifat(&fat, &fat_sector_ids);
    let mini_stream_chain = audit.audit_chains(
        &fat,
        &fat_sector_ids,
        &difat_chain,
        &directory_chain,
        &minifat_chain,
        &minifat,
        &entries,
    );
    audit.corruptions.sort_by(|a, b| {
        (a.layer, a.kind, a.offset, a.sector, a.owner.clone(), a.detail.clone())
            .cmp(&(
                b.layer,
                b.kind,
                b.offset,
                b.sector,
                b.owner.clone(),
                b.detail.clone(),
            ))
    });
    audit.corruptions.dedup();
    let digest = AuditDigest::of(&audit.bytes);
    Ok(AuditReport {
        version: audit.header.version,
        file_len: audit.bytes.len() as u64,
        sector_len,
        num_sectors,
        digest,
        corruptions: audit.corruptions,
        layout: Layout {
            fat_sector_ids,
            fat,
            directory_chain,
            minifat,
            entries,
            minifat_chain,
            mini_stream_chain,
            header: HeaderView {
                num_fat_sectors: audit.header.num_fat_sectors,
                first_dir_sector: audit.header.first_dir_sector,
                num_dir_sectors: audit.header.num_dir_sectors,
                first_minifat_sector: audit.header.first_minifat_sector,
                num_minifat_sectors: audit.header.num_minifat_sectors,
                first_difat_sector: audit.header.first_difat_sector,
                num_difat_sectors: audit.header.num_difat_sectors,
            },
        },
    })
}

// ---------------------------------------------------------------------------
// DIFAT and FAT parsing
//

impl Audit {
    fn read_u32(&self, offset: usize) -> Option<u32> {
        le_u32(&self.bytes, offset)
    }

    /// Parses the DIFAT chain and FAT, recording DIFAT-layer evidence for
    /// bad pointers.  Returns (fat sector ids, fat entries, difat sector ids).
    fn parse_fat(&mut self) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
        let sector_len = self.header.sector_len as usize;
        let entries_per_sector = sector_len / 4;
        let mut fat_sector_ids: Vec<u32> =
            Vec::with_capacity(self.header.num_fat_sectors as usize);
        for &id in self.header.initial_difat.iter() {
            if id != consts::FREE_SECTOR {
                fat_sector_ids.push(id);
            }
        }

        // Walk the DIFAT sector chain from the header.
        let mut difat_chain: Vec<u32> = Vec::new();
        let mut seen: FnvHashMap<u32, usize> = FnvHashMap::default();
        let mut current = self.header.first_difat_sector;
        let mut difat_step = 0;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            let pointer_offset =
                68u64 + (difat_step as u64) * (sector_len as u64);
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(ChainOwner::Difat),
                    Some(pointer_offset),
                    Some(current as u64),
                    format!(
                        "DIFAT chain step {} points to sector {}, outside the \
                         {} sectors of the file",
                        difat_step, current, self.num_sectors
                    ),
                );
                break;
            }
            if let Some(&earlier) = seen.get(&current) {
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::Cycle,
                    Some(ChainOwner::Difat),
                    Some(pointer_offset),
                    Some(current as u64),
                    format!(
                        "DIFAT chain revisits sector {} first seen at step {}",
                        current, earlier
                    ),
                );
                break;
            }
            seen.insert(current, difat_step);
            difat_chain.push(current);
            let base = sector_offset(self.header.sector_len, current);
            for slot in 0..entries_per_sector - 1 {
                if let Some(next) = le_u32(&self.bytes, base + slot * 4) {
                    if next != consts::FREE_SECTOR
                        && next <= consts::MAX_REGULAR_SECTOR
                    {
                        fat_sector_ids.push(next);
                    } else if next != consts::FREE_SECTOR {
                        self.evidence(
                            AuditLayer::Difat,
                            CorruptionKind::OutOfBounds,
                            Some(ChainOwner::FatSectors),
                            Some((base + slot * 4) as u64),
                            Some(next as u64),
                            format!(
                                "DIFAT sector {} slot {} names invalid FAT \
                                 sector {:#010x}",
                                current, slot, next
                            ),
                        );
                    }
                }
            }
            let next_offset = base + (entries_per_sector - 1) * 4;
            current = match le_u32(&self.bytes, next_offset) {
                Some(value) => value,
                None => break,
            };
            difat_step += 1;
        }

        // Check DIFAT payload pointers for FAT sectors that are out of range.
        for (index, &fat_sector) in fat_sector_ids.iter().enumerate() {
            if fat_sector as u32 >= self.num_sectors
                || fat_sector > consts::MAX_REGULAR_SECTOR
            {
                let offset = if index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
                    Some((76 + index * 4) as u64)
                } else {
                    None
                };
                self.evidence(
                    AuditLayer::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(ChainOwner::FatSectors),
                    offset,
                    Some(fat_sector as u64),
                    format!(
                        "DIFAT entry {} names FAT sector {}, outside the {} \
                         sectors of the file",
                        index, fat_sector, self.num_sectors
                    ),
                );
            }
        }

        // Read the FAT itself.
        let mut fat = Vec::with_capacity(self.num_sectors as usize);
        for &fat_sector in &fat_sector_ids {
            if fat_sector >= self.num_sectors
                || fat_sector > consts::MAX_REGULAR_SECTOR
            {
                continue;
            }
            let base = sector_offset(self.header.sector_len, fat_sector);
            for slot in 0..entries_per_sector {
                match le_u32(&self.bytes, base + slot * 4) {
                    Some(entry) => fat.push(entry),
                    None => break,
                }
            }
        }
        fat.truncate(self.num_sectors as usize);
        while (fat.len() as u32) < self.num_sectors {
            fat.push(consts::FREE_SECTOR);
        }
        (fat_sector_ids, fat, difat_chain)
    }
}

// ---------------------------------------------------------------------------
// Directory chain and entries
//

impl Audit {
    fn parse_directory(
        &mut self,
        fat: &[u32],
        fat_sector_ids: &[u32],
    ) -> (Vec<u32>, Vec<EntryView>) {
        let sector_len = self.header.sector_len as usize;
        let entries_per_sector =
            sector_len / consts::DIR_ENTRY_LEN;

        // Walk the directory chain from the header, reporting the first bad
        // link distinctly (truncation shows up as an out-of-bounds link).
        let mut chain: Vec<u32> = Vec::new();
        let mut current = self.header.first_dir_sector;
        let mut seen: FnvHashMap<u32, usize> = FnvHashMap::default();
        let mut step = 0usize;
        while current != consts::END_OF_CHAIN {
            let pointer_offset = self.fat_entry_offset(
                fat_sector_ids,
                *chain.last().unwrap_or(&self.header.first_dir_sector),
            );
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.evidence(
                    AuditLayer::Directory,
                    CorruptionKind::OutOfBounds,
                    Some(ChainOwner::Directory),
                    pointer_offset,
                    Some(current as u64),
                    format!(
                        "directory chain step {} points to sector {} outside \
                         the file; the directory is truncated there",
                        step, current
                    ),
                );
                break;
            }
            if let Some(&earlier) = seen.get(&current) {
                self.evidence(
                    AuditLayer::Directory,
                    CorruptionKind::Cycle,
                    Some(ChainOwner::Directory),
                    pointer_offset,
                    Some(current as u64),
                    format!(
                        "directory chain revisits sector {} first seen at \
                         step {}",
                        current, earlier
                    ),
                );
                break;
            }
            seen.insert(current, step);
            chain.push(current);
            current = fat.get(current as usize).copied().unwrap_or(consts::FREE_SECTOR);
            if current <= consts::MAX_REGULAR_SECTOR
                && current >= self.num_sectors
            {
                // Handled on the next loop iteration with the correct kind.
            }
            step += 1;
        }

        // Parse entries from each sector of the (partial) chain.  A damaged
        // individual entry must not stop the audit, so fall back to raw
        // fields when the production parser rejects it.
        let mut entries = Vec::new();
        for (chain_index, &sector_id) in chain.iter().enumerate() {
            let base = sector_offset(self.header.sector_len, sector_id);
            for slot in 0..entries_per_sector {
                let entry_offset = base + slot * consts::DIR_ENTRY_LEN;
                let buffer = match self
                    .bytes
                    .get(entry_offset..entry_offset + consts::DIR_ENTRY_LEN)
                {
                    Some(buffer) => buffer,
                    None => break,
                };
                let stream_id =
                    (chain_index * entries_per_sector + slot) as u32;
                let parsed = {
                    let mut cursor = io::Cursor::new(buffer);
                    DirEntry::read_from(
                        &mut cursor,
                        self.header.version,
                        Validation::Permissive,
                    )
                };
                let view = match parsed {
                    Ok(entry) => EntryView {
                        stream_id,
                        name: entry.name,
                        obj_type_byte: match entry.obj_type {
                            ObjType::Unallocated => {
                                consts::OBJ_TYPE_UNALLOCATED
                            }
                            ObjType::Storage => consts::OBJ_TYPE_STORAGE,
                            ObjType::Stream => consts::OBJ_TYPE_STREAM,
                            ObjType::Root => consts::OBJ_TYPE_ROOT,
                        },
                        start_sector: entry.start_sector,
                        stream_len: entry.stream_len,
                    },
                    Err(_) => {
                        let name_len =
                            le_u16(buffer, 64).unwrap_or(0) as usize;
                        let mut name = String::new();
                        if name_len >= 2 && name_len <= 64 {
                            let nchars = name_len / 2 - 1;
                            let mut units = Vec::with_capacity(nchars);
                            for i in 0..nchars {
                                if let Some(unit) = le_u16(buffer, 2 * i) {
                                    units.push(unit);
                                }
                            }
                            name = String::from_utf16_lossy(&units);
                        }
                        EntryView {
                            stream_id,
                            name,
                            obj_type_byte: *buffer.get(66).unwrap_or(&0),
                            start_sector: le_u32(buffer, 116)
                                .unwrap_or(consts::END_OF_CHAIN),
                            stream_len: le_u64(buffer, 120).unwrap_or(0)
                                & self.header.version.stream_len_mask(),
                        }
                    }
                };
                entries.push(view);
            }
        }
        (chain, entries)
    }
}

// ---------------------------------------------------------------------------
// MiniFAT chain and entries
//

impl Audit {
    fn parse_minifat(
        &mut self,
        fat: &[u32],
        fat_sector_ids: &[u32],
    ) -> (Vec<u32>, Vec<u32>) {
        let sector_len = self.header.sector_len as usize;
        let entries_per_sector = sector_len / 4;
        let mut chain = Vec::new();
        let start = self.header.first_minifat_sector;
        if start != consts::END_OF_CHAIN {
            let outcome = walk_table(start, fat);
            chain = outcome.ids;
            if let Some((step, bad)) = outcome.out_of_bounds {
                let pointer_offset = if step == 0 {
                    Some(60u64)
                } else {
                    self.fat_entry_offset(fat_sector_ids, chain[step - 1])
                };
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::OutOfBounds,
                    Some(ChainOwner::MiniFat),
                    pointer_offset,
                    Some(bad as u64),
                    format!(
                        "MiniFAT chain step {} points to sector {} outside \
                         the file",
                        step, bad
                    ),
                );
            }
            if let Some(earlier) = outcome.cycle_at {
                self.evidence(
                    AuditLayer::MiniFat,
                    CorruptionKind::Cycle,
                    Some(ChainOwner::MiniFat),
                    self.fat_entry_offset(
                        fat_sector_ids,
                        chain[chain.len().saturating_sub(1)],
                    ),
                    chain.get(earlier).copied().map(u64::from),
                    format!(
                        "MiniFAT chain cycles back to sector {} first seen at \
                         step {}",
                        chain.get(earlier).copied().unwrap_or(0),
                        earlier
                    ),
                );
            }
        }
        let mut minifat = Vec::new();
        for &sector_id in &chain {
            let base = sector_offset(self.header.sector_len, sector_id);
            for slot in 0..entries_per_sector {
                if let Some(entry) = le_u32(&self.bytes, base + slot * 4) {
                    minifat.push(entry);
                }
            }
        }
        while minifat.last() == Some(&consts::FREE_SECTOR) {
            minifat.pop();
        }
        (chain, minifat)
    }
}
