//! Opt-in, read-only structural auditing of Compound File Binary images.
//!
//! The regular entry points ([`crate::open`], [`crate::OpenOptions`]) parse
//! permissively and return the first error they hit; they never modify the
//! file, but they cannot give a complete picture of a corrupted allocation
//! layout.  This module audits the *raw bytes* of a CFB image instead: it
//! walks the DIFAT, FAT, MiniFAT and directory chains tolerantly, collects
//! every piece of structural evidence, and keeps the corruption classes
//! required by CFB recovery strictly separate:
//!
//! * cycles ([`EvidenceKind::Cycle`]),
//! * out-of-bounds references ([`EvidenceKind::OutOfBounds`]),
//! * double occupancy ([`EvidenceKind::DoubleOccupancy`]),
//! * orphan sectors ([`EvidenceKind::Orphan`]), and
//! * declared-length disagreements
//!   ([`EvidenceKind::DeclaredLengthMismatch`]).
//!
//! An audit never writes a byte.  Its result is a pure value: no cache,
//! counter or temporary state is shared between calls, so identical input
//! always produces an identical report, and a failed call leaves nothing
//! behind for the next one.  When the damage is repairable, the report
//! produces a [`RepairPlan`] stamped with the SHA-256 *precondition digest*
//! of the audited bytes; the plan can only be applied against bytes whose
//! digest still matches, and applying rebuilds a compacted, valid file
//! through the same production write path as
//! [`CompoundFile::copy_to`](crate::CompoundFile::copy_to).
//!
//! The tolerant chain walkers below share their parsing primitives
//! ([`Header`], [`DirEntry`], [`Version`], the MS-CFB constants) and their
//! chain-walking semantics with the production parser; the repair path
//! reuses the production `CompoundFile` writer directly.

use std::fmt;
use std::fs;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use fnv::{FnvHashMap, FnvHashSet};
use uuid::Uuid;
use web_time::SystemTime;

use crate::internal::consts;
use crate::internal::sha256;
use crate::internal::{
    DirEntry, Header, ObjType, Validation, Version,
};
use crate::CompoundFile;

//===========================================================================//
// Public data model
//===========================================================================//

/// Which of the four CFB allocation structures a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Layer {
    /// The double-indirect FAT: the chain of sectors listing FAT sectors.
    Difat,
    /// The file allocation table and the regular sector chains it describes.
    Fat,
    /// The MiniFAT and the mini-sector chains it describes.
    MiniFat,
    /// The chain of directory sectors.
    Directory,
}

impl fmt::Display for Layer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Layer::Difat => "DIFAT",
            Layer::Fat => "FAT",
            Layer::MiniFat => "MiniFAT",
            Layer::Directory => "directory",
        })
    }
}

/// The particular kind of structural corruption that was observed.
///
/// The categories required by the CFB recovery contract are kept distinct:
/// cycles, out-of-range references, double occupancy, orphan sectors, and
/// declared-length disagreements are never conflated with each other.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum EvidenceKind {
    /// A chain eventually points back to a sector it visited earlier.
    Cycle,
    /// A table entry names a sector beyond the end of the file or table.
    OutOfBounds,
    /// The same sector is claimed by two distinct owners.
    DoubleOccupancy,
    /// A marked-in-use sector is reachable from no owner at all.
    Orphan,
    /// A stream's declared length disagrees with its chain capacity.
    DeclaredLengthMismatch,
    /// The directory chain ends before all directory entries are covered.
    DirectoryTruncated,
    /// A directory entry's 128-byte record cannot be parsed.
    MalformedDirectoryEntry,
    /// A header count field does not match the corresponding on-disk chain.
    HeaderCountMismatch,
}

impl EvidenceKind {
    /// A short, stable, machine-readable identifier for the category.
    pub fn code(&self) -> &'static str {
        match self {
            EvidenceKind::Cycle => "cycle",
            EvidenceKind::OutOfBounds => "out_of_bounds",
            EvidenceKind::DoubleOccupancy => "double_occupancy",
            EvidenceKind::Orphan => "orphan_sector",
            EvidenceKind::DeclaredLengthMismatch => {
                "declared_length_mismatch"
            }
            EvidenceKind::DirectoryTruncated => "directory_truncated",
            EvidenceKind::MalformedDirectoryEntry => {
                "malformed_directory_entry"
            }
            EvidenceKind::HeaderCountMismatch => "header_count_mismatch",
        }
    }
}

impl fmt::Display for EvidenceKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            EvidenceKind::Cycle => "chain contains a cycle",
            EvidenceKind::OutOfBounds => "chain pointer is out of bounds",
            EvidenceKind::DoubleOccupancy => {
                "sector is claimed by more than one owner"
            }
            EvidenceKind::Orphan => "allocated sector has no owner",
            EvidenceKind::DeclaredLengthMismatch => {
                "declared stream length does not match its chain"
            }
            EvidenceKind::DirectoryTruncated => {
                "directory chain is truncated"
            }
            EvidenceKind::MalformedDirectoryEntry => {
                "directory entry is malformed"
            }
            EvidenceKind::HeaderCountMismatch => {
                "header count disagrees with the actual chain"
            }
        })
    }
}

/// The object that claims ownership of a sector or mini sector.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Owner {
    /// A DIFAT (FAT-locator) sector.
    DifatSector,
    /// A FAT sector; the index is its position in the DIFAT list.
    FatSector(u32),
    /// The directory chain.
    Directory,
    /// The MiniFAT chain.
    MiniFat,
    /// The root entry's mini-stream container chain.
    RootContainer,
    /// A stream entry, identified by its directory stream ID.
    Stream {
        /// Directory stream ID of the owning entry.
        stream_id: u32,
        /// Whether the stream lives in the MiniFAT (`true`) or FAT (`false`).
        mini: bool,
    },
}

impl fmt::Display for Owner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Owner::DifatSector => f.write_str("a DIFAT sector"),
            Owner::FatSector(index) => write!(f, "FAT sector #{index}"),
            Owner::Directory => f.write_str("the directory chain"),
            Owner::MiniFat => f.write_str("the MiniFAT chain"),
            Owner::RootContainer => {
                f.write_str("the root mini-stream container")
            }
            Owner::Stream { stream_id, mini } => {
                let table = if *mini { "mini stream" } else { "stream" };
                write!(f, "{table} (directory entry {stream_id})")
            }
        }
    }
}

/// A precise location for a piece of evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Location {
    /// A byte offset into the file image.
    ByteOffset(u64),
    /// An index into one of the allocation tables.
    TableIndex(u32),
    /// A directory entry index (0-based, in chain order).
    DirEntry(u32),
    /// A regular sector ID.
    Sector(u32),
    /// A mini-sector ID within the root mini-stream container.
    MiniSector(u32),
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Location::ByteOffset(offset) => write!(f, "byte offset {offset}"),
            Location::TableIndex(index) => write!(f, "table index {index}"),
            Location::DirEntry(index) => write!(f, "directory entry {index}"),
            Location::Sector(id) => write!(f, "sector {id}"),
            Location::MiniSector(id) => write!(f, "mini sector {id}"),
        }
    }
}

/// One observed structural problem, with enough context to locate it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evidence {
    layer: Layer,
    kind: EvidenceKind,
    location: Location,
    sector_id: Option<u32>,
    owners: Vec<Owner>,
    detail: String,
}

impl Evidence {
    /// The allocation structure this evidence concerns.
    pub fn layer(&self) -> Layer {
        self.layer
    }

    /// The category of corruption; distinct categories are never merged.
    pub fn kind(&self) -> EvidenceKind {
        self.kind
    }

    /// The most precise location available for the first offending byte.
    pub fn location(&self) -> Location {
        self.location
    }

    /// The regular sector involved, when one applies.
    pub fn sector_id(&self) -> Option<u32> {
        self.sector_id
    }

    /// The distinct owners involved (populated for double occupancy).
    pub fn owners(&self) -> &[Owner] {
        &self.owners
    }

    /// A human-readable description of the violation.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}] {} at {}",
            self.layer,
            self.kind.code(),
            self.location
        )?;
        if !self.owners.is_empty() {
            write!(f, " (owners:")?;
            for owner in self.owners.iter() {
                write!(f, " {owner}")?;
            }
            write!(f, ")")?;
        }
        write!(f, ": {}", self.detail)
    }
}

/// A high-level description of one repair step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RepairAction {
    /// Re-read the directory chain and rebuild the object tree.
    RebuildObjectTree,
    /// Recompute all FAT chains, dropping unreachable (orphan) sectors.
    RebuildFat,
    /// Recompute the MiniFAT and the root mini-stream container.
    RebuildMiniFat,
    /// Rebuild the DIFAT to match the rebuilt FAT.
    RebuildDifat,
    /// Truncate a stream's allocation to its declared length.
    TruncateStream {
        /// Directory stream ID of the affected stream.
        stream_id: u32,
    },
}

impl fmt::Display for RepairAction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RepairAction::RebuildObjectTree => {
                f.write_str("rebuild the storage/stream tree from the \
                             salvageable directory entries")
            }
            RepairAction::RebuildFat => {
                f.write_str("rebuild the FAT, dropping orphan sectors")
            }
            RepairAction::RebuildMiniFat => {
                f.write_str("rebuild the MiniFAT and root mini-stream \
                             container, dropping orphan mini sectors")
            }
            RepairAction::RebuildDifat => {
                f.write_str("rebuild the DIFAT to match the rebuilt FAT")
            }
            RepairAction::TruncateStream { stream_id } => {
                write!(
                    f,
                    "truncate the allocation of stream (directory entry \
                     {stream_id}) to its declared length"
                )
            }
        }
    }
}

//===========================================================================//
// Audit report
//===========================================================================//

/// The result of a read-only structural audit of one CFB image.
///
/// A report is a pure snapshot of a single audit call: it owns all of its
/// data, shares nothing with previous or later calls, and compares equal to
/// any other report produced from the same input bytes.
#[derive(Clone, Debug)]
pub struct AuditReport {
    version: Version,
    file_len: u64,
    num_sectors: u32,
    evidence: Vec<Evidence>,
    digest: [u8; 32],
    reparable: bool,
    repair_actions: Vec<RepairAction>,
    recipe: Option<Recipe>,
}

impl AuditReport {
    /// The format version recorded in the image header.
    pub fn version(&self) -> Version {
        self.version
    }

    /// Total length, in bytes, of the audited image.
    pub fn file_len(&self) -> u64 {
        self.file_len
    }

    /// Number of regular sectors implied by the image length.
    pub fn num_sectors(&self) -> u32 {
        self.num_sectors
    }

    /// All observed problems, in the report's deterministic order.
    ///
    /// Evidence is sorted by layer, then kind, then location, so that
    /// changing enumeration order, cache state, or thread scheduling around
    /// the audit cannot change the result for a given input.
    pub fn evidence(&self) -> &[Evidence] {
        &self.evidence
    }

    /// The first violation in deterministic order, if any, together with its
    /// location and context.
    pub fn first_evidence(&self) -> Option<&Evidence> {
        self.evidence.first()
    }

    /// True iff at least one piece of evidence was found.
    pub fn is_corrupt(&self) -> bool {
        !self.evidence.is_empty()
    }

    /// SHA-256 digest of the exact bytes that were audited.  This is the
    /// version identity of the report: plans and retries are only ever
    /// matched against inputs with the same digest.
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// The digest formatted as lowercase hexadecimal.
    pub fn digest_hex(&self) -> String {
        hex_digest(&self.digest)
    }

    /// Whether a read-only salvage of the reachable tree is possible.
    pub fn is_repairable(&self) -> bool {
        self.reparable
    }

    /// The human-readable steps the repair plan would perform.
    pub fn repair_actions(&self) -> &[RepairAction] {
        &self.repair_actions
    }

    /// Produces the repair plan for this report.
    ///
    /// The plan is inert: obtaining it (like everything else in an audit)
    /// writes nothing.  It becomes effective only through an explicit
    /// `apply`/`render` call, and only if the input still matches the
    /// recorded precondition digest.
    pub fn plan(&self) -> RepairPlan {
        RepairPlan {
            digest: self.digest,
            reparable: self.reparable,
            actions: self.repair_actions.clone(),
            recipe: self.recipe.clone(),
        }
    }
}

impl PartialEq for AuditReport {
    fn eq(&self, other: &Self) -> bool {
        // Two reports are equivalent when their observable output matches;
        // the salvage recipe is an internal function of the same input.
        self.version == other.version
            && self.file_len == other.file_len
            && self.num_sectors == other.num_sectors
            && self.evidence == other.evidence
            && self.digest == other.digest
            && self.reparable == other.reparable
            && self.repair_actions == other.repair_actions
    }
}

impl Eq for AuditReport {}

//===========================================================================//
// Repair plan
//===========================================================================//

/// A read-only, digest-gated plan for repairing an audited image.
///
/// The plan records the SHA-256 digest of the bytes it was built from.  Every
/// application re-verifies that digest before doing anything else; if the
/// input changed since the audit, the application fails with
/// [`io::ErrorKind::InvalidData`] without writing a single byte.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    digest: [u8; 32],
    reparable: bool,
    actions: Vec<RepairAction>,
    recipe: Option<Recipe>,
}

impl RepairPlan {
    /// SHA-256 digest the input bytes must still have for this plan to apply.
    pub fn precondition_digest(&self) -> [u8; 32] {
        self.digest
    }

    /// The precondition digest formatted as lowercase hexadecimal.
    pub fn precondition_digest_hex(&self) -> String {
        hex_digest(&self.digest)
    }

    /// The ordered steps the repair would perform.
    pub fn actions(&self) -> &[RepairAction] {
        &self.actions
    }

    /// Whether this plan can be applied at all (some corruption, such as
    /// double occupancy, has no unambiguous read-only repair).
    pub fn is_applicable(&self) -> bool {
        self.reparable && self.recipe.is_some()
    }

    /// Describes what the plan would do.  This is a pure function of the
    /// plan: it opens no file and writes no byte, to any sink, ever.
    pub fn dry_run(&self) -> String {
        let mut out = String::new();
        out.push_str("CFB repair plan (dry run; no bytes are written)\n");
        out.push_str(&format!(
            "precondition: input SHA-256 must be {}\n",
            self.precondition_digest_hex()
        ));
        if !self.is_applicable() {
            out.push_str(
                "not applicable: the observed corruption has no unambiguous \
                 read-only repair\n",
            );
            return out;
        }
        for (index, action) in self.actions.iter().enumerate() {
            out.push_str(&format!("  {}. {action}\n", index + 1));
        }
        out.push_str(
            "then: rebuild a compacted valid file through the production \
             copy path and, for path targets, replace the original \
             atomically only after re-verifying the digest\n",
        );
        out
    }

    /// Builds the repaired image in memory.
    ///
    /// `current_input` must be the bytes the plan is meant to repair; they
    /// are hashed and compared against the precondition digest first.  The
    /// input is only read; the repaired image is returned as a fresh `Vec`.
    pub fn render_repaired(&self, current_input: &[u8]) -> io::Result<Vec<u8>> {
        self.verify_precondition(current_input)?;
        let recipe = self.recipe.as_ref().expect("checked above");
        render_recipe(recipe)
    }

    /// Applies the plan to a seekable, writable sink.
    ///
    /// The digest is verified against `current_input` before the sink is
    /// touched, so a stale plan or an inapplicable plan writes nothing.  The
    /// repaired image is written from offset zero.  Note that a generic sink
    /// cannot be replaced atomically and cannot be truncated through this
    /// API; use [`RepairPlan::apply_to_path`] when repairing a file on disk.
    pub fn apply_to_writer<W: Write + Seek>(
        &self,
        current_input: &[u8],
        writer: &mut W,
    ) -> io::Result<()> {
        let repaired = self.render_repaired(current_input)?;
        writer.seek(SeekFrom::Start(0))?;
        writer.write_all(&repaired)?;
        writer.flush()?;
        Ok(())
    }

    /// Applies the plan to a file path, replacing it atomically.
    ///
    /// The file is re-hashed immediately before replacement; if it changed
    /// since the audit, or the plan is not applicable, an
    /// [`io::ErrorKind::InvalidData`] error is returned and no byte of the
    /// file is modified.  Otherwise the repaired image is written and
    /// fsynced to a sibling temporary file and renamed over the original, so
    /// a mid-write I/O failure leaves the original file intact and leaves no
    /// temporary files behind.
    pub fn apply_to_path<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let path = path.as_ref();
        let current = fs::read(path)?;
        let repaired = self.render_repaired(&current)?;
        let tmp_path = sibling_temp_path(path)?;
        let result = write_temp_file(&tmp_path, &repaired)
            .and_then(|()| rename_repair(&tmp_path, path));
        if let Err(error) = result {
            let _ = fs::remove_file(&tmp_path);
            return Err(error);
        }
        Ok(())
    }

    fn verify_precondition(&self, current_input: &[u8]) -> io::Result<()> {
        if !self.is_applicable() {
            invalid_data!(
                "Cannot apply repair plan: the audited corruption has no \
                 unambiguous read-only repair"
            );
        }
        let actual = sha256::digest(current_input);
        if actual != self.digest {
            invalid_data!(
                "Cannot apply repair plan: the input changed since the \
                 audit (expected SHA-256 {}, found {})",
                hex_digest(&self.digest),
                hex_digest(&actual)
            );
        }
        Ok(())
    }
}

fn hex_digest(digest: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(64);
    for byte in digest.iter() {
        let _ = write!(&mut out, "{byte:02x}");
    }
    out
}

fn sibling_temp_path(path: &Path) -> io::Result<PathBuf> {
    let file_name = match path.file_name() {
        Some(name) => name.to_os_string(),
        None => invalid_input!("Path has no file name: {:?}", path),
    };
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let mut tmp_name = file_name;
    tmp_name.push(format!(
        ".repair-{}-{nanos}.tmp",
        std::process::id()
    ));
    Ok(path.with_file_name(tmp_name))
}

fn write_temp_file(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut tmp = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    tmp.write_all(bytes)?;
    tmp.flush()?;
    tmp.sync_all()?;
    Ok(())
}

#[cfg(not(windows))]
fn rename_repair(tmp_path: &Path, path: &Path) -> io::Result<()> {
    // POSIX rename(2) atomically replaces the destination.
    fs::rename(tmp_path, path)
}

#[cfg(windows)]
fn rename_repair(tmp_path: &Path, path: &Path) -> io::Result<()> {
    // Windows cannot rename over an existing file; remove it first.  This
    // is a best-effort fallback for a platform without atomic replace.
    let _ = fs::remove_file(path);
    fs::rename(tmp_path, path)
}
