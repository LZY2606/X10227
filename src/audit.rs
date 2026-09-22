//! Opt-in, read-only structural audits of compound files.
//!
//! A normal [`crate::CompoundFile::open`] parses the file lazily and may only
//! discover corruption when a particular stream is touched.  The functions
//! and types in this module instead walk every allocation structure of a
//! compound file up front -- the DIFAT, the FAT, the directory chain, the
//! MiniFAT and the mini stream -- without ever mutating the input, and report
//! every piece of corruption they find as a labelled [`Finding`].
//!
//! The audit is requested explicitly through
//! [`crate::OpenOptions::audit_with`] (or the convenience helpers [`audit`]
//! and [`OpenOptions::audit`]); existing open/create entry points keep their
//! original behavior.
//!
//! The returned [`AuditReport`] also carries a read-only [`RepairPlan`].  The
//! plan records a precondition digest of the audited bytes; it can only be
//! applied explicitly with [`RepairPlan::apply_to`], and only if the input
//! still hashes the same.  Applying a plan compacts the recoverable entries
//! into a *new* compound file written to the given destination, so the input
//! file itself is never modified.  [`RepairPlan::dry_run`] describes what the
//! plan would do without touching any `Write` target at all.
//!
//! Auditing is a pure function of the input bytes: every call rebuilds its
//! analysis from scratch and keeps no thread-local or global state, so
//! repeated audits, reordered inputs, and concurrent audits cannot leak
//! findings or counters into one another.

use std::collections::BTreeMap;
use std::fmt;
use std::hash::Hasher;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::mem::size_of;

use fnv::FnvHasher;

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::{CompoundFile, OpenOptions, ReadLeNumber};

//===========================================================================//
// Public evidence types
//===========================================================================//

/// The allocation structure that a piece of corruption evidence concerns.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum Layer {
    /// The double-indirect FAT (the chain of sectors listing FAT sectors).
    Difat,
    /// The main file allocation table.
    Fat,
    /// The chain of sectors holding directory entries.
    Directory,
    /// The mini-FAT and the root mini stream.
    MiniFat,
    /// A sibling/child tree of directory entries.
    DirectoryTree,
}

impl fmt::Display for Layer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Layer::Difat => "DIFAT",
            Layer::Fat => "FAT",
            Layer::Directory => "directory chain",
            Layer::MiniFat => "MiniFAT",
            Layer::DirectoryTree => "directory tree",
        })
    }
}

/// The kind of damage found at one location.
///
/// The variants deliberately separate the five distinct ways an allocation
/// structure can be broken:
///
/// * [`CorruptionKind::ChainCycle`] -- a chain loops back onto itself;
/// * [`CorruptionKind::OutOfBoundsPointer`] -- a pointer names a sector that
///   does not exist or a table entry value that is not legal;
/// * [`CorruptionKind::DoubleClaim`] -- one sector is reachable from more
///   than one chain (a crossed chain);
/// * [`CorruptionKind::Orphan`] -- a sector is allocated but not reachable
///   from any chain;
/// * [`CorruptionKind::LengthMismatch`] -- a declared length does not match
///   the sectors actually available.
///
/// [`CorruptionKind::CountMismatch`] and [`CorruptionKind::InvalidValue`]
/// cover structural lies in header fields and dangling directory links.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum CorruptionKind {
    /// A chain contains a cycle: a sector is reached a second time.
    ChainCycle,
    /// A FAT/MiniFAT entry or directory link points outside its table or at
    /// an illegal value.
    OutOfBoundsPointer,
    /// A sector belongs to more than one chain (crossed chains).
    DoubleClaim,
    /// A sector is marked allocated but no chain reaches it.
    Orphan,
    /// A declared length (stream length or chain capacity) disagrees with
    /// the sectors actually available.
    LengthMismatch,
    /// A header count field disagrees with the chain it describes.
    CountMismatch,
    /// A directory sibling/child link names an entry that does not exist, or
    /// a table entry holds an otherwise-illegal value.
    InvalidValue,
}

impl CorruptionKind {
    /// A short, stable keyword identifying this kind of corruption.
    pub fn keyword(self) -> &'static str {
        match self {
            CorruptionKind::ChainCycle => "chain-cycle",
            CorruptionKind::OutOfBoundsPointer => "out-of-bounds-pointer",
            CorruptionKind::DoubleClaim => "double-claim",
            CorruptionKind::Orphan => "orphan-sector",
            CorruptionKind::LengthMismatch => "length-mismatch",
            CorruptionKind::CountMismatch => "count-mismatch",
            CorruptionKind::InvalidValue => "invalid-value",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.keyword())
    }
}

/// Where a [`Finding`] was observed.
///
/// Every field is optional except the layer; the accessors that apply to a
/// given layer are populated so that the first violated location can be
/// pinpointed without re-parsing the file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Location {
    layer: Layer,
    sector_id: Option<u32>,
    table_index: Option<u32>,
    stream_id: Option<u32>,
    entry_name: Option<String>,
    detail: String,
}

impl Location {
    /// The allocation structure involved.
    pub fn layer(&self) -> Layer {
        self.layer
    }
    /// The regular sector ID at fault, if the finding concerns one.
    pub fn sector_id(&self) -> Option<u32> {
        self.sector_id
    }
    /// The FAT/MiniFAT/DIFAT entry index at fault, when applicable.
    pub fn table_index(&self) -> Option<u32> {
        self.table_index
    }
    /// The directory stream ID involved, when applicable.
    pub fn stream_id(&self) -> Option<u32> {
        self.stream_id
    }
    /// The name of the offending directory entry, when applicable.
    pub fn entry_name(&self) -> Option<&str> {
        self.entry_name.as_deref()
    }
    /// Human-readable context for this location.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.layer)?;
        if let Some(index) = self.table_index {
            write!(f, " entry {index}")?;
        }
        if let Some(sector) = self.sector_id {
            write!(f, " sector {sector}")?;
        }
        if let Some(stream_id) = self.stream_id {
            write!(f, " directory entry {stream_id}")?;
        }
        if let Some(name) = &self.entry_name {
            write!(f, " ({name:?})")?;
        }
        write!(f, ": {}", self.detail)
    }
}

/// One piece of corruption evidence.
///
/// Findings are numbered from zero in a fixed, input-driven order (DIFAT,
/// then the FAT, then the directory chain, then the MiniFAT, then directory
/// trees and orphan scans), so `findings()[0]` is always the first violation
/// and the numbering is stable across repeated audits and changes to call
/// ordering or scheduling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    index: usize,
    kind: CorruptionKind,
    location: Location,
}

impl Finding {
    /// The position of this finding in the deterministic evidence list.
    pub fn index(&self) -> usize {
        self.index
    }
    /// What kind of corruption this is.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }
    /// Where the corruption was observed.
    pub fn location(&self) -> &Location {
        &self.location
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{} [{}] {}", self.index, self.kind.keyword(), self.location)
    }
}

/// What kind of directory entry an [`AuditedEntry`] is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum AuditedEntryKind {
    /// The root storage entry.
    Root,
    /// A storage (directory) object.
    Storage,
    /// A stream object.
    Stream,
    /// A directory slot whose object type byte is unallocated.
    Unallocated,
    /// A directory slot whose object type byte is not a legal value.
    Invalid,
}

/// One directory slot as the audit saw it.
///
/// This is the audit's own value type; it is rebuilt from the file bytes on
/// every audit and never aliases the mutable internals of an opened
/// [`CompoundFile`].
#[derive(Clone, Debug)]
pub struct AuditedEntry {
    stream_id: u32,
    kind: AuditedEntryKind,
    name: String,
    start_sector: u32,
    stream_len: u64,
    left_sibling: u32,
    right_sibling: u32,
    child: u32,
    reachable: bool,
}

impl AuditedEntry {
    /// The directory stream ID (slot index) of this entry.
    pub fn stream_id(&self) -> u32 {
        self.stream_id
    }
    /// The object type recorded in this slot.
    pub fn kind(&self) -> AuditedEntryKind {
        self.kind
    }
    /// The raw name recorded in this slot (`"Root Entry"` for the root).
    pub fn name(&self) -> &str {
        &self.name
    }
    /// The entry's declared starting sector (or mini sector for small
    /// streams).
    pub fn start_sector(&self) -> u32 {
        self.start_sector
    }
    /// The entry's declared stream length, in bytes.
    pub fn stream_len(&self) -> u64 {
        self.stream_len
    }
    /// The raw left-sibling pointer.
    pub fn left_sibling(&self) -> u32 {
        self.left_sibling
    }
    /// The raw right-sibling pointer.
    pub fn right_sibling(&self) -> u32 {
        self.right_sibling
    }
    /// The raw child pointer.
    pub fn child(&self) -> u32 {
        self.child
    }
    /// Whether the slot is reachable from the root through well-formed
    /// sibling/child links.
    pub fn is_reachable(&self) -> bool {
        self.reachable
    }
    /// Whether this slot names a data stream (as opposed to a storage).
    pub fn is_stream(&self) -> bool {
        self.kind == AuditedEntryKind::Stream
    }
    /// Whether this slot's declared length puts its data in the mini stream.
    pub fn is_mini(&self) -> bool {
        self.is_stream()
            && self.stream_len < consts::MINI_STREAM_CUTOFF as u64
    }
}

/// A precondition fingerprint of the bytes a plan was computed from.
///
/// Two `AuditDigest` values are equal exactly when the audited input bytes
/// are identical.  The digest uses a deterministic, non-cryptographic hash;
/// it is an accidental-change guard, not a security boundary.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct AuditDigest(u64);

impl AuditDigest {
    /// The raw 64-bit digest value.
    pub fn value(self) -> u64 {
        self.0
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

//===========================================================================//
// Internal, rebuilt-per-call analysis
//===========================================================================//

/// What one regular sector is used for, as ownership is discovered.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Fat,
    Difat,
    Directory,
    /// A data chain starting at a directory stream ID.
    Chain(u32),
    /// The MiniFAT chain.
    Minifat,
}

/// A parsed directory slot plus the stream ID it lives at.
#[derive(Clone)]
struct RawSlot {
    stream_id: u32,
    entry: DirEntry,
}

/// The outcome of walking one table chain with cycle and bounds guards.
#[derive(Default)]
struct Walk {
    sectors: Vec<u32>,
    /// Set when the walk stopped before END_OF_CHAIN.
    stopped: Option<(CorruptionKind, String)>,
}

/// The source of one recovered stream's bytes when applying a repair plan.
#[derive(Clone, Debug, PartialEq, Eq)]
enum StreamSource {
    /// A chain of regular sectors; bytes are truncated to `len`.
    Fat { start: u32, len: u64 },
    /// A chain of mini sectors within the root mini stream.
    Mini { start: u32, len: u64 },
    /// The stream could not be recovered (its start pointer is unusable).
    Unrecoverable,
    /// The stream was intact but empty.
    Empty,
}

/// A salvagable directory entry described by full path.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SalvageItem {
    Storage(String),
    Stream(String, StreamSource),
}

/// Everything one audit derives from the input bytes.  Borrows only the
/// in-memory byte snapshot and holds no handles, thread-locals, or globals,
/// so each invocation is an isolated pure recomputation.
struct Analysis<'a> {
    bytes: &'a [u8],
    version: Version,
    sector_len: u32,
    num_sectors: u32,
    header: Header,
    difat: Vec<u32>,
    difat_sector_ids: Vec<u32>,
    fat: Vec<u32>,
    findings: Vec<Finding>,
    /// owner[i] records who first claimed regular sector i.
    owners: Vec<Option<Owner>>,
    /// Whether FAT entry i marks sector i allocated in some way.
    fat_allocated: Vec<bool>,
    dir_chain: Vec<u32>,
    slots: Vec<RawSlot>,
    minifat: Vec<u32>,
    /// owner[i] = stream ID that first claimed mini sector i.
    mini_owners: Vec<Option<u32>>,
    entries: Vec<AuditedEntry>,
    /// Full path for every reachable entry keyed by stream ID.
    paths: BTreeMap<u32, String>,
    /// Recovered-stream metadata per stream ID; paths are attached after the
    /// directory-tree pass.
    stream_sources: BTreeMap<u32, StreamSource>,
}

impl<'a> Analysis<'a> {
    fn finding(
        &mut self,
        kind: CorruptionKind,
        layer: Layer,
        detail: impl Into<String>,
    ) {
        let index = self.findings.len();
        self.findings.push(Finding {
            index,
            kind,
            location: Location {
                layer,
                sector_id: None,
                table_index: None,
                stream_id: None,
                entry_name: None,
                detail: detail.into(),
            },
        });
    }

    fn finding_at(
        &mut self,
        kind: CorruptionKind,
        layer: Layer,
        sector_id: Option<u32>,
        table_index: Option<u32>,
        detail: impl Into<String>,
    ) {
        let index = self.findings.len();
        self.findings.push(Finding {
            index,
            kind,
            location: Location {
                layer,
                sector_id,
                table_index,
                stream_id: None,
                entry_name: None,
                detail: detail.into(),
            },
        });
    }

    fn finding_for_entry(
        &mut self,
        kind: CorruptionKind,
        layer: Layer,
        stream_id: u32,
        name: Option<String>,
        detail: impl Into<String>,
    ) {
        let index = self.findings.len();
        self.findings.push(Finding {
            index,
            kind,
            location: Location {
                layer,
                sector_id: None,
                table_index: None,
                stream_id: Some(stream_id),
                entry_name: name,
                detail: detail.into(),
            },
        });
    }

    // -- raw byte helpers ------------------------------------------------ //

    fn sector_offset(&self, sector_id: u32) -> usize {
        consts::HEADER_LEN + (sector_id as usize) * (self.sector_len as usize)
    }

    /// Reads one regular sector, recording an out-of-bounds finding when the
    /// sector ID is beyond the file instead of panicking.
    fn sector_bytes(
        &mut self,
        sector_id: u32,
        layer: Layer,
        table_index: Option<u32>,
    ) -> Option<&'a [u8]> {
        let start = self.sector_offset(sector_id);
        let end = match start.checked_add(self.sector_len as usize) {
            Some(end) => end,
            None => {
                self.finding_at(
                    CorruptionKind::OutOfBoundsPointer,
                    layer,
                    Some(sector_id),
                    table_index,
                    format!("sector {sector_id} is beyond the file"),
                );
                return None;
            }
        };
        if sector_id > consts::MAX_REGULAR_SECTOR || end > self.bytes.len() {
            self.finding_at(
                CorruptionKind::OutOfBoundsPointer,
                layer,
                Some(sector_id),
                table_index,
                format!(
                    "sector {sector_id} is beyond the file ({} sectors)",
                    self.num_sectors
                ),
            );
            None
        } else {
            Some(&self.bytes[start..end])
        }
    }

    fn read_u32_at(&self, offset: usize) -> u32 {
        u32::from_le_bytes([
            self.bytes[offset],
            self.bytes[offset + 1],
            self.bytes[offset + 2],
            self.bytes[offset + 3],
        ])
    }

    // -- generic chain walks --------------------------------------------- //

    /// Walks a chain in `table` (the FAT or MiniFAT) starting at `start`,
    /// stopping -- rather than looping or indexing out of bounds -- on the
    /// first cycle or illegal pointer.
    fn walk_table(
        &self,
        table: &[u32],
        start: u32,
    ) -> Walk {
        let mut walk = Walk::default();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return walk;
        }
        let mut current = start;
        loop {
            walk.sectors.push(current);
            if current as usize >= table.len() {
                walk.stopped = Some((
                    CorruptionKind::OutOfBoundsPointer,
                    format!(
                        "sector {current} has no entry (table has {} entries)",
                        table.len()
                    ),
                ));
                return walk;
            }
            let next = table[current as usize];
            if next == consts::END_OF_CHAIN {
                return walk;
            }
            if next == consts::FREE_SECTOR
                || next > consts::MAX_REGULAR_SECTOR
                || next as usize >= table.len()
            {
                walk.stopped = Some((
                    CorruptionKind::OutOfBoundsPointer,
                    format!("entry {current} has invalid next pointer {next}"),
                ));
                return walk;
            }
            if walk.sectors.contains(&next) {
                walk.stopped = Some((
                    CorruptionKind::ChainCycle,
                    format!("chain loops back to sector {next}"),
                ));
                return walk;
            }
            current = next;
        }
    }

    /// Claims each regular sector in `sectors` for `owner`; records a
    /// double-claim finding for the first sector already owned by someone
    /// else.
    fn claim_regular_sectors(
        &mut self,
        sectors: &[u32],
        owner: Owner,
        layer: Layer,
    ) {
        for &sector_id in sectors {
            if sector_id as usize >= self.owners.len() {
                continue;
            }
            if let Some(existing) = self.owners[sector_id as usize] {
                if !same_owner(existing, owner) {
                    self.finding_at(
                        CorruptionKind::DoubleClaim,
                        layer,
                        Some(sector_id),
                        None,
                        format!(
                            "sector {sector_id} is shared between {} and {}",
                            owner_label(existing),
                            owner_label(owner)
                        ),
                    );
                }
            } else {
                self.owners[sector_id as usize] = Some(owner);
            }
        }
    }

    // -- data extraction shared with the repair path --------------------- //

    /// Gathers the raw bytes of a FAT chain, truncating to `len` bytes.
    fn fat_chain_bytes(
        &self,
        walk: &Walk,
        len: u64,
    ) -> (Vec<u8>, Option<CorruptionKind>) {
        let sector_len = self.sector_len as u64;
        let capacity = walk.sectors.len() as u64 * sector_len;
        let mut out = Vec::with_capacity(len.min(capacity) as usize);
        for &sector_id in &walk.sectors {
            let start = self.sector_offset(sector_id);
            let end = start + self.sector_len as usize;
            if sector_id > consts::MAX_REGULAR_SECTOR
                || end > self.bytes.len()
            {
                return (out, Some(CorruptionKind::OutOfBoundsPointer));
            }
            out.extend_from_slice(&self.bytes[start..end]);
        }
        out.truncate(len as usize);
        let stop = walk.stopped.map(|(kind, _)| kind);
        if len > capacity && stop.is_none() {
            (out, Some(CorruptionKind::LengthMismatch))
        } else {
            (out, stop)
        }
    }

    /// Walks the root mini stream's FAT chain once and returns its bytes.
    fn mini_stream_bytes(&self) -> (Vec<u8>, Option<(CorruptionKind, String)>) {
        let root = &self.slots[0].entry;
        let walk = self.walk_table(&self.fat, root.start_sector);
        let sector_len = self.sector_len as usize;
        let mut out = Vec::with_capacity(walk.sectors.len() * sector_len);
        for &sector_id in &walk.sectors {
            let start = self.sector_offset(sector_id);
            let end = start + sector_len;
            if sector_id > consts::MAX_REGULAR_SECTOR
                || end > self.bytes.len()
            {
                return (
                    out,
                    Some((
                        CorruptionKind::OutOfBoundsPointer,
                        format!("mini stream sector {sector_id} beyond file"),
                    )),
                );
            }
            out.extend_from_slice(&self.bytes[start..end]);
        }
        (out, walk.stopped)
    }

    /// Gathers mini-sector bytes out of the mini stream for one mini chain.
    fn mini_chain_bytes(
        &self,
        mini_stream: &[u8],
        walk: &Walk,
        len: u64,
    ) -> (Vec<u8>, Option<CorruptionKind>) {
        let mini_len = consts::MINI_SECTOR_LEN as u64;
        let capacity = walk.sectors.len() as u64 * mini_len;
        let mut out = Vec::with_capacity(len.min(capacity) as usize);
        for &mini_id in &walk.sectors {
            let start = mini_id as usize * consts::MINI_SECTOR_LEN;
            let end = start + consts::MINI_SECTOR_LEN;
            if end > mini_stream.len() {
                return (out, Some(CorruptionKind::OutOfBoundsPointer));
            }
            out.extend_from_slice(&mini_stream[start..end]);
        }
        out.truncate(len as usize);
        let stop = walk.stopped.map(|(kind, _)| kind);
        if len > capacity && stop.is_none() {
            (out, Some(CorruptionKind::LengthMismatch))
        } else {
            (out, stop)
        }
    }
}

fn same_owner(a: Owner, b: Owner) -> bool {
    match (a, b) {
        (Owner::Chain(x), Owner::Chain(y)) => x == y,
        (Owner::Fat, Owner::Fat)
        | (Owner::Difat, Owner::Difat)
        | (Owner::Directory, Owner::Directory)
        | (Owner::Minifat, Owner::Minifat) => true,
        _ => false,
    }
}

fn owner_label(owner: Owner) -> String {
    match owner {
        Owner::Fat => "a FAT sector".to_string(),
        Owner::Difat => "a DIFAT sector".to_string(),
        Owner::Directory => "the directory chain".to_string(),
        Owner::Minifat => "the MiniFAT chain".to_string(),
        Owner::Chain(stream_id) => {
            format!("the chain of directory entry {stream_id}")
        }
    }
}

//===========================================================================//
// The audit itself
//===========================================================================//

/// Runs the full audit over an in-memory snapshot.  This function is the
/// single analysis used by both public auditing and plan application; the
/// repair path never carries a second, test-only copy of these rules.
fn analyze(bytes: &[u8]) -> io::Result<Analysis<'_>> {
    if bytes.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            bytes.len()
        );
    }
    // Reuse the production header parser; audit always parses permissively so
    // that it can continue and gather evidence behind a lenient header.
    let mut header_cursor = io::Cursor::new(bytes);
    let header = Header::read_from(&mut header_cursor, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len() as u32;
    if bytes.len() < sector_len as usize {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            bytes.len(),
            sector_len
        );
    }
    let num_sectors =
        ((bytes.len() - consts::HEADER_LEN) / sector_len as usize) as u32;

    let mut analysis = Analysis {
        bytes,
        version,
        sector_len,
        num_sectors,
        header: header.clone(),
        difat: Vec::new(),
        difat_sector_ids: Vec::new(),
        fat: Vec::new(),
        findings: Vec::new(),
        owners: vec![None; num_sectors as usize],
        fat_allocated: vec![false; num_sectors as usize],
        dir_chain: Vec::new(),
        slots: Vec::new(),
        minifat: Vec::new(),
        mini_owners: Vec::new(),
        entries: Vec::new(),
        paths: BTreeMap::new(),
        stream_sources: BTreeMap::new(),
    };

    analyze_difat(&mut analysis)?;
    analyze_fat(&mut analysis)?;
    analyze_directory(&mut analysis)?;
    analyze_minifat(&mut analysis)?;
    analyze_streams_and_mini(&mut analysis)?;
    analyze_directory_tree(&mut analysis);
    analyze_orphans(&mut analysis);

    Ok(analysis)
}

/// Reads the DIFAT, mirroring the bounded traversal the normal open path uses
/// but collecting evidence instead of bailing at the first problem.
fn analyze_difat(analysis: &mut Analysis<'_>) -> io::Result<()> {
    let sector_len = analysis.sector_len as usize;
    let entries_per_difat_sector = sector_len / size_of::<u32>() - 1;

    analysis.difat.extend_from_slice(&analysis.header.initial_difat_entries);

    let mut current = analysis.header.first_difat_sector;
    while current != consts::END_OF_CHAIN
        && current != consts::FREE_SECTOR
    {
        if current > consts::MAX_REGULAR_SECTOR
            || current >= analysis.num_sectors
        {
            analysis.finding_at(
                CorruptionKind::OutOfBoundsPointer,
                Layer::Difat,
                Some(current),
                None,
                format!(
                    "DIFAT chain names sector {current}, but sector count is {}",
                    analysis.num_sectors
                ),
            );
            break;
        }
        // The DIFAT chain itself must not loop or cross other chains.
        if let Some(existing) = analysis.owners[current as usize] {
            analysis.finding_at(
                if same_owner(existing, Owner::Difat) {
                    CorruptionKind::ChainCycle
                } else {
                    CorruptionKind::DoubleClaim
                },
                Layer::Difat,
                Some(current),
                None,
                format!(
                    "DIFAT sector {current} already belongs to {}",
                    owner_label(existing)
                ),
            );
            break;
        }
        analysis.owners[current as usize] = Some(Owner::Difat);
        analysis.difat_sector_ids.push(current);

        let mut buffer = [0u8; 4];
        let base = analysis.sector_offset(current);
        for slot in 0..entries_per_difat_sector {
            let offset = base + slot * 4;
            buffer.copy_from_slice(&analysis.bytes[offset..offset + 4]);
            let next = u32::from_le_bytes(buffer);
            if next != consts::FREE_SECTOR
                && next > consts::MAX_REGULAR_SECTOR
            {
                analysis.finding_at(
                    CorruptionKind::OutOfBoundsPointer,
                    Layer::Difat,
                    Some(current),
                    Some(slot as u32),
                    format!("DIFAT entry points to invalid sector {next}"),
                );
            }
            analysis.difat.push(next);
        }
        let next_offset = base + entries_per_difat_sector * 4;
        current = analysis.read_u32_at(next_offset);
    }

    if analysis.header.num_difat_sectors as usize
        != analysis.difat_sector_ids.len()
    {
        analysis.finding(
            CorruptionKind::CountMismatch,
            Layer::Difat,
            format!(
                "header says {} DIFAT sectors, chain has {}",
                analysis.header.num_difat_sectors,
                analysis.difat_sector_ids.len()
            ),
        );
    }
    // Match the open path's permissive tolerance for zero-padding, but only
    // for trailing slots beyond the declared FAT-sector count.
    while analysis.difat.len()
        > consts::NUM_DIFAT_ENTRIES_IN_HEADER
        && analysis.difat.len() > analysis.header.num_fat_sectors as usize
        && analysis.difat.last() == Some(&0)
    {
        analysis.difat.pop();
    }
    while analysis.difat.last() == Some(&consts::FREE_SECTOR) {
        analysis.difat.pop();
    }
    if analysis.header.num_fat_sectors as usize != analysis.difat.len() {
        analysis.finding(
            CorruptionKind::CountMismatch,
            Layer::Difat,
            format!(
                "header says {} FAT sectors, DIFAT lists {}",
                analysis.header.num_fat_sectors,
                analysis.difat.len()
            ),
        );
    }
    Ok(())
}

/// Reads every FAT sector listed by the DIFAT and records which sectors the
/// FAT itself marks as allocated.
fn analyze_fat(analysis: &mut Analysis<'_>) -> io::Result<()> {
    let sector_len = analysis.sector_len as usize;
    let entries_per_sector = sector_len / size_of::<u32>();
    let num_sectors = analysis.num_sectors as usize;

    for &fat_sector in analysis.difat.iter() {
        if fat_sector as usize >= num_sectors {
            analysis.finding_at(
                CorruptionKind::OutOfBoundsPointer,
                Layer::Fat,
                Some(fat_sector),
                None,
                format!(
                    "DIFAT names FAT sector {fat_sector}, but sector count \
                     is {num_sectors}"
                ),
            );
            // Pad with free entries so later indexing stays in bounds.
            analysis.fat.resize(analysis.fat.len() + entries_per_sector, 0);
            continue;
        }
        if let Some(existing) = analysis.owners[fat_sector as usize] {
            analysis.finding_at(
                if same_owner(existing, Owner::Fat) {
                    CorruptionKind::DoubleClaim
                } else {
                    CorruptionKind::DoubleClaim
                },
                Layer::Fat,
                Some(fat_sector),
                None,
                format!(
                    "FAT sector {fat_sector} also belongs to {}",
                    owner_label(existing)
                ),
            );
        }
        analysis.owners[fat_sector as usize] = Some(Owner::Fat);

        let base = analysis.sector_offset(fat_sector);
        for slot in 0..entries_per_sector {
            let value = analysis.read_u32_at(base + slot * 4);
            analysis.fat.push(value);
        }
    }

    // Tolerate the same over-long FAT padding the open path strips.
    while analysis.fat.len() > num_sectors {
        match analysis.fat.last() {
            Some(&0)
            | Some(&consts::DIFAT_SECTOR)
            | Some(&consts::FAT_SECTOR)
            | Some(&consts::FREE_SECTOR) => {
                analysis.fat.pop();
            }
            _ => break,
        }
    }
    while analysis.fat.len() < num_sectors {
        analysis.fat.push(consts::FREE_SECTOR);
    }

    for (index, &value) in analysis.fat.iter().enumerate().take(num_sectors) {
        let allocated = match value {
            consts::FREE_SECTOR => false,
            consts::END_OF_CHAIN
            | consts::FAT_SECTOR
            | consts::DIFAT_SECTOR => true,
            sector if sector <= consts::MAX_REGULAR_SECTOR => true,
            _ => {
                analysis.finding_at(
                    CorruptionKind::OutOfBoundsPointer,
                    Layer::Fat,
                    None,
                    Some(index as u32),
                    format!("FAT entry {index} has illegal value {value}"),
                );
                false
            }
        };
        analysis.fat_allocated[index] = allocated;
    }
    Ok(())
}

/// Walks the directory chain defensively and parses every reachable slot.
fn analyze_directory(analysis: &mut Analysis<'_>) -> io::Result<()> {
    let mut current = analysis.header.first_dir_sector;
    if current == consts::END_OF_CHAIN || current == consts::FREE_SECTOR {
        analysis.finding(
            CorruptionKind::LengthMismatch,
            Layer::Directory,
            "file has no directory chain",
        );
        return Ok(());
    }
    let mut dir_sector_count = 0u32;
    loop {
        dir_sector_count += 1;
        if current > consts::MAX_REGULAR_SECTOR
            || current >= analysis.num_sectors
        {
            analysis.finding_at(
                CorruptionKind::OutOfBoundsPointer,
                Layer::Directory,
                Some(current),
                None,
                format!(
                    "directory chain names sector {current}, but sector \
                     count is {}",
                    analysis.num_sectors
                ),
            );
            break;
        }
        if let Some(existing) = analysis.owners[current as usize] {
            analysis.finding_at(
                if same_owner(existing, Owner::Directory) {
                    CorruptionKind::ChainCycle
                } else {
                    CorruptionKind::DoubleClaim
                },
                Layer::Directory,
                Some(current),
                None,
                format!(
                    "directory sector {current} already belongs to {}",
                    owner_label(existing)
                ),
            );
            if same_owner(existing, Owner::Directory) {
                break;
            }
        } else {
            analysis.owners[current as usize] = Some(Owner::Directory);
        }
        analysis.dir_chain.push(current);

        let base = analysis.sector_offset(current);
        let entries_per_sector =
            analysis.version.dir_entries_per_sector();
        for slot in 0..entries_per_sector {
            let stream_id =
                (analysis.slots.len()) as u32;
            let entry_start =
                base + slot * consts::DIR_ENTRY_LEN;
            let entry_end = entry_start + consts::DIR_ENTRY_LEN;
            let raw = &analysis.bytes[entry_start..entry_end];
            match DirEntry::read_from(
                &mut io::Cursor::new(raw),
                analysis.version,
                Validation::Permissive,
            ) {
                Ok(entry) => {
                    analysis.slots.push(RawSlot { stream_id, entry });
                }
                Err(error) => {
                    // One unparsable slot: record it and stop trusting further
                    // slots, which is exactly what the open path would do.
                    analysis.finding_at(
                        CorruptionKind::InvalidValue,
                        Layer::Directory,
                        Some(current),
                        Some(stream_id),
                        format!(
                            "directory entry {stream_id} is malformed: \
                             {error}"
                        ),
                    );
                    return Ok(());
                }
            }
        }

        let next = if (current as usize) < analysis.fat.len() {
            analysis.fat[current as usize]
        } else {
            analysis.finding_at(
                CorruptionKind::OutOfBoundsPointer,
                Layer::Directory,
                Some(current),
                Some(current),
                format!(
                    "directory sector {current} has no FAT entry"
                ),
            );
            break;
        };
        match next {
            consts::END_OF_CHAIN => break,
            consts::FREE_SECTOR => {
                analysis.finding_at(
                    CorruptionKind::LengthMismatch,
                    Layer::Directory,
                    Some(current),
                    Some(current),
                    "directory chain terminates with FREE_SECTOR instead of \
                     END_OF_CHAIN (truncated chain)",
                );
                break;
            }
            _ => current = next,
        }
    }

    if analysis.version == Version::V4
        && dir_sector_count != analysis.header.num_dir_sectors
    {
        analysis.finding(
            CorruptionKind::CountMismatch,
            Layer::Directory,
            format!(
                "header says {} directory sectors, chain has {}",
                analysis.header.num_dir_sectors, dir_sector_count
            ),
        );
    }

    if analysis.slots.is_empty()
        || analysis.slots[0].entry.obj_type != ObjType::Root
    {
        analysis.finding(
            CorruptionKind::InvalidValue,
            Layer::Directory,
            "first directory entry is not the root storage",
        );
    }
    Ok(())
}

/// Walks the MiniFAT chain and validates the mini allocation table.
fn analyze_minifat(analysis: &mut Analysis<'_>) -> io::Result<()> {
    let first = analysis.header.first_minifat_sector;
    let mut walk = Walk::default();
    if first != consts::END_OF_CHAIN && first != consts::FREE_SECTOR {
        walk = analysis.walk_table(&analysis.fat, first);
        analysis.claim_regular_sectors(
            &walk.sectors,
            Owner::Minifat,
            Layer::MiniFat,
        );
        if let Some((kind, detail)) = &walk.stopped {
            analysis.finding_at(
                *kind,
                Layer::MiniFat,
                Some(first),
                None,
                format!("MiniFAT chain is broken: {detail}"),
            );
        }
        for &sector_id in &walk.sectors {
            let base = analysis.sector_offset(sector_id);
            let entries = analysis.sector_len as usize / size_of::<u32>();
            for slot in 0..entries {
                analysis
                    .minifat
                    .push(analysis.read_u32_at(base + slot * 4));
            }
        }
        while analysis.minifat.last() == Some(&consts::FREE_SECTOR) {
            analysis.minifat.pop();
        }
    }

    if analysis.header.num_minifat_sectors as usize != walk.sectors.len() {
        analysis.finding(
            CorruptionKind::CountMismatch,
            Layer::MiniFat,
            format!(
                "header says {} MiniFAT sectors, chain has {}",
                analysis.header.num_minifat_sectors,
                walk.sectors.len()
            ),
        );
    }

    let root_mini_sectors = if analysis.slots.is_empty() {
        0
    } else {
        analysis.slots[0].entry.stream_len / consts::MINI_SECTOR_LEN as u64
    };
    if root_mini_sectors < analysis.minifat.len() as u64 {
        analysis.finding(
            CorruptionKind::LengthMismatch,
            Layer::MiniFat,
            format!(
                "MiniFAT has {} entries, but root mini stream provides only \
                 {root_mini_sectors} mini sectors",
                analysis.minifat.len()
            ),
        );
        analysis.minifat.truncate(root_mini_sectors as usize);
    }

    analysis.mini_owners = vec![None; analysis.minifat.len()];

    // Each mini sector may be the target of at most one MiniFAT pointer.
    let mut pointees = std::collections::HashSet::<u32>::new();
    for (from, &to) in analysis.minifat.iter().enumerate() {
        if to <= consts::MAX_REGULAR_SECTOR {
            if to as usize >= analysis.minifat.len() {
                analysis.finding_at(
                    CorruptionKind::OutOfBoundsPointer,
                    Layer::MiniFat,
                    None,
                    Some(from as u32),
                    format!(
                        "MiniFAT entry {from} points to mini sector {to}, but \
                         MiniFAT has {} entries",
                        analysis.minifat.len()
                    ),
                );
            } else if !pointees.insert(to) {
                analysis.finding_at(
                    CorruptionKind::DoubleClaim,
                    Layer::MiniFat,
                    None,
                    Some(to),
                    format!("mini sector {to} is pointed to twice"),
                );
            }
        }
    }
    Ok(())
}

/// Validates every stream entry's data chain (FAT or MiniFAT), claims its
/// sectors, and records what can be salvaged.
fn analyze_streams_and_mini(
    analysis: &mut Analysis<'_>,
) -> io::Result<()> {
    // The root entry's chain backs the mini stream; mini streams live inside
    // it.  Walk it once and note root-level length/cycle problems first.
    let (mini_stream, mini_stream_stop) = analysis.mini_stream_bytes();
    if !analysis.slots.is_empty() {
        let root = &analysis.slots[0].entry;
        if root.start_sector != consts::END_OF_CHAIN
            && root.start_sector != consts::FREE_SECTOR
        {
            let walk = analysis.walk_table(&analysis.fat, root.start_sector);
            analysis.claim_regular_sectors(
                &walk.sectors,
                Owner::Chain(consts::ROOT_STREAM_ID),
                Layer::Fat,
            );
            let capacity =
                walk.sectors.len() as u64 * analysis.sector_len as u64;
            if let Some((kind, detail)) = &walk.stopped {
                analysis.finding_at(
                    *kind,
                    Layer::Fat,
                    Some(root.start_sector),
                    None,
                    format!("root mini stream chain is broken: {detail}"),
                );
            } else if root.stream_len > capacity {
                analysis.finding_for_entry(
                    CorruptionKind::LengthMismatch,
                    Layer::Fat,
                    consts::ROOT_STREAM_ID,
                    Some(root.name.clone()),
                    format!(
                        "root mini stream declares {} bytes but its chain \
                         holds {capacity}",
                        root.stream_len
                    ),
                );
            }
        }
    }
    if let Some((kind, detail)) = mini_stream_stop {
        analysis.finding(
            kind,
            Layer::MiniFat,
            format!("mini stream chain is broken: {detail}"),
        );
    }

    let slots = analysis.slots.clone();
    for slot in slots.iter().skip(1) {
        let entry = &slot.entry;
        let stream_id = slot.stream_id;
        match entry.obj_type {
            ObjType::Stream => {}
            ObjType::Storage | ObjType::Root | ObjType::Unallocated => {
                continue;
            }
        }
        let len = entry.stream_len;
        let start = entry.start_sector;
        let mut source = StreamSource::Empty;

        if len < consts::MINI_STREAM_CUTOFF as u64 && len > 0 {
            if start != consts::END_OF_CHAIN
                && start != consts::FREE_SECTOR
            {
                if start as usize >= analysis.minifat.len() {
                    analysis.finding_for_entry(
                        CorruptionKind::OutOfBoundsPointer,
                        Layer::MiniFat,
                        stream_id,
                        Some(entry.name.clone()),
                        format!(
                            "stream starts at mini sector {start}, but \
                             MiniFAT has {} entries",
                            analysis.minifat.len()
                        ),
                    );
                    source = StreamSource::Unrecoverable;
                } else {
                    let walk = analysis.walk_table(&analysis.minifat, start);
                    let mut damaged = false;
                    for &mini_id in &walk.sectors {
                        match analysis.mini_owners[mini_id as usize] {
                            Some(owner) if owner != stream_id => {
                                analysis.finding_for_entry(
                                    CorruptionKind::DoubleClaim,
                                    Layer::MiniFat,
                                    stream_id,
                                    Some(entry.name.clone()),
                                    format!(
                                        "mini sector {mini_id} is shared with \
                                         directory entry {owner}"
                                    ),
                                );
                                damaged = true;
                            }
                            _ => {
                                analysis.mini_owners[mini_id as usize] =
                                    Some(stream_id);
                            }
                        }
                    }
                    if let Some((kind, detail)) = &walk.stopped {
                        analysis.finding_for_entry(
                            *kind,
                            Layer::MiniFat,
                            stream_id,
                            Some(entry.name.clone()),
                            format!("mini chain is broken: {detail}"),
                        );
                        damaged = true;
                    }
                    let capacity = walk.sectors.len() as u64
                        * consts::MINI_SECTOR_LEN as u64;
                    if !damaged && len > capacity {
                        analysis.finding_for_entry(
                            CorruptionKind::LengthMismatch,
                            Layer::MiniFat,
                            stream_id,
                            Some(entry.name.clone()),
                            format!(
                                "stream declares {len} bytes but its mini \
                                 chain holds {capacity}"
                            ),
                        );
                    }
                    let (_bytes, byte_problem) =
                        analysis.mini_chain_bytes(&mini_stream, &walk, len);
                    if byte_problem.is_some() {
                        source = StreamSource::Unrecoverable;
                    } else {
                        source = StreamSource::Mini { start, len };
                    }
                }
            } else if len > 0 {
                analysis.finding_for_entry(
                    CorruptionKind::LengthMismatch,
                    Layer::MiniFat,
                    stream_id,
                    Some(entry.name.clone()),
                    format!("stream declares {len} bytes but has no chain"),
                );
            }
        } else if len >= consts::MINI_STREAM_CUTOFF as u64 {
            if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
                analysis.finding_for_entry(
                    CorruptionKind::LengthMismatch,
                    Layer::Fat,
                    stream_id,
                    Some(entry.name.clone()),
                    format!("stream declares {len} bytes but has no chain"),
                );
            } else if start >= analysis.num_sectors {
                analysis.finding_for_entry(
                    CorruptionKind::OutOfBoundsPointer,
                    Layer::Fat,
                    stream_id,
                    Some(entry.name.clone()),
                    format!(
                        "stream starts at sector {start}, but file has only \
                         {} sectors",
                        analysis.num_sectors
                    ),
                );
                source = StreamSource::Unrecoverable;
            } else {
                let walk = analysis.walk_table(&analysis.fat, start);
                analysis.claim_regular_sectors(
                    &walk.sectors,
                    Owner::Chain(stream_id),
                    Layer::Fat,
                );
                if let Some((kind, detail)) = &walk.stopped {
                    analysis.finding_for_entry(
                        *kind,
                        Layer::Fat,
                        stream_id,
                        Some(entry.name.clone()),
                        format!("stream chain is broken: {detail}"),
                    );
                    source = StreamSource::Unrecoverable;
                } else {
                    let capacity =
                        walk.sectors.len() as u64 * analysis.sector_len as u64;
                    if len > capacity {
                        analysis.finding_for_entry(
                            CorruptionKind::LengthMismatch,
                            Layer::Fat,
                            stream_id,
                            Some(entry.name.clone()),
                            format!(
                                "stream declares {len} bytes but its chain \
                                 holds {capacity}"
                            ),
                        );
                    }
                    let (_bytes, problem) =
                        analysis.fat_chain_bytes(&walk, len);
                    match problem {
                        Some(CorruptionKind::OutOfBoundsPointer) => {
                            source = StreamSource::Unrecoverable;
                        }
                        _ => source = StreamSource::Fat { start, len },
                    }
                }
            }
        }

        analysis.stream_sources.insert(stream_id, source);
    }
    Ok(())
}

/// Walks the sibling/child tree from the root with cycle and bounds guards,
/// recording dangling links and which slots are actually reachable.
fn analyze_directory_tree(analysis: &mut Analysis<'_>) {
    let num_slots = analysis.slots.len();
    let mut reachable = vec![false; num_slots.max(1)];
    if num_slots == 0 {
        return;
    }
    if analysis.slots[0].entry.obj_type != ObjType::Root {
        return;
    }
    reachable[0] = true;

    // (stream_id, parent_id); visited guards against cycles in links.
    let mut visited = std::collections::HashSet::<u32>::new();
    let mut stack: Vec<(u32, u32)> = vec![(consts::ROOT_STREAM_ID, 0)];
    while let Some((stream_id, parent_id)) = stack.pop() {
        if !visited.insert(stream_id) {
            continue;
        }
        let entry = analysis.slots[stream_id as usize].entry.clone();
        let name = entry.name.clone();
        for (link, linked) in [
            ("left sibling", entry.left_sibling),
            ("right sibling", entry.right_sibling),
            ("child", entry.child),
        ] {
            if linked == consts::NO_STREAM {
                continue;
            }
            if linked as usize >= num_slots {
                analysis.finding_for_entry(
                    CorruptionKind::OutOfBoundsPointer,
                    Layer::DirectoryTree,
                    stream_id,
                    Some(name.clone()),
                    format!(
                        "{link} pointer names entry {linked}, but the \
                         directory chain provides only {num_slots} entries"
                    ),
                );
                continue;
            }
            let target = &analysis.slots[linked as usize].entry;
            if target.obj_type == ObjType::Unallocated {
                analysis.finding_for_entry(
                    CorruptionKind::InvalidValue,
                    Layer::DirectoryTree,
                    stream_id,
                    Some(name.clone()),
                    format!(
                        "{link} pointer names unallocated entry {linked}"
                    ),
                );
                continue;
            }
            if link == "child" && target.obj_type == ObjType::Stream {
                analysis.finding_for_entry(
                    CorruptionKind::InvalidValue,
                    Layer::DirectoryTree,
                    stream_id,
                    Some(name.clone()),
                    format!("child pointer names stream entry {linked}"),
                );
            }
            if !reachable[linked as usize] {
                reachable[linked as usize] = true;
                let parent = if link == "child" {
                    stream_id
                } else {
                    parent_id
                };
                stack.push((linked, parent));
            }
        }
    }

    // Build public entry views and full paths for reachable objects.
    analysis.paths.insert(0, String::new());
    for (id, slot) in analysis.slots.iter().enumerate() {
        let stream_id = id as u32;
        let entry = &slot.entry;
        let kind = match entry.obj_type {
            ObjType::Root => AuditedEntryKind::Root,
            ObjType::Storage => AuditedEntryKind::Storage,
            ObjType::Stream => AuditedEntryKind::Stream,
            ObjType::Unallocated => AuditedEntryKind::Unallocated,
        };
        analysis.entries.push(AuditedEntry {
            stream_id,
            kind,
            name: entry.name.clone(),
            start_sector: entry.start_sector,
            stream_len: entry.stream_len,
            left_sibling: entry.left_sibling,
            right_sibling: entry.right_sibling,
            child: entry.child,
            reachable: reachable[id],
        });
    }

    // Resolve full paths by walking the guarded red-black sibling tree: a
    // node's left/right siblings share its parent, while its child starts the
    // next level.  `path_seen` makes the walk safe against link cycles.
    let mut path_stack: Vec<(u32, String)> = vec![(0, String::new())];
    let mut path_seen = std::collections::HashSet::new();
    while let Some((stream_id, parent_path)) = path_stack.pop() {
        if !path_seen.insert(stream_id) {
            continue;
        }
        let child = analysis.slots[stream_id as usize].entry.child;
        if child == consts::NO_STREAM || child as usize >= num_slots {
            continue;
        }
        let mut node = child;
        while node != consts::NO_STREAM && (node as usize) < num_slots {
            if !path_seen.insert(node) {
                break;
            }
            let target = &analysis.slots[node as usize].entry;
            if target.obj_type == ObjType::Unallocated {
                break;
            }
            let node_path = format!("{parent_path}/{}", target.name);
            analysis.paths.insert(node, node_path.clone());
            if target.child != consts::NO_STREAM
                && (target.child as usize) < num_slots
                && reachable[target.child as usize]
            {
                path_stack.push((target.child, node_path));
            }
            node = target.right_sibling;
        }
    }


    // Any allocated slot the tree never reached is effectively severed.
    for (id, slot) in analysis.slots.iter().enumerate().skip(1) {
        if !reachable[id] && slot.entry.obj_type != ObjType::Unallocated {
            analysis.finding_for_entry(
                CorruptionKind::InvalidValue,
                Layer::DirectoryTree,
                id as u32,
                Some(slot.entry.name.clone()),
                "directory entry is not reachable from the root entry",
            );
        }
    }
}

/// Scans for allocated-but-unreachable regular and mini sectors.
fn analyze_orphans(analysis: &mut Analysis<'_>) {
    for sector_id in 0..analysis.num_sectors {
        let index = sector_id as usize;
        if analysis.fat_allocated[index] && analysis.owners[index].is_none() {
            analysis.finding_at(
                CorruptionKind::Orphan,
                Layer::Fat,
                Some(sector_id),
                Some(sector_id),
                format!(
                    "sector {sector_id} is marked allocated in the FAT but no \
                     chain reaches it"
                ),
            );
        }
    }
    for mini_id in 0..analysis.mini_owners.len() as u32 {
        if analysis.minifat[mini_id as usize] != consts::FREE_SECTOR
            && analysis.mini_owners[mini_id as usize].is_none()
        {
            analysis.finding_at(
                CorruptionKind::Orphan,
                Layer::MiniFat,
                None,
                Some(mini_id),
                format!(
                    "mini sector {mini_id} is marked allocated in the \
                     MiniFAT but no mini chain reaches it"
                ),
            );
        }
    }
}

