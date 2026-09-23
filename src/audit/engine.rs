//! Corruption-tolerant structural walk used by [`AuditReport`](super::AuditReport).
//!
//! This module is the internal boundary behind the public audit entry point.
//! It shares the production code's understanding of the format:
//! [`Header`](crate::internal::Header) is parsed with the exact same routine
//! used by [`CompoundFile::open`](crate::internal), and all sector numbers and
//! layouts come from the shared [`consts`](crate::internal::consts) and
//! [`Version`] modules.  The only difference is that, where the open path
//! returns the first malformed-chain error, the audit keeps walking and
//! records [`Evidence`] instead.  No production code is changed by this
//! module.

use std::convert::TryInto;
use std::io::{self, Cursor, Read, Seek};

use std::collections::HashMap;

use crate::internal::{consts, Header, ObjType, Validation, Version};

use super::plan::Digest;

//===========================================================================//

/// Which allocation table or chain a piece of evidence is about.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum ChainLayer {
    /// The DIFAT chain that lists FAT sectors.
    Difat,
    /// The main file allocation table.
    Fat,
    /// The directory chain / the sibling and child trees in the directory.
    Directory,
    /// The mini FAT that chains 64-byte mini sectors inside the mini stream.
    MiniFat,
}

impl ChainLayer {
    fn rank(self) -> u8 {
        // Fixed report order: DIFAT, FAT, directory, MiniFAT.
        match self {
            ChainLayer::Difat => 0,
            ChainLayer::Fat => 1,
            ChainLayer::Directory => 2,
            ChainLayer::MiniFat => 3,
        }
    }
}

impl std::fmt::Display for ChainLayer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ChainLayer::Difat => "DIFAT",
            ChainLayer::Fat => "FAT",
            ChainLayer::Directory => "directory chain",
            ChainLayer::MiniFat => "MiniFAT",
        })
    }
}

/// Kind of regular-sector chain whose owner claims a sector.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ChainKind {
    /// Sector listed in the DIFAT as a DIFAT sector.
    DifatSector,
    /// Sector listed in the DIFAT as a FAT sector.
    FatSector,
    /// Sector of the directory chain starting at `first_dir_sector`.
    Directory,
    /// Sector of the root entry's mini stream.
    MiniStream,
    /// Sector of the MiniFAT chain.
    MiniFat,
    /// Sector of a regular stream described by a directory entry.
    Stream,
}

/// What owns a regular sector, used to describe the second claimant when two
/// chains cross.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Owner {
    /// A directory-entry chain: stream name is recorded when known.
    Entry(u32, ChainKind),
    /// A metadata sector of the given kind.
    Meta(ChainKind),
}

/// One piece of corruption evidence.
///
/// The five required corruption classes are separate variants so callers can
/// distinguish them programmatically; every variant carries the first
/// violating index and the context needed to understand it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evidence {
    /// A chain link points back to a sector already seen in that chain, so
    /// following it would loop forever.  Records the layer, the repeated
    /// sector id, and the chain start it belongs to.
    Cycle {
        /// Allocation structure containing the cycle.
        layer: ChainLayer,
        /// First sector revisited when the cycle closes.
        sector_id: u32,
        /// Start sector of the cycling chain.
        chain_start: u32,
        /// Directory entry that owns the chain, when applicable.
        entry_id: Option<u32>,
    },
    /// A chain link points outside the file / table (or to a reserved invalid
    /// value).  Records the layer, the sector holding the bad link, and the
    /// invalid target.
    OutOfBounds {
        /// Allocation structure containing the bad pointer.
        layer: ChainLayer,
        /// Sector or mini sector whose cell holds the bad pointer.
        at: u32,
        /// Pointer value that falls outside the valid range.
        target: u32,
        /// Number of valid sectors / entries the pointer must be within.
        bound: u32,
        /// Directory entry that owns the chain, when applicable.
        entry_id: Option<u32>,
    },
    /// One sector is claimed by two different chains (a crossed chain), or by
    /// a chain and a metadata marker.  Records the layer walked, the sector,
    /// the later claimant, and what already owned it.
    DoubleAllocation {
        /// Allocation structure being walked when the clash was found.
        layer: ChainLayer,
        /// Sector claimed twice.
        sector_id: u32,
        /// The later claimant.
        claimant: Owner,
        /// What already claimed the sector.
        incumbent: Owner,
    },
    /// A sector (or mini sector) is neither free, metadata, nor reachable from
    /// the directory: it is detached from every chain.
    OrphanSector {
        /// Table in which the sector is unreachable (`Fat` or `MiniFat`).
        layer: ChainLayer,
        /// Sector id that no chain reaches.
        sector_id: u32,
    },
    /// A declared length does not match what its chain can provide: a stream
    /// is shorter or longer than its directory entry claims, the MiniFAT
    /// count disagrees with the header, or a chain terminates early into a
    /// `FREESECT` cell.
    LengthMismatch {
        /// Allocation structure the declaration belongs to.
        layer: ChainLayer,
        /// Directory entry with the wrong `stream_len`, if any.
        entry_id: Option<u32>,
        /// Declared length (or count).
        declared: u64,
        /// Length actually reachable through the chain.
        actual: u64,
        /// What length is being compared (for the error context).
        what: LengthSubject,
    },
    /// A sibling/child pointer in the directory tree points at a directory
    /// entry that is not present (the directory chain ends before reaching
    /// it), or the directory chain itself ends early.
    TruncatedDirectory {
        /// Directory entry holding the dangling pointer; `None` for a chain
        /// that ends with sectors still expected (e.g. a wrong header count).
        from_entry: Option<u32>,
        /// Entry id / sector id that cannot be reached.
        missing: u32,
        /// Which field holds the pointer, when it is a tree pointer.
        field: DirField,
    },
}

/// Which declared length disagrees with reality.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LengthSubject {
    /// A stream's `stream_len` versus the bytes its chain reaches.
    StreamLen,
    /// Header `num_FAT_sectors` / `num_MiniFAT_sectors` vs actual chains.
    SectorCount,
    /// Root entry `stream_len` (mini stream size) vs its chain capacity.
    MiniStreamLen,
}

impl std::fmt::Display for LengthSubject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            LengthSubject::StreamLen => "stream length",
            LengthSubject::SectorCount => "sector count",
            LengthSubject::MiniStreamLen => "mini stream length",
        })
    }
}

/// Directory-entry field involved in a truncation finding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DirField {
    /// The directory chain itself (FAT link / header first sector).
    Chain,
    /// `left_sibling_id`.
    LeftSibling,
    /// `right_sibling_id`.
    RightSibling,
    /// `child_id`.
    Child,
}

impl Evidence {
    /// Layer this evidence belongs to (DIFAT/FAT/directory/MiniFAT).
    pub fn layer(&self) -> ChainLayer {
        match self {
            Evidence::Cycle { layer, .. }
            | Evidence::OutOfBounds { layer, .. }
            | Evidence::DoubleAllocation { layer, .. }
            | Evidence::OrphanSector { layer, .. }
            | Evidence::LengthMismatch { layer, .. } => *layer,
            Evidence::TruncatedDirectory { .. } => ChainLayer::Directory,
        }
    }

    /// First violating sector/entry index, for ordering and for tests that
    /// assert on the first breach location.
    pub fn first_location(&self) -> u32 {
        match self {
            Evidence::Cycle { sector_id, .. } => *sector_id,
            Evidence::OutOfBounds { at, .. } => *at,
            Evidence::DoubleAllocation { sector_id, .. } => *sector_id,
            Evidence::OrphanSector { sector_id, .. } => *sector_id,
            Evidence::LengthMismatch { entry_id, .. } => {
                entry_id.unwrap_or(u32::MAX)
            }
            Evidence::TruncatedDirectory { missing, .. } => *missing,
        }
    }

    /// Deterministic sort key: layer order, then first location, then variant
    /// order, so re-auditing with any visitation schedule reports identically
    /// ordered evidence.
    pub(crate) fn sort_key(&self) -> (u8, u32, u8) {
        let variant = match self {
            Evidence::Cycle { .. } => 0,
            Evidence::OutOfBounds { .. } => 1,
            Evidence::DoubleAllocation { .. } => 2,
            Evidence::TruncatedDirectory { .. } => 3,
            Evidence::OrphanSector { .. } => 4,
            Evidence::LengthMismatch { .. } => 5,
        };
        (self.layer().rank(), self.first_location(), variant)
    }
}

impl std::fmt::Display for Evidence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Evidence::Cycle { layer, sector_id, chain_start, entry_id } => {
                write!(
                    f,
                    "{layer} chain starting at {chain_start} cycles back to \
                     sector {sector_id}"
                )?;
                if let Some(id) = entry_id {
                    write!(f, " (directory entry {id})")?;
                }
                Ok(())
            }
            Evidence::OutOfBounds { layer, at, target, bound, entry_id } => {
                write!(
                    f,
                    "{layer} cell at {at} points to {target}, but only \
                     {bound} sectors are valid"
                )?;
                if let Some(id) = entry_id {
                    write!(f, " (directory entry {id})")?;
                }
                Ok(())
            }
            Evidence::DoubleAllocation { layer, sector_id, claimant, incumbent } => {
                write!(
                    f,
                    "{layer}: sector {sector_id} is claimed by both {} and \
                     {}",
                    fmt_owner(claimant),
                    fmt_owner(incumbent)
                )
            }
            Evidence::OrphanSector { layer, sector_id } => write!(
                f,
                "{layer} sector {sector_id} is orphaned (reachable from no \
                 chain)"
            ),
            Evidence::LengthMismatch { layer, entry_id, declared, actual, what } => {
                write!(
                    f,
                    "{layer}: declared {what} is {declared} but the chain \
                     provides {actual}"
                )?;
                if let Some(id) = entry_id {
                    write!(f, " (directory entry {id})")?;
                }
                Ok(())
            }
            Evidence::TruncatedDirectory { from_entry, missing, field } => {
                let field = match field {
                    DirField::Chain => "directory chain",
                    DirField::LeftSibling => "left sibling",
                    DirField::RightSibling => "right sibling",
                    DirField::Child => "child",
                };
                match from_entry {
                    Some(id) => write!(
                        f,
                        "directory entry {id} {field} points at {missing}, \
                         which is beyond the reachable directory"
                    ),
                    None => write!(
                        f,
                        "{field} ends before reaching entry/sector {missing}"
                    ),
                }
            }
        }
    }
}

fn fmt_owner(owner: &Owner) -> String {
    match owner {
        Owner::Meta(kind) => format!("{kind} metadata"),
        Owner::Entry(id, kind) => format!("entry {id} {kind} chain"),
    }
}

impl std::fmt::Display for ChainKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ChainKind::DifatSector => "DIFAT-sector",
            ChainKind::FatSector => "FAT-sector",
            ChainKind::Directory => "directory",
            ChainKind::MiniStream => "mini-stream",
            ChainKind::MiniFat => "MiniFAT",
            ChainKind::Stream => "stream",
        })
    }
}

//===========================================================================//
// Raw, corruption-tolerant view of an on-disk compound file.

const DIR_OBJ_TYPE_OFFSET: u64 = 66;
const DIR_LEFT_SIBLING_OFFSET: u64 = 68;
const DIR_RIGHT_SIBLING_OFFSET: u64 = 72;
const DIR_CHILD_OFFSET: u64 = 76;
const DIR_START_SECTOR_OFFSET: u64 = 116;
const DIR_STREAM_LEN_OFFSET: u64 = 120;

/// Parsed raw directory entry; only fields needed by the audit are decoded.
#[derive(Clone, Debug)]
struct RawEntry {
    obj_type: ObjType,
    left_sibling: u32,
    right_sibling: u32,
    child: u32,
    start_sector: u32,
    stream_len: u64,
}

/// State of the tolerant audit walk.
pub(crate) struct AuditState {
    version: Version,
    sector_len: u64,
    num_sectors: u32,
    data: Vec<u8>,
    fat: Vec<u32>,
    /// FAT sectors listed by the DIFAT, in DIFAT order.
    fat_sector_ids: Vec<u32>,
    /// DIFAT sectors reached via the DIFAT chain.
    difat_sector_ids: Vec<u32>,
    /// Directory entries reachable through the directory chain, in order.
    entries: Vec<RawEntry>,
    /// Sector ids of the directory chain as walked.
    dir_sector_ids: Vec<u32>,
    /// First regular-sector id that is not part of the reachable directory
    /// chain (used to distinguish a truncated directory from orphans).
    first_dir_sector_beyond: Option<u32>,
    evidence: Vec<Evidence>,
    /// owner[sector] = who claims the regular sector.
    owners: HashMap<u32, Owner>,
}

impl AuditState {
    fn sector_offset(&self, sector_id: u32, within: u64) -> u64 {
        (sector_id as u64 + 1) * self.sector_len + within
    }

    fn read_u32(&self, offset: u64) -> io::Result<u32> {
        let end = offset + 4;
        if end > self.data.len() as u64 {
            invalid_data!(
                "Cannot read at offset {} of {}-byte file",
                offset,
                self.data.len()
            );
        }
        Ok(u32::from_le_bytes(
            self.data[offset as usize..end as usize].try_into().unwrap(),
        ))
    }

    fn read_u64(&self, offset: u64) -> io::Result<u64> {
        let end = offset + 8;
        if end > self.data.len() as u64 {
            invalid_data!(
                "Cannot read at offset {} of {}-byte file",
                offset,
                self.data.len()
            );
        }
        Ok(u64::from_le_bytes(
            self.data[offset as usize..end as usize].try_into().unwrap(),
        ))
    }

    fn fat_next(&self, sector_id: u32) -> Option<u32> {
        self.fat.get(sector_id as usize).copied()
    }

    /// Records evidence, suppressing later duplicates of the same finding so
    /// the report shows the first violating location once.
    fn add(&mut self, finding: Evidence) {
        if !self.evidence.contains(&finding) {
            self.evidence.push(finding);
        }
    }
}

/// Public audit entry: reads all bytes, computes their [`Digest`], parses the
/// header with the production [`Header`] routine, then tolerantly walks the
/// allocation structures.
pub(crate) fn audit<F: Read + Seek>(
    mut reader: F,
) -> io::Result<super::AuditReport> {
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    let report = audit_bytes(&data)?;
    Ok(report)
}

/// Core of the audit over an in-memory byte slice.  Shared by `audit` and by
/// repair-plan construction, so plans reason about exactly the structures the
/// audit reported.
fn audit_bytes(data: &[u8]) -> io::Result<super::AuditReport> {
    let len = data.len() as u64;
    let digest = Digest::of_bytes(data);

    // Parse the header exactly like the production open path.  A file whose
    // header itself is unreadable is rejected there (InvalidData), rather
    // than producing fabricated audit evidence.
    let mut cursor = Cursor::new(data);
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len() as u64;
    if len < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            len,
            sector_len
        );
    }
    let num_sectors = (len / sector_len - 1) as u32;

    let mut state = AuditState {
        version,
        sector_len,
        num_sectors,
        data: data.to_vec(),
        fat: Vec::new(),
        fat_sector_ids: Vec::new(),
        difat_sector_ids: Vec::new(),
        entries: Vec::new(),
        dir_sector_ids: Vec::new(),
        first_dir_sector_beyond: None,
        evidence: Vec::new(),
        owners: HashMap::new(),
    };

    read_difat_and_fat(&mut state, &header)?;
    mark_metadata_owners(&mut state);
    read_directory(&mut state, &header);
    walk_stream_chains(&mut state);
    scan_fat_orphans(&mut state);
    audit_minifat(&mut state, &header);
    audit_directory_tree(&mut state);

    state.evidence.sort_by_key(Evidence::sort_key);
    Ok(super::AuditReport { digest, evidence: state.evidence })
}

/// Re-reads the current bytes, refuses unless their digest still matches the
/// report, and synthesizes byte-level repair steps with the same tolerant
/// parse used for the evidence.
pub(crate) fn build_repair_plan<F: Read + Seek>(
    report: &super::AuditReport,
    mut reader: F,
) -> io::Result<super::plan::RepairPlan> {
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    let current = Digest::of_bytes(&data);
    if current != report.digest {
        invalid_data!(
            "Cannot build repair plan: the compound file changed since the \
             audit (content digest no longer matches)"
        );
    }
    let mut builder = BuildContext::new(&data)?;
    for evidence in report.evidence() {
        builder.build(evidence);
    }
    Ok(super::plan::RepairPlan::from_parts(
        report.digest,
        builder.into_steps(),
    ))
}

//===========================================================================//
// DIFAT and FAT.

/// Tolerant counterpart of the DIFAT/FAT reading block in
/// `CompoundFile::open_internal`.  Same layout rules, but links that would
/// make the open path error out are recorded and then skipped/stopped.
fn read_difat_and_fat(state: &mut AuditState, header: &Header) -> io::Result<()> {
    let sector_len = state.sector_len as usize;
    let entries_per_difat_sector = sector_len / 4 - 1;

    // FAT sector ids listed directly in the header.
    let mut fat_ids: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();

    // Walk the DIFAT chain tolerantly.
    let mut current = header.first_difat_sector;
    let mut seen = std::collections::HashSet::new();
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= state.num_sectors || current > consts::MAX_REGULAR_SECTOR
        {
            state.add(Evidence::OutOfBounds {
                layer: ChainLayer::Difat,
                at: state.difat_sector_ids.last().copied().unwrap_or(current),
                target: current,
                bound: state.num_sectors,
                entry_id: None,
            });
            break;
        }
        if !seen.insert(current) {
            state.add(Evidence::Cycle {
                layer: ChainLayer::Difat,
                sector_id: current,
                chain_start: header.first_difat_sector,
                entry_id: None,
            });
            break;
        }
        state.difat_sector_ids.push(current);
        let base = state.sector_offset(current, 0);
        for i in 0..entries_per_difat_sector {
            let entry = state.read_u32(base + (i as u64) * 4)?;
            fat_ids.push(entry);
        }
        current = state.read_u32(base + sector_len as u64 - 4)?;
    }

    // Strip trailing free entries, mirroring the open path's trimming.
    while fat_ids.last() == Some(&consts::FREE_SECTOR) {
        fat_ids.pop();
    }
    while fat_ids.len() > header.num_fat_sectors as usize
        && fat_ids.last() == Some(&0u32)
        && fat_ids.len() > consts::NUM_DIFAT_ENTRIES_IN_HEADER
    {
        fat_ids.pop();
    }

    // Read the FAT from every listed sector that exists; out-of-range FAT
    // sector pointers are evidence, not a hard stop.
    for &fat_sector in fat_ids.iter() {
        if fat_sector == consts::FREE_SECTOR {
            continue;
        }
        if fat_sector >= state.num_sectors
            || fat_sector > consts::MAX_REGULAR_SECTOR
        {
            state.add(Evidence::OutOfBounds {
                layer: ChainLayer::Difat,
                at: fat_sector,
                target: fat_sector,
                bound: state.num_sectors,
                entry_id: None,
            });
            continue;
        }
        if state
            .fat_sector_ids
            .iter()
            .any(|&id| id == fat_sector)
        {
            state.add(Evidence::DoubleAllocation {
                layer: ChainLayer::Difat,
                sector_id: fat_sector,
                claimant: Owner::Meta(ChainKind::FatSector),
                incumbent: Owner::Meta(ChainKind::FatSector),
            });
            continue;
        }
        state.fat_sector_ids.push(fat_sector);
        let base = state.sector_offset(fat_sector, 0);
        for i in 0..sector_len / 4 {
            state
                .fat
                .push(state.read_u32(base + (i as u64) * 4)?);
        }
    }

    // Normalize FAT length to the sector count, as the open path does, but
    // keep the raw values for evidence.  Pad with FREE_SECTOR if short.
    if state.fat.len() < state.num_sectors as usize {
        state
            .fat
            .resize(state.num_sectors as usize, consts::FREE_SECTOR);
    }

    // Header count mismatches are declared-length inconsistencies, distinct
    // from chain corruption.
    if header.num_fat_sectors as usize != state.fat_sector_ids.len() {
        state.add(Evidence::LengthMismatch {
            layer: ChainLayer::Difat,
            entry_id: None,
            declared: header.num_fat_sectors as u64,
            actual: state.fat_sector_ids.len() as u64,
            what: LengthSubject::SectorCount,
        });
    }
    Ok(())
}

/// Marks DIFAT and FAT sectors with their metadata owner.  The audit does not
/// enforce the strict-only "must be marked" rule, but if a sector is marked
/// `FATSECT`/`DIFSECT` while a data chain also reaches it, that is a double
/// allocation reported during chain walks.
fn mark_metadata_owners(state: &mut AuditState) {
    for &id in state.difat_sector_ids.iter() {
        state.owners.insert(id, Owner::Meta(ChainKind::DifatSector));
    }
    for &id in state.fat_sector_ids.iter() {
        state.owners.insert(id, Owner::Meta(ChainKind::FatSector));
    }
}

//===========================================================================//
// Directory chain and raw entries.

fn read_directory(state: &mut AuditState, header: &Header) {
    let entries_per_sector = state.version.dir_entries_per_sector();
    let chain_start = header.first_dir_sector;
    if chain_start == consts::END_OF_CHAIN || chain_start == consts::FREE_SECTOR
    {
        return;
    }
    let mut current = chain_start;
    let mut seen = std::collections::HashSet::new();
    let mut truncated = false;
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= state.num_sectors || current > consts::MAX_REGULAR_SECTOR
        {
            state.add(Evidence::OutOfBounds {
                layer: ChainLayer::Directory,
                at: state.dir_sector_ids.last().copied().unwrap_or(current),
                target: current,
                bound: state.num_sectors,
                entry_id: None,
            });
            truncated = true;
            break;
        }
        if !seen.insert(current) {
            state.add(Evidence::Cycle {
                layer: ChainLayer::Directory,
                sector_id: current,
                chain_start,
                entry_id: None,
            });
            truncated = true;
            break;
        }
        // A directory sector that metadata or an earlier chain already owns
        // is a crossed chain.
        if let Some(incumbent) = state.owners.get(&current).copied() {
            if incumbent != Owner::Meta(ChainKind::Directory) {
                state.add(Evidence::DoubleAllocation {
                    layer: ChainLayer::Directory,
                    sector_id: current,
                    claimant: Owner::Meta(ChainKind::Directory),
                    incumbent,
                });
                truncated = true;
                break;
            }
        }
        state
            .owners
            .insert(current, Owner::Meta(ChainKind::Directory));
        state.dir_sector_ids.push(current);

        // Decode raw entries from this sector.
        let base = state.sector_offset(current, 0);
        for slot in 0..entries_per_sector {
            let entry_base = base + (slot as u64) * consts::DIR_ENTRY_LEN as u64;
            let entry = read_raw_entry(state, entry_base);
            state.entries.push(entry);
        }

        match state.fat_next(current) {
            Some(next) => current = next,
            None => {
                state.add(Evidence::OutOfBounds {
                    layer: ChainLayer::Directory,
                    at: current,
                    target: current,
                    bound: state.fat.len() as u32,
                    entry_id: None,
                });
                truncated = true;
                break;
            }
        }
    }
    if truncated {
        // Every former directory sector that the chain stopped short of is
        // the context for the truncation; record the first such sector so
        // evidence shows where the chain went missing.
        if let Some(&next_expected) = state.fat.get(
            state
                .dir_sector_ids
                .last()
                .copied()
                .unwrap_or(chain_start) as usize,
        ) {
            if next_expected != consts::END_OF_CHAIN
                && next_expected < state.num_sectors
                && !seen.contains(&next_expected)
            {
                state.first_dir_sector_beyond = Some(next_expected);
                state.add(Evidence::TruncatedDirectory {
                    from_entry: None,
                    missing: next_expected,
                    field: DirField::Chain,
                });
            }
        }
    }
}

fn read_raw_entry(state: &AuditState, base: u64) -> RawEntry {
    let obj_byte = state
        .data
        .get(base as usize + DIR_OBJ_TYPE_OFFSET as usize)
        .copied()
        .unwrap_or(consts::OBJ_TYPE_UNALLOCATED);
    let obj_type = match obj_byte {
        consts::OBJ_TYPE_STORAGE => ObjType::Storage,
        consts::OBJ_TYPE_STREAM => ObjType::Stream,
        consts::OBJ_TYPE_ROOT => ObjType::Root,
        _ => ObjType::Unallocated,
    };
    let read = |off: u64| state.read_u32(base + off).unwrap_or(consts::NO_STREAM);
    RawEntry {
        obj_type,
        left_sibling: read(DIR_LEFT_SIBLING_OFFSET),
        right_sibling: read(DIR_RIGHT_SIBLING_OFFSET),
        child: read(DIR_CHILD_OFFSET),
        start_sector: read(DIR_START_SECTOR_OFFSET),
        stream_len: state
            .read_u64(base + DIR_STREAM_LEN_OFFSET)
            .unwrap_or(0)
            & state.version.stream_len_mask(),
    }
}

//===========================================================================//
// Regular-stream chain walks.

fn is_regular_pointer(value: u32) -> bool {
    value <= consts::MAX_REGULAR_SECTOR
}

/// Walks every stream chain (including the root's mini-stream chain and the
/// MiniFAT chain), claiming sectors and reporting cycles, out-of-bounds
/// links, crossed chains, and early FREESECT termination.
fn walk_stream_chains(state: &mut AuditState) {
    // Collect (entry_id, start, declared_len, kind) from the raw directory.
    let mut roots: Vec<(u32, u32, u64, ChainKind)> = Vec::new();
    for (id, entry) in state.entries.iter().enumerate() {
        let id = id as u32;
        match entry.obj_type {
            ObjType::Root => {
                roots.push((
                    id,
                    entry.start_sector,
                    entry.stream_len,
                    ChainKind::MiniStream,
                ));
            }
            ObjType::Stream => {
                if entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64 {
                    roots.push((
                        id,
                        entry.start_sector,
                        entry.stream_len,
                        ChainKind::Stream,
                    ));
                }
            }
            _ => {}
        }
    }

    for (entry_id, start, declared_len, kind) in roots {
        let owner = Owner::Entry(entry_id, kind);
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            if declared_len > 0 && kind == ChainKind::Stream {
                state.add(Evidence::LengthMismatch {
                    layer: ChainLayer::Fat,
                    entry_id: Some(entry_id),
                    declared: declared_len,
                    actual: 0,
                    what: LengthSubject::StreamLen,
                });
            }
            continue;
        }
        let (reached, early_free) = walk_fat_chain(state, start, owner);
        let capacity = reached as u64 * state.sector_len;
        if early_free {
            // Chain ran into a FREESECT cell: it is shorter than its links
            // promised, which for a stream also disagrees with stream_len.
            state.add(Evidence::LengthMismatch {
                layer: ChainLayer::Fat,
                entry_id: Some(entry_id),
                declared: declared_len,
                actual: capacity,
                what: LengthSubject::StreamLen,
            });
        } else if kind == ChainKind::Stream {
            let needed = declared_len.div_ceil(state.sector_len) as u32;
            if reached != needed {
                state.add(Evidence::LengthMismatch {
                    layer: ChainLayer::Fat,
                    entry_id: Some(entry_id),
                    declared: declared_len,
                    actual: capacity,
                    what: LengthSubject::StreamLen,
                });
            }
        }
    }
}

/// Walks one FAT chain tolerantly, claiming sectors for `owner`.  Returns
/// `(number of sectors successfully reached, whether the chain ended on a
/// FREESECT cell)`.
pub(crate) fn walk_fat_chain(
    state: &mut AuditState,
    start: u32,
    owner: Owner,
) -> (u32, bool) {
    let mut current = start;
    let mut count = 0u32;
    let mut path = Vec::new();
    loop {
        if !is_regular_pointer(current) || current >= state.num_sectors {
            state.add(Evidence::OutOfBounds {
                layer: ChainLayer::Fat,
                at: path.last().copied().unwrap_or(start),
                target: current,
                bound: state.num_sectors,
                entry_id: owner_entry(&owner),
            });
            return (count, false);
        }
        if path.contains(&current) {
            state.add(Evidence::Cycle {
                layer: ChainLayer::Fat,
                sector_id: current,
                chain_start: start,
                entry_id: owner_entry(&owner),
            });
            return (count, false);
        }
        if let Some(incumbent) = state.owners.get(&current).copied() {
            if incumbent != owner {
                state.add(Evidence::DoubleAllocation {
                    layer: ChainLayer::Fat,
                    sector_id: current,
                    claimant: owner,
                    incumbent,
                });
                return (count, false);
            }
        }
        state.owners.insert(current, owner);
        path.push(current);
        count += 1;

        let next = match state.fat_next(current) {
            Some(value) => value,
            None => {
                state.add(Evidence::OutOfBounds {
                    layer: ChainLayer::Fat,
                    at: current,
                    target: current,
                    bound: state.fat.len() as u32,
                    entry_id: owner_entry(&owner),
                });
                return (count, false);
            }
        };
        if next == consts::END_OF_CHAIN {
            return (count, false);
        }
        if next == consts::FREE_SECTOR {
            // FREESECT inside a referenced chain: the chain is truncated.
            return (count, true);
        }
        current = next;
    }
}

fn owner_entry(owner: &Owner) -> Option<u32> {
    match owner {
        Owner::Entry(id, _) => Some(*id),
        Owner::Meta(_) => None,
    }
}

/// Marks every non-free FAT cell that no metadata and no walked chain owns as
/// an orphan.  Sectors that the directory truncation cut off are reported as
/// truncation rather than orphans.
fn scan_fat_orphans(state: &mut AuditState) {
    let mut suppressed: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    if let Some(first) = state.first_dir_sector_beyond {
        // Sectors the FAT still chains from the cut point were directory
        // sectors before the chain was shortened.
        let mut cur = first;
        while is_regular_pointer(cur) && cur < state.num_sectors {
            if !suppressed.insert(cur) {
                break;
            }
            match state.fat_next(cur) {
                Some(next) if next != consts::END_OF_CHAIN
                    && next != consts::FREE_SECTOR =>
                {
                    cur = next;
                }
                _ => break,
            }
        }
    }
    for sector_id in 0..state.num_sectors {
        let value = match state.fat.get(sector_id as usize) {
            Some(&value) => value,
            None => break,
        };
        let used = value != consts::FREE_SECTOR;
        let owned = state.owners.contains_key(&sector_id);
        if used && !owned && !suppressed.contains(&sector_id) {
            state.add(Evidence::OrphanSector {
                layer: ChainLayer::Fat,
                sector_id,
            });
        }
    }
}

//===========================================================================//
// MiniFAT and mini stream.

fn audit_minifat(state: &mut AuditState, header: &Header) {
    if state.entries.is_empty() {
        return;
    }
    // Walk the MiniFAT's own regular chain first so its sectors are owned.
    let mut minifat_sector_count = 0u32;
    if header.first_minifat_sector != consts::END_OF_CHAIN
        && header.first_minifat_sector != consts::FREE_SECTOR
    {
        let (reached, _) = walk_fat_chain(
            state,
            header.first_minifat_sector,
            Owner::Meta(ChainKind::MiniFat),
        );
        minifat_sector_count = reached;
    }

    // MiniFAT contents: read one sector worth of u32s per chain sector.
    let entries_per_sector = (state.sector_len / 4) as usize;
    let mut minifat: Vec<u32> =
        Vec::with_capacity(minifat_sector_count as usize * entries_per_sector);
    let mut cur = header.first_minifat_sector;
    let mut guard = std::collections::HashSet::new();
    while cur != consts::END_OF_CHAIN && cur != consts::FREE_SECTOR {
        if !is_regular_pointer(cur) || cur >= state.num_sectors {
            break;
        }
        if !guard.insert(cur) {
            break;
        }
        let base = state.sector_offset(cur, 0);
        for i in 0..entries_per_sector {
            if let Ok(value) = state.read_u32(base + (i as u64) * 4) {
                minifat.push(value);
            }
        }
        cur = state.fat_next(cur).unwrap_or(consts::END_OF_CHAIN);
    }
    while minifat.last() == Some(&consts::FREE_SECTOR) {
        minifat.pop();
    }

    if header.num_minifat_sectors != minifat_sector_count {
        state.add(Evidence::LengthMismatch {
            layer: ChainLayer::MiniFat,
            entry_id: None,
            declared: header.num_minifat_sectors as u64,
            actual: minifat_sector_count as u64,
            what: LengthSubject::SectorCount,
        });
    }

    // Mini stream capacity comes from the root entry's regular chain.
    let root = state.entries.get(0).cloned();
    let mini_capacity_sectors = match &root {
        Some(_entry) => {
            // Count sectors claimed for the mini stream chain (already walked
            // in walk_stream_chains).
            count_owner_sectors(
                state,
                Owner::Entry(0, ChainKind::MiniStream),
            )
        }
        None => 0,
    };
    let mini_capacity_bytes =
        mini_capacity_sectors as u64 * state.sector_len;

    if let Some(root) = &root {
        if root.stream_len > mini_capacity_bytes {
            state.add(Evidence::LengthMismatch {
                layer: ChainLayer::MiniFat,
                entry_id: Some(0),
                declared: root.stream_len,
                actual: mini_capacity_bytes,
                what: LengthSubject::MiniStreamLen,
            });
        }
    }
    let mini_chain_limit =
        (mini_capacity_bytes / consts::MINI_SECTOR_LEN as u64) as u32;

    // Walk each small stream's mini chain.  Snapshot the relevant entries
    // first so the walk can mutate `state.evidence`.
    let small_streams: Vec<(u32, u32, u64)> = state
        .entries
        .iter()
        .enumerate()
        .filter(|(_, entry)| {
            entry.obj_type == ObjType::Stream
                && entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
        })
        .map(|(id, entry)| (id as u32, entry.start_sector, entry.stream_len))
        .collect();
    let mut claimed: HashMap<u32, u32> = HashMap::new();
    for (id, start, stream_len) in small_streams {
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            if stream_len > 0 {
                state.add(Evidence::LengthMismatch {
                    layer: ChainLayer::MiniFat,
                    entry_id: Some(id),
                    declared: stream_len,
                    actual: 0,
                    what: LengthSubject::StreamLen,
                });
            }
            continue;
        }
        let mut current = start;
        let mut reached = 0u64;
        let mut path = Vec::new();
        loop {
            if !is_regular_pointer(current)
                || current as usize >= minifat.len()
            {
                state.add(Evidence::OutOfBounds {
                    layer: ChainLayer::MiniFat,
                    at: path.last().copied().unwrap_or(start),
                    target: current,
                    bound: minifat.len() as u32,
                    entry_id: Some(id as u32),
                });
                break;
            }
            if current >= mini_chain_limit {
                state.add(Evidence::OutOfBounds {
                    layer: ChainLayer::MiniFat,
                    at: path.last().copied().unwrap_or(start),
                    target: current,
                    bound: mini_chain_limit,
                    entry_id: Some(id as u32),
                });
                break;
            }
            if path.contains(&current) {
                state.add(Evidence::Cycle {
                    layer: ChainLayer::MiniFat,
                    sector_id: current,
                    chain_start: start,
                    entry_id: Some(id as u32),
                });
                break;
            }
            if let Some(&other) = claimed.get(&current) {
                if other != id as u32 {
                    state.add(Evidence::DoubleAllocation {
                        layer: ChainLayer::MiniFat,
                        sector_id: current,
                        claimant: Owner::Entry(id as u32, ChainKind::Stream),
                        incumbent: Owner::Entry(other, ChainKind::Stream),
                    });
                    break;
                }
            }
            claimed.insert(current, id as u32);
            path.push(current);
            reached += 1;
            let next = minifat[current as usize];
            if next == consts::END_OF_CHAIN {
                break;
            }
            if next == consts::FREE_SECTOR {
                break;
            }
            current = next;
        }
        let needed =
            stream_len.div_ceil(consts::MINI_SECTOR_LEN as u64);
        if needed != reached && is_regular_pointer(start) {
            state.add(Evidence::LengthMismatch {
                layer: ChainLayer::MiniFat,
                entry_id: Some(id as u32),
                declared: stream_len,
                actual: reached * consts::MINI_SECTOR_LEN as u64,
                what: LengthSubject::StreamLen,
            });
        }
    }

    // Orphan mini sectors: non-free MiniFAT cells no stream claims, bounded
    // by the mini stream's real size.
    for (index, &value) in minifat.iter().enumerate() {
        let index = index as u32;
        if index >= mini_chain_limit {
            break;
        }
        if value != consts::FREE_SECTOR
            && !claimed.contains_key(&index)
        {
            state.add(Evidence::OrphanSector {
                layer: ChainLayer::MiniFat,
                sector_id: index,
            });
        }
    }
}

fn count_owner_sectors(state: &AuditState, owner: Owner) -> u32 {
    state
        .owners
        .values()
        .filter(|&&value| value == owner)
        .count() as u32
}

//===========================================================================//
// Directory tree invariants.

/// Checks every live directory entry's sibling/child pointers against the
/// entries that actually exist, and verifies that the sibling subtree is
/// acyclic.  Dangling pointers are "truncated directory" evidence; they are
/// kept separate from FAT-level out-of-bounds findings.
fn audit_directory_tree(state: &mut AuditState) {
    // Snapshot the tree pointers so findings can be pushed while iterating.
    let pointers: Vec<(u32, ObjType, u32, u32, u32)> = state
        .entries
        .iter()
        .enumerate()
        .map(|(id, entry)| {
            (
                id as u32,
                entry.obj_type,
                entry.left_sibling,
                entry.right_sibling,
                entry.child,
            )
        })
        .collect();
    let num_entries = pointers.len() as u32;

    let is_missing = |target: u32| -> bool {
        if target == consts::NO_STREAM {
            return false;
        }
        if target >= num_entries || target > consts::MAX_REGULAR_STREAM_ID {
            return true;
        }
        pointers[target as usize].1 == ObjType::Unallocated
    };

    for (id, obj_type, left, right, child) in pointers.iter().copied() {
        if obj_type == ObjType::Unallocated {
            continue;
        }
        for (target, field) in [
            (left, DirField::LeftSibling),
            (right, DirField::RightSibling),
            (child, DirField::Child),
        ] {
            if is_missing(target) {
                state.add(Evidence::TruncatedDirectory {
                    from_entry: Some(id),
                    missing: target,
                    field,
                });
            }
        }
    }

    // Cheap cycle check over each entry's child subtree's right spine.
    for (id, obj_type, _left, _right, child) in pointers.iter().copied() {
        if obj_type == ObjType::Unallocated {
            continue;
        }
        let mut seen = std::collections::HashSet::new();
        let mut cur = child;
        while cur != consts::NO_STREAM && cur < num_entries {
            if pointers[cur as usize].1 == ObjType::Unallocated {
                break;
            }
            if !seen.insert(cur) {
                state.add(Evidence::Cycle {
                    layer: ChainLayer::Directory,
                    sector_id: cur,
                    chain_start: child,
                    entry_id: Some(id),
                });
                break;
            }
            cur = pointers[cur as usize].3; // right sibling
        }
    }
}


//===========================================================================//
// Repair-step synthesis.
//
// Every step is a four-byte cell overwrite (FAT/MiniFAT/directory pointer);
// no sector is added or removed, so a failed apply can restore the exact
// original bytes.  Cell offsets are derived from the same sector geometry
// and directory-entry field offsets the audit used; there is no second
// description of the format.

use super::plan::RepairStep;

struct BuildContext {
    version: Version,
    sector_len: u64,
    data: Vec<u8>,
    fat_sector_ids: Vec<u32>,
    minifat_sector_ids: Vec<u32>,
    dir_sector_ids: Vec<u32>,
    steps: Vec<RepairStep>,
}

impl BuildContext {
    fn new(data: &[u8]) -> io::Result<BuildContext> {
        let mut cursor = Cursor::new(data);
        let header = Header::read_from(&mut cursor, Validation::Permissive)?;
        let version = header.version;
        let sector_len = version.sector_len() as u64;
        let len = data.len() as u64;
        let num_sectors = if len >= sector_len {
            (len / sector_len - 1) as u32
        } else {
            0
        };

        // Recover FAT/DIFAT/directory geometry with the same tolerant walks
        // the audit uses.
        let mut probe = AuditState {
            version,
            sector_len,
            num_sectors,
            data: data.to_vec(),
            fat: Vec::new(),
            fat_sector_ids: Vec::new(),
            difat_sector_ids: Vec::new(),
            entries: Vec::new(),
            dir_sector_ids: Vec::new(),
            first_dir_sector_beyond: None,
            evidence: Vec::new(),
            owners: HashMap::new(),
        };
        read_difat_and_fat(&mut probe, &header)?;
        read_directory(&mut probe, &header);

        let mut minifat_sector_ids = Vec::new();
        let mut cur = header.first_minifat_sector;
        let mut guard = std::collections::HashSet::new();
        while cur != consts::END_OF_CHAIN && cur != consts::FREE_SECTOR {
            if !is_regular_pointer(cur) || cur >= num_sectors || !guard.insert(cur)
            {
                break;
            }
            minifat_sector_ids.push(cur);
            cur = probe.fat_next(cur).unwrap_or(consts::END_OF_CHAIN);
        }

        Ok(BuildContext {
            version,
            sector_len,
            data: data.to_vec(),
            fat_sector_ids: probe.fat_sector_ids,
            minifat_sector_ids,
            dir_sector_ids: probe.dir_sector_ids,
            steps: Vec::new(),
        })
    }

    fn into_steps(self) -> Vec<RepairStep> {
        let mut steps = self.steps;
        steps.sort_by(|a, b| a.offset.cmp(&b.offset));
        steps.dedup_by(|a, b| a.offset == b.offset);
        steps
    }

    fn build(&mut self, evidence: &Evidence) {
        match evidence {
            Evidence::Cycle { layer, .. } => match layer {
                ChainLayer::Fat | ChainLayer::Difat => {
                    let at = cycle_cell_to_terminate(evidence);
                    self.fat_cell(at, consts::END_OF_CHAIN, "break FAT cycle");
                }
                ChainLayer::MiniFat => {
                    let at = evidence.first_location();
                    self.minifat_cell(
                        at,
                        consts::END_OF_CHAIN,
                        "break MiniFAT cycle",
                    );
                }
                ChainLayer::Directory => {
                    self.dir_field(
                        evidence.first_location(),
                        DIR_RIGHT_SIBLING_OFFSET,
                        consts::NO_STREAM,
                        "break directory tree cycle",
                    );
                }
            },
            Evidence::OutOfBounds { layer, at, .. } => match layer {
                ChainLayer::MiniFat => self.minifat_cell(
                    *at,
                    consts::END_OF_CHAIN,
                    "terminate mini chain before out-of-bounds link",
                ),
                ChainLayer::Directory => self.fat_cell(
                    *at,
                    consts::END_OF_CHAIN,
                    "terminate directory chain before out-of-bounds link",
                ),
                _ => self.fat_cell(
                    *at,
                    consts::END_OF_CHAIN,
                    "terminate chain before out-of-bounds link",
                ),
            },
            Evidence::DoubleAllocation { sector_id, .. } => {
                if evidence.layer() == ChainLayer::MiniFat {
                    self.minifat_cell(
                        *sector_id,
                        consts::END_OF_CHAIN,
                        "separate crossed mini chains",
                    );
                } else {
                    self.fat_cell(
                        *sector_id,
                        consts::END_OF_CHAIN,
                        "separate crossed chains",
                    );
                }
            }
            Evidence::OrphanSector { sector_id, .. } => {
                if evidence.layer() == ChainLayer::MiniFat {
                    self.minifat_cell(
                        *sector_id,
                        consts::FREE_SECTOR,
                        "mark orphaned mini sector free",
                    );
                } else {
                    self.fat_cell(
                        *sector_id,
                        consts::FREE_SECTOR,
                        "mark orphaned sector free",
                    );
                }
            }
            Evidence::TruncatedDirectory { from_entry, field, .. } => {
                if let Some(id) = from_entry {
                    let (offset, label) = match field {
                        DirField::LeftSibling => (
                            DIR_LEFT_SIBLING_OFFSET,
                            "null dangling left sibling",
                        ),
                        DirField::RightSibling => (
                            DIR_RIGHT_SIBLING_OFFSET,
                            "null dangling right sibling",
                        ),
                        DirField::Child => {
                            (DIR_CHILD_OFFSET, "null dangling child")
                        }
                        DirField::Chain => return,
                    };
                    self.dir_field(*id, offset, consts::NO_STREAM, label);
                }
                // A chain-level truncation ends at an EOC/FREE cell already.
            }
            // Declared-length mismatches are reported for the caller; chains
            // that are *also* structurally broken carry their own
            // cycle/out-of-bounds/early-end evidence which is what gets
            // patched.  Repairing stream_len itself cannot be guessed safely.
            Evidence::LengthMismatch { .. } => {}
        }
    }

    fn push(&mut self, offset: u64, new_value: u32, description: &str) {
        if offset + 4 > self.data.len() as u64 {
            return;
        }
        let start = offset as usize;
        let old_bytes = self.data[start..start + 4].to_vec();
        let new_bytes = new_value.to_le_bytes().to_vec();
        if old_bytes != new_bytes {
            self.steps.push(RepairStep {
                offset,
                old_bytes,
                new_bytes,
                description: description.to_string(),
            });
        }
    }

    fn fat_cell(&mut self, sector_id: u32, new_value: u32, description: &str) {
        let entries_per_sector = self.sector_len / 4;
        if let Some((fat_sector, within)) = self.table_cell_location(
            &self.fat_sector_ids,
            entries_per_sector,
            sector_id,
        ) {
            let offset =
                (fat_sector as u64 + 1) * self.sector_len + within * 4;
            self.push(offset, new_value, description);
        }
    }

    fn minifat_cell(
        &mut self,
        mini_sector: u32,
        new_value: u32,
        description: &str,
    ) {
        let entries_per_sector = self.sector_len / 4;
        if let Some((sector_id, within)) = self.table_cell_location(
            &self.minifat_sector_ids,
            entries_per_sector,
            mini_sector,
        ) {
            let offset =
                (sector_id as u64 + 1) * self.sector_len + within * 4;
            self.push(offset, new_value, description);
        }
    }

    fn table_cell_location(
        &self,
        sector_ids: &[u32],
        entries_per_sector: u64,
        index: u32,
    ) -> Option<(u32, u64)> {
        let sector_index = index as u64 / entries_per_sector;
        let within = index as u64 % entries_per_sector;
        sector_ids
            .get(sector_index as usize)
            .copied()
            .map(|id| (id, within))
    }

    fn dir_field(
        &mut self,
        entry_id: u32,
        field_offset: u64,
        new_value: u32,
        description: &str,
    ) {
        let entries_per_sector = self.version.dir_entries_per_sector() as u64;
        let sector_index = entry_id as u64 / entries_per_sector;
        let within_entry = entry_id as u64 % entries_per_sector;
        let Some(&sector_id) =
            self.dir_sector_ids.get(sector_index as usize)
        else {
            return;
        };
        let offset = (sector_id as u64 + 1) * self.sector_len
            + within_entry * consts::DIR_ENTRY_LEN as u64
            + field_offset;
        self.push(offset, new_value, description);
    }
}

/// For FAT cycles, terminates the cell of the first sector revisited: that
/// cell currently points back into the chain; writing ENDOFCHAIN there
/// detaches the loop without moving any sector.
fn cycle_cell_to_terminate(evidence: &Evidence) -> u32 {
    evidence.first_location()
}
