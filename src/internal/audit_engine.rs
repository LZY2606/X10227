//! Opt-in structural audit and read-only repair planning.
//!
//! This module is shared by the public [`crate::audit`] API and the
//! production open path: both parse the same header, FAT, directory and
//! MiniFAT bytes with the same primitives.  The audit never writes; it builds
//! a model of the file in memory, classifies corruption evidence, and plans
//! byte-level patches.  Applying those patches is a separate, explicitly
//! requested step that is digest-gated and journaled.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Read, Write};

use fnv::{FnvHashMap, FnvHashSet};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
#[allow(unused_imports)]
use crate::{ReadLeNumber, WriteLeNumber};

/// Which allocation structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AuditTable {
    /// The double-indirect FAT (header array and DIFAT sectors).
    Difat,
    /// The file allocation table.
    Fat,
    /// The directory entry chain.
    Directory,
    /// The mini-stream FAT.
    MiniFat,
}

/// The category of structural violation.
///
/// Cycles, out-of-bounds references, double occupancy, orphans, and declared
/// length disagreements are always reported as distinct categories, even when
/// the same damaged chain exhibits more than one.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AuditCorruption {
    /// A chain loops back on itself.
    Cycle,
    /// A pointer names a sector or entry that does not exist.
    OutOfBounds,
    /// The same sector is reachable from two different owners.
    DoubleOccupancy,
    /// An allocated sector is not reachable from any root.
    Orphan,
    /// A declared length (stream size, directory size, or table size in the
    /// header) disagrees with the chains on disk.
    LengthMismatch,
    /// A directory sector or entry cannot be parsed at all.
    Malformed,
}

impl AuditCorruption {
    pub fn as_str(self) -> &'static str {
        match self {
            AuditCorruption::Cycle => "cycle",
            AuditCorruption::OutOfBounds => "out-of-bounds reference",
            AuditCorruption::DoubleOccupancy => "double occupancy",
            AuditCorruption::Orphan => "orphan sector",
            AuditCorruption::LengthMismatch => "declared length mismatch",
            AuditCorruption::Malformed => "malformed structure",
        }
    }
}

/// One diagnosed violation, with the first offending location and enough
/// context to explain it without re-reading the file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RawFinding {
    pub table: AuditTable,
    pub corruption: AuditCorruption,
    /// First violating sector/entry/index.
    pub location: u64,
    /// Human-readable context (always in English).
    pub detail: String,
}

/// One planned byte patch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Patch {
    pub offset: u64,
    pub old_bytes: Vec<u8>,
    pub new_bytes: Vec<u8>,
}

impl Patch {
    fn u32(offset: u64, old: u32, new: u32) -> Patch {
        Patch {
            offset,
            old_bytes: old.to_le_bytes().to_vec(),
            new_bytes: new.to_le_bytes().to_vec(),
        }
    }

    fn u64(offset: u64, old: u64, new: u64) -> Patch {
        Patch {
            offset,
            old_bytes: old.to_le_bytes().to_vec(),
            new_bytes: new.to_le_bytes().to_vec(),
        }
    }

    fn bytes(offset: u64, old: &[u8], new: &[u8]) -> Patch {
        debug_assert_eq!(old.len(), new.len());
        Patch {
            offset,
            old_bytes: old.to_vec(),
            new_bytes: new.to_vec(),
        }
    }
}

/// FNV-1a (64-bit) digest of the analyzed bytes, paired with the byte length.
pub fn digest_bytes(data: &[u8]) -> (u64, u64) {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    let mut hash = OFFSET;
    for &byte in data {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(PRIME);
    }
    (hash, data.len() as u64)
}

fn u32_at(data: &[u8], offset: usize) -> Option<u32> {
    let bytes = data.get(offset..offset + 4)?;
    Some(u32::from_le_bytes([
        bytes[0], bytes[1], bytes[2], bytes[3],
    ]))
}

fn sector_start(version: Version, sector_id: u32) -> u64 {
    (sector_id as u64 + 1) * version.sector_len() as u64
}

fn fat_entry_offset(version: Version, fat_sector_id: u32, index: u32) -> u64 {
    sector_start(version, fat_sector_id)
        + (index as u64 % (version.sector_len() / 4) as u64) * 4
}

fn dir_entry_offset(version: Version, dir_sector_id: u32, slot: u32) -> u64 {
    sector_start(version, dir_sector_id)
        + (slot as u64 % version.dir_entries_per_sector() as u64)
            * consts::DIR_ENTRY_LEN as u64
}

/// Reads every byte from a reader.
pub fn read_all<R: Read>(reader: &mut R) -> io::Result<Vec<u8>> {
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    Ok(data)
}

//===========================================================================//

/// A tolerant in-memory model of a CFB image.
struct Model<'a> {
    data: &'a [u8],
    version: Version,
    header: Header,
    num_sectors: u32,
    difat: Vec<u32>,
    difat_sectors: Vec<u32>,
    fat: Vec<u32>,
    findings: Vec<RawFinding>,
    /// Directory entries found by walking the directory chain, in order.
    dir_entries: Vec<DirEntry>,
    /// Sector ID of the directory sector holding each entry.
    dir_entry_sector: Vec<u32>,
    dir_chain: Vec<u32>,
    /// Directory sectors that hold parseable entries but dropped off the
    /// directory chain.
    dropped_dir_sectors: Vec<u32>,
    /// Entries parsed from dropped directory sectors (stream id, entry).
    dropped_entries: Vec<(u32, DirEntry)>,
    minifat: Vec<u32>,
    minifat_chain: Vec<u32>,
}

impl<'a> Model<'a> {
    fn fat_is_used(&self, id: u32) -> bool {
        (id as usize) < self.fat.len()
            && self.fat[id as usize] != consts::FREE_SECTOR
    }

    fn fat_entry(&self, id: u32) -> Option<u32> {
        self.fat.get(id as usize).copied()
    }
}

//===========================================================================//
// Tolerant parsing.  Every byte interpretation here uses the same primitives
// as CompoundFile::open_internal (Header::read_from, DirEntry::read_from);
// the audit simply never gives up after the first damaged pointer.

fn finding(
    table: AuditTable,
    corruption: AuditCorruption,
    location: u64,
    detail: String,
) -> RawFinding {
    RawFinding { table, corruption, location, detail }
}

fn build_model(data: &[u8]) -> io::Result<Model<'_>> {
    let mut cursor = std::io::Cursor::new(data);
    // Headers use the same reader as the production open path.
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len() as u64;
    let num_sectors =
        (data.len() as u64 / sector_len).saturating_sub(1) as u32;
    let mut findings = Vec::new();

    // ---- DIFAT ----------------------------------------------------------
    let mut difat: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();
    let mut difat_sectors: Vec<u32> = Vec::new();
    let mut seen_difat: FnvHashSet<u32> = FnvHashSet::default();
    let mut current = header.first_difat_sector;
    let mut difat_broke = false;
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current > consts::MAX_REGULAR_SECTOR || current >= num_sectors {
            findings.push(finding(
                AuditTable::Difat,
                AuditCorruption::OutOfBounds,
                current as u64,
                format!(
                    "DIFAT chain reaches sector {} but the file has only {} \
                     sectors",
                    current, num_sectors
                ),
            ));
            difat_broke = true;
            break;
        }
        if !seen_difat.insert(current) {
            findings.push(finding(
                AuditTable::Difat,
                AuditCorruption::Cycle,
                current as u64,
                format!(
                    "DIFAT chain revisits sector {} and never terminates",
                    current
                ),
            ));
            difat_broke = true;
            break;
        }
        difat_sectors.push(current);
        let entries_per_sector = sector_len as usize / 4;
        let start = sector_start(version, current) as usize;
        if start + sector_len as usize > data.len() {
            findings.push(finding(
                AuditTable::Difat,
                AuditCorruption::OutOfBounds,
                current as u64,
                format!(
                    "DIFAT sector {} runs past end of file ({} bytes)",
                    current,
                    data.len()
                ),
            ));
            difat_broke = true;
            break;
        }
        for i in 0..entries_per_sector - 1 {
            if let Some(entry) = u32_at(data, start + 4 * i) {
                if entry != consts::FREE_SECTOR {
                    difat.push(entry);
                }
            }
        }
        current = u32_at(data, start + sector_len as usize - 4)
            .unwrap_or(consts::END_OF_CHAIN);
    }
    // Trim DIFAT padding the same permissive way the open path does.
    while difat.len() > consts::NUM_DIFAT_ENTRIES_IN_HEADER
        && difat.len() > header.num_fat_sectors as usize
        && difat.last() == Some(&0)
    {
        difat.pop();
    }
    while difat.last() == Some(&consts::FREE_SECTOR) {
        difat.pop();
    }
    if !difat_broke && difat_sectors.len() as u32 != header.num_difat_sectors
    {
        findings.push(finding(
            AuditTable::Difat,
            AuditCorruption::LengthMismatch,
            68,
            format!(
                "header declares {} DIFAT sectors, but the DIFAT chain has {}",
                header.num_difat_sectors,
                difat_sectors.len()
            ),
        ));
    }

    // Duplicate FAT-sector pointers inside the DIFAT array itself.
    {
        let mut seen: FnvHashSet<u32> = FnvHashSet::default();
        for &fat_sector in difat.iter() {
            if fat_sector == consts::FREE_SECTOR {
                continue;
            }
            if !seen.insert(fat_sector) {
                findings.push(finding(
                    AuditTable::Difat,
                    AuditCorruption::DoubleOccupancy,
                    fat_sector as u64,
                    format!(
                        "DIFAT lists FAT sector {} more than once",
                        fat_sector
                    ),
                ));
            }
            if fat_sector >= num_sectors {
                findings.push(finding(
                    AuditTable::Difat,
                    AuditCorruption::OutOfBounds,
                    fat_sector as u64,
                    format!(
                        "DIFAT points at FAT sector {} but the file has only \
                         {} sectors",
                        fat_sector, num_sectors
                    ),
                ));
            }
        }
    }

    // ---- FAT ------------------------------------------------------------
    let mut fat: Vec<u32> = Vec::new();
    let entries_per_sector = sector_len as usize / 4;
    for &fat_sector_id in difat.iter() {
        if fat_sector_id == consts::FREE_SECTOR
            || fat_sector_id >= num_sectors
        {
            continue;
        }
        let start = sector_start(version, fat_sector_id) as usize;
        if start + sector_len as usize > data.len() {
            findings.push(finding(
                AuditTable::Fat,
                AuditCorruption::OutOfBounds,
                fat_sector_id as u64,
                format!(
                    "FAT sector {} runs past end of file",
                    fat_sector_id
                ),
            ));
            continue;
        }
        for i in 0..entries_per_sector {
            fat.push(
                u32_at(data, start + 4 * i).unwrap_or(consts::FREE_SECTOR),
            );
        }
    }
    // Match the open path's tolerant trimming/padding of the tail.
    while fat.len() > num_sectors as usize {
        match fat.last() {
            Some(&0)
            | Some(&consts::DIFAT_SECTOR)
            | Some(&consts::FAT_SECTOR)
            | Some(&consts::FREE_SECTOR) => {
                fat.pop();
            }
            _ => break,
        }
    }
    while fat.len() < num_sectors as usize {
        fat.push(consts::FREE_SECTOR);
    }
    if fat.len() as u32 > num_sectors {
        findings.push(finding(
            AuditTable::Fat,
            AuditCorruption::LengthMismatch,
            fat.len() as u64,
            format!(
                "FAT has {} entries but the file has only {} sectors",
                fat.len(),
                num_sectors
            ),
        ));
    }
    if difat.len() as u32 != header.num_fat_sectors {
        findings.push(finding(
            AuditTable::Difat,
            AuditCorruption::LengthMismatch,
            44,
            format!(
                "header declares {} FAT sectors, but DIFAT lists {}",
                header.num_fat_sectors,
                difat.len()
            ),
        ));
    }

    // Mark FAT/DIFAT sectors the way Allocator::validate does, so they are
    // not mistaken for orphans or data.
    let mut fat = fat;
    for &id in difat_sectors.iter().chain(difat.iter()) {
        if (id as usize) < fat.len() {
            fat[id as usize] = if difat_sectors.contains(&id) {
                consts::DIFAT_SECTOR
            } else {
                consts::FAT_SECTOR
            };
        }
    }

    let mut model = Model {
        data,
        version,
        header,
        num_sectors,
        difat,
        difat_sectors,
        fat,
        findings,
        dir_entries: Vec::new(),
        dir_entry_sector: Vec::new(),
        dir_chain: Vec::new(),
        dropped_dir_sectors: Vec::new(),
        dropped_entries: Vec::new(),
        minifat: Vec::new(),
        minifat_chain: Vec::new(),
    };
    model.parse_directory_chain(data);
    model.parse_minifat(data);
    Ok(model)
}

//===========================================================================//
impl<'a> Model<'a> {
    /// Returns the IDs of the FAT chain starting at `start`, tolerating
    /// out-of-bounds pointers, cycles, and cross-links.  A chain that leaves
    /// the valid sector range or re-enters itself ends there.
    fn walk_fat_chain(&self, start: u32) -> Vec<u32> {
        let mut ids = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ids;
        }
        let mut current = start;
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current as usize >= self.fat.len()
            {
                break;
            }
            if !local.insert(current) {
                break;
            }
            ids.push(current);
            current = self.fat[current as usize];
        }
        ids
    }

    fn parse_directory_chain(&mut self, data: &[u8]) {
        let per_sector = self.version.dir_entries_per_sector();
        let mut current = self.header.first_dir_sector;
        let mut seen: FnvHashSet<u32> = FnvHashSet::default();
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.findings.push(finding(
                    AuditTable::Directory,
                    AuditCorruption::OutOfBounds,
                    current as u64,
                    format!(
                        "directory chain reaches sector {} but the file has \
                         only {} sectors",
                        current, self.num_sectors
                    ),
                ));
                break;
            }
            if !seen.insert(current) {
                self.findings.push(finding(
                    AuditTable::Directory,
                    AuditCorruption::Cycle,
                    current as u64,
                    format!(
                        "directory chain revisits sector {} and never \
                         terminates",
                        current
                    ),
                ));
                break;
            }
            self.dir_chain.push(current);
            let start = sector_start(self.version, current) as usize;
            let base_index = self.dir_entries.len() as u32;
            for slot in 0..per_sector {
                let offset = start + slot * consts::DIR_ENTRY_LEN;
                if offset + consts::DIR_ENTRY_LEN > data.len() {
                    self.findings.push(finding(
                        AuditTable::Directory,
                        AuditCorruption::OutOfBounds,
                        base_index as u64 + slot as u64,
                        format!(
                            "directory entry {} in sector {} runs past end                              of file",
                            base_index + slot as u32,
                            current
                        ),
                    ));
                    return;
                }
                let mut slice =
                    &data[offset..offset + consts::DIR_ENTRY_LEN];
                match DirEntry::read_from(
                    &mut slice,
                    self.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => {
                        self.dir_entries.push(entry);
                        self.dir_entry_sector.push(current);
                    }
                    Err(err) => {
                        self.findings.push(finding(
                            AuditTable::Directory,
                            AuditCorruption::Malformed,
                            base_index as u64 + slot as u64,
                            format!(
                                "directory entry {} in sector {} is \
                                 unparseable: {}",
                                base_index + slot as u32,
                                current,
                                err
                            ),
                        ));
                        return;
                    }
                }
            }
            match self.fat_entry(current) {
                Some(next) => current = next,
                None => break,
            }
        }
    }

    fn parse_minifat(&mut self, data: &[u8]) {
        let chain =
            self.walk_fat_chain(self.header.first_minifat_sector);
        let per_sector = self.version.sector_len() / 4;
        let mut bytes = Vec::new();
        for &sector_id in chain.iter() {
            let start = sector_start(self.version, sector_id) as usize;
            for i in 0..per_sector {
                bytes.push(
                    u32_at(data, start + 4 * i)
                        .unwrap_or(consts::FREE_SECTOR),
                );
            }
        }
        while bytes.last() == Some(&consts::FREE_SECTOR) {
            bytes.pop();
        }
        self.minifat_chain = chain;
        self.minifat = bytes;
    }
}

//===========================================================================//
/// Result of analyzing an image.
pub struct RawReport {
    pub findings: Vec<RawFinding>,
    /// Patches of one repair round, in deterministic application order.
    pub planned_patches: Vec<Patch>,
}

//===========================================================================//
// Classification.
//
// Root priority decides ownership of a merged (cross-linked) sector: the
// earlier root in this order keeps it.  The order is purely deterministic so
// repeated audits always name the same first violation.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
enum RootKind {
    Directory,
    MiniFat,
    MiniStream,
    Stream(u32),
}

struct ChainVisit {
    /// Sectors reached, in walk order.
    sectors: Vec<u32>,
    /// Set if the walk revisited one of its own sectors; value is that id.
    cycle: Option<u32>,
    /// Set if a pointer left the FAT; value is the source sector.
    out_edge: Option<u32>,
}

struct Analysis {
    /// First owner of each reached data sector.
    owner: FnvHashMap<u32, RootKind>,
    /// First owning stream entry of each reached mini sector.
    owner_mini: FnvHashMap<u32, u32>,
    /// Chain reached from each root.
    root_chains: FnvHashMap<RootKind, Vec<u32>>,
    /// Raw edits planned in this round: (offset, new bytes).
    edits: BTreeMap<u64, Vec<u8>>,
    /// FAT cycle members, for deterministic edge cutting.
    fat_cycles: Vec<Vec<u32>>,
    /// MiniFAT cycle members.
    mini_cycles: Vec<Vec<u32>>,
    /// Orphan FAT chains, in ascending start-sector order.
    orphan_fat_chains: Vec<Vec<u32>>,
    /// Orphan MiniFAT chains.
    orphan_mini_chains: Vec<Vec<u32>>,
    /// Directory sector chains that look like the dropped tail of the
    /// directory chain and can be reattached.
    reattach_dir: Option<Vec<u32>>,
    /// Cross-owner collisions observed while walking roots:
    /// (sector, first owner, other owner).
    conflicts: Vec<(u32, RootKind, RootKind)>,
}

fn is_special(entry: u32) -> bool {
    matches!(
        entry,
        consts::FREE_SECTOR
            | consts::END_OF_CHAIN
            | consts::FAT_SECTOR
            | consts::DIFAT_SECTOR
            | consts::INVALID_SECTOR
    )
}

impl<'a> Model<'a> {
    /// Walks one data chain from `start`, recording cycle and out-of-range
    /// edges.  Metadata sectors stop the walk.
    fn visit_data_chain(&self, start: u32) -> ChainVisit {
        let mut sectors = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ChainVisit {
                sectors,
                cycle: None,
                out_edge: None,
            };
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = start;
        while current <= consts::MAX_REGULAR_SECTOR {
            if !local.insert(current) {
                return ChainVisit {
                    sectors,
                    cycle: Some(current),
                    out_edge: None,
                };
            }
            if current as usize >= self.fat.len() {
                sectors.push(current);
                return ChainVisit {
                    sectors,
                    cycle: None,
                    out_edge: Some(current),
                };
            }
            sectors.push(current);
            let next = self.fat[current as usize];
            if next == consts::END_OF_CHAIN || next == consts::FREE_SECTOR {
                break;
            }
            if next > consts::MAX_REGULAR_SECTOR {
                return ChainVisit {
                    sectors,
                    cycle: None,
                    out_edge: Some(current),
                };
            }
            if next as usize >= self.fat.len() {
                return ChainVisit {
                    sectors,
                    cycle: None,
                    out_edge: Some(current),
                };
            }
            current = next;
        }
        ChainVisit { sectors, cycle: None, out_edge: None }
    }

    fn visit_mini_chain(&self, start: u32) -> ChainVisit {
        let mut sectors = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ChainVisit {
                sectors,
                cycle: None,
                out_edge: None,
            };
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = start;
        while current <= consts::MAX_REGULAR_SECTOR {
            if !local.insert(current) {
                return ChainVisit {
                    sectors,
                    cycle: Some(current),
                    out_edge: None,
                };
            }
            if current as usize >= self.minifat.len() {
                sectors.push(current);
                return ChainVisit {
                    sectors,
                    cycle: None,
                    out_edge: Some(current),
                };
            }
            sectors.push(current);
            let next = self.minifat[current as usize];
            if next == consts::END_OF_CHAIN || next == consts::FREE_SECTOR {
                break;
            }
            if next > consts::MAX_REGULAR_SECTOR
                || next as usize >= self.minifat.len()
            {
                return ChainVisit {
                    sectors,
                    cycle: None,
                    out_edge: Some(current),
                };
            }
            current = next;
        }
        ChainVisit { sectors, cycle: None, out_edge: None }
    }
}

/// Adds a finding unless an equivalent one is already present.
fn push_unique(findings: &mut Vec<RawFinding>, new: RawFinding) {
    if !findings.iter().any(|f| {
        f.table == new.table
            && f.corruption == new.corruption
            && f.location == new.location
    }) {
        findings.push(new);
    }
}

/// Sorts findings deterministically: table, then category, then first
/// violating location.
fn sort_findings(findings: &mut Vec<RawFinding>) {
    findings.sort_by(|a, b| {
        (a.table, a.corruption, a.location)
            .cmp(&(b.table, b.corruption, b.location))
    });
}

//===========================================================================//
impl<'a> Model<'a> {
    /// FAT entry marking a sector as metadata (FAT or DIFAT sector).
    fn is_metadata_sector(&self, id: u32) -> bool {
        matches!(
            self.fat_entry(id),
            Some(consts::FAT_SECTOR) | Some(consts::DIFAT_SECTOR)
        )
    }

    /// Analyzes the model and plans one round of repairs.  Findings from the
    /// parsing phase are already in `self.findings`.
    fn analyze_round(&mut self) -> (Vec<Patch>, bool) {
        let mut findings = std::mem::take(&mut self.findings);
        let mut analysis = Analysis {
            owner: FnvHashMap::default(),
            owner_mini: FnvHashMap::default(),
            root_chains: FnvHashMap::default(),
            edits: BTreeMap::new(),
            fat_cycles: Vec::new(),
            mini_cycles: Vec::new(),
            orphan_fat_chains: Vec::new(),
            orphan_mini_chains: Vec::new(),
            reattach_dir: None,
            conflicts: Vec::new(),
        };

        self.analyze_fat_static(&mut findings);
        self.visit_roots(&mut findings, &mut analysis);
        self.find_fat_orphans(&mut findings, &mut analysis);
        self.analyze_directory_semantics(&mut findings);
        self.analyze_streams(&mut findings, &analysis);
        self.analyze_minifat_static(&mut findings, &mut analysis);
        self.find_mini_orphans(&mut findings, &mut analysis);

        let repairable = self.plan_patches(&mut findings, &mut analysis);

        sort_findings(&mut findings);
        self.findings = findings;
        let mut patches: Vec<Patch> = Vec::new();
        for (offset, new_bytes) in analysis.edits {
            let start = offset as usize;
            if start + new_bytes.len() > self.data.len() {
                continue;
            }
            let old_bytes =
                self.data[start..start + new_bytes.len()].to_vec();
            if old_bytes != new_bytes {
                patches.push(Patch {
                    offset,
                    old_bytes,
                    new_bytes,
                });
            }
        }
        (patches, repairable)
    }

    fn data_len(&self) -> usize {
        self.data.len()
    }

    fn slice_at(&self, offset: usize, len: usize) -> &[u8] {
        &self.data[offset..offset + len]
    }

    /// Static FAT checks independent of chain roots: out-of-range regular
    /// entries, INVALID entries, and static double occupancy.
    fn analyze_fat_static(&self, findings: &mut Vec<RawFinding>) {
        let mut pointees: FnvHashMap<u32, u32> = FnvHashMap::default();
        for (from, &to) in self.fat.iter().enumerate() {
            let from = from as u32;
            if to == consts::INVALID_SECTOR {
                push_unique(
                    findings,
                    finding(
                        AuditTable::Fat,
                        AuditCorruption::OutOfBounds,
                        from as u64,
                        format!(
                            "FAT entry for sector {} is the reserved invalid \
                             value 0x{:08X}",
                            from,
                            consts::INVALID_SECTOR
                        ),
                    ),
                );
            } else if to <= consts::MAX_REGULAR_SECTOR {
                if to as usize >= self.fat.len() {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Fat,
                            AuditCorruption::OutOfBounds,
                            from as u64,
                            format!(
                                "FAT entry for sector {} points to sector {} \
                                 beyond the {}-entry FAT",
                                from,
                                to,
                                self.fat.len()
                            ),
                        ),
                    );
                } else if let Some(&first_from) = pointees.get(&to) {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Fat,
                            AuditCorruption::DoubleOccupancy,
                            to as u64,
                            format!(
                                "sector {} is pointed to by both FAT entries \
                                 {} and {}",
                                to, first_from, from
                            ),
                        ),
                    );
                }
                pointees.entry(to).or_insert(from);
            }
        }
    }

    fn visit_roots(&self, findings: &mut Vec<RawFinding>, a: &mut Analysis) {
        let mut roots: Vec<(RootKind, u32)> = Vec::new();
        roots.push((RootKind::Directory, self.header.first_dir_sector));
        roots.push((RootKind::MiniFat, self.header.first_minifat_sector));
        // Root entry's mini stream.
        if !self.dir_entries.is_empty() {
            let root = &self.dir_entries[0];
            roots.push((RootKind::MiniStream, root.start_sector));
        }
        for (id, entry) in self.dir_entries.iter().enumerate().skip(1) {
            if entry.obj_type == ObjType::Stream
                && entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
            {
                roots.push((RootKind::Stream(id as u32), entry.start_sector));
            }
        }
        for (kind, start) in roots {
            let visit = self.visit_data_chain(start);
            if let Some(cycle_id) = visit.cycle {
                push_unique(
                    findings,
                    finding(
                        AuditTable::Fat,
                        AuditCorruption::Cycle,
                        cycle_id as u64,
                        format!(
                            "FAT chain rooted at {} loops back to sector {}",
                            root_label(kind),
                            cycle_id
                        ),
                    ),
                );
            }
            if let Some(source) = visit.out_edge {
                // Static scan reports the exact out-of-range target too; add
                // the chain-level first violation only when the static scan
                // missed it.
                if let Some(&to) = self.fat.get(source as usize) {
                    if to <= consts::MAX_REGULAR_SECTOR
                        && to as usize >= self.fat.len()
                    {
                        push_unique(
                            findings,
                            finding(
                                AuditTable::Fat,
                                AuditCorruption::OutOfBounds,
                                source as u64,
                                format!(
                                    "FAT chain rooted at {} leaves the FAT at \
                                     sector {} pointing to {}",
                                    root_label(kind),
                                    source,
                                    to
                                ),
                            ),
                        );
                    }
                }
            }
            // Register ownership for cross-link detection.
            for &sector in visit.sectors.iter() {
                if self.is_metadata_sector(sector) {
                    continue;
                }
                if let Some(&first) = a.owner.get(&sector) {
                    if first != kind {
                        a.conflicts.push((sector, first, kind));
                        push_unique(
                            findings,
                            finding(
                                AuditTable::Fat,
                                AuditCorruption::DoubleOccupancy,
                                sector as u64,
                                format!(
                                    "sector {} is reachable from both {} and \
                                     {}",
                                    sector,
                                    root_label(first),
                                    root_label(kind)
                                ),
                            ),
                        );
                    }
                } else {
                    a.owner.insert(sector, kind);
                }
            }
            a.root_chains.insert(kind, visit.sectors);
        }
    }

    fn find_fat_orphans(
        &self,
        findings: &mut Vec<RawFinding>,
        a: &mut Analysis,
    ) {
        // Sectors still unvisited after walking all roots: collect chains.
        let mut scanned: BTreeSet<u32> = BTreeSet::new();
        let mut cycles: Vec<Vec<u32>> = Vec::new();
        for id in 0..self.fat.len() as u32 {
            let entry = match self.fat_entry(id) {
                Some(entry) => entry,
                None => continue,
            };
            if is_special(entry) || scanned.contains(&id) {
                continue;
            }
            if a.owner.contains_key(&id) {
                continue;
            }
            // Walk the unreachable chain.
            let mut chain = Vec::new();
            let mut local: FnvHashSet<u32> = FnvHashSet::default();
            let mut current = id;
            let mut is_cycle = false;
            while current <= consts::MAX_REGULAR_SECTOR
                && (current as usize) < self.fat.len()
            {
                let entry = self.fat[current as usize];
                if entry == consts::END_OF_CHAIN
                    || entry == consts::FREE_SECTOR
                {
                    chain.push(current);
                    scanned.insert(current);
                    break;
                }
                if !local.insert(current) {
                    is_cycle = true;
                    break;
                }
                if a.owner.contains_key(&current) {
                    // Joins a reachable chain; the merge itself is a cycle/
                    // cross-link, the joined tail is not orphaned.
                    break;
                }
                chain.push(current);
                scanned.insert(current);
                if entry > consts::MAX_REGULAR_SECTOR
                    || entry as usize >= self.fat.len()
                {
                    break;
                }
                current = entry;
            }
            if chain.is_empty() {
                continue;
            }
            if is_cycle {
                cycles.push(chain);
            } else {
                a.orphan_fat_chains.push(chain);
            }
        }
        for cycle in cycles {
            if let Some(&first) = cycle.iter().min() {
                a.fat_cycles.push(cycle);
                push_unique(
                    findings,
                    finding(
                        AuditTable::Fat,
                        AuditCorruption::Cycle,
                        first as u64,
                        format!(
                            "unreachable FAT sector chain loops on itself \
                             starting at sector {}",
                            first
                        ),
                    ),
                );
            }
        }
        // Also detect root-rooted cycles not caught above (pure cycles where
        // the start is inside the loop): the visit_roots cycle path handles
        // those, so nothing else is needed here.
        for orphan_chain in a.orphan_fat_chains.iter() {
            let start = orphan_chain[0];
            // Can the chain be the dropped tail of the directory chain?
            if self.looks_like_directory_tail(orphan_chain) {
                if a.reattach_dir.is_none() {
                    a.reattach_dir = Some(orphan_chain.clone());
                }
                push_unique(
                    findings,
                    finding(
                        AuditTable::Directory,
                        AuditCorruption::LengthMismatch,
                        start as u64,
                        format!(
                            "directory chain ends early: sector {} holds \
                             parseable directory entries but is not linked \
                             from the directory chain",
                            start
                        ),
                    ),
                );
                continue;
            }
            push_unique(
                findings,
                finding(
                    AuditTable::Fat,
                    AuditCorruption::Orphan,
                    start as u64,
                    format!(
                        "allocated sector chain starting at {} is not \
                         reachable from the directory, MiniFAT, or mini \
                         stream",
                        start
                    ),
                ),
            );
        }
    }

    fn looks_like_directory_tail(&self, chain: &[u32]) -> bool {
        let per_sector = self.version.dir_entries_per_sector();
        for &sector_id in chain {
            let start = sector_start(self.version, sector_id) as usize;
            let mut parseable = 0;
            for slot in 0..per_sector {
                let offset = start + slot * consts::DIR_ENTRY_LEN;
                if offset + consts::DIR_ENTRY_LEN > self.data_len() {
                    return false;
                }
                // Read directly through the production entry parser.
                let bytes = self.slice_at(offset, consts::DIR_ENTRY_LEN);
                let mut slice = &bytes[..];
                match DirEntry::read_from(
                    &mut slice,
                    self.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => match entry.obj_type {
                        ObjType::Unallocated => {}
                        ObjType::Storage | ObjType::Stream => parseable += 1,
                        ObjType::Root => return false,
                    },
                    Err(_) => return false,
                }
            }
            if parseable == 0 {
                return false;
            }
        }
        true
    }
}

fn root_label(kind: RootKind) -> String {
    match kind {
        RootKind::Directory => "the directory chain".to_string(),
        RootKind::MiniFat => "the MiniFAT chain".to_string(),
        RootKind::MiniStream => "the mini stream".to_string(),
        RootKind::Stream(id) => format!("stream directory entry {}", id),
    }
}

//===========================================================================//
impl<'a> Model<'a> {
    /// Walks the sibling/child tree starting at the root, checking pointers
    /// and cycle-freeness.
    fn analyze_directory_semantics(&self, findings: &mut Vec<RawFinding>) {
        if self.dir_entries.is_empty() {
            push_unique(
                findings,
                finding(
                    AuditTable::Directory,
                    AuditCorruption::Malformed,
                    0,
                    "root directory entry is missing".to_string(),
                ),
            );
            return;
        }
        if self.dir_entries[0].obj_type != ObjType::Root {
            push_unique(
                findings,
                finding(
                    AuditTable::Directory,
                    AuditCorruption::Malformed,
                    0,
                    format!(
                        "directory entry 0 has object type {:?}, not root",
                        self.dir_entries[0].obj_type
                    ),
                ),
            );
        }
        let count = self.dir_entries.len() as u32;
        let mut visited: FnvHashSet<u32> = FnvHashSet::default();
        let mut stack: Vec<(u32, u32)> = vec![(consts::ROOT_STREAM_ID, 0)];
        while let Some((stream_id, depth)) = stack.pop() {
            if !visited.insert(stream_id) {
                push_unique(
                    findings,
                    finding(
                        AuditTable::Directory,
                        AuditCorruption::Cycle,
                        stream_id as u64,
                        format!(
                            "directory sibling/child tree revisits entry {} \
                             (tree depth {})",
                            stream_id, depth
                        ),
                    ),
                );
                continue;
            }
            let entry = &self.dir_entries[stream_id as usize];
            for (field, target) in [
                ("left sibling", entry.left_sibling),
                ("right sibling", entry.right_sibling),
                ("child", entry.child),
            ] {
                if target == consts::NO_STREAM {
                    continue;
                }
                if target >= count {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Directory,
                            AuditCorruption::OutOfBounds,
                            stream_id as u64,
                            format!(
                                "directory entry {} {} points to entry {}, \
                                 beyond the {}-entry directory",
                                stream_id, field, target, count
                            ),
                        ),
                    );
                } else if self.dir_entries[target as usize].obj_type
                    == ObjType::Unallocated
                {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Directory,
                            AuditCorruption::OutOfBounds,
                            stream_id as u64,
                            format!(
                                "directory entry {} {} points to unallocated \
                                 entry {}",
                                stream_id, field, target
                            ),
                        ),
                    );
                } else {
                    stack.push((target, depth + 1));
                }
            }
        }
        // V4 carries the directory sector count in the header.
        if self.version == Version::V4
            && self.header.num_dir_sectors as usize != self.dir_chain.len()
        {
            push_unique(
                findings,
                finding(
                    AuditTable::Directory,
                    AuditCorruption::LengthMismatch,
                    40,
                    format!(
                        "header declares {} directory sectors, but the \
                         directory chain has {}",
                        self.header.num_dir_sectors,
                        self.dir_chain.len()
                    ),
                ),
            );
        }
    }

    /// Checks declared stream lengths against the chains they name.
    fn analyze_streams(
        &self,
        findings: &mut Vec<RawFinding>,
        a: &Analysis,
    ) {
        let regular_len = self.version.sector_len() as u64;
        // Root entry: mini stream length consistency.
        if !self.dir_entries.is_empty() {
            let root = &self.dir_entries[0];
            if root.stream_len % consts::MINI_SECTOR_LEN as u64 != 0 {
                push_unique(
                    findings,
                    finding(
                        AuditTable::Directory,
                        AuditCorruption::LengthMismatch,
                        0,
                        format!(
                            "root mini stream length {} is not a multiple of \
                             {} mini-sector bytes",
                            root.stream_len,
                            consts::MINI_SECTOR_LEN
                        ),
                    ),
                );
            }
            if let Some(chain) = a.root_chains.get(&RootKind::MiniStream) {
                let capacity = chain.len() as u64 * regular_len;
                if root.stream_len > capacity {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Directory,
                            AuditCorruption::LengthMismatch,
                            0,
                            format!(
                                "root entry declares a {} byte mini stream, \
                                 but its chain holds only {} bytes",
                                root.stream_len, capacity
                            ),
                        ),
                    );
                }
            }
            // The MiniFAT must fit inside the declared mini stream.
            let mini_capacity_sectors =
                root.stream_len / consts::MINI_SECTOR_LEN as u64;
            if (self.minifat.len() as u64) > mini_capacity_sectors {
                push_unique(
                    findings,
                    finding(
                        AuditTable::MiniFat,
                        AuditCorruption::LengthMismatch,
                        self.header.first_minifat_sector as u64,
                        format!(
                            "MiniFAT has {} entries, but the declared mini \
                             stream covers only {} mini sectors",
                            self.minifat.len(),
                            mini_capacity_sectors
                        ),
                    ),
                );
            }
        }
        for (id, entry) in self.dir_entries.iter().enumerate().skip(1) {
            if entry.obj_type != ObjType::Stream {
                continue;
            }
            let id = id as u32;
            if entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64 {
                let start = entry.start_sector;
                if start > consts::MAX_REGULAR_SECTOR
                    || start as usize >= self.fat.len()
                    || self.is_metadata_sector(start)
                {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::Fat,
                            AuditCorruption::OutOfBounds,
                            id as u64,
                            format!(
                                "stream entry {} names start sector {} for a \
                                 {} byte stream, which is outside the data \
                                 region",
                                id, start, entry.stream_len
                            ),
                        ),
                    );
                    continue;
                }
                if let Some(chain) = a.root_chains.get(&RootKind::Stream(id))
                {
                    let capacity = chain.len() as u64 * regular_len;
                    if entry.stream_len > capacity {
                        push_unique(
                            findings,
                            finding(
                                AuditTable::Fat,
                                AuditCorruption::LengthMismatch,
                                id as u64,
                                format!(
                                    "stream entry {} declares {} bytes but \
                                     its chain starting at sector {} holds \
                                     only {} bytes",
                                    id,
                                    entry.stream_len,
                                    start,
                                    capacity
                                ),
                            ),
                        );
                    }
                }
            } else if entry.stream_len > 0
                || entry.start_sector != consts::END_OF_CHAIN
            {
                let start = entry.start_sector;
                if start != consts::END_OF_CHAIN
                    && start != consts::FREE_SECTOR
                    && (start > consts::MAX_REGULAR_SECTOR
                        || start as usize >= self.minifat.len())
                {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::MiniFat,
                            AuditCorruption::OutOfBounds,
                            id as u64,
                            format!(
                                "stream entry {} names mini sector {} for a \
                                 {} byte mini stream, but the MiniFAT has \
                                 only {} entries",
                                id,
                                start,
                                entry.stream_len,
                                self.minifat.len()
                            ),
                        ),
                    );
                    continue;
                }
                if start != consts::END_OF_CHAIN
                    && start != consts::FREE_SECTOR
                {
                    let visit = self.visit_mini_chain(start);
                    let capacity = visit.sectors.len() as u64
                        * consts::MINI_SECTOR_LEN as u64;
                    if entry.stream_len > capacity {
                        push_unique(
                            findings,
                            finding(
                                AuditTable::MiniFat,
                                AuditCorruption::LengthMismatch,
                                id as u64,
                                format!(
                                    "stream entry {} declares {} bytes but \
                                     its mini chain starting at mini sector \
                                     {} holds only {} bytes",
                                    id,
                                    entry.stream_len,
                                    start,
                                    capacity
                                ),
                            ),
                        );
                    }
                }
            }
        }
    }
}

//===========================================================================//
impl<'a> Model<'a> {
    fn analyze_minifat_static(
        &self,
        findings: &mut Vec<RawFinding>,
        a: &mut Analysis,
    ) {
        let mut pointees: FnvHashMap<u32, u32> = FnvHashMap::default();
        for (from, &to) in self.minifat.iter().enumerate() {
            let from = from as u32;
            if to == consts::INVALID_SECTOR {
                push_unique(
                    findings,
                    finding(
                        AuditTable::MiniFat,
                        AuditCorruption::OutOfBounds,
                        from as u64,
                        format!(
                            "MiniFAT entry {} is the reserved invalid value \
                             0x{:08X}",
                            from,
                            consts::INVALID_SECTOR
                        ),
                    ),
                );
            } else if to <= consts::MAX_REGULAR_SECTOR
                && to as usize >= self.minifat.len()
            {
                push_unique(
                    findings,
                    finding(
                        AuditTable::MiniFat,
                        AuditCorruption::OutOfBounds,
                        from as u64,
                        format!(
                            "mini sector {} points to mini sector {} beyond \
                             the {}-entry MiniFAT",
                            from,
                            to,
                            self.minifat.len()
                        ),
                    ),
                );
            } else if to <= consts::MAX_REGULAR_SECTOR {
                if let Some(&first) = pointees.get(&to) {
                    push_unique(
                        findings,
                        finding(
                            AuditTable::MiniFat,
                            AuditCorruption::DoubleOccupancy,
                            to as u64,
                            format!(
                                "mini sector {} is pointed to by MiniFAT \
                                 entries {} and {}",
                                to, first, from
                            ),
                        ),
                    );
                }
                pointees.entry(to).or_insert(from);
            }
        }
        // Walk all named mini chains for cycle detection and ownership.
        let mut owner: FnvHashMap<u32, u32> = FnvHashMap::default();
        for (id, entry) in self.dir_entries.iter().enumerate().skip(1) {
            if entry.obj_type != ObjType::Stream
                || entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
                || entry.start_sector == consts::END_OF_CHAIN
                || entry.start_sector == consts::FREE_SECTOR
            {
                continue;
            }
            let visit = self.visit_mini_chain(entry.start_sector);
            if let Some(cycle_id) = visit.cycle {
                push_unique(
                    findings,
                    finding(
                        AuditTable::MiniFat,
                        AuditCorruption::Cycle,
                        cycle_id as u64,
                        format!(
                            "mini chain of stream entry {} loops back to \
                             mini sector {}",
                            id, cycle_id
                        ),
                    ),
                );
            }
            for sector in visit.sectors {
                if let Some(&first) = owner.get(&sector) {
                    if first != id as u32 {
                        push_unique(
                            findings,
                            finding(
                                AuditTable::MiniFat,
                                AuditCorruption::DoubleOccupancy,
                                sector as u64,
                                format!(
                                    "mini sector {} is reachable from stream \
                                     entries {} and {}",
                                    sector, first, id
                                ),
                            ),
                        );
                    }
                } else {
                    owner.insert(sector, id as u32);
                }
            }
        }
        a.owner_mini = owner;
        // Pure cycles among unreachable mini sectors.
        let mut scanned: BTreeSet<u32> = BTreeSet::new();
        for id in 0..self.minifat.len() as u32 {
            let entry = self.minifat[id as usize];
            if is_special(entry) || scanned.contains(&id) {
                continue;
            }
            if a.owner_mini.contains_key(&id) {
                continue;
            }
            let mut chain = Vec::new();
            let mut local: FnvHashSet<u32> = FnvHashSet::default();
            let mut current = id;
            let mut is_cycle = false;
            while current <= consts::MAX_REGULAR_SECTOR
                && (current as usize) < self.minifat.len()
            {
                let to = self.minifat[current as usize];
                if to == consts::END_OF_CHAIN || to == consts::FREE_SECTOR {
                    chain.push(current);
                    scanned.insert(current);
                    break;
                }
                if !local.insert(current) {
                    is_cycle = true;
                    break;
                }
                if a.owner_mini.contains_key(&current) {
                    break;
                }
                chain.push(current);
                scanned.insert(current);
                if to > consts::MAX_REGULAR_SECTOR
                    || to as usize >= self.minifat.len()
                {
                    break;
                }
                current = to;
            }
            if chain.is_empty() {
                continue;
            }
            if is_cycle {
                if let Some(&first) = chain.iter().min() {
                    a.mini_cycles.push(chain);
                    push_unique(
                        findings,
                        finding(
                            AuditTable::MiniFat,
                            AuditCorruption::Cycle,
                            first as u64,
                            format!(
                                "unreachable mini sector chain loops on \
                                 itself starting at mini sector {}",
                                first
                            ),
                        ),
                    );
                }
            } else {
                a.orphan_mini_chains.push(chain);
            }
        }
    }

    fn find_mini_orphans(
        &self,
        findings: &mut Vec<RawFinding>,
        a: &mut Analysis,
    ) {
        for orphan in a.orphan_mini_chains.iter() {
            let start = orphan[0];
            push_unique(
                findings,
                finding(
                    AuditTable::MiniFat,
                    AuditCorruption::Orphan,
                    start as u64,
                    format!(
                        "allocated mini sector chain starting at {} is not \
                         named by any stream directory entry",
                        start
                    ),
                ),
            );
        }
    }
}

//===========================================================================//
// Repair planning.  Every repair is an in-place fixed-width byte patch; the
// planner never grows or truncates the image, so the sector layout and the
// production parser stay in one-to-one correspondence.

impl<'a> Model<'a> {
    fn plan_patches(
        &mut self,
        findings: &[RawFinding],
        a: &mut Analysis,
    ) -> bool {
        let mut repairable = true;

        // ---- FAT: cycles ------------------------------------------------
        let fat_cycles = a.fat_cycles.clone();
        let orphan_fat_chains = a.orphan_fat_chains.clone();
        let mini_cycles = a.mini_cycles.clone();
        let orphan_mini_chains = a.orphan_mini_chains.clone();
        let reattach_dir = a.reattach_dir.clone();
        for cycle in fat_cycles.iter() {
            // Cut the edge entering the smallest-id member of the loop.
            let cut_target = *cycle.iter().min().unwrap();
            let predecessor = self.predecessor_in_fat(cut_target);
            if let Some(pred) = predecessor {
                self.queue_fat(a, pred, consts::END_OF_CHAIN);
            }
        }
        // Root-rooted cycles: the smallest revisit id recorded by the chain
        // walk has a FAT predecessor inside the same chain.
        for f in findings.iter().filter(|f| {
            f.table == AuditTable::Fat && f.corruption == AuditCorruption::Cycle
        }) {
            let target = f.location as u32;
            if (target as usize) < self.fat.len() {
                if let Some(pred) = self.predecessor_in_fat(target) {
                    self.queue_fat(a, pred, consts::END_OF_CHAIN);
                }
            }
        }

        // ---- FAT: out-of-bounds / invalid entries ----------------------
        for (from, &to) in self.fat.iter().enumerate() {
            let from = from as u32;
            if to == consts::INVALID_SECTOR {
                self.queue_fat(a, from, consts::FREE_SECTOR);
            } else if to <= consts::MAX_REGULAR_SECTOR
                && to as usize >= self.fat.len()
            {
                self.queue_fat(a, from, consts::END_OF_CHAIN);
            }
        }

        // ---- FAT: double occupancy --------------------------------------
        // Collect every target sector named by a double-occupancy finding
        // (whether the merge is between two FAT predecessors or a chain
        // starting at another chain's sector).
        let mut targets: BTreeSet<u32> = BTreeSet::new();
        for f in findings.iter().filter(|f| {
            f.table == AuditTable::Fat
                && f.corruption == AuditCorruption::DoubleOccupancy
        }) {
            targets.insert(f.location as u32);
        }
        for target in targets {
            // Claimants: the root owner recorded by chain walking, plus the
            // owners of every FAT predecessor (covers merges whose second
            // owner is not in `owner` because its walk joined the first
            // chain immediately).
            let mut claimants: BTreeSet<RootKind> = BTreeSet::new();
            if let Some(&kind) = a.owner.get(&target) {
                claimants.insert(kind);
            }
            for (from, &to) in self.fat.iter().enumerate() {
                if to == target {
                    let pred = from as u32;
                    let kind = a.owner.get(&pred).copied().unwrap_or(
                        RootKind::Stream(u32::MAX),
                    );
                    claimants.insert(kind);
                }
            }
            let winner = claimants.iter().copied().min().unwrap_or(
                RootKind::Stream(u32::MAX),
            );
            // Every FAT predecessor not belonging to the winning chain loses
            // its outgoing edge.
            for (from, &to) in self.fat.iter().enumerate() {
                if to != target {
                    continue;
                }
                let pred = from as u32;
                let pred_owner = a.owner.get(&pred).copied();
                if pred_owner != Some(winner) {
                    self.queue_fat(a, pred, consts::END_OF_CHAIN);
                }
            }
            // If the loser starts its chain exactly at `target`, there is no
            // FAT predecessor to cut: the loser's start pointer (directory
            // entry, or the MiniFAT root in the header) must be cleared.
            for (sector, first, other) in a.conflicts.iter().cloned() {
                if sector != target {
                    continue;
                }
                // A loser whose chain begins exactly at the contested
                // sector has no FAT predecessor for us to cut.
                for claimant in [first, other] {
                    if claimant != winner
                        && self.root_start_of(claimant) == target
                    {
                        self.clear_root_start(a, claimant);
                    }
                }
            }
        }

        // ---- FAT: orphans ----------------------------------------------
        if let Some(reattach) = reattach_dir.clone() {
            // Link the current directory chain's last sector to the dropped
            // chain, then the dropped tail is terminated.  Also repair the V4
            // directory sector count in the header.
            if let Some(&last_dir_sector) = self.dir_chain.last() {
                self.queue_fat(a, last_dir_sector, reattach[0]);
            }
            if let Some(&last) = reattach.last() {
                self.queue_fat(a, last, consts::END_OF_CHAIN);
            }
            if self.version == Version::V4 {
                let new_count =
                    (self.dir_chain.len() + reattach.len()) as u32;
                self.queue_u32_header(a, 40, new_count);
            }
        }
        for orphan in orphan_fat_chains.iter() {
            if reattach_dir.as_ref() == Some(orphan) {
                continue;
            }
            for &id in orphan {
                self.queue_fat(a, id, consts::FREE_SECTOR);
            }
        }

        // ---- Directory: pointers and declared lengths -----------------
        if !self.dir_entries.is_empty() {
            let count = self.dir_entries.len() as u32;
            for (id, entry) in self.dir_entries.iter().enumerate() {
                let mut patched = entry.clone();
                let mut changed = false;
                for (field, target) in [
                    ("left", &mut patched.left_sibling),
                    ("right", &mut patched.right_sibling),
                    ("child", &mut patched.child),
                ] {
                    let _ = field;
                    if *target != consts::NO_STREAM
                        && (*target >= count
                            || self.dir_entries[*target as usize].obj_type
                                == ObjType::Unallocated)
                    {
                        *target = consts::NO_STREAM;
                        changed = true;
                    }
                }
                if changed {
                    self.queue_dir_entry(a, id as u32, &patched);
                }
            }
            // Root mini stream declared length clamp.
            let root = &self.dir_entries[0];
            if let Some(chain) = a.root_chains.get(&RootKind::MiniStream) {
                let capacity =
                    chain.len() as u64 * self.version.sector_len() as u64;
                let new_len = root.stream_len.min(capacity)
                    - (root.stream_len.min(capacity)
                        % consts::MINI_SECTOR_LEN as u64);
                if new_len != root.stream_len {
                    self.queue_dir_field_u64(
                        a,
                        0,
                        120,
                        root.stream_len,
                        new_len,
                    );
                }
            }
            if root_stream_len_not_multiple(root) {
                let new_len = root.stream_len
                    - root.stream_len % consts::MINI_SECTOR_LEN as u64;
                self.queue_dir_field_u64(a, 0, 120, root.stream_len, new_len);
            }

            // Stream declared-length / bad start repairs.
            let regular_len = self.version.sector_len() as u64;
            for (id, entry) in self.dir_entries.iter().enumerate().skip(1) {
                let id = id as u32;
                if entry.obj_type != ObjType::Stream {
                    continue;
                }
                let mut patched = entry.clone();
                if entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64 {
                    let bad_start = entry.start_sector
                        > consts::MAX_REGULAR_SECTOR
                        || entry.start_sector as usize >= self.fat.len()
                        || self.is_metadata_sector(entry.start_sector);
                    let chain =
                        a.root_chains.get(&RootKind::Stream(id)).cloned();
                    if bad_start {
                        patched.start_sector = consts::END_OF_CHAIN;
                        patched.stream_len = 0;
                        self.queue_dir_entry(a, id, &patched);
                    } else if let Some(chain) = chain {
                        let capacity = chain.len() as u64 * regular_len;
                        if entry.stream_len > capacity {
                            self.queue_dir_field_u64(
                                a,
                                id,
                                120,
                                entry.stream_len,
                                capacity,
                            );
                        }
                    }
                } else {
                    let start = entry.start_sector;
                    let bad_start = start != consts::END_OF_CHAIN
                        && start != consts::FREE_SECTOR
                        && (start > consts::MAX_REGULAR_SECTOR
                            || start as usize >= self.minifat.len());
                    if bad_start {
                        self.queue_dir_field_u32(
                            a,
                            id,
                            116,
                            start,
                            consts::END_OF_CHAIN,
                        );
                        self.queue_dir_field_u64(a, id, 120, entry.stream_len, 0);
                    } else if start != consts::END_OF_CHAIN
                        && start != consts::FREE_SECTOR
                    {
                        let visit = self.visit_mini_chain(start);
                        let capacity = visit.sectors.len() as u64
                            * consts::MINI_SECTOR_LEN as u64;
                        if entry.stream_len > capacity {
                            self.queue_dir_field_u64(
                                a,
                                id,
                                120,
                                entry.stream_len,
                                capacity,
                            );
                        }
                    }
                }
            }
        }

        // ---- MiniFAT: cycles, OOB, doubles, orphans --------------------
        for cycle in mini_cycles.iter() {
            let target = *cycle.iter().min().unwrap();
            if let Some(pred) = self.predecessor_in_minifat(target) {
                self.queue_minifat(a, pred, consts::END_OF_CHAIN);
            }
        }
        for f in findings.iter().filter(|f| {
            f.table == AuditTable::MiniFat
                && f.corruption == AuditCorruption::Cycle
        }) {
            let target = f.location as u32;
            if (target as usize) < self.minifat.len() {
                if let Some(pred) = self.predecessor_in_minifat(target) {
                    self.queue_minifat(a, pred, consts::END_OF_CHAIN);
                }
            }
        }
        for (from, &to) in self.minifat.iter().enumerate() {
            let from = from as u32;
            if to == consts::INVALID_SECTOR {
                self.queue_minifat(a, from, consts::FREE_SECTOR);
            } else if to <= consts::MAX_REGULAR_SECTOR
                && to as usize >= self.minifat.len()
            {
                self.queue_minifat(a, from, consts::END_OF_CHAIN);
            }
        }
        let mut mini_targets: BTreeSet<u32> = BTreeSet::new();
        for f in findings.iter().filter(|f| {
            f.table == AuditTable::MiniFat
                && f.corruption == AuditCorruption::DoubleOccupancy
        }) {
            mini_targets.insert(f.location as u32);
        }
        for target in mini_targets {
            let predecessors: Vec<u32> = self
                .minifat
                .iter()
                .enumerate()
                .filter(|(_, &to)| to == target)
                .map(|(from, _)| from as u32)
                .collect();
            if predecessors.len() < 2 {
                continue;
            }
            // The lowest stream-id owner keeps the mini sector.
            let winner = predecessors
                .iter()
                .copied()
                .min_by_key(|&pred| {
                    (
                        a.owner_mini
                            .iter()
                            .find_map(|(&sector, &owner)| {
                                if sector == target {
                                    Some(owner)
                                } else {
                                    None
                                }
                            })
                            .unwrap_or(u32::MAX),
                        pred,
                    )
                })
                .unwrap();
            for pred in predecessors {
                if pred != winner {
                    self.queue_minifat(a, pred, consts::END_OF_CHAIN);
                }
            }
        }
        for orphan in orphan_mini_chains.iter() {
            for &id in orphan {
                self.queue_minifat(a, id, consts::FREE_SECTOR);
            }
        }

        // ---- Header count disagreements that we keep consistent -------
        if self.version == Version::V4
            && self.header.num_dir_sectors as usize != self.dir_chain.len()
                + reattach_dir
                    .as_ref()
                    .map(|chain| chain.len())
                    .unwrap_or(0)
        {
            if reattach_dir.is_some() {
                // Already queued above.
            } else {
                self.queue_u32_header(
                    a,
                    40,
                    self.dir_chain.len() as u32,
                );
            }
        }

        // ---- Anything we do not know how to repair --------------------
        for f in findings {
            if !self.is_planned(f) {
                repairable = false;
            }
        }
        repairable
    }

    fn is_planned(&self, f: &RawFinding) -> bool {
        // DIFAT chain damage and unparseable directory entries cannot be
        // repaired in place without risking data loss; an oversized MiniFAT
        // cannot be shrunk without relocating the mini stream.
        match (f.table, f.corruption) {
            (AuditTable::Difat, AuditCorruption::Cycle)
            | (AuditTable::Difat, AuditCorruption::OutOfBounds)
            | (AuditTable::Directory, AuditCorruption::Malformed)
            | (AuditTable::MiniFat, AuditCorruption::LengthMismatch)
            | (AuditTable::Difat, AuditCorruption::LengthMismatch) => false,
            _ => true,
        }
    }

    fn root_start_of(&self, kind: RootKind) -> u32 {
        match kind {
            RootKind::Directory => self.header.first_dir_sector,
            RootKind::MiniFat => self.header.first_minifat_sector,
            RootKind::MiniStream => {
                self.dir_entries.first().map(|e| e.start_sector).unwrap_or(
                    consts::END_OF_CHAIN,
                )
            }
            RootKind::Stream(id) => self
                .dir_entries
                .get(id as usize)
                .map(|e| e.start_sector)
                .unwrap_or(consts::END_OF_CHAIN),
        }
    }

    /// Severs a root's start pointer when a cross-linked chain's first
    /// sector belongs to another chain.  The damaged root loses its data.
    fn clear_root_start(&self, a: &mut Analysis, loser: RootKind) {
        match loser {
            RootKind::Directory => {
                self.queue_u32_header(a, 48, consts::END_OF_CHAIN);
            }
            RootKind::MiniFat => {
                self.queue_u32_header(a, 60, consts::END_OF_CHAIN);
                self.queue_u32_header(a, 64, 0);
            }
            RootKind::MiniStream => {
                self.queue_dir_field_u32(
                    a,
                    0,
                    116,
                    self.header.first_minifat_sector,
                    consts::END_OF_CHAIN,
                );
                self.queue_dir_field_u64(a, 0, 120, 0, 0);
            }
            RootKind::Stream(id) => {
                if let Some(entry) = self.dir_entries.get(id as usize) {
                    self.queue_dir_field_u32(
                        a,
                        id,
                        116,
                        entry.start_sector,
                        consts::END_OF_CHAIN,
                    );
                    self.queue_dir_field_u64(a, id, 120, entry.stream_len, 0);
                }
            }
        }
    }

    fn predecessor_in_fat(&self, target: u32) -> Option<u32> {
        self.fat
            .iter()
            .position(|&to| to == target)
            .map(|idx| idx as u32)
    }

    fn predecessor_in_minifat(&self, target: u32) -> Option<u32> {
        self.minifat
            .iter()
            .position(|&to| to == target)
            .map(|idx| idx as u32)
    }

    fn owner_of_sector(
        &self,
        sector: u32,
        a: &Analysis,
    ) -> Option<RootKind> {
        if a.owner.contains_key(&sector) {
            return a.owner.get(&sector).copied();
        }
        // A predecessor might itself be unreachable; treat such chains with
        // the lowest priority so a named root always wins.
        None
    }
}

fn root_stream_len_not_multiple(root: &DirEntry) -> bool {
    root.stream_len % consts::MINI_SECTOR_LEN as u64 != 0
}


//===========================================================================//
// Edit queue helpers.  Offsets are derived from the same on-disk layout the
// production reader/writer uses (header at 0, sectors at (id+1)*sector_len).

fn dir_entry_field_offset(
    version: Version,
    stream_id: u32,
    dir_sector_id: u32,
    slot_within_sector: u32,
    field_offset: u64,
) -> u64 {
    let _ = stream_id;
    let _ = slot_within_sector;
    sector_start(version, dir_sector_id) + field_offset
}

impl<'a> Model<'a> {
    fn queue_fat(&self, a: &mut Analysis, index: u32, value: u32) {
        let entries_per_sector = (self.version.sector_len() / 4) as u32;
        let fat_sector_index = index / entries_per_sector;
        let Some(&fat_sector_id) =
            self.difat.get(fat_sector_index as usize)
        else {
            return;
        };
        if fat_sector_id >= self.num_sectors {
            return;
        }
        let offset = fat_entry_offset(
            self.version,
            fat_sector_id,
            index,
        );
        a.edits.insert(offset, value.to_le_bytes().to_vec());
    }

    fn queue_minifat(&self, a: &mut Analysis, index: u32, value: u32) {
        let entries_per_sector = (self.version.sector_len() / 4) as u32;
        let minifat_sector_index = index / entries_per_sector;
        let Some(&sector_id) = self
            .minifat_chain
            .get(minifat_sector_index as usize)
        else {
            return;
        };
        let offset = sector_start(self.version, sector_id)
            + (index % entries_per_sector) as u64 * 4;
        a.edits.insert(offset, value.to_le_bytes().to_vec());
    }

    fn queue_u32_header(&self, a: &mut Analysis, offset: u64, value: u32) {
        a.edits.insert(offset, value.to_le_bytes().to_vec());
    }

    fn dir_field_offset(
        &self,
        stream_id: u32,
        field_offset: u64,
    ) -> Option<u64> {
        let slot = stream_id;
        let sector = *self.dir_entry_sector.get(slot as usize)?;
        let within = stream_id
            % self.version.dir_entries_per_sector() as u32;
        Some(
            sector_start(self.version, sector)
                + within as u64 * consts::DIR_ENTRY_LEN as u64
                + field_offset,
        )
    }

    fn queue_dir_field_u32(
        &self,
        a: &mut Analysis,
        stream_id: u32,
        field_offset: u64,
        _old: u32,
        new: u32,
    ) {
        if let Some(offset) = self.dir_field_offset(stream_id, field_offset) {
            a.edits.insert(offset, new.to_le_bytes().to_vec());
        }
    }

    fn queue_dir_field_u64(
        &self,
        a: &mut Analysis,
        stream_id: u32,
        field_offset: u64,
        _old: u64,
        new: u64,
    ) {
        if let Some(offset) = self.dir_field_offset(stream_id, field_offset) {
            a.edits.insert(offset, new.to_le_bytes().to_vec());
        }
    }

    fn queue_dir_entry(
        &self,
        a: &mut Analysis,
        stream_id: u32,
        entry: &DirEntry,
    ) {
        let Some(sector) =
            self.dir_entry_sector.get(stream_id as usize).copied()
        else {
            return;
        };
        let within =
            stream_id % self.version.dir_entries_per_sector() as u32;
        let base = sector_start(self.version, sector)
            + within as u64 * consts::DIR_ENTRY_LEN as u64;
        let mut bytes = Vec::with_capacity(consts::DIR_ENTRY_LEN);
        if entry.write_to(&mut bytes).is_ok()
            && bytes.len() == consts::DIR_ENTRY_LEN
        {
            for (i, byte) in bytes.into_iter().enumerate() {
                a.edits.insert(base + i as u64, vec![byte]);
            }
        }
    }
}

//===========================================================================//
// Fixed-point driver.  The same analyze->patch->re-analyze loop is used by
// dry runs (in memory only) and by real application (after a digest check),
// so a plan is always validated against the bytes it would produce.

fn apply_patches_to_vec(data: &mut Vec<u8>, patches: &[Patch]) {
    for patch in patches {
        let start = patch.offset as usize;
        if start + patch.new_bytes.len() > data.len() {
            continue;
        }
        data[start..start + patch.new_bytes.len()]
            .copy_from_slice(&patch.new_bytes);
    }
}

/// Full result of auditing one image.
pub struct AuditOutcome {
    pub findings: Vec<RawFinding>,
    pub patches: Vec<Patch>,
    /// True iff the fixed point is reachable with only in-place repairs.
    pub repairable: bool,
    pub converged: bool,
    /// Digest of the image the patches converge on.
    pub target_digest: (u64, u64),
}

/// Analyzes `data`, iterating repairs until no findings remain or no further
/// progress can be made.  Never mutates `data`.
pub fn analyze_image(data: &[u8]) -> io::Result<AuditOutcome> {
    const MAX_ROUNDS: usize = 16;
    // Patches are fixed-width and in place, so offsets never move.  Keeping
    // them in an offset-keyed map makes rounds idempotent and order-stable.
    let mut merged: BTreeMap<u64, Vec<u8>> = BTreeMap::new();
    let mut repairable = true;
    let mut converged = false;
    let mut final_findings = Vec::new();
    let mut working = data.to_vec();
    for _ in 0..MAX_ROUNDS {
        let mut model = build_model(&working)?;
        let (round_patches, round_repairable) = model.analyze_round();
        final_findings = model.findings;
        if !round_repairable {
            repairable = false;
        }
        if final_findings.is_empty() {
            converged = true;
            break;
        }
        if round_patches.is_empty() {
            break;
        }
        for patch in round_patches {
            merged.insert(patch.offset, patch.new_bytes);
        }
        // Rebuild the working image from the whole merged set each round, so
        // later rounds always see the bytes earlier rounds produced.
        working = data.to_vec();
        for (offset, bytes) in merged.iter() {
            let start = *offset as usize;
            if start + bytes.len() <= working.len() {
                working[start..start + bytes.len()].copy_from_slice(bytes);
            }
        }
    }
    let mut patches: Vec<Patch> = merged
        .into_iter()

        .map(|(offset, new_bytes)| {
            let start = offset as usize;
            let old_bytes = data[start..start + new_bytes.len()].to_vec();
            Patch { offset, old_bytes, new_bytes }
        })
        .collect();
    patches.sort_by_key(|p| p.offset);
    let target_digest = digest_bytes(&working);
    Ok(AuditOutcome {
        findings: final_findings,
        patches,
        repairable: repairable && converged,
        converged,
        target_digest,
    })
}

/// Verifies that `old == patch.old_bytes`, writes `new_bytes`, and returns a
/// rollback closure's data.  Used by the journaled applier below.
pub struct AppliedPatch {
    pub offset: u64,
    pub old_bytes: Vec<u8>,
}

/// Applies `patches` to `writer`, journaling each write so a failure rolls
/// every earlier write back.  On success every patch is on disk (the caller
/// is responsible for flushing); on error the image is restored byte-for-byte
/// and the error is returned.  This routine is shared by byte-buffer and
/// file-backed applications.
pub fn apply_patches_journaled<W>(
    writer: &mut W,
    patches: &[Patch],
) -> io::Result<()>
where
    W: Write + std::io::Seek,
{
    use std::io::SeekFrom;
    let mut journal: Vec<AppliedPatch> = Vec::new();
    let result: io::Result<()> = (|| {
        for patch in patches {
            writer.seek(SeekFrom::Start(patch.offset))?;
            writer.write_all(&patch.new_bytes)?;
            journal.push(AppliedPatch {
                offset: patch.offset,
                old_bytes: patch.old_bytes.clone(),
            });
        }
        Ok(())
    })();
    if let Err(err) = result {
        for applied in journal.into_iter().rev() {
            // Rollback must surface errors; an image left half-updated is
            // worse than a failed repair, so a rollback failure replaces the
            // original error.
            writer.seek(SeekFrom::Start(applied.offset))?;
            writer.write_all(&applied.old_bytes)?;
        }
        return Err(err);
    }
    Ok(())
}
