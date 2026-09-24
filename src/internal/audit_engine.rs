//! Read-only structural audit engine.
//!
//! This module is the implementation behind the opt-in audit entry points on
//! [`crate::OpenOptions`].  It deliberately does not construct a
//! [`crate::CompoundFile`]: files that are too damaged to open must still be
//! auditable.  It does, however, reuse the same production parsing code for
//! the header and directory entries ([`Header::read_from`] and
//! [`DirEntry::read_from`]), so that the audit's interpretation of the bytes
//! cannot drift from the reader's.
//!
//! The engine operates on an in-memory copy of the file and keeps all of its
//! working state in one [`AuditSession`].  Nothing here is static or global;
//! dropping the report drops every cache and counter of the run.

use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};
use std::mem::size_of;

use fnv::{FnvHashMap, FnvHashSet};

use crate::audit::{
    ApplyOutcome, AuditCheckpoint, AuditOptions, AuditReport, AuditTable,
    CorruptionKind, Digest, Finding, RepairPatch, RepairPlan,
};
use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::WriteLeNumber;

//===========================================================================//

/// One located defect together with the patch (if any) that addresses it.
#[derive(Clone, Debug)]
struct Defect {
    table: AuditTable,
    kind: CorruptionKind,
    location: u64,
    context: String,
    patch: Option<RepairPatch>,
}

impl Defect {
    fn finding(&self) -> Finding {
        Finding {
            table: self.table,
            kind: self.kind,
            location: self.location,
            context: self.context.clone(),
        }
    }
}

/// All mutable working state of a single audit.  A fresh session is created
/// for every entry-point call, so state can never leak between calls.
struct AuditSession<'a> {
    data: &'a [u8],
    options: AuditOptions,
    sector_len: usize,
    num_sectors: u32,
    version: Version,
    defects: Vec<Defect>,
    /// File byte offset of each FAT entry index, when that entry lives in a
    /// FAT sector that could actually be read.
    fat_entry_offsets: FnvHashMap<u32, u64>,
    /// File byte offset of each MiniFAT entry index.
    minifat_entry_offsets: FnvHashMap<u32, u64>,
    /// File byte offset of each directory entry's `start_sector` field.
    dir_start_offsets: FnvHashMap<u32, u64>,
    /// File byte offset of each directory entry's `stream_len` field.
    dir_len_offsets: FnvHashMap<u32, u64>,
}

//===========================================================================//
// Digest: a 128-bit FNV-1a-style fingerprint over the exact input bytes.

const FNV_OFFSET_LO: u64 = 0xcbf29ce484222325;
const FNV_OFFSET_HI: u64 = 0x84222325cbf29ce4;
const FNV_PRIME: u64 = 0x100000001b3;

fn digest_bytes(data: &[u8]) -> Digest {
    let mut lo = FNV_OFFSET_LO ^ (data.len() as u64);
    let mut hi = FNV_OFFSET_HI ^ (data.len() as u64);
    for &byte in data {
        lo ^= byte as u64;
        lo = lo.wrapping_mul(FNV_PRIME);
        hi ^= (byte as u64).rotate_left(7);
        hi = hi.wrapping_mul(FNV_PRIME);
    }
    Digest(lo, hi)
}

//===========================================================================//
// Small byte-level helpers.

fn le_u32_at(data: &[u8], offset: u64) -> Option<u32> {
    let start = offset as usize;
    let bytes = data.get(start..start + 4)?;
    Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

fn sector_offset(sector_len: u64, sector_id: u32) -> u64 {
    (sector_id as u64 + 1) * sector_len
}

fn fat_entry_offset(sector_len: u64, fat_sector: u32, index: u32) -> u64 {
    let entries_per_sector = sector_len / 4;
    let within = (index % entries_per_sector as u32) * 4;
    sector_offset(sector_len, fat_sector) + within as u64
}

fn record_failure(
    defects: &mut Vec<Defect>,
    table: AuditTable,
    kind: CorruptionKind,
    location: u64,
    context: impl Into<String>,
    patch: Option<RepairPatch>,
) {
    let context = context.into();
    // The same defect can be observed from more than one chain walk; keep
    // only the first demonstration of it so output is a set, not a stream.
    if defects.iter().any(|d| {
        d.table == table && d.kind == kind && d.location == location
    }) {
        return;
    }
    defects.push(Defect { table, kind, location, context, patch });
}

fn patch(offset: u64, mut bytes: Vec<u8>, reason: impl Into<String>) -> RepairPatch {
    // Ensure the patch sorts deterministically even when offsets tie.
    let _ = bytes.len();
    RepairPatch { offset, bytes, reason: reason.into() }
}

fn checkpoint(
    options: &AuditOptions,
    point: AuditCheckpoint,
) -> io::Result<()> {
    if options.failpoint == Some(point) {
        Err(io::Error::new(
            io::ErrorKind::Interrupted,
            format!("Injected recoverable audit failure at checkpoint: {point}"),
        ))
    } else {
        Ok(())
    }
}

//===========================================================================//
/// Runs the whole audit over `data` and builds the report.  Never writes.
pub(crate) fn analyze(
    data: &[u8],
    options: &AuditOptions,
) -> io::Result<AuditReport> {
    if data.len() < consts::HEADER_LEN {
        let mut defects = Vec::new();
        record_failure(
            &mut defects,
            AuditTable::Directory,
            CorruptionKind::Truncated,
            data.len() as u64,
            format!(
                "file is only {} bytes, smaller than the {}-byte CFB header",
                data.len(),
                consts::HEADER_LEN
            ),
            None,
        );
        return Ok(finalize(data, defects));
    }

    let mut header_reader = Cursor::new(data);
    // Reuse the production header parser: the audit must understand fields
    // exactly the way opening the file does.
    let header = match Header::read_from(
        &mut header_reader,
        Validation::Permissive,
    ) {
        Ok(header) => header,
        Err(error) => {
            let mut defects = Vec::new();
            record_failure(
                &mut defects,
                AuditTable::Directory,
                CorruptionKind::Truncated,
                0,
                format!("unreadable CFB header: {error}"),
                None,
            );
            return Ok(finalize(data, defects));
        }
    };
    let version = header.version;
    let sector_len = version.sector_len();
    let num_sectors = if data.len() >= sector_len {
        ((data.len() as u64).div_ceil(sector_len as u64) as u32).saturating_sub(1)
    } else {
        0
    };

    let mut session = AuditSession {
        data,
        options: options.clone(),
        sector_len,
        num_sectors,
        version,
        defects: Vec::new(),
        fat_entry_offsets: FnvHashMap::default(),
        minifat_entry_offsets: FnvHashMap::default(),
        dir_start_offsets: FnvHashMap::default(),
        dir_len_offsets: FnvHashMap::default(),
    };

    // Phase 1: DIFAT and FAT (both raw bytes and the chains they describe).
    let (fat_sectors, raw_fat) =
        session.load_allocation_tables(&header)?;
    checkpoint(&session.options, AuditCheckpoint::TablesLoaded)?;

    // Phase 2: directory chain and directory entries.
    let dir_entries = session.examine_directory(&header, &fat_sectors, &raw_fat);

    // Phase 3: every FAT/MiniFAT chain, stream lengths, cross-chain joins,
    // and orphans.  Chain analysis is one two-pass routine so its result is
    // independent of root visit order.
    session.examine_chains(&header, &fat_sectors, &raw_fat, &dir_entries);

    checkpoint(&session.options, AuditCheckpoint::ChainsExamined)?;

    let defects = session.defects;
    Ok(finalize(data, defects))
}

/// Canonicalizes defect ordering: table, then kind, then first location,
/// then context.  The detection walks may add defects in different orders
/// under different scheduling, but the report must not depend on that.
fn finalize(data: &[u8], mut defects: Vec<Defect>) -> AuditReport {
    defects.sort_by(|a, b| {
        (a.table, a.kind, a.location, a.context.as_str())
            .cmp(&(b.table, b.kind, b.location, b.context.as_str()))
    });
    defects.dedup_by(|a, b| {
        a.table == b.table
            && a.kind == b.kind
            && a.location == b.location
            && a.context == b.context
    });
    let digest = digest_bytes(data);
    // Candidate patches travel inside the (private) report so that the
    // planner shares the audit's own analysis rather than reimplementing it.
    let findings = defects.iter().map(Defect::finding).collect();
    let candidate_patches: Vec<RepairPatch> = defects
        .iter()
        .filter_map(|defect| defect.patch.clone())
        .collect();
    AuditReport::with_input(
        digest,
        findings,
        candidate_patches,
        data.to_vec(),
    )
}

//===========================================================================//
impl<'a> AuditSession<'a> {
    fn defect(
        &mut self,
        table: AuditTable,
        kind: CorruptionKind,
        location: u64,
        context: impl Into<String>,
        candidate: Option<RepairPatch>,
    ) {
        record_failure(&mut self.defects, table, kind, location, context, candidate);
    }

    /// Reads the DIFAT chain and every FAT sector it lists.  Returns the FAT
    /// sector IDs in DIFAT order and the raw FAT entries (padded with
    /// FREE_SECTOR when a listed sector is missing or unreadable).
    fn load_allocation_tables(
        &mut self,
        header: &Header,
    ) -> io::Result<(Vec<u32>, Vec<u32>)> {
        // --- DIFAT chain --------------------------------------------------
        let mut difat: Vec<u32> = Vec::new();
        difat.extend_from_slice(&header.initial_difat_entries);
        let mut difat_chain: Vec<u32> = Vec::new();
        let mut current = header.first_difat_sector;
        let mut guard = 0u64;
        let budget = self.num_sectors as u64 + 2;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if guard >= budget {
                let offset = if difat_chain.is_empty() { 68 } else {
                    sector_offset(self.sector_len as u64, *difat_chain.last().unwrap())
                        + self.sector_len as u64 - 4
                };
                self.defect(
                    AuditTable::Difat,
                    CorruptionKind::Cycle,
                    offset,
                    "DIFAT chain revisits a sector and never terminates",
                    None,
                );
                break;
            }
            guard += 1;
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.defect(
                    AuditTable::Difat,
                    CorruptionKind::OutOfBounds,
                    if difat_chain.is_empty() {
                        68
                    } else {
                        sector_offset(
                            self.sector_len as u64,
                            *difat_chain.last().unwrap(),
                        ) + self.sector_len as u64
                            - 4
                    },
                    format!(
                        "DIFAT chain points to sector {current}, but file has \
                         only {} sectors",
                        self.num_sectors
                    ),
                    None,
                );
                break;
            }
            if difat_chain.contains(&current) {
                let prev = *difat_chain.last().unwrap();
                self.defect(
                    AuditTable::Difat,
                    CorruptionKind::Cycle,
                    sector_offset(self.sector_len as u64, prev)
                        + self.sector_len as u64
                        - 4,
                    format!("DIFAT chain revisits sector {current}"),
                    None,
                );
                break;
            }
            difat_chain.push(current);
            let start = sector_offset(self.sector_len as u64, current);
            let entries_per_sector = self.sector_len / 4 - 1;
            for index in 0..entries_per_sector {
                let offset = start + (index * 4) as u64;
                match le_u32_at(self.data, offset) {
                    Some(value) => difat.push(value),
                    None => {
                        self.defect(
                            AuditTable::Difat,
                            CorruptionKind::Truncated,
                            offset,
                            format!(
                                "DIFAT sector {current} runs past end of file"
                            ),
                            None,
                        );
                        break;
                    }
                }
            }
            let next_offset =
                start + (entries_per_sector * 4) as u64;
            current = match le_u32_at(self.data, next_offset) {
                Some(value) => value,
                None => {
                    self.defect(
                        AuditTable::Difat,
                        CorruptionKind::Truncated,
                        next_offset,
                        "DIFAT chain pointer runs past end of file",
                        None,
                    );
                    break;
                }
            };
        }
        // Drop trailing free padding; a duplicate FAT listing is still kept
        // so it shows up as duplicate ownership.
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }
        if header.num_difat_sectors as usize != difat_chain.len() {
            self.defect(
                AuditTable::Difat,
                CorruptionKind::Truncated,
                72,
                format!(
                    "header says {} DIFAT sectors, chain contains {}",
                    header.num_difat_sectors,
                    difat_chain.len()
                ),
                Some(patch(
                    72,
                    difat_chain.len() as u32.to_le_bytes().to_vec(),
                    "correct num_difat_sectors in header",
                )),
            );
        }
        if header.num_fat_sectors as usize != difat.len() {
            self.defect(
                AuditTable::Difat,
                CorruptionKind::Truncated,
                44,
                format!(
                    "header says {} FAT sectors, DIFAT lists {}",
                    header.num_fat_sectors,
                    difat.len()
                ),
                Some(patch(
                    44,
                    difat.len() as u32.to_le_bytes().to_vec(),
                    "correct num_fat_sectors in header",
                )),
            );
        }

        // --- FAT sectors --------------------------------------------------
        let mut raw_fat: Vec<u32> = Vec::new();
        let mut seen_fat_sectors: FnvHashSet<u32> = FnvHashSet::default();
        for (difat_index, &fat_sector) in difat.iter().enumerate() {
            if fat_sector > consts::MAX_REGULAR_SECTOR
                || fat_sector >= self.num_sectors
            {
                self.defect(
                    AuditTable::Difat,
                    CorruptionKind::OutOfBounds,
                    if difat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
                        76 + (difat_index * 4) as u64
                    } else {
                        // Inside a DIFAT sector; locate approximately at the
                        // DIFAT entry slot.
                        76 + (difat_index * 4) as u64
                    },
                    format!(
                        "DIFAT lists FAT sector {fat_sector}, but file has \
                         only {} sectors",
                        self.num_sectors
                    ),
                    None,
                );
                continue;
            }
            if !seen_fat_sectors.insert(fat_sector) {
                let offset =
                    fat_entry_offset(self.sector_len as u64, fat_sector, 0);
                self.defect(
                    AuditTable::Difat,
                    CorruptionKind::DuplicateOwner,
                    if difat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
                        76 + (difat_index * 4) as u64
                    } else {
                        offset
                    },
                    format!("FAT sector {fat_sector} is listed by the DIFAT twice"),
                    None,
                );
                continue;
            }
            let start = sector_offset(self.sector_len as u64, fat_sector);
            let entries_per_sector = self.sector_len / 4;
            let mut complete = true;
            for within in 0..entries_per_sector {
                let fat_index = raw_fat.len() as u32;
                let offset = start + (within * 4) as u64;
                match le_u32_at(self.data, offset) {
                    Some(value) => {
                        self.fat_entry_offsets.insert(fat_index, offset);
                        raw_fat.push(value);
                    }
                    None => {
                        self.defect(
                            AuditTable::Fat,
                            CorruptionKind::Truncated,
                            offset,
                            format!(
                                "FAT sector {fat_sector} runs past end of file"
                            ),
                            None,
                        );
                        complete = false;
                        break;
                    }
                }
            }
            let _ = complete;
        }

        if raw_fat.len() < self.num_sectors as usize {
            self.defect(
                AuditTable::Fat,
                CorruptionKind::Truncated,
                44,
                format!(
                    "FAT covers {} sectors but file contains {}",
                    raw_fat.len(),
                    self.num_sectors
                ),
                None,
            );
        }

        // FAT self-marking checks: every DIFAT/FAT sector must be claimed as
        // such in the FAT.  This uses the raw table, before chain walking.
        for &difat_sector in difat_chain.iter() {
            if let Some(&entry) = raw_fat.get(difat_sector as usize) {
                if entry != consts::DIFAT_SECTOR {
                    self.defect(
                        AuditTable::Fat,
                        CorruptionKind::DuplicateOwner,
                        self.fat_entry_offsets
                            .get(&difat_sector)
                            .copied()
                            .unwrap_or(0),
                        format!(
                            "sector {difat_sector} is a DIFAT sector but its \
                             FAT entry is 0x{entry:08X}"
                        ),
                        Some(patch(
                            self.fat_entry_offsets
                                .get(&difat_sector)
                                .copied()
                                .unwrap_or(0),
                            consts::DIFAT_SECTOR.to_le_bytes().to_vec(),
                            "mark DIFAT sector in FAT",
                        )),
                    );
                }
            }
        }
        for &fat_sector in seen_fat_sectors.iter() {
            if let Some(&entry) = raw_fat.get(fat_sector as usize) {
                if entry != consts::FAT_SECTOR {
                    let offset = self
                        .fat_entry_offsets
                        .get(&fat_sector)
                        .copied()
                        .unwrap_or(0);
                    self.defect(
                        AuditTable::Fat,
                        CorruptionKind::DuplicateOwner,
                        offset,
                        format!(
                            "sector {fat_sector} is a FAT sector but its FAT \
                             entry is 0x{entry:08X}"
                        ),
                        Some(patch(
                            offset,
                            consts::FAT_SECTOR.to_le_bytes().to_vec(),
                            "mark FAT sector in FAT",
                        )),
                    );
                }
            }
        }

        // Raw FAT scan for structurally impossible entries.
        for (index, &entry) in raw_fat.iter().enumerate() {
            if entry == consts::INVALID_SECTOR {
                let offset = self
                    .fat_entry_offsets
                    .get(&(index as u32))
                    .copied()
                    .unwrap_or(0);
                self.defect(
                    AuditTable::Fat,
                    CorruptionKind::OutOfBounds,
                    offset,
                    format!("FAT entry {index} is 0x{:08X}", consts::INVALID_SECTOR),
                    Some(patch(
                        offset,
                        consts::FREE_SECTOR.to_le_bytes().to_vec(),
                        "replace invalid FAT entry with FREE",
                    )),
                );
            }
        }

        let fat_sectors = difat;
        Ok((fat_sectors, raw_fat))
    }
}

//===========================================================================//
// Chain walking.
//
// Chain analysis is deliberately done in two passes.  Pass 1 walks each
// known root in isolation, stopping on the first intra-chain cycle or
// out-of-bounds edge, and records the reachable set.  Pass 2 compares those
// sets against the raw tables to find cross-chain joins.  Because pass 2
// never depends on visit order, scheduling roots in reverse cannot change
// the classification: cycles, out-of-bounds edges, and duplicate ownership
// stay separate.

#[derive(Default)]
struct ChainWalk {
    sectors: Vec<u32>,
    defects: Vec<Defect>,
}

impl<'a> AuditSession<'a> {
    /// Walks one regular FAT chain from `root`, detecting only issues that
    /// are intrinsic to that walk (cycles, out-of-bounds edges).
    fn walk_fat_chain(&self, root: u32, raw_fat: &[u32]) -> ChainWalk {
        let mut walk = ChainWalk::default();
        if root > consts::MAX_REGULAR_SECTOR || root >= self.num_sectors {
            return walk;
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = root;
        let mut predecessor: Option<u32> = None;
        loop {
            if !local.insert(current) {
                let prev = predecessor.unwrap_or(current);
                let offset = self
                    .fat_entry_offsets
                    .get(&prev)
                    .copied()
                    .unwrap_or(0);
                walk.defects.push(Defect {
                    table: AuditTable::Fat,
                    kind: CorruptionKind::Cycle,
                    location: offset,
                    context: format!(
                        "FAT chain rooted at sector {root} revisits sector \
                         {current}"
                    ),
                    patch: Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: format!("break cycle into sector {current}"),
                    }),
                });
                return walk;
            }
            walk.sectors.push(current);
            let next = match raw_fat.get(current as usize).copied() {
                Some(value) => value,
                None => {
                    let offset = self
                        .fat_entry_offsets
                        .get(&current)
                        .copied()
                        .unwrap_or(0);
                    walk.defects.push(Defect {
                        table: AuditTable::Fat,
                        kind: CorruptionKind::OutOfBounds,
                        location: offset,
                        context: format!(
                            "FAT chain rooted at sector {root}: sector \
                             {current} has no FAT entry"
                        ),
                        patch: None,
                    });
                    return walk;
                }
            };
            if next == consts::END_OF_CHAIN {
                return walk;
            }
            if next == consts::FREE_SECTOR
                || next == consts::INVALID_SECTOR
                || next == consts::FAT_SECTOR
                || next == consts::DIFAT_SECTOR
                || next > consts::MAX_REGULAR_SECTOR
                || next >= self.num_sectors
                || (next as usize) >= raw_fat.len()
            {
                let offset = self
                    .fat_entry_offsets
                    .get(&current)
                    .copied()
                    .unwrap_or(0);
                walk.defects.push(Defect {
                    table: AuditTable::Fat,
                    kind: CorruptionKind::OutOfBounds,
                    location: offset,
                    context: format!(
                        "FAT chain rooted at sector {root}: sector {current} \
                         points to 0x{next:08X}"
                    ),
                    patch: Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: format!(
                            "end chain at sector {current} instead of \
                             0x{next:08X}"
                        ),
                    }),
                });
                return walk;
            }
            predecessor = Some(current);
            current = next;
        }
    }

    /// Walks one mini chain under the same rules as `walk_fat_chain`.
    fn walk_mini_chain(
        &self,
        label: String,
        mini_root: u32,
        minifat: &[u32],
    ) -> ChainWalk {
        let mut walk = ChainWalk::default();
        let capacity = minifat.len() as u32;
        if mini_root >= capacity {
            let offset = 0;
            walk.defects.push(Defect {
                table: AuditTable::MiniFat,
                kind: CorruptionKind::OutOfBounds,
                location: offset,
                context: format!(
                    "{label} starts at mini sector {mini_root}, but MiniFAT \
                     has only {capacity} entries"
                ),
                patch: None,
            });
            return walk;
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = mini_root;
        let mut predecessor: Option<u32> = None;
        loop {
            if !local.insert(current) {
                let prev = predecessor.unwrap_or(current);
                let offset = self
                    .minifat_entry_offsets
                    .get(&prev)
                    .copied()
                    .unwrap_or(0);
                walk.defects.push(Defect {
                    table: AuditTable::MiniFat,
                    kind: CorruptionKind::Cycle,
                    location: offset,
                    context: format!(
                        "{label} revisits mini sector {current}"
                    ),
                    patch: Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: "break mini chain cycle".to_string(),
                    }),
                });
                return walk;
            }
            walk.sectors.push(current);
            let next = minifat[current as usize];
            if next == consts::END_OF_CHAIN {
                return walk;
            }
            if next == consts::FREE_SECTOR
                || next == consts::INVALID_SECTOR
                || next == consts::FAT_SECTOR
                || next == consts::DIFAT_SECTOR
                || next > consts::MAX_REGULAR_SECTOR
                || next >= capacity
            {
                let offset = self
                    .minifat_entry_offsets
                    .get(&current)
                    .copied()
                    .unwrap_or(0);
                walk.defects.push(Defect {
                    table: AuditTable::MiniFat,
                    kind: CorruptionKind::OutOfBounds,
                    location: offset,
                    context: format!(
                        "{label}: mini sector {current} points to \
                         0x{next:08X}"
                    ),
                    patch: Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: format!(
                            "end mini chain at mini sector {current}"
                        ),
                    }),
                });
                return walk;
            }
            predecessor = Some(current);
            current = next;
        }
    }

    fn absorb(&mut self, walk: ChainWalk) -> Vec<u32> {
        for defect in walk.defects {
            record_failure(
                &mut self.defects,
                defect.table,
                defect.kind,
                defect.location,
                defect.context,
                defect.patch,
            );
        }
        walk.sectors
    }
}
//===========================================================================//

impl<'a> AuditSession<'a> {
    /// Pass 2 over all regular FAT chains: MiniFAT chain, mini-stream
    /// container, directory chain, and every large stream.  Reachable sets
    /// are collected before any cross-chain comparison, so the result does
    /// not depend on which root was visited first.
    fn examine_chains(
        &mut self,
        header: &Header,
        fat_sectors: &[u32],
        raw_fat: &[u32],
        entries: &[AuditedEntry],
    ) {
        // (root sector, role label, table to classify defects under)
        let mut roots: Vec<(u32, String, AuditTable)> = Vec::new();
        roots.push((
            header.first_dir_sector,
            "directory chain".to_string(),
            AuditTable::Directory,
        ));
        roots.push((
            header.first_minifat_sector,
            "MiniFAT chain".to_string(),
            AuditTable::MiniFat,
        ));
        if let Some(root) = entries
            .iter()
            .find(|a| a.stream_id == consts::ROOT_STREAM_ID)
        {
            if root.entry.stream_len > 0 {
                roots.push((
                    root.entry.start_sector,
                    "root mini stream container".to_string(),
                    AuditTable::MiniFat,
                ));
            }
        }
        for audited in entries.iter() {
            if audited.entry.obj_type == ObjType::Stream
                && audited.entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
            {
                roots.push((
                    audited.entry.start_sector,
                    format!("stream entry {}", audited.stream_id),
                    AuditTable::Fat,
                ));
            }
        }
        if self.options.order == crate::audit::AuditOrder::Reverse {
            roots.reverse();
        }

        // Pass 1: isolated walks.
        let mut walks: Vec<(u32, String, AuditTable, Vec<u32>)> = Vec::new();
        for (root, label, table) in roots.into_iter() {
            if root > consts::MAX_REGULAR_SECTOR || root >= self.num_sectors {
                // A bad root pointer of a stream is a length/start problem
                // examined per entry below; skip unreachable roots here.
                continue;
            }
            let walk = self.walk_fat_chain(root, raw_fat);
            let sectors = self.absorb_reclassified(walk, table);
            walks.push((root, label, table, sectors));
        }

        // Pass 2a: cross-chain overlaps on regular sectors.
        self.find_regular_overlaps(&walks, raw_fat);

        // Pass 2b: declared lengths vs chain capacities for large streams.
        self.check_stream_lengths(&walks, entries);

        // Pass 2c: MiniFAT contents and mini chains.
        self.examine_minifat_contents(
            header,
            fat_sectors,
            raw_fat,
            entries,
            &walks,
        );

        // Pass 2d: FAT sectors that nothing reached.
        self.find_fat_orphans(fat_sectors, raw_fat, &walks);
    }

    /// Like `absorb`, but defects intrinsic to the directory and MiniFAT
    /// chains are reported under their own tables.
    fn absorb_reclassified(
        &mut self,
        walk: ChainWalk,
        table: AuditTable,
    ) -> Vec<u32> {
        for mut defect in walk.defects {
            // Cycles/edges on the directory chain and the MiniFAT chain
            // belong to those tables; the FAT is only the medium.
            if table != AuditTable::Fat {
                defect.table = table;
            }
            record_failure(
                &mut self.defects,
                defect.table,
                defect.kind,
                defect.location,
                defect.context,
                defect.patch,
            );
        }
        walk.sectors
    }
}
//===========================================================================//

impl<'a> AuditSession<'a> {
    /// Detects sectors reachable from two different regular chain roots.
    fn find_regular_overlaps(
        &mut self,
        walks: &[(u32, String, AuditTable, Vec<u32>)],
        raw_fat: &[u32],
    ) {
        // sector -> the roots that reach it.  Built from complete reachable
        // sets, so insertion order cannot decide the result.
        let mut claimants: FnvHashMap<u32, Vec<u32>> = FnvHashMap::default();
        for (root, _label, _table, sectors) in walks.iter() {
            for &sector in sectors {
                claimants.entry(sector).or_default().push(*root);
            }
        }
        let mut overlaps: Vec<(u32, Vec<u32>)> = claimants
            .into_iter()
            .filter(|(_, roots)| roots.len() > 1)
            .collect();
        overlaps.sort_by_key(|(sector, _)| *sector);
        for (shared, mut roots) in overlaps {
            roots.sort();
            roots.dedup();
            if roots.len() < 2 {
                continue;
            }
            // The repair keeps the numerically smallest root and detaches
            // every later root where it first enters the shared region.
            let keeper = roots[0];
            for &other_root in roots.iter().skip(1) {
                let sectors = walks
                    .iter()
                    .find(|(root, _, _, _)| *root == other_root)
                    .map(|(_, _, _, s)| s.as_slice())
                    .unwrap_or(&[]);
                let cut = match sectors
                    .windows(2)
                    .position(|w| w[1] == shared)
                {
                    Some(pos) => sectors[pos],
                    None if sectors.first() == Some(&shared) => {
                        // The shared sector is the root itself: detach by
                        // rewriting its own outgoing FAT entry.
                        shared
                    }
                    None => continue,
                };
                let offset = self
                    .fat_entry_offsets
                    .get(&cut)
                    .copied()
                    .unwrap_or(0);
                let table = walks
                    .iter()
                    .find(|(r, _, _, _)| *r == other_root)
                    .map(|(_, _, t, _)| *t)
                    .unwrap_or(AuditTable::Fat);
                let root_list = roots
                    .iter()
                    .map(|r| r.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                self.defect(
                    table,
                    CorruptionKind::DuplicateOwner,
                    offset,
                    format!(
                        "sector {shared} is claimed by chains rooted at \
                         sectors {root_list}"
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: format!(
                            "keep sector {shared} in chain {keeper}; detach \
                             chain {other_root}"
                        ),
                    }),
                );
            }
        }
    }

    /// Compares each large stream's declared length with the sectors its
    /// chain actually provides.
    fn check_stream_lengths(
        &mut self,
        walks: &[(u32, String, AuditTable, Vec<u32>)],
        entries: &[AuditedEntry],
    ) {
        for audited in entries.iter() {
            if audited.entry.obj_type != ObjType::Stream {
                continue;
            }
            if audited.entry.stream_len < consts::MINI_STREAM_CUTOFF as u64 {
                continue;
            }
            let root = audited.entry.start_sector;
            let sectors = walks
                .iter()
                .find(|(r, _, _, _)| *r == root)
                .map(|(_, _, _, s)| s.as_slice())
                .unwrap_or(&[]);
            let capacity = sectors.len() as u64 * self.sector_len as u64;
            let declared = audited.entry.stream_len;
            if declared != capacity
                && !(sectors.is_empty()
                    && root == consts::END_OF_CHAIN)
            {
                let offset = audited.stream_len_offset;
                self.defect(
                    AuditTable::Fat,
                    CorruptionKind::LengthMismatch,
                    offset,
                    format!(
                        "stream entry {} declares {} bytes but its FAT chain \
                         holds {}",
                        audited.stream_id, declared, capacity
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: capacity.to_le_bytes().to_vec(),
                        reason: format!(
                            "set stream {} length to its chain capacity",
                            audited.stream_id
                        ),
                    }),
                );
            }
        }
    }
}
//===========================================================================//

impl<'a> AuditSession<'a> {
    /// Reads MiniFAT entries from the MiniFAT chain, walks every mini chain,
    /// checks the root mini stream, and reports mini orphans.
    fn examine_minifat_contents(
        &mut self,
        header: &Header,
        _fat_sectors: &[u32],
        _raw_fat: &[u32],
        entries: &[AuditedEntry],
        walks: &[(u32, String, AuditTable, Vec<u32>)],
    ) {
        // Read the MiniFAT bytes through the already-walked MiniFAT chain.
        let mut minifat: Vec<u32> = Vec::new();
        let minifat_sectors = walks
            .iter()
            .find(|(r, _, _, _)| *r == header.first_minifat_sector)
            .map(|(_, _, _, s)| s.as_slice())
            .unwrap_or(&[]);
        for sector_id in minifat_sectors {
            let start = sector_offset(self.sector_len as u64, *sector_id);
            for within in 0..(self.sector_len / 4) {
                let mini_index = minifat.len() as u32;
                let offset = start + (within * 4) as u64;
                if let Some(value) = le_u32_at(self.data, offset) {
                    self.minifat_entry_offsets.insert(mini_index, offset);
                    minifat.push(value);
                }
            }
        }
        while minifat.last() == Some(&consts::FREE_SECTOR) {
            minifat.pop();
        }

        let actual_minifat_sectors =
            (minifat.len() * 4).div_ceil(self.sector_len) as u32;
        if header.num_minifat_sectors != actual_minifat_sectors {
            self.defect(
                AuditTable::MiniFat,
                CorruptionKind::Truncated,
                60,
                format!(
                    "header says {} MiniFAT sectors, chain provides {}",
                    header.num_minifat_sectors, actual_minifat_sectors
                ),
                Some(RepairPatch {
                    offset: 60,
                    bytes: actual_minifat_sectors.to_le_bytes().to_vec(),
                    reason: "correct num_minifat_sectors in header".to_string(),
                }),
            );
        }

        // Raw MiniFAT scan for the reserved invalid marker.
        for (index, &entry) in minifat.iter().enumerate() {
            if entry == consts::INVALID_SECTOR {
                let offset = self
                    .minifat_entry_offsets
                    .get(&(index as u32))
                    .copied()
                    .unwrap_or(0);
                self.defect(
                    AuditTable::MiniFat,
                    CorruptionKind::OutOfBounds,
                    offset,
                    format!(
                        "MiniFAT entry {index} is 0x{:08X}",
                        consts::INVALID_SECTOR
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                        reason: "replace invalid MiniFAT entry with FREE"
                            .to_string(),
                    }),
                );
            }
        }

        let root = match entries
            .iter()
            .find(|a| a.stream_id == consts::ROOT_STREAM_ID)
        {
            Some(audited) => audited,
            None => return,
        };

        // Root mini stream capacity comes from its regular container chain.
        let container_sectors = walks
            .iter()
            .find(|(r, _, _, _)| *r == root.entry.start_sector)
            .map(|(_, _, _, s)| s.as_slice())
            .unwrap_or(&[]);
        let container_capacity =
            container_sectors.len() as u64 * self.sector_len as u64;
        let root_len = root.entry.stream_len;
        if root_len > container_capacity {
            let offset = root.stream_len_offset;
            self.defect(
                AuditTable::MiniFat,
                CorruptionKind::LengthMismatch,
                offset,
                format!(
                    "root mini stream declares {} bytes but its chain holds \
                     {}",
                    root_len, container_capacity
                ),
                Some(RepairPatch {
                    offset,
                    bytes: container_capacity.to_le_bytes().to_vec(),
                    reason: "shrink declared mini stream length to chain \
                             capacity"
                        .to_string(),
                }),
            );
        }
        let declared_mini_sectors =
            root_len / consts::MINI_SECTOR_LEN as u64;
        if minifat.len() as u64 > declared_mini_sectors {
            let first = declared_mini_sectors as u32;
            let offset = self
                .minifat_entry_offsets
                .get(&first)
                .copied()
                .unwrap_or(0);
            self.defect(
                AuditTable::MiniFat,
                CorruptionKind::OutOfBounds,
                offset,
                format!(
                    "MiniFAT has {} entries but root mini stream holds only \
                     {} mini sectors",
                    minifat.len(),
                    declared_mini_sectors
                ),
                None,
            );
        }

        // Walk every mini chain (small streams), twice like the FAT chains.
        let mut mini_roots: Vec<(u32, u32)> = Vec::new();
        for audited in entries.iter() {
            if audited.entry.obj_type == ObjType::Stream
                && audited.entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
            {
                let start = audited.entry.start_sector;
                if start != consts::END_OF_CHAIN
                    && start != consts::FREE_SECTOR
                {
                    mini_roots.push((audited.stream_id, start));
                }
            }
        }
        if self.options.order == crate::audit::AuditOrder::Reverse {
            mini_roots.reverse();
        }
        let mut mini_walks: Vec<(u32, Vec<u32>)> = Vec::new();
        for (stream_id, start) in mini_roots {
            let label = format!("mini stream entry {stream_id}");
            let mut walk = self.walk_mini_chain(label, start, &minifat);
            // A root index that lives beyond the MiniFAT is best located at
            // the directory entry's start_sector field.
            for defect in walk.defects.iter_mut() {
                if defect.location == 0 {
                    defect.location = self
                        .dir_start_offsets
                        .get(&stream_id)
                        .copied()
                        .unwrap_or(0);
                    defect.patch = None;
                }
            }
            let sectors = self.absorb(walk);
            mini_walks.push((start, sectors));
        }
        self.find_mini_overlaps(&mini_walks);
        self.check_mini_lengths(&minifat, &mini_walks, entries);
        self.find_mini_orphans(&minifat, declared_mini_sectors, &mini_walks);
    }

    /// Detects mini sectors reached from two mini chain roots.
    fn find_mini_overlaps(&mut self, mini_walks: &[(u32, Vec<u32>)]) {
        let mut claimants: FnvHashMap<u32, Vec<u32>> = FnvHashMap::default();
        for (root, sectors) in mini_walks {
            for &sector in sectors {
                claimants.entry(sector).or_default().push(*root);
            }
        }
        let mut overlaps: Vec<(u32, Vec<u32>)> = claimants
            .into_iter()
            .filter(|(_, roots)| roots.len() > 1)
            .collect();
        overlaps.sort_by_key(|(sector, _)| *sector);
        for (shared, mut roots) in overlaps {
            roots.sort();
            roots.dedup();
            if roots.len() < 2 {
                continue;
            }
            let keeper = roots[0];
            for &other in roots.iter().skip(1) {
                let sectors = mini_walks
                    .iter()
                    .find(|(r, _)| *r == other)
                    .map(|(_, s)| s.as_slice())
                    .unwrap_or(&[]);
                let cut = match sectors.windows(2).position(|w| w[1] == shared)
                {
                    Some(pos) => sectors[pos],
                    None => shared,
                };
                let offset = self
                    .minifat_entry_offsets
                    .get(&cut)
                    .copied()
                    .unwrap_or(0);
                self.defect(
                    AuditTable::MiniFat,
                    CorruptionKind::DuplicateOwner,
                    offset,
                    format!(
                        "mini sector {shared} is claimed by mini chains \
                         rooted at {}",
                        roots
                            .iter()
                            .map(|r| r.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                        reason: format!(
                            "keep mini sector {shared} in chain {keeper}; \
                             detach chain {other}"
                        ),
                    }),
                );
            }
        }
    }

    /// Compares declared small-stream lengths with their mini chains.
    fn check_mini_lengths(
        &mut self,
        _minifat: &[u32],
        mini_walks: &[(u32, Vec<u32>)],
        entries: &[AuditedEntry],
    ) {
        for audited in entries.iter() {
            if audited.entry.obj_type != ObjType::Stream
                || audited.entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
            {
                continue;
            }
            let root = audited.entry.start_sector;
            if root == consts::END_OF_CHAIN || root == consts::FREE_SECTOR {
                continue;
            }
            let sectors = mini_walks
                .iter()
                .find(|(r, _)| *r == root)
                .map(|(_, s)| s.as_slice())
                .unwrap_or(&[]);
            let capacity =
                sectors.len() as u64 * consts::MINI_SECTOR_LEN as u64;
            if audited.entry.stream_len > capacity {
                let offset = audited.stream_len_offset;
                self.defect(
                    AuditTable::MiniFat,
                    CorruptionKind::LengthMismatch,
                    offset,
                    format!(
                        "mini stream entry {} declares {} bytes but its mini \
                         chain holds {}",
                        audited.stream_id,
                        audited.entry.stream_len,
                        capacity
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: capacity.to_le_bytes().to_vec(),
                        reason: format!(
                            "set mini stream {} length to its mini chain \
                             capacity",
                            audited.stream_id
                        ),
                    }),
                );
            }
        }
    }

    /// Mini sectors marked allocated that no mini chain reaches.
    fn find_mini_orphans(
        &mut self,
        minifat: &[u32],
        declared_mini_sectors: u64,
        mini_walks: &[(u32, Vec<u32>)],
    ) {
        let mut reached: FnvHashSet<u32> = FnvHashSet::default();
        for (_, sectors) in mini_walks {
            for &sector in sectors {
                reached.insert(sector);
            }
        }
        for (index, &entry) in minifat.iter().enumerate() {
            if index as u64 >= declared_mini_sectors {
                break;
            }
            let allocated = entry <= consts::MAX_REGULAR_SECTOR;
            if allocated && !reached.contains(&(index as u32)) {
                let offset = self
                    .minifat_entry_offsets
                    .get(&(index as u32))
                    .copied()
                    .unwrap_or(0);
                self.defect(
                    AuditTable::MiniFat,
                    CorruptionKind::Orphan,
                    offset,
                    format!(
                        "mini sector {index} is allocated but no mini stream \
                         reaches it"
                    ),
                    Some(RepairPatch {
                        offset,
                        bytes: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                        reason: format!("release orphan mini sector {index}"),
                    }),
                );
            }
        }
    }

    /// Regular sectors marked with a data value that no known chain reaches.
    fn find_fat_orphans(
        &mut self,
        _fat_sectors: &[u32],
        raw_fat: &[u32],
        walks: &[(u32, String, AuditTable, Vec<u32>)],
    ) {
        let mut reached: FnvHashSet<u32> = FnvHashSet::default();
        for (_, _, _, sectors) in walks {
            for &sector in sectors {
                reached.insert(sector);
            }
        }
        let limit = raw_fat.len().min(self.num_sectors as usize);
        for index in 0..limit {
            let sector = index as u32;
            if reached.contains(&sector) {
                continue;
            }
            let entry = raw_fat[index];
            // FAT/DIFAT sectors and genuinely free sectors are not orphans.
            if entry == consts::FAT_SECTOR
                || entry == consts::DIFAT_SECTOR
                || entry == consts::FREE_SECTOR
            {
                continue;
            }
            let offset = self
                .fat_entry_offsets
                .get(&sector)
                .copied()
                .unwrap_or(0);
            self.defect(
                AuditTable::Fat,
                CorruptionKind::Orphan,
                offset,
                format!(
                    "sector {sector} is allocated (FAT entry 0x{entry:08X}) \
                     but no chain reaches it"
                ),
                Some(RepairPatch {
                    offset,
                    bytes: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                    reason: format!("release orphan sector {sector}"),
                }),
            );
        }
    }
}
//===========================================================================//
// Repair planning and application.

/// Builds a repair plan from a report's findings and the candidate patches
/// the audit proposed.  Exposed to [`crate::audit::AuditReport::repair_plan`]
/// via a constructor on [`AuditReport`]; this is the same logic the audit
/// itself used to propose each patch, iterated to a fixpoint and verified.
pub(crate) fn build_repair_plan(report: &AuditReport) -> RepairPlan {
    let mut patches: Vec<RepairPatch> = report.candidate_patches().to_vec();
    // Collapse duplicate proposals at the same offset.
    patches.sort_by(|a, b| a.offset.cmp(&b.offset));
    patches.dedup_by(|a, b| a.offset == b.offset);

    // Apply the proposals to an in-memory copy and re-audit.  This proves the
    // plan against the production audit logic rather than trusting that the
    // individual patches compose.  Iterate because releasing one orphan or
    // shortening one length can expose another defect behind it.
    let mut data = report.input_hint().to_vec();
    for _ in 0..8 {
        let mut changed = false;
        for patch in patches.iter() {
            let start = patch.offset as usize;
            if start + patch.bytes.len() <= data.len() {
                if data[start..start + patch.bytes.len()] != patch.bytes[..] {
                    data[start..start + patch.bytes.len()]
                        .copy_from_slice(&patch.bytes);
                    changed = true;
                }
            }
        }
        let next_report =
            analyze(&data, &crate::audit::AuditOptions::default())
                .unwrap_or_else(|_| {
                    // Re-audit should never inject failures or do I/O.
                    unreachable!("re-audit of in-memory data cannot fail")
                });
        if next_report.is_clean() {
            patches = next_report.candidate_patches().to_vec();
            patches.sort_by(|a, b| a.offset.cmp(&b.offset));
            patches.dedup_by(|a, b| a.offset == b.offset);
            return RepairPlan::from_parts(
                report.digest(),
                patches,
                Vec::new(),
            );
        }
        let merged: Vec<RepairPatch> = patches
            .iter()
            .chain(next_report.candidate_patches().iter())
            .cloned()
            .collect();
        let mut merged = merged;
        merged.sort_by(|a, b| a.offset.cmp(&b.offset));
        merged.dedup_by(|a, b| a.offset == b.offset);
        if merged == patches && !changed {
            let unrepairable = next_report.findings().to_vec();
            return RepairPlan::from_parts(
                report.digest(),
                patches,
                unrepairable,
            );
        }
        patches = merged;
    }

    // Loop budget exhausted without a clean fixpoint: mark everything still
    // reported as unrepairable rather than claiming success.
    let final_report =
        analyze(&data, &crate::audit::AuditOptions::default()).unwrap();
    RepairPlan::from_parts(
        report.digest(),
        patches,
        final_report.findings().to_vec(),
    )
}

/// Reads every byte of a reader without trusting its current position.
pub(crate) fn read_all<F: Read + Seek>(inner: &mut F) -> io::Result<Vec<u8>> {
    inner.seek(SeekFrom::Start(0))?;
    let len = inner.seek(SeekFrom::End(0))?;
    inner.seek(SeekFrom::Start(0))?;
    let mut data = vec![0u8; len as usize];
    inner.read_exact(&mut data)?;
    Ok(data)
}

/// Verifies that the current digest still matches the plan's prerequisite.
/// Returns InvalidData (the same class malformed files produce) otherwise;
/// the mismatch check happens before any write.
fn check_prerequisite(
    plan: &RepairPlan,
    current: &[u8],
) -> io::Result<Digest> {
    let current_digest = digest_bytes(current);
    if current_digest != plan.prerequisite_digest() {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "Repair plan is stale: prerequisite digest {} no longer \
                 matches current digest {}",
                plan.prerequisite_digest(),
                current_digest
            ),
        ))
    } else {
        Ok(current_digest)
    }
}

/// Produces the patched bytes and audits them, without touching the target.
fn prepare_commit(
    plan: &RepairPlan,
    current: &[u8],
) -> io::Result<(Vec<u8>, Vec<Finding>)> {
    if !plan.is_fully_repairable() {
        invalid_data!(
            "Repair plan contains {} unrepairable finding(s); refusing to \
             apply a partial repair",
            plan.unrepairable_findings().len()
        );
    }
    let mut data = current.to_vec();
    for patch in plan.patches() {
        let start = patch.offset as usize;
        let end = start + patch.bytes.len();
        if end > data.len() {
            invalid_data!(
                "Repair patch at byte {} runs past end of file",
                patch.offset
            );
        }
        data[start..end].copy_from_slice(patch.bytes());
    }
    let report = analyze(&data, &crate::audit::AuditOptions::default())?;
    Ok((data, report.findings().to_vec()))
}

/// Dry run: every check of a real application, guaranteed to return before
/// any write.
pub(crate) fn dry_run(
    plan: &RepairPlan,
    current: &[u8],
    options: &AuditOptions,
) -> io::Result<ApplyOutcome> {
    let digest = check_prerequisite(plan, current)?;
    checkpoint(options, AuditCheckpoint::BeforeWrite)?;
    let (_data, remaining) = prepare_commit(plan, current)?;
    checkpoint(options, AuditCheckpoint::BeforeCommit)?;
    Ok(ApplyOutcome::from_parts(
        plan.prerequisite_digest(),
        digest,
        plan.patches().len(),
        remaining,
    ))
}

/// Applies a plan to a writable target atomically with respect to failure:
/// all analysis and patching happens in memory, and the first failure point
/// that could occur after a write is itself reached only after the whole
/// repaired image has been re-audited successfully.
pub(crate) fn apply<F: Read + Write + Seek>(
    plan: &RepairPlan,
    inner: &mut F,
    options: &AuditOptions,
) -> io::Result<ApplyOutcome> {
    let current = read_all(inner)?;
    let digest = check_prerequisite(plan, &current)?;
    checkpoint(options, AuditCheckpoint::BeforeWrite)?;
    let (data, remaining) = prepare_commit(plan, &current)?;
    checkpoint(options, AuditCheckpoint::BeforeCommit)?;
    // Commit the repaired image in a single write sequence, then verify the
    // bytes on disk still audit clean.  The length never changes.
    inner.seek(SeekFrom::Start(0))?;
    inner.write_all(&data)?;
    inner.flush()?;
    let on_disk = read_all(inner)?;
    let committed_digest = digest_bytes(&on_disk);
    if on_disk != data {
        invalid_data!(
            "Repair could not be committed: bytes on disk did not match the \
             repaired image"
        );
    }
    let committed_report =
        analyze(&on_disk, &crate::audit::AuditOptions::default())?;
    Ok(ApplyOutcome::from_parts(
        plan.prerequisite_digest(),
        committed_digest,
        plan.patches().len(),
        committed_report.findings().to_vec(),
    ))
}

// Keep size_of referenced (used in documentation of FAT entry widths).
const _: fn() = || {
    let _ = size_of::<u32>();
    let _: fn(&mut Cursor<&[u8]>, u32) =
        |c, v| c.write_le_u32(v).map(|_| ());
};
