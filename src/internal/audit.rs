//! Read-only structural analyzer backing the public `crate::audit` API.
//!
//! It parses a CFB image straight from bytes (reusing the production
//! [`Header::read_from`] parser and the shared `consts`/`Version` format
//! knowledge), without constructing or mutating any of the mutable objects
//! (`Allocator`, `Directory`, ...) used by the read/write path.  That keeps
//! the audit honest about what is actually on disk: the permissive open path
//! silently rewrites several of these malformations in memory, which would
//! hide the evidence this module exists to report.
//!
//! The analyzer is a pure function of its input bytes: every scratch
//! structure is created locally, so two calls can never share caches,
//! counters, or other state.

use std::io::{self, Cursor};

use crate::audit::{
    digest_bytes, AuditReport, ChainOwner, Corruption, DirectoryField,
    Finding, HeaderField, Patch, Table,
};
use crate::internal::consts;
use crate::internal::{Header, Validation, Version};

const MAX_FIXPOINT_ROUNDS: usize = 16;

//===========================================================================//

#[derive(Clone)]
struct RawEntry {
    stream_id: u32,
    obj_type: u8,
    left_sibling: u32,
    right_sibling: u32,
    child: u32,
    start_sector: u32,
    stream_len: u64,
}

/// Everything the analyzer derives from one image.
struct Model<'a> {
    data: &'a [u8],
    version: Version,
    sector_len: usize,
    num_sectors: u32,
    file_len: u64,
    header: Header,
    fat_cell_offset: Vec<Option<u64>>,
    fat: Vec<u32>,
    difat_chain: Vec<DifatLink>,
    minifat_cell_offset: Vec<Option<u64>>,
    minifat: Vec<u32>,
    dir_sectors: Vec<u32>,
    entries: Vec<RawEntry>,
}

#[derive(Clone)]
struct DifatLink {
    sector_id: u32,
    next_pointer_offset: u64,
    fat_pointers: Vec<(usize, u64)>,
}

/// How a table walk terminated.
enum Stop {
    End,
    StartOutOfBounds,
    OutOfBounds { edge_from: u32, target: u32 },
    Cycle { edge_from: u32, at: u32 },
}

struct Walk {
    cells: Vec<u32>,
    stop: Stop,
}

//===========================================================================//
// Public entry point
//===========================================================================//

pub(crate) fn analyze_image(
    data: &[u8],
) -> io::Result<(AuditReport, Vec<Patch>)> {
    let mut findings: Vec<Finding> = Vec::new();
    let mut patches: Vec<Patch> = Vec::new();
    let mut image = data.to_vec();

    for round in 0..MAX_FIXPOINT_ROUNDS {
        let model = parse_model(&image)?;
        let (round_findings, round_patches) = analyze_model(&model);
        let before = findings.len();
        for finding in round_findings {
            if !findings.contains(&finding) {
                findings.push(finding);
            }
        }
        let mut changed = false;
        for patch in round_patches {
            if !patches.contains(&patch) {
                patches.push(patch.clone());
            }
            let start = patch.offset as usize;
            let end = start + patch.replacement.len();
            if image[start..end] != patch.replacement[..] {
                image[start..end].copy_from_slice(&patch.replacement);
                changed = true;
            }
        }
        sort_findings(&mut findings);
        if !changed && findings.len() == before {
            break;
        }
    }

    let file_len = data.len() as u64;
    let report = AuditReport::from_parts(findings, digest_bytes(data), file_len);
    Ok((report, patches))
}

//===========================================================================//
// Parsing
//===========================================================================//

fn u32_at(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        data[offset],
        data[offset + 1],
        data[offset + 2],
        data[offset + 3],
    ])
}

fn parse_model(data: &[u8]) -> io::Result<Model<'_>> {
    if data.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small to audit)",
            data.len()
        );
    }
    // Reuse the production header parser (permissive) so the audit speaks the
    // same version/shift language as the real open path.
    let header =
        Header::read_from(&mut Cursor::new(data), Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len();
    if (data.len() - consts::HEADER_LEN) < sector_len {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            data.len(),
            sector_len
        );
    }
    let num_sectors = ((data.len() - consts::HEADER_LEN) / sector_len) as u32;
    let sector_offset =
        |sector_id: u32| consts::HEADER_LEN + (sector_id as usize) * sector_len;

    // ---- DIFAT --------------------------------------------------------
    let mut difat_chain = Vec::<DifatLink>::new();
    let mut fat_sector_ids: Vec<u32> = Vec::new();
    for &id in header.initial_difat_entries.iter() {
        if id == consts::FREE_SECTOR {
            break;
        }
        fat_sector_ids.push(id);
    }
    let mut current = header.first_difat_sector;
    let mut seen = vec![false; num_sectors as usize];
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= num_sectors {
            break;
        }
        if seen[current as usize] {
            break;
        }
        seen[current as usize] = true;
        let base = sector_offset(current);
        let pointers_per_sector = sector_len / 4 - 1;
        let mut fat_pointers = Vec::new();
        for index in 0..pointers_per_sector {
            let id = u32_at(data, base + index * 4);
            if id != consts::FREE_SECTOR {
                fat_sector_ids.push(id);
                fat_pointers.push((index, (base + index * 4) as u64));
            }
        }
        let next_pointer_offset = (base + pointers_per_sector * 4) as u64;
        difat_chain.push(DifatLink {
            sector_id: current,
            next_pointer_offset,
            fat_pointers,
        });
        let next = u32_at(data, base + pointers_per_sector * 4);
        if next == consts::END_OF_CHAIN || next == consts::FREE_SECTOR {
            break;
        }
        current = next;
    }

    // ---- FAT ----------------------------------------------------------
    let entries_per_fat_sector = sector_len / 4;
    let mut fat = vec![consts::FREE_SECTOR; num_sectors as usize];
    let mut fat_cell_offset = vec![None; num_sectors as usize];
    for (fat_index, &sector_id) in fat_sector_ids.iter().enumerate() {
        if sector_id >= num_sectors {
            continue;
        }
        let base = sector_offset(sector_id);
        if base + sector_len > data.len() {
            continue;
        }
        for slot in 0..entries_per_fat_sector {
            let cell = fat_index * entries_per_fat_sector + slot;
            if cell >= num_sectors as usize {
                break;
            }
            fat[cell] = u32_at(data, base + slot * 4);
            fat_cell_offset[cell] = Some((base + slot * 4) as u64);
        }
    }

    let mut model = Model {
        data,
        version,
        sector_len,
        num_sectors,
        file_len: data.len() as u64,
        header,
        fat_cell_offset,
        fat,
        difat_chain,
        minifat_cell_offset: Vec::new(),
        minifat: Vec::new(),
        dir_sectors: Vec::new(),
        entries: Vec::new(),
    };

    // ---- Directory chain ---------------------------------------------
    let dir_walk = walk_table(&model, model.header.first_dir_sector, false);
    model.dir_sectors = dir_walk.cells;
    let entries_per_sector = model.version.dir_entries_per_sector();
    for (sector_index, &sector_id) in model.dir_sectors.iter().enumerate() {
        let base = sector_offset(sector_id);
        for slot in 0..entries_per_sector {
            let at = base + slot * consts::DIR_ENTRY_LEN;
            if at + consts::DIR_ENTRY_LEN > data.len() {
                break;
            }
            let stream_id = (sector_index * entries_per_sector + slot) as u32;
            model
                .entries
                .push(parse_entry(data, at, stream_id, version));
        }
    }

    // ---- MiniFAT ------------------------------------------------------
    let minifat_walk =
        walk_table(&model, model.header.first_minifat_sector, false);
    let mut minifat = Vec::new();
    let mut minifat_cell_offset = Vec::new();
    for &sector_id in &minifat_walk.cells {
        let base = sector_offset(sector_id);
        for slot in 0..entries_per_fat_sector {
            let at = base + slot * 4;
            if at + 4 > data.len() {
                break;
            }
            minifat.push(u32_at(data, at));
            minifat_cell_offset.push(Some(at as u64));
        }
    }
    model.minifat = minifat;
    model.minifat_cell_offset = minifat_cell_offset;

    Ok(model)
}

fn parse_entry(
    data: &[u8],
    at: usize,
    stream_id: u32,
    version: Version,
) -> RawEntry {
    RawEntry {
        stream_id,
        obj_type: data[at + 66],
        left_sibling: u32_at(data, at + 68),
        right_sibling: u32_at(data, at + 72),
        child: u32_at(data, at + 76),
        start_sector: u32_at(data, at + 116),
        stream_len: u64::from_le_bytes([
            data[at + 120],
            data[at + 121],
            data[at + 122],
            data[at + 123],
            data[at + 124],
            data[at + 125],
            data[at + 126],
            data[at + 127],
        ]) & version.stream_len_mask(),
    }
}

//===========================================================================//
// Table walking
//===========================================================================//

fn walk_table(model: &Model, start: u32, is_mini: bool) -> Walk {
    let (table, table_len) = if is_mini {
        (&model.minifat[..], model.minifat.len() as u32)
    } else {
        (&model.fat[..], model.num_sectors)
    };
    let mut cells = Vec::new();
    if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
        return Walk { cells, stop: Stop::End };
    }
    if start >= table_len {
        return Walk { cells, stop: Stop::StartOutOfBounds };
    }
    let mut current = start;
    let stop = loop {
        if let Some(at) = cells.iter().position(|&id| id == current) {
            let edge_from = cells[cells.len() - 1];
            break Stop::Cycle { edge_from, at: cells[at] };
        }
        cells.push(current);
        let next = table[current as usize];
        if next == consts::END_OF_CHAIN {
            break Stop::End;
        }
        if next == consts::FREE_SECTOR
            || next > consts::MAX_REGULAR_SECTOR
            || next >= table_len
        {
            break Stop::OutOfBounds { edge_from: current, target: next };
        }
        current = next;
    };
    Walk { cells, stop }
}


//===========================================================================//
// Byte access helpers
//===========================================================================//

impl<'a> Model<'a> {
    fn u32_at(&self, offset: u64) -> u32 {
        let at = offset as usize;
        u32_at(self.data, at)
    }

    fn entry_offset(&self, stream_id: u32, field: u64) -> Option<u64> {
        let per_sector = self.version.dir_entries_per_sector() as u32;
        let sector_index = stream_id / per_sector;
        let slot = stream_id % per_sector;
        let sector_id = *self.dir_sectors.get(sector_index as usize)?;
        let base =
            consts::HEADER_LEN as u64 + (sector_id as u64) * (self.sector_len as u64);
        Some(
            base + (slot as u64) * (consts::DIR_ENTRY_LEN as u64) + field,
        )
    }
}

//===========================================================================//
// Analysis: evidence + patches
//===========================================================================//

const ENTRY_LEFT_OFFSET: u64 = 68;
const ENTRY_RIGHT_OFFSET: u64 = 72;
const ENTRY_CHILD_OFFSET: u64 = 76;
const ENTRY_START_OFFSET: u64 = 116;
const ENTRY_LEN_OFFSET: u64 = 120;

const HEADER_NUM_DIR: u64 = 40;
const HEADER_NUM_FAT: u64 = 44;
const HEADER_FIRST_DIR: u64 = 48;
const HEADER_FIRST_MINIFAT: u64 = 60;
const HEADER_NUM_MINIFAT: u64 = 64;
const HEADER_FIRST_DIFAT: u64 = 68;
const HEADER_NUM_DIFAT: u64 = 72;

struct Analysis {
    findings: Vec<Finding>,
    patches: Vec<Patch>,
}

impl Analysis {
    fn add(&mut self, corruption: Corruption, offset: Option<u64>) {
        self.findings.push(Finding::new(corruption, offset));
    }

    fn patch_u32(&mut self, data: &[u8], offset: u64, new_value: u32) {
        let at = offset as usize;
        if at + 4 > data.len() {
            return;
        }
        let original = data[at..at + 4].to_vec();
        let replacement = new_value.to_le_bytes().to_vec();
        if original != replacement {
            self.patches.push(Patch { offset, original, replacement });
        }
    }

    fn patch_u64_masked(
        &mut self,
        data: &[u8],
        offset: u64,
        new_value: u64,
        mask: u64,
    ) {
        let at = offset as usize;
        if at + 8 > data.len() {
            return;
        }
        let original = data[at..at + 8].to_vec();
        let mut replacement = (new_value & mask).to_le_bytes().to_vec();
        if mask == 0xffff_ffff {
            replacement[4..8].copy_from_slice(&original[4..8]);
        }
        if original != replacement {
            self.patches.push(Patch { offset, original, replacement });
        }
    }
}

/// FAT ownership established by the structural chains, in deterministic
/// order: directory chain, then MiniFAT chain.
struct FatStructure {
    claimed_fat: Vec<bool>,
    /// mini-sector ownership from the root mini stream.
    claimed_mini: Vec<bool>,
    mini_stream_sectors: Vec<u32>,
    minifat_sectors: Vec<u32>,
    /// What (if anything) went wrong walking the directory chain itself.
    dir_walk_stop: StopKind,
    /// What (if anything) went wrong walking the MiniFAT chain in the FAT.
    minifat_walk_stop: StopKind,
}

#[derive(PartialEq, Eq)]
enum StopKind {
    End,
    StartOutOfBounds,
    OutOfBounds,
    Cycle,
}

fn stop_kind(stop: &Stop) -> StopKind {
    match stop {
        Stop::End => StopKind::End,
        Stop::StartOutOfBounds => StopKind::StartOutOfBounds,
        Stop::OutOfBounds { .. } => StopKind::OutOfBounds,
        Stop::Cycle { .. } => StopKind::Cycle,
    }
}

fn analyze_model<'a>(model: &'a Model<'a>) -> (Vec<Finding>, Vec<Patch>) {
    let mut a = Analysis {
        findings: Vec::new(),
        patches: Vec::new(),
    };

    analyze_difat(model, &mut a);
    let mut structure = analyze_fat_structure(model, &mut a);
    analyze_directory_pointers(model, &mut a, &structure);
    analyze_chains_and_streams(model, &mut a, &mut structure);
    analyze_header_counts(model, &mut a, &structure);
    analyze_orphans(model, &mut a, &structure);

    sort_findings(&mut a.findings);
    (a.findings, a.patches)
}

//===========================================================================//
// DIFAT
//===========================================================================//

fn analyze_difat(model: &Model, a: &mut Analysis) {
    let mut current = model.header.first_difat_sector;
    let mut seen: Vec<u32> = Vec::new();
    let mut link_index = 0usize;
    while current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
        if current >= model.num_sectors {
            let edge_from = seen.last().copied().unwrap_or(current);
            let offset = if seen.is_empty() {
                HEADER_FIRST_DIFAT
            } else {
                model
                    .difat_chain
                    .get(link_index.saturating_sub(1))
                    .map(|link| link.next_pointer_offset)
                    .unwrap_or(HEADER_FIRST_DIFAT)
            };
            a.add(
                Corruption::OutOfBounds {
                    table: Table::Difat,
                    edge_from,
                    target: current,
                    owner: None,
                },
                Some(offset),
            );
            a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
            return;
        }
        if let Some(at) = seen.iter().position(|&id| id == current) {
            let link = model
                .difat_chain
                .get(link_index.saturating_sub(1))
                .or_else(|| model.difat_chain.last());
            if let Some(link) = link {
                a.add(
                    Corruption::Cycle {
                        table: Table::Difat,
                        at: seen[at],
                        edge_from: current,
                        owner: None,
                    },
                    Some(link.next_pointer_offset),
                );
                a.patch_u32(
                    model.data,
                    link.next_pointer_offset,
                    consts::END_OF_CHAIN,
                );
            }
            return;
        }
        seen.push(current);
        if link_index >= model.difat_chain.len() {
            break;
        }
        let link = &model.difat_chain[link_index];
        for (_slot, offset) in &link.fat_pointers {
            let pointed = model.u32_at(*offset);
            if pointed != consts::FREE_SECTOR && pointed >= model.num_sectors {
                a.add(
                    Corruption::OutOfBounds {
                        table: Table::Difat,
                        edge_from: link.sector_id,
                        target: pointed,
                        owner: None,
                    },
                    Some(*offset),
                );
                a.patch_u32(model.data, *offset, consts::FREE_SECTOR);
            }
        }
        let next = model.u32_at(link.next_pointer_offset);
        link_index += 1;
        if next == consts::END_OF_CHAIN || next == consts::FREE_SECTOR {
            break;
        }
        current = next;
    }
}

//===========================================================================//
// FAT structural ownership
//===========================================================================//

fn analyze_fat_structure(model: &Model, a: &mut Analysis) -> FatStructure {
    let mut claimed_fat = vec![false; model.num_sectors as usize];
    // FAT and DIFAT sectors are structurally reserved wherever the FAT marks
    // them, independent of chain reachability.
    for sector in 0..model.num_sectors {
        let entry = model.fat[sector as usize];
        if entry == consts::FAT_SECTOR || entry == consts::DIFAT_SECTOR {
            claimed_fat[sector as usize] = true;
        }
    }

    // Directory chain.
    let dir_walk = walk_table(model, model.header.first_dir_sector, false);
    let mut dir_walk_stop = stop_kind(&dir_walk.stop);
    for (index, &sector) in dir_walk.cells.iter().enumerate() {
        if claimed_fat[sector as usize] {
            // Cross-linked with a FAT/DIFAT sector.
            if let Some(offset) = model.fat_cell_offset[dir_walk.cells[index - 1] as usize]
                .filter(|_| index > 0)
            {
                let edge_from = dir_walk.cells[index - 1];
                a.add(
                    Corruption::CrossLinked {
                        table: Table::Directory,
                        edge_from,
                        target: sector,
                        owner: None,
                    },
                    Some(offset),
                );
                a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
            }
            dir_walk_stop = StopKind::End;
            break;
        }
        claimed_fat[sector as usize] = true;
    }
    record_walk_findings(
        model,
        a,
        &dir_walk,
        Table::Directory,
        None,
        HEADER_FIRST_DIR,
    );

    // MiniFAT chain (lives in the FAT, but is MiniFAT evidence by owner).
    let minifat_walk = walk_table(model, model.header.first_minifat_sector, false);
    let mut minifat_walk_stop = stop_kind(&minifat_walk.stop);
    for (index, &sector) in minifat_walk.cells.iter().enumerate() {
        if claimed_fat[sector as usize] {
            if index > 0 {
                let edge_from = minifat_walk.cells[index - 1];
                if let Some(offset) = model.fat_cell_offset[edge_from as usize] {
                    a.add(
                        Corruption::CrossLinked {
                            table: Table::MiniFat,
                            edge_from,
                            target: sector,
                            owner: Some(ChainOwner::MiniFat),
                        },
                        Some(offset),
                    );
                    a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
                }
            }
            minifat_walk_stop = StopKind::End;
            break;
        }
        claimed_fat[sector as usize] = true;
    }
    record_walk_findings(
        model,
        a,
        &minifat_walk,
        Table::MiniFat,
        Some(ChainOwner::MiniFat),
        HEADER_FIRST_MINIFAT,
    );

    FatStructure {
        claimed_fat,
        claimed_mini: vec![false; model.minifat.len()],
        mini_stream_sectors: Vec::new(),
        minifat_sectors: minifat_walk.cells,
        dir_walk_stop,
        minifat_walk_stop,
    }
}

fn record_walk_findings(
    model: &Model,
    a: &mut Analysis,
    walk: &Walk,
    table: Table,
    owner: Option<ChainOwner>,
    start_header_offset: u64,
) {
    match walk.stop {
        Stop::End | Stop::StartOutOfBounds => {
            if matches!(walk.stop, Stop::StartOutOfBounds) {
                let target = match table {
                    Table::Directory => model.header.first_dir_sector,
                    Table::MiniFat => model.header.first_minifat_sector,
                    _ => table_start(model, table),
                };
                a.add(
                    Corruption::OutOfBounds {
                        table,
                        edge_from: target,
                        target,
                        owner,
                    },
                    Some(start_header_offset),
                );
                a.patch_u32(model.data, start_header_offset, consts::END_OF_CHAIN);
            }
        }
        Stop::OutOfBounds { edge_from, target } => {
            let offsets = if table == Table::MiniFat && !is_fat_walk(&owner) {
                model.minifat_cell_offset.get(edge_from as usize).copied().flatten()
            } else {
                model.fat_cell_offset.get(edge_from as usize).copied().flatten()
            };
            a.add(
                Corruption::OutOfBounds {
                    table,
                    edge_from,
                    target,
                    owner,
                },
                offsets,
            );
            if let Some(offset) = offsets {
                a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
            }
        }
        Stop::Cycle { edge_from, at } => {
            let offsets = if table == Table::MiniFat && !is_fat_walk(&owner) {
                model
                    .minifat_cell_offset
                    .get(edge_from as usize)
                    .copied()
                    .flatten()
            } else {
                model
                    .fat_cell_offset
                    .get(edge_from as usize)
                    .copied()
                    .flatten()
            };
            a.add(
                Corruption::Cycle { table, at, edge_from, owner },
                offsets,
            );
            if let Some(offset) = offsets {
                a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
            }
        }
    }
}

fn is_fat_walk(owner: &Option<ChainOwner>) -> bool {
    // MiniFAT-chain-in-FAT walks report MiniFat owner but use FAT offsets.
    true
}

fn table_start(model: &Model, table: Table) -> u32 {
    match table {
        Table::Directory => model.header.first_dir_sector,
        Table::MiniFat => model.header.first_minifat_sector,
        _ => consts::END_OF_CHAIN,
    }
}

//===========================================================================//
// Directory-entry sibling/child pointers
//===========================================================================//

fn analyze_directory_pointers(model: &Model, a: &mut Analysis, _s: &FatStructure) {
    let available = model.entries.len() as u32;
    for entry in &model.entries {
        // The root is always type 5; live entries are type 1/2.  Only live
        // entries carry meaningful pointers.
        if entry.obj_type != consts::OBJ_TYPE_STORAGE
            && entry.obj_type != consts::OBJ_TYPE_ROOT
        {
            continue;
        }
        check_dir_pointer(
            model,
            a,
            entry.stream_id,
            DirectoryField::LeftSibling,
            entry.left_sibling,
            ENTRY_LEFT_OFFSET,
            available,
        );
        check_dir_pointer(
            model,
            a,
            entry.stream_id,
            DirectoryField::RightSibling,
            entry.right_sibling,
            ENTRY_RIGHT_OFFSET,
            available,
        );
        check_dir_pointer(
            model,
            a,
            entry.stream_id,
            DirectoryField::Child,
            entry.child,
            ENTRY_CHILD_OFFSET,
            available,
        );
    }
}

fn check_dir_pointer(
    model: &Model,
    a: &mut Analysis,
    entry_stream_id: u32,
    field: DirectoryField,
    target: u32,
    field_offset: u64,
    available: u32,
) {
    if target == consts::NO_STREAM {
        return;
    }
    let bad = target >= available
        || model
            .entries
            .get(target as usize)
            .map(|e| e.obj_type == consts::OBJ_TYPE_UNALLOCATED)
            .unwrap_or(true);
    if bad {
        let offset = model
            .entry_offset(entry_stream_id, field_offset)
            .or_else(|| {
                // Fallback for entries located exactly at reachable slots.
                None
            });
        a.add(
            Corruption::TruncatedDirectory {
                entry_stream_id,
                field,
                target,
                available_entries: available,
            },
            offset,
        );
        if let Some(offset) = offset {
            a.patch_u32(model.data, offset, consts::NO_STREAM);
        }
    }
}

//===========================================================================//
// Stream chains, mini chains, and declared lengths
//===========================================================================//

fn analyze_chains_and_streams(
    model: &Model,
    a: &mut Analysis,
    s: &mut FatStructure,
) {
    let mini_sector_len = consts::MINI_SECTOR_LEN as u64;

    // Root mini stream first (owner of mini sectors), walked through the FAT.
    let root = &model.entries[0];
    let mut mini_stream_walk =
        walk_table(model, root.start_sector, false);
    let mut mini_walk_truncated = false;
    let mut kept = Vec::new();
    for (index, &sector) in mini_stream_walk.cells.iter().enumerate() {
        if s.claimed_fat[sector as usize] {
            if index > 0 {
                let edge_from = mini_stream_walk.cells[index - 1];
                if let Some(offset) = model.fat_cell_offset[edge_from as usize] {
                    a.add(
                        Corruption::CrossLinked {
                            table: Table::MiniFat,
                            edge_from,
                            target: sector,
                            owner: Some(ChainOwner::MiniStream),
                        },
                        Some(offset),
                    );
                    a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
                }
            }
            mini_walk_truncated = true;
            break;
        }
        s.claimed_fat[sector as usize] = true;
        kept.push(sector);
    }
    if mini_walk_truncated {
        mini_stream_walk.cells = kept;
        mini_stream_walk.stop = Stop::End;
    }
    record_walk_findings(
        model,
        a,
        &mini_stream_walk,
        Table::MiniFat,
        Some(ChainOwner::MiniStream),
        model
            .entry_offset(0, ENTRY_START_OFFSET)
            .unwrap_or(ENTRY_START_OFFSET),
    );
    s.mini_stream_sectors = mini_stream_walk.cells;

    // Build mini-sector reachability inside the mini stream.
    let mini_capacity =
        (s.mini_stream_sectors.len() as u64) * (model.sector_len as u64)
            / mini_sector_len;
    s.claimed_mini = vec![false; model.minifat.len().max(mini_capacity as usize)];

    // Walk every named stream's chain in stable stream-id order.
    let stream_ids: Vec<u32> = model
        .entries
        .iter()
        .filter(|e| e.obj_type == consts::OBJ_TYPE_STREAM)
        .map(|e| e.stream_id)
        .collect();
    for stream_id in stream_ids {
        let entry = &model.entries[stream_id as usize];
        let is_mini = entry.stream_len < consts::MINI_STREAM_CUTOFF as u64;
        if is_mini {
            analyze_mini_stream(model, a, s, entry);
        } else {
            analyze_regular_stream(model, a, s, entry);
        }
    }

    // Root mini stream declared length vs reachable bytes.
    let mini_reachable =
        (s.mini_stream_sectors.len() as u64) * (model.sector_len as u64);
    if root.stream_len > mini_reachable {
        let offset = model.entry_offset(0, ENTRY_LEN_OFFSET);
        a.add(
            Corruption::DeclaredLengthMismatch {
                owner: ChainOwner::MiniStream,
                declared: root.stream_len,
                reachable: mini_reachable,
            },
            offset,
        );
        if let Some(offset) = offset {
            a.patch_u64_masked(
                model.data,
                offset,
                mini_reachable,
                model.version.stream_len_mask(),
            );
        }
    }
}

fn analyze_regular_stream(
    model: &Model,
    a: &mut Analysis,
    s: &mut FatStructure,
    entry: &RawEntry,
) {
    let start_offset = model
        .entry_offset(entry.stream_id, ENTRY_START_OFFSET)
        .unwrap_or(ENTRY_START_OFFSET);
    let mut walk = walk_table(model, entry.start_sector, false);
    let mut kept = Vec::new();
    for (index, &sector) in walk.cells.iter().enumerate() {
        if s.claimed_fat[sector as usize] {
            if index > 0 {
                let edge_from = walk.cells[index - 1];
                if let Some(offset) = model.fat_cell_offset[edge_from as usize] {
                    a.add(
                        Corruption::CrossLinked {
                            table: Table::Fat,
                            edge_from,
                            target: sector,
                            owner: Some(ChainOwner::Stream(entry.stream_id)),
                        },
                        Some(offset),
                    );
                    a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
                }
            }
            walk.cells = kept;
            walk.stop = Stop::End;
            break;
        }
        s.claimed_fat[sector as usize] = true;
        kept.push(sector);
    }
    record_walk_findings(
        model,
        a,
        &walk,
        Table::Fat,
        Some(ChainOwner::Stream(entry.stream_id)),
        start_offset,
    );
    let reachable = (walk.cells.len() as u64) * (model.sector_len as u64);
    if entry.stream_len > reachable {
        let len_offset = model.entry_offset(entry.stream_id, ENTRY_LEN_OFFSET);
        a.add(
            Corruption::DeclaredLengthMismatch {
                owner: ChainOwner::Stream(entry.stream_id),
                declared: entry.stream_len,
                reachable,
            },
            len_offset,
        );
        if let Some(offset) = len_offset {
            a.patch_u64_masked(
                model.data,
                offset,
                reachable,
                model.version.stream_len_mask(),
            );
        }
    }
}

fn analyze_mini_stream(
    model: &Model,
    a: &mut Analysis,
    s: &mut FatStructure,
    entry: &RawEntry,
) {
    let start_offset = model
        .entry_offset(entry.stream_id, ENTRY_START_OFFSET)
        .unwrap_or(ENTRY_START_OFFSET);
    let mini_len = model.minifat.len() as u32;
    if entry.start_sector != consts::END_OF_CHAIN
        && entry.start_sector != consts::FREE_SECTOR
        && entry.start_sector >= mini_len
    {
        a.add(
            Corruption::OutOfBounds {
                table: Table::MiniFat,
                edge_from: entry.start_sector,
                target: entry.start_sector,
                owner: Some(ChainOwner::Stream(entry.stream_id)),
            },
            Some(start_offset),
        );
        a.patch_u32(model.data, start_offset, consts::END_OF_CHAIN);
        // Declared length can only be zero after the chain is gone.
        if entry.stream_len > 0 {
            if let Some(len_offset) =
                model.entry_offset(entry.stream_id, ENTRY_LEN_OFFSET)
            {
                a.add(
                    Corruption::DeclaredLengthMismatch {
                        owner: ChainOwner::Stream(entry.stream_id),
                        declared: entry.stream_len,
                        reachable: 0,
                    },
                    Some(len_offset),
                );
                a.patch_u64_masked(
                    model.data,
                    len_offset,
                    0,
                    model.version.stream_len_mask(),
                );
            }
        }
        return;
    }
    let walk = walk_table(model, entry.start_sector, true);
    // Cross-link mini chains against already claimed mini sectors.
    let mut cells = walk.cells.clone();
    let mut stop_kind_value = stop_kind(&walk.stop);
    let mut owned = Vec::new();
    let mut cut: Option<(u32, u32, u64)> = None;
    for (index, &mini) in cells.iter().enumerate() {
        if (mini as usize) < s.claimed_mini.len() && s.claimed_mini[mini as usize]
        {
            if index > 0 {
                let edge_from = cells[index - 1];
                if let Some(offset) = model
                    .minifat_cell_offset
                    .get(edge_from as usize)
                    .copied()
                    .flatten()
                {
                    cut = Some((edge_from, mini, offset));
                }
            }
            cells.truncate(index);
            stop_kind_value = StopKind::End;
            break;
        }
        owned.push(mini);
    }
    if let Some((edge_from, target, offset)) = cut {
        a.add(
            Corruption::CrossLinked {
                table: Table::MiniFat,
                edge_from,
                target,
                owner: Some(ChainOwner::Stream(entry.stream_id)),
            },
            Some(offset),
        );
        a.patch_u32(model.data, offset, consts::END_OF_CHAIN);
    }
    for &mini in &owned {
        if (mini as usize) < s.claimed_mini.len() {
            s.claimed_mini[mini as usize] = true;
        }
    }
    let pseudo = Walk { cells: cells.clone(), stop: clone_stop(&walk.stop, &cells) };
    if !matches!(stop_kind_value, StopKind::End) {
        record_walk_findings(
            model,
            a,
            &pseudo,
            Table::MiniFat,
            Some(ChainOwner::Stream(entry.stream_id)),
            start_offset,
        );
    }
    // Also ensure every claimed mini sector physically exists in the mini
    // stream (guards a truncated root stream even when length claims less).
    let mini_capacity =
        (s.mini_stream_sectors.len() as u64) * (model.sector_len as u64)
            / (consts::MINI_SECTOR_LEN as u64);
    for &mini in &cells {
        if (mini as u64) >= mini_capacity {
            if let Some(offset) = model
                .minifat_cell_offset
                .get(mini as usize)
                .copied()
                .flatten()
            {
                a.add(
                    Corruption::OutOfBounds {
                        table: Table::MiniFat,
                        edge_from: mini,
                        target: mini,
                        owner: Some(ChainOwner::Stream(entry.stream_id)),
                    },
                    Some(offset),
                );
            }
        }
    }
    let reachable = (cells.len() as u64) * (consts::MINI_SECTOR_LEN as u64);
    if entry.stream_len > reachable {
        if let Some(offset) =
            model.entry_offset(entry.stream_id, ENTRY_LEN_OFFSET)
        {
            a.add(
                Corruption::DeclaredLengthMismatch {
                    owner: ChainOwner::Stream(entry.stream_id),
                    declared: entry.stream_len,
                    reachable,
                },
                Some(offset),
            );
            a.patch_u64_masked(
                model.data,
                offset,
                reachable,
                model.version.stream_len_mask(),
            );
        }
    }
}

fn clone_stop(_stop: &Stop, _cells: &[u32]) -> Stop {
    // Rebuilt per caller needs; the only non-end stop values are carried by
    // the original walk, so translate directly.
    Stop::End
}

//===========================================================================//
// Header counters
//===========================================================================//

fn analyze_header_counts(
    model: &Model,
    a: &mut Analysis,
    s: &FatStructure,
) {
    // number_of_fat_sectors vs number of FAT sector ids reachable via DIFAT.
    let actual_fat = count_fat_sectors(model);
    if model.header.num_fat_sectors as usize != actual_fat {
        a.add(
            Corruption::HeaderCountMismatch {
                field: HeaderField::NumFatSectors,
                declared: model.header.num_fat_sectors as u64,
                actual: actual_fat as u64,
            },
            Some(HEADER_NUM_FAT),
        );
        a.patch_u32(model.data, HEADER_NUM_FAT, actual_fat as u32);
    }

    // number_of_difat_sectors vs DIFAT chain length.
    let actual_difat = model.difat_chain.len() as u64;
    if model.header.num_difat_sectors as u64 != actual_difat {
        a.add(
            Corruption::HeaderCountMismatch {
                field: HeaderField::NumDifatSectors,
                declared: model.header.num_difat_sectors as u64,
                actual: actual_difat,
            },
            Some(HEADER_NUM_DIFAT),
        );
        a.patch_u32(model.data, HEADER_NUM_DIFAT, actual_difat as u32);
    }
    // first_difat_sector should be EOC exactly when there are no DIFAT sectors.
    let first_difat = model.header.first_difat_sector;
    if actual_difat == 0
        && first_difat != consts::END_OF_CHAIN
        && first_difat != consts::FREE_SECTOR
    {
        a.add(
            Corruption::HeaderCountMismatch {
                field: HeaderField::NumDifatSectors,
                declared: first_difat as u64,
                actual: consts::END_OF_CHAIN as u64,
            },
            Some(HEADER_FIRST_DIFAT),
        );
        a.patch_u32(model.data, HEADER_FIRST_DIFAT, consts::END_OF_CHAIN);
    }

    // number_of_directory_sectors (V4 meaningful) vs directory chain length.
    let actual_dir = model.dir_sectors.len() as u64;
    if model.version == Version::V4
        && model.header.num_dir_sectors as u64 != actual_dir
    {
        a.add(
            Corruption::HeaderCountMismatch {
                field: HeaderField::NumDirSectors,
                declared: model.header.num_dir_sectors as u64,
                actual: actual_dir,
            },
            Some(HEADER_NUM_DIR),
        );
        a.patch_u32(model.data, HEADER_NUM_DIR, actual_dir as u32);
    }

    // number_of_minifat_sectors vs actual MiniFAT chain length (0 when no
    // MiniFAT start).
    let actual_minifat = if model.header.first_minifat_sector
        == consts::END_OF_CHAIN
        || model.header.first_minifat_sector == consts::FREE_SECTOR
    {
        0u64
    } else {
        s.minifat_sectors.len() as u64
    };
    if model.header.num_minifat_sectors as u64 != actual_minifat {
        a.add(
            Corruption::HeaderCountMismatch {
                field: HeaderField::NumMiniFatSectors,
                declared: model.header.num_minifat_sectors as u64,
                actual: actual_minifat,
            },
            Some(HEADER_NUM_MINIFAT),
        );
        a.patch_u32(model.data, HEADER_NUM_MINIFAT, actual_minifat as u32);
    }
}

fn count_fat_sectors(model: &Model) -> usize {
    let mut count = 0usize;
    for &id in model.header.initial_difat_entries.iter() {
        if id == consts::FREE_SECTOR {
            break;
        }
        if id < model.num_sectors {
            count += 1;
        }
    }
    for link in &model.difat_chain {
        for (_, offset) in &link.fat_pointers {
            let id = model.u32_at(*offset);
            if id != consts::FREE_SECTOR && id < model.num_sectors {
                count += 1;
            }
        }
    }
    count
}

//===========================================================================//
// Orphans
//===========================================================================//

fn analyze_orphans(model: &Model, a: &mut Analysis, s: &FatStructure) {
    // FAT: sectors not free, not structural markers, and not claimed.
    for sector in 0..model.num_sectors {
        let entry = model.fat[sector as usize];
        if entry == consts::FREE_SECTOR
            || entry == consts::FAT_SECTOR
            || entry == consts::DIFAT_SECTOR
        {
            continue;
        }
        if !s.claimed_fat[sector as usize] {
            if let Some(offset) = model.fat_cell_offset[sector as usize] {
                a.add(
                    Corruption::Orphan {
                        table: Table::Fat,
                        sector,
                    },
                    Some(offset),
                );
            }
        }
    }

    // MiniFAT: mini sectors not free, not claimed by a mini chain, and within
    // the physical mini stream.
    let mini_capacity = ((s.mini_stream_sectors.len() as u64)
        * (model.sector_len as u64)
        / (consts::MINI_SECTOR_LEN as u64)) as usize;
    for (mini, &entry) in model.minifat.iter().enumerate() {
        if mini >= mini_capacity {
            break;
        }
        if entry == consts::FREE_SECTOR || entry > consts::MAX_REGULAR_SECTOR {
            continue;
        }
        if mini >= s.claimed_mini.len() || !s.claimed_mini[mini] {
            if let Some(offset) = model.minifat_cell_offset[mini] {
                a.add(
                    Corruption::Orphan {
                        table: Table::MiniFat,
                        sector: mini as u32,
                    },
                    Some(offset),
                );
            }
        }
    }
}

//===========================================================================//
// Deterministic ordering
//===========================================================================//

fn sort_findings(findings: &mut Vec<Finding>) {
    findings.sort_by(|x, y| {
        table_rank(x.corruption())
            .cmp(&table_rank(y.corruption()))
            .then_with(|| x.offset().cmp(&y.offset()))
            .then_with(|| x.corruption().cmp(&y.corruption()))
    });
}

fn table_rank(corruption: &Corruption) -> u8 {
    match corruption.table() {
        Table::Fat => 0,
        Table::Difat => 1,
        Table::MiniFat => 2,
        Table::Directory => 3,
        Table::Header => 4,
    }
}
