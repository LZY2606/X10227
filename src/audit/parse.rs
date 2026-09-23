//! Defensive parsing of a raw compound file image.
//!
//! This parser is deliberately independent of the production opening path:
//! the production path validates and repairs eagerly so that it can offer a
//! usable `CompoundFile`, while an audit must keep going after a broken chain
//! to catalogue *every* defect.  Both paths interpret the same on-disk
//! structures (header fields, sector numbers, the constants in
//! [`crate::internal::consts`], and [`crate::internal::DirEntry`]'s byte
//! layout), and the repair path proves agreement by rebuilding through the
//! production write code.

use fnv::{FnvHashMap, FnvHashSet};
use std::mem::size_of;

use crate::internal::{
    consts, DirEntry, Header, ObjType, Validation, Version,
};

/// A regular sector ID together with the byte offset of the FAT entry that
/// pointed to it (the first such entry, for double-occupancy reporting).
#[derive(Clone, Copy)]
pub(super) struct Claim {
    pub by: u32,
    pub fat_entry_offset: u64,
}

/// One directory entry as read from the raw directory chain, plus where it
/// lives in the file.
#[derive(Clone, Debug)]
pub(super) struct RawDirEntry {
    pub stream_id: u32,
    pub entry: DirEntry,
    /// Byte offset of this 128-byte entry within the input file.
    pub offset: u64,
}

/// Everything the audit could extract from a raw image without rejecting it.
pub(super) struct RawImage {
    pub data_len: u64,
    pub sector_len: u64,
    pub num_sectors: u32,
    pub header: Header,
    /// The FAT entries as they are on disk, one per sector for the sectors
    /// that exist.  Entries that could not be read are absent.
    pub fat: Vec<Option<u32>>,
    /// Sector IDs listed as FAT sectors by the DIFAT, in DIFAT order.
    pub fat_sector_ids: Vec<u32>,
    /// Sector IDs of DIFAT sectors, in chain order.
    pub difat_sector_ids: Vec<u32>,
    /// Some(sector) if following the DIFAT chain looped back into a sector
    /// already visited; records the repeated sector.
    pub difat_cycle: Option<u32>,
    /// The raw "next DIFAT sector" pointer at the end of the last readable
    /// DIFAT sector, when it is neither END_OF_CHAIN nor FREE_SECTOR.
    pub difat_next_after_last: Option<u32>,
    /// The directory chain as walked from the header: sector IDs until a
    /// defect forced the walk to stop.
    pub dir_chain: Vec<u32>,
    pub dir_chain_truncated: bool,
    pub dir_entries: Vec<RawDirEntry>,
    /// The MiniFAT entries as on disk.
    pub minifat: Vec<Option<u32>>,
    pub minifat_chain: Vec<u32>,
}

impl RawImage {
    /// Byte offset of sector `id` within the file.
    fn sector_offset(sector_len: u64, id: u32) -> u64 {
        (id as u64 + 1) * sector_len
    }

    fn u32_at(data: &[u8], offset: u64) -> Option<u32> {
        let start = offset as usize;
        let bytes = data.get(start..start + 4)?;
        Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// Reads the file header, falling back to V3 layout if the header itself
    /// is too broken for the production parser.  `None` only when the file is
    /// too small even to contain a header.
    fn parse_header(
        data: &[u8],
        validation: Validation,
    ) -> Option<Header> {
        let mut cursor = std::io::Cursor::new(data);
        match Header::read_from(&mut cursor, validation) {
            Ok(header) => Some(header),
            Err(_) => {
                // Recover enough to audit when only a non-structural header
                // field is wrong: assume V3 and decode the fields directly.
                if data.len() < consts::HEADER_LEN {
                    return None;
                }
                let version_number = Self::u32_at(data, 26)? as u16;
                let version = Version::from_number(version_number)
                    .unwrap_or(Version::V3);
                Some(Self::raw_header(data, version))
            }
        }
    }

    fn raw_header(data: &[u8], version: Version) -> Header {
        let at = |offset: u64| Self::u32_at(data, offset).unwrap_or(0);
        let mut initial = [consts::FREE_SECTOR;
            consts::NUM_DIFAT_ENTRIES_IN_HEADER];
        for (index, slot) in initial.iter_mut().enumerate() {
            let entry = at(76 + 4 * index as u64);
            if entry == consts::FREE_SECTOR {
                break;
            }
            *slot = entry;
        }
        Header {
            version,
            num_dir_sectors: at(40),
            num_fat_sectors: at(44),
            first_dir_sector: at(48),
            first_minifat_sector: at(60),
            num_minifat_sectors: at(64),
            first_difat_sector: at(68),
            num_difat_sectors: at(72),
            initial_difat_entries: initial,
        }
    }
}

impl RawImage {
    pub(super) fn parse(
        data: &[u8],
        validation: Validation,
    ) -> std::io::Result<RawImage> {
        let header = Self::parse_header(data, validation).ok_or_else(|| {
            invalid_data!(
                "Invalid CFB file ({} bytes is too small for a header)",
                data.len()
            )
        })?;
        let sector_len = header.version.sector_len() as u64;
        if data.len() < sector_len as usize {
            invalid_data!(
                "Invalid CFB file (length of {} < sector length of {})",
                data.len(),
                sector_len
            );
        }
        let num_sectors = (data.len() as u64 / sector_len) - 1;
        let num_sectors = u32::try_from(num_sectors).unwrap_or(u32::MAX);

        // ---- DIFAT and FAT ------------------------------------------------
        let mut difat: Vec<u32> =
            header.initial_difat_entries.iter().copied().collect();
        let mut difat_sector_ids: Vec<u32> = Vec::new();
        let mut seen_difat: FnvHashSet<u32> = FnvHashSet::default();
        let mut difat_cycle: Option<u32> = None;
        let mut difat_next_after_last: Option<u32> = None;
        let mut current = header.first_difat_sector;
        let mut guard = 0u64;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
            && current <= consts::MAX_REGULAR_SECTOR
            && (current as u64) < num_sectors as u64
        {
            if !seen_difat.insert(current) {
                difat_cycle = Some(current);
                break;
            }
            difat_sector_ids.push(current);
            let base = Self::sector_offset(sector_len, current);
            let entries = sector_len as usize / 4;
            for index in 0..entries - 1 {
                if let Some(entry) = Self::u32_at(data, base + 4 * index as u64)
                {
                    difat.push(entry);
                }
            }
            let next = Self::u32_at(data, base + sector_len - 4)
                .unwrap_or(consts::END_OF_CHAIN);
            difat_next_after_last = Some(next);
            current = next;
            guard += 1;
            if guard > num_sectors as u64 + 1 {
                break;
            }
        }
        if current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
            difat_next_after_last = Some(current);
        } else {
            difat_next_after_last = None;
        }
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }

        // Read the FAT entries from every sector the DIFAT names, in order.
        let mut fat: Vec<Option<u32>> = vec![None; num_sectors as usize];
        let entries_per_sector = sector_len as usize / 4;
        let mut fat_sector_ids: Vec<u32> = Vec::new();
        for &fat_sector in difat.iter() {
            let difat_slot = fat_sector_ids.len();
            fat_sector_ids.push(fat_sector);
            if fat_sector > consts::MAX_REGULAR_SECTOR
                || fat_sector as u64 >= num_sectors as u64
            {
                continue;
            }
            let base = Self::sector_offset(sector_len, fat_sector);
            for index in 0..entries_per_sector {
                let Some(entry) =
                    Self::u32_at(data, base + 4 * index as u64)
                else {
                    continue;
                };
                let slot = difat_slot * entries_per_sector + index;
                if slot < fat.len() {
                    fat[slot] = Some(entry);
                }
            }
        }

        // ---- Directory chain ---------------------------------------------
        let mut dir_chain: Vec<u32> = Vec::new();
        let mut dir_chain_truncated = false;
        let mut seen_dir: FnvHashSet<u32> = FnvHashSet::default();
        current = header.first_dir_sector;
        guard = 0;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
            && current <= consts::MAX_REGULAR_SECTOR
            && (current as u64) < num_sectors as u64
            && seen_dir.insert(current)
        {
            dir_chain.push(current);
            current = match fat.get(current as usize).copied().flatten() {
                Some(next) => next,
                None => {
                    dir_chain_truncated = true;
                    consts::END_OF_CHAIN
                }
            };
            guard += 1;
            if guard > num_sectors as u64 + 1 {
                break;
            }
        }
        if current != consts::END_OF_CHAIN && current != consts::FREE_SECTOR {
            // Reaching here means the walk stopped on a defect the caller
            // classifies (cycle, out-of-range, duplicate, or sentinel).
            if current as u64 >= num_sectors as u64
                || current > consts::MAX_REGULAR_SECTOR
            {
                dir_chain_truncated = true;
            }
        }

        let entries_per_dir_sector =
            header.version.dir_entries_per_sector() as u32;
        let mut dir_entries: Vec<RawDirEntry> = Vec::new();
        for (chain_index, &sector_id) in dir_chain.iter().enumerate() {
            let base = Self::sector_offset(sector_len, sector_id);
            for slot in 0..entries_per_dir_sector {
                let stream_id =
                    chain_index as u32 * entries_per_dir_sector + slot;
                let offset = base + 128 * slot as u64;
                let Some(blob) = data.get(
                    offset as usize..offset as usize + consts::DIR_ENTRY_LEN,
                ) else {
                    continue;
                };
                if let Ok(entry) =
                    DirEntry::read_from(&mut &blob[..], header.version, validation)
                {
                    dir_entries
                        .push(RawDirEntry { stream_id, entry, offset });
                }
            }
        }

        // ---- MiniFAT ------------------------------------------------------
        let mut minifat_chain: Vec<u32> = Vec::new();
        let mut seen_mini_fat: FnvHashSet<u32> = FnvHashSet::default();
        current = header.first_minifat_sector;
        guard = 0;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
            && current <= consts::MAX_REGULAR_SECTOR
            && (current as u64) < num_sectors as u64
            && seen_mini_fat.insert(current)
        {
            minifat_chain.push(current);
            current = fat
                .get(current as usize)
                .copied()
                .flatten()
                .unwrap_or(consts::END_OF_CHAIN);
            guard += 1;
            if guard > num_sectors as u64 + 1 {
                break;
            }
        }
        let mut minifat: Vec<Option<u32>> = Vec::new();
        for &sector_id in minifat_chain.iter() {
            let base = Self::sector_offset(sector_len, sector_id);
            for index in 0..entries_per_sector {
                minifat.push(Self::u32_at(data, base + 4 * index as u64));
            }
        }
        while minifat.last() == Some(&Some(consts::FREE_SECTOR)) {
            minifat.pop();
        }

        Ok(RawImage {
            data_len: data.len() as u64,
            sector_len,
            num_sectors,
            header,
            fat,
            fat_sector_ids,
            difat_sector_ids,
            difat_cycle,
            difat_next_after_last,
            dir_chain,
            dir_chain_truncated,
            dir_entries,
            minifat,
            minifat_chain,
        })
    }
}

//===========================================================================//
// Evidence collection
//===========================================================================//

use super::report::{DamageKind, Evidence, Structure};

impl RawImage {
    fn fat_entry_offset(
        &self,
        fat_sector_index: usize,
        index_within_sector: usize,
    ) -> Option<u64> {
        let entries_per_sector = self.sector_len as usize / 4;
        let fat_sector = *self.fat_sector_ids.get(fat_sector_index)?;
        if fat_sector as u64 >= self.num_sectors as u64 {
            return None;
        }
        Some(
            Self::sector_offset(self.sector_len, fat_sector)
                + 4 * index_within_sector as u64,
        )
    }

    /// Byte offset of the FAT entry for `sector`, if it lives on a readable
    /// FAT sector.
    fn fat_entry_for_sector(&self, sector: u32) -> Option<u64> {
        let entries_per_sector = self.sector_len as usize / 4;
        let fat_sector_index = sector as usize / entries_per_sector;
        let index_within = sector as usize % entries_per_sector;
        self.fat_entry_offset(fat_sector_index, index_within)
    }

type Note<'a> = &'a mut dyn FnMut(Structure, DamageKind, Option<u64>, String, &'static str);

pub(super) fn collect(
    image: &RawImage,
) -> (Vec<Evidence>, Vec<String>) {
    let mut evidence: Vec<Evidence> = Vec::new();
    let mut step_tags: FnvHashSet<&'static str> = FnvHashSet::default();
    {
        let mut note: Note = &mut |structure, kind, offset, context, tag| {
            evidence.push(Evidence::new(structure, kind, offset, context));
            step_tags.insert(tag);
        };
        collect_fat(image, &mut note);
        collect_difat(image, &mut note);
        collect_directory(image, &mut note);
        collect_minifat(image, &mut note);
        collect_orphans(image, &mut note);
        collect_lengths(image, &mut note);
    }

    // Deterministic order: structure, then kind, then offset, then context.
    evidence.sort_by(|a, b| {
        (a.structure(), a.kind(), a.offset(), a.context())
            .cmp(&(b.structure(), b.kind(), b.offset(), b.context()))
    });
    evidence.dedup();

    let steps: Vec<String> = REPAIR_STEPS
        .iter()
        .filter(|tag| step_tags.contains(**tag))
        .map(|tag| String::from(*tag))
        .collect();
    (evidence, steps)
}

const REPAIR_STEPS: &[&str] = &[
    "rebuild a fresh FAT and DIFAT for all reachable sectors",
    "end chains that enter a cycle, keeping the sectors before the loop",
    "end chains at the last in-range sector instead of following \
     out-of-bounds pointers",
    "assign each multiply-claimed sector to its first chain and detach the \
     later claimant",
    "leave unreachable (orphan) sectors out of the rebuilt file",
    "rebuild the directory chain from the readable directory entries",
    "rebuild the MiniFAT and mini stream from readable mini chains",
    "reset each stream's declared length to the bytes its repaired chain \
     holds",
    "compact storages and streams into a new, fully linked compound file",
];

//===========================================================================//
// FAT: out-of-bounds pointers, cycles, and double occupancy between chains.
//===========================================================================//

/// Who a chain belongs to, for double-occupancy context messages.
#[derive(Clone, Copy)]
enum ChainOwner {
    DirectoryChain,
    MiniFatChain,
    MiniStream,
    Stream(u32),
}

impl ChainOwner {
    fn label(self) -> String {
        match self {
            ChainOwner::DirectoryChain => "directory chain".to_string(),
            ChainOwner::MiniFatChain => "MiniFAT chain".to_string(),
            ChainOwner::MiniStream => "mini stream".to_string(),
            ChainOwner::Stream(id) => format!("stream entry {}", id),
        }
    }
}

const STEP_FRESH_FAT: &str =
    "rebuild a fresh FAT and DIFAT for all reachable sectors";
const STEP_CYCLE: &str =
    "end chains that enter a cycle, keeping the sectors before the loop";
const STEP_OOB: &str =
    "end chains at the last in-range sector instead of following \
     out-of-bounds pointers";
const STEP_DOUBLE: &str =
    "assign each multiply-claimed sector to its first chain and detach the \
     later claimant";
const STEP_ORPHAN: &str =
    "leave unreachable (orphan) sectors out of the rebuilt file";
const STEP_DIR: &str =
    "rebuild the directory chain from the readable directory entries";
const STEP_MINIFAT: &str =
    "rebuild the MiniFAT and mini stream from readable mini chains";
const STEP_LEN: &str =
    "reset each stream's declared length to the bytes its repaired chain \
     holds";
const STEP_COMPACT: &str =
    "compact storages and streams into a new, fully linked compound file";

impl RawImage {
    /// Walks one FAT chain, reporting cycles, out-of-bounds pointers, and
    /// sectors already claimed by another chain.  Returns the in-range,
    /// non-repeating sector IDs that can safely be kept.
    fn walk_fat_chain(
        &self,
        start: u32,
        owner: ChainOwner,
        claimed: &mut FnvHashMap<u32, String>,
        evidence: &mut Vec<(Structure, DamageKind, Option<u64>, String, &'static str)>,
    ) -> Vec<u32> {
        let mut ids = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ids;
        }
        if start > consts::MAX_REGULAR_SECTOR || start as u64 >= self.num_sectors as u64
        {
            evidence.push((
                Structure::Fat,
                DamageKind::OutOfBounds,
                None,
                format!(
                    "{} starts at sector {} which is beyond the file",
                    owner.label(),
                    start
                ),
                STEP_OOB,
            ));
            return ids;
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = start;
        loop {
            // Double occupancy: some other chain already owns this sector.
            if let Some(first_owner) = claimed.get(&current) {
                evidence.push((
                    Structure::Fat,
                    DamageKind::DoubleOccupancy,
                    self.fat_entry_for_sector(current),
                    format!(
                        "sector {} is used by both {} and {}",
                        current,
                        first_owner,
                        owner.label()
                    ),
                    STEP_DOUBLE,
                ));
                return ids;
            }
            claimed.insert(current, owner.label());
            local.insert(current);
            ids.push(current);

            let Some(entry) = self.fat.get(current as usize).copied().flatten()
            else {
                evidence.push((
                    Structure::Fat,
                    DamageKind::OutOfBounds,
                    None,
                    format!(
                        "{}: sector {} has no readable FAT entry",
                        owner.label(),
                        current
                    ),
                    STEP_OOB,
                ));
                return ids;
            };
            if entry == consts::END_OF_CHAIN || entry == consts::FREE_SECTOR {
                return ids;
            }
            if entry > consts::MAX_REGULAR_SECTOR
                || entry as u64 >= self.num_sectors as u64
            {
                evidence.push((
                    Structure::Fat,
                    DamageKind::OutOfBounds,
                    self.fat_entry_for_sector(current),
                    format!(
                        "{}: sector {} points past the file to {}",
                        owner.label(),
                        current,
                        entry
                    ),
                    STEP_OOB,
                ));
                return ids;
            }
            if local.contains(&entry) {
                evidence.push((
                    Structure::Fat,
                    DamageKind::Cycle,
                    self.fat_entry_for_sector(current),
                    format!(
                        "{}: sector {} loops back to {}",
                        owner.label(),
                        current,
                        entry
                    ),
                    STEP_CYCLE,
                ));
                return ids;
            }
            current = entry;
        }
    }

    /// Every chain root named by the structures we can read, in a fixed
    /// order, so that "first owner" is deterministic.
    fn chain_roots(&self) -> Vec<(u32, ChainOwner)> {
        let mut roots: Vec<(u32, ChainOwner)> = Vec::new();
        roots.push((self.header.first_dir_sector, ChainOwner::DirectoryChain));
        roots
            .push((self.header.first_minifat_sector, ChainOwner::MiniFatChain));
        if let Some(root) = self.dir_entries.first() {
            if root.stream_id == consts::ROOT_STREAM_ID {
                roots.push((root.entry.start_sector, ChainOwner::MiniStream));
            }
        }
        for raw in self.dir_entries.iter() {
            if raw.entry.obj_type == ObjType::Stream {
                roots
                    .push((raw.entry.start_sector, ChainOwner::Stream(raw.stream_id)));
            }
        }
        roots
    }

    /// Returns the safely-walkable sectors of every named chain, keyed by
    /// owner label.  Used both for evidence and for orphan detection.
    fn walk_all_chains(
        &self,
        raw_evidence: &mut Vec<(
            Structure,
            DamageKind,
            Option<u64>,
            String,
            &'static str,
        )>,
    ) -> FnvHashSet<u32> {
        let mut claimed: FnvHashMap<u32, String> = FnvHashSet::default();
        for (start, owner) in self.chain_roots() {
            self.walk_fat_chain(start, owner, &mut claimed, raw_evidence);
        }
        claimed.into_keys().collect()
    }
}

fn collect_fat(image: &RawImage, note: Note) {
    let mut raw_evidence = Vec::new();
    image.walk_all_chains(&mut raw_evidence);
    // Report any invalid sentinel entries (e.g. INVALID_SECTOR) inside the
    // FAT itself.
    for (sector, entry) in image.fat.iter().enumerate() {
        if let Some(consts::INVALID_SECTOR) = *entry {
            note(
                Structure::Fat,
                DamageKind::OutOfBounds,
                image.fat_entry_for_sector(sector as u32),
                format!(
                    "sector {} has invalid FAT entry 0x{:08X}",
                    sector,
                    consts::INVALID_SECTOR
                ),
                STEP_OOB,
            );
        }
    }
    for (structure, kind, offset, context, tag) in raw_evidence {
        note(structure, kind, offset, context, tag);
    }
}

//===========================================================================//
// DIFAT: duplicated or out-of-range FAT sector pointers, and DIFAT chains
// that cycle.
//===========================================================================//

fn collect_difat(image: &RawImage, note: Note) {
    // Duplicate FAT sector entries within the combined DIFAT (header array
    // plus DIFAT sectors).
    let mut seen: FnvHashMap<u32, u64> = FnvHashMap::default();
    let mut header_index = 0usize;
    for (flat_index, &fat_sector) in
        image.fat_sector_ids.iter().enumerate()
    {
        let offset = difat_entry_offset(image, flat_index);
        if fat_sector == consts::FREE_SECTOR
            || fat_sector > consts::MAX_REGULAR_SECTOR
        {
            header_index += 1;
            continue;
        }
        if fat_sector as u64 >= image.num_sectors as u64 {
            note(
                Structure::Difat,
                DamageKind::OutOfBounds,
                offset,
                format!(
                    "DIFAT entry {} names FAT sector {} beyond the file",
                    flat_index, fat_sector
                ),
                STEP_FRESH_FAT,
            );
        }
        if let Some(&first_offset) = seen.get(&fat_sector) {
            note(
                Structure::Difat,
                DamageKind::DoubleOccupancy,
                offset,
                format!(
                    "DIFAT lists FAT sector {} twice (first at file byte {})",
                    fat_sector, first_offset
                ),
                STEP_FRESH_FAT,
            );
        } else {
            seen.insert(fat_sector, offset.unwrap_or(0));
        }
        let _ = header_index;
    }

    // A DIFAT sector chain that points back into itself never terminates.
    if let Some(cycled) = image.difat_cycle {
        note(
            Structure::Difat,
            DamageKind::Cycle,
            image
                .difat_sector_ids
                .last()
                .map(|s| difat_sector_next_offset(image, *s)),
            format!("DIFAT chain enters a cycle at sector {}", cycled),
            STEP_FRESH_FAT,
        );
    } else if let Some(next) = image.difat_next_after_last {
        if next != consts::END_OF_CHAIN && next != consts::FREE_SECTOR {
            note(
                Structure::Difat,
                DamageKind::OutOfBounds,
                image
                    .difat_sector_ids
                    .last()
                    .map(|s| difat_sector_next_offset(image, *s)),
                format!(
                    "DIFAT chain continues past readable sectors to {}",
                    next
                ),
                STEP_FRESH_FAT,
            );
        }
    }
}

fn difat_entry_offset(image: &RawImage, flat_index: usize) -> Option<u64> {
    if flat_index < consts::NUM_DIFAT_ENTRIES_IN_HEADER {
        return Some(76 + 4 * flat_index as u64);
    }
    let within = flat_index - consts::NUM_DIFAT_ENTRIES_IN_HEADER;
    let entries_per_sector = image.sector_len as usize / 4 - 1;
    let difat_sector_index = within / entries_per_sector;
    let slot = within % entries_per_sector;
    let sector = *image.difat_sector_ids.get(difat_sector_index)?;
    Some(RawImage::sector_offset(image.sector_len, sector) + 4 * slot as u64)
}

fn difat_sector_next_offset(image: &RawImage, sector: u32) -> u64 {
    RawImage::sector_offset(image.sector_len, sector) + image.sector_len - 4
}

//===========================================================================//
// Directory chain: truncated chain, and sibling-tree defects in entries.
//===========================================================================//

fn collect_directory(image: &RawImage, note: Note) {
    // The walk stopping before reaching END_OF_CHAIN means truncation (an
    // out-of-range or duplicate sector, or an unreadable FAT entry).
    let last_points_to = image
        .dir_chain
        .last()
        .and_then(|&sector| {
            image.fat.get(sector as usize).copied().flatten()
        });
    if image.dir_chain_truncated
        || (!image.dir_chain.is_empty()
            && last_points_to != Some(consts::END_OF_CHAIN)
            && last_points_to != Some(consts::FREE_SECTOR))
    {
        let after_last = image.dir_chain.last().copied();
        let next = after_last
            .and_then(|s| image.fat.get(s as usize).copied().flatten())
            .unwrap_or(consts::END_OF_CHAIN);
        let kind = if next != consts::END_OF_CHAIN
            && (next as u64 >= image.num_sectors as u64
                || next > consts::MAX_REGULAR_SECTOR)
        {
            DamageKind::OutOfBounds
        } else if next != consts::END_OF_CHAIN
            && image.dir_chain.contains(&next)
        {
            DamageKind::Cycle
        } else {
            DamageKind::OutOfBounds
        };
        note(
            Structure::Directory,
            kind,
            after_last.and_then(|s| image.fat_entry_for_sector(s)),
            format!(
                "directory chain ends early after sector {} (next is {})",
                after_last.unwrap_or(0),
                next
            ),
            STEP_DIR,
        );
    }

    // Truncated directory: the root or named entries reference stream IDs
    // beyond what the (shortened) directory chain provides.
    for raw in image.dir_entries.iter() {
        for &sibling in
            [raw.entry.left_sibling, raw.entry.right_sibling, raw.entry.child]
            .iter()
        {
            if sibling != consts::NO_STREAM
                && sibling as usize >= image.dir_entries.len()
            {
                note(
                    Structure::Directory,
                    DamageKind::OutOfBounds,
                    Some(raw.offset + 68),
                    format!(
                        "directory entry {} ({:?}) references missing entry {}",
                        raw.stream_id, raw.entry.name, sibling
                    ),
                    STEP_DIR,
                );
            }
        }
    }
}

//===========================================================================//
// MiniFAT: cycles, out-of-bounds mini sectors, double occupancy, and mini
// chains that run past the mini stream.
//===========================================================================//

impl RawImage {
    fn mini_stream_len(&self) -> u64 {
        self.dir_entries
            .first()
            .filter(|raw| raw.stream_id == consts::ROOT_STREAM_ID)
            .map(|raw| raw.entry.stream_len)
            .unwrap_or(0)
    }

    fn minifat_entry_offset(&self, mini_sector: u32) -> Option<u64> {
        let entries_per_sector = self.sector_len as usize / 4;
        let chain_index = mini_sector as usize / entries_per_sector;
        let slot = mini_sector as usize % entries_per_sector;
        let sector = *self.minifat_chain.get(chain_index)?;
        Some(
            RawImage::sector_offset(self.sector_len, sector)
                + 4 * slot as u64,
        )
    }

    /// Walks one mini chain, returning its mini sector IDs and pushing any
    /// defects: cycles, out-of-range mini sectors, and double occupancy.
    fn walk_mini_chain(
        &self,
        start: u32,
        owner: String,
        claimed: &mut FnvHashMap<u32, String>,
        raw_evidence: &mut Vec<(
            Structure,
            DamageKind,
            Option<u64>,
            String,
            &'static str,
        )>,
    ) -> Vec<u32> {
        let mut ids = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ids;
        }
        let mut local: FnvHashSet<u32> = FnvHashSet::default();
        let mut current = start;
        loop {
            if current as usize >= self.minifat.len() {
                raw_evidence.push((
                    Structure::MiniFat,
                    DamageKind::OutOfBounds,
                    ids.last()
                        .and_then(|s| self.minifat_entry_offset(*s)),
                    format!(
                        "{}: mini sector {} is beyond the MiniFAT",
                        owner, current
                    ),
                    STEP_MINIFAT,
                ));
                return ids;
            }
            if let Some(first_owner) = claimed.get(&current) {
                raw_evidence.push((
                    Structure::MiniFat,
                    DamageKind::DoubleOccupancy,
                    self.minifat_entry_offset(current),
                    format!(
                        "mini sector {} is used by both {} and {}",
                        current, first_owner, owner
                    ),
                    STEP_MINIFAT,
                ));
                return ids;
            }
            claimed.insert(current, owner.clone());
            local.insert(current);
            ids.push(current);

            let Some(entry) = self.minifat[current as usize] else {
                raw_evidence.push((
                    Structure::MiniFat,
                    DamageKind::OutOfBounds,
                    self.minifat_entry_offset(current),
                    format!(
                        "{}: mini sector {} has no readable MiniFAT entry",
                        owner, current
                    ),
                    STEP_MINIFAT,
                ));
                return ids;
            };
            if entry == consts::END_OF_CHAIN || entry == consts::FREE_SECTOR {
                return ids;
            }
            if entry > consts::MAX_REGULAR_SECTOR {
                raw_evidence.push((
                    Structure::MiniFat,
                    DamageKind::OutOfBounds,
                    self.minifat_entry_offset(current),
                    format!(
                        "{}: mini sector {} points to invalid {}",
                        owner, current, entry
                    ),
                    STEP_MINIFAT,
                ));
                return ids;
            }
            if local.contains(&entry) {
                raw_evidence.push((
                    Structure::MiniFat,
                    DamageKind::Cycle,
                    self.minifat_entry_offset(current),
                    format!(
                        "{}: mini sector {} loops back to {}",
                        owner, current, entry
                    ),
                    STEP_MINIFAT,
                ));
                return ids;
            }
            current = entry;
        }
    }
}

fn collect_minifat(image: &RawImage, note: Note) {
    let mini_stream_len = image.mini_stream_len();
    let mini_sectors_available =
        mini_stream_len / consts::MINI_SECTOR_LEN as u64;
    let mut claimed: FnvHashMap<u32, String> = FnvHashMap::default();
    let mut raw_evidence: Vec<(
        Structure,
        DamageKind,
        Option<u64>,
        String,
        &'static str,
    )> = Vec::new();
    for raw in image.dir_entries.iter() {
        if raw.entry.obj_type != ObjType::Stream
            || raw.entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
        {
            continue;
        }
        let owner = format!(
            "mini stream {:?} (entry {})",
            raw.entry.name, raw.stream_id
        );
        let ids = image.walk_mini_chain(
            raw.entry.start_sector,
            owner,
            &mut claimed,
            &mut raw_evidence,
        );
        // Mini stream bounds: a mini sector beyond the root stream's length.
        if let Some(&beyond) = ids
            .iter()
            .find(|&&id| (id as u64) >= mini_sectors_available)
        {
            note(
                Structure::MiniFat,
                DamageKind::OutOfBounds,
                image.minifat_entry_offset(beyond),
                format!(
                    "{:?}: mini sector {} lies outside the {}-byte mini stream",
                    raw.entry.name, beyond, mini_stream_len
                ),
                STEP_MINIFAT,
            );
        }
    }
    for (structure, kind, offset, context, tag) in raw_evidence {
        note(structure, kind, offset, context, tag);
    }

    // Orphan mini sectors: allocated MiniFAT entries claimed by no mini chain.
    for (mini_sector, entry) in image.minifat.iter().enumerate() {
        if let Some(value) = *entry {
            if value != consts::FREE_SECTOR
                && !claimed.contains_key(&(mini_sector as u32))
            {
                note(
                    Structure::MiniFat,
                    DamageKind::Orphan,
                    image.minifat_entry_offset(mini_sector as u32),
                    format!(
                        "mini sector {} is allocated but used by no stream",
                        mini_sector
                    ),
                    STEP_MINIFAT,
                );
            }
        }
    }
}

//===========================================================================//
// Orphan regular sectors and declared-length mismatches.
//===========================================================================//

fn collect_orphans(image: &RawImage, note: Note) {
    let mut raw_evidence = Vec::new();
    let claimed = image.walk_all_chains(&mut raw_evidence);
    // walk_all_chains duplicates chain evidence found in collect_fat, but
    // evidence is deduplicated after sorting, so this is harmless and keeps
    // ownership logic in one place.
    for sector in 0..image.num_sectors {
        let Some(entry) = image.fat.get(sector as usize).copied().flatten()
        else {
            continue;
        };
        let is_metadata = image.fat_sector_ids.contains(&sector)
            || image.difat_sector_ids.contains(&sector);
        let looks_allocated = entry != consts::FREE_SECTOR
            && entry != consts::FAT_SECTOR
            && entry != consts::DIFAT_SECTOR;
        if looks_allocated && !is_metadata && !claimed.contains(&sector) {
            note(
                Structure::Fat,
                DamageKind::Orphan,
                image.fat_entry_for_sector(sector),
                format!(
                    "sector {} (FAT entry 0x{:08X}) is reachable from no chain",
                    sector, entry
                ),
                STEP_ORPHAN,
            );
        }
    }
}

fn collect_lengths(image: &RawImage, note: Note) {
    let mut raw_evidence = Vec::new();
    // Re-walk chains to learn each stream entry's safe sector count.
    let mut claimed: FnvHashMap<u32, String> = FnvHashMap::default();
    for (start, owner) in image.chain_roots() {
        image.walk_fat_chain(start, owner, &mut claimed, &mut raw_evidence);
    }
    let mini_stream_len = image.mini_stream_len();
    let mini_sectors_available =
        mini_stream_len / consts::MINI_SECTOR_LEN as u64;
    let mut mini_claimed: FnvHashMap<u32, String> = FnvHashMap::default();
    let mut mini_raw = Vec::new();
    for raw in image.dir_entries.iter() {
        if raw.entry.obj_type != ObjType::Stream
            || raw.entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
        {
            continue;
        }
        let owner = format!("{:?}", raw.entry.name);
        let ids = image.walk_mini_chain(
            raw.entry.start_sector,
            owner,
            &mut mini_claimed,
            &mut mini_raw,
        );
        let available_capacity = ids
            .iter()
            .filter(|&&id| (id as u64) < mini_sectors_available)
            .count()
            * consts::MINI_SECTOR_LEN;
        if raw.entry.stream_len > available_capacity as u64 {
            note(
                Structure::MiniFat,
                DamageKind::LengthMismatch,
                Some(raw.offset + 120),
                format!(
                    "{:?} declares {} bytes but its mini chain holds {}",
                    raw.entry.name,
                    raw.entry.stream_len,
                    available_capacity
                ),
                STEP_LEN,
            );
        }
    }

    // Regular streams.
    for raw in image.dir_entries.iter() {
        if raw.entry.obj_type != ObjType::Stream
            || raw.entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
        {
            continue;
        }
        let start = raw.entry.start_sector;
        let mut claimed_for_stream: FnvHashMap<u32, String> =
            FnvHashMap::default();
        let ids = image.walk_fat_chain(
            start,
            ChainOwner::Stream(raw.stream_id),
            &mut claimed_for_stream,
            &mut Vec::new(),
        );
        let capacity = ids.len() as u64 * image.sector_len;
        if raw.entry.stream_len > capacity
            || raw.entry.stream_len + image.sector_len - 1 < capacity
                && capacity.saturating_sub(raw.entry.stream_len)
                    >= image.sector_len
        {
            // The first condition (declared longer than the chain) is the
            // substantive mismatch; a chain longer than needed by a full
            // sector is reported as well.
            note(
                Structure::Fat,
                DamageKind::LengthMismatch,
                Some(raw.offset + 120),
                format!(
                    "{:?} declares {} bytes but its chain holds {}",
                    raw.entry.name, raw.entry.stream_len, capacity
                ),
                STEP_LEN,
            );
        }
    }
}
