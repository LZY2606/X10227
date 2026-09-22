// Fail-soft, read-only structural analysis of CFB bytes.
//
// The normal opening path (`CompoundFile::open`) is a *mutable* consumer of a
// file: under Permissive validation it repairs table entries in memory, and
// under Strict validation it rejects the whole file on the first violation.
// The audit must instead (a) never modify the input, (b) keep going past the
// first violation so every corruption category is reported separately, and
// (c) survive damage that prevents the file opening at all.
//
// To avoid maintaining a second copy of the format grammar, the audit reuses
// the production parser for the header (`Header::read_from`) and the exact
// production on-disk layout constants and offsets (`internal::consts`).  The
// traversal and diagnosis logic in this file is itself production code: it
// is the single implementation behind both the public audit entry points and
// the verifier that validates a staged repair; there is no test-only copy.

use std::collections::{BTreeMap, BTreeSet};

use crate::internal::consts;
use crate::internal::{Header, ObjType, Validation, Version};
use crate::ReadLeNumber;

use super::model::{CorruptionKind, Finding, FindingLocation, Table};

//===========================================================================//

/// A raw, unvalidated directory slot, read straight from the bytes.
#[derive(Clone, Debug)]
pub(super) struct RawEntry {
    pub name: String,
    pub obj_type: ObjType,
    pub child: u32,
    pub left_sibling: u32,
    pub right_sibling: u32,
    pub start_sector: u32,
    pub stream_len: u64,
}

/// Everything the audit managed to parse from the file bytes.
pub(super) struct ParsedFile {
    pub version: Version,
    pub sector_len: u64,
    pub num_sectors: u32,
    pub num_fat_sectors_header: u32,
    pub num_difat_sectors_header: u32,
    pub num_minifat_sectors_header: u32,
    pub first_dir_sector: u32,
    pub first_minifat_sector: u32,
    /// DIFAT entries (header array first, then DIFAT sectors), raw.
    pub difat: Vec<u32>,
    /// DIFAT sector IDs in chain order (as far as walkable).
    pub difat_sector_ids: Vec<u32>,
    /// If the DIFAT chain loops back, the last reachable sector (its
    /// next-sector slot closes the loop); otherwise None.
    pub difat_cycle_from: Option<u32>,
    /// If the DIFAT chain points past end of file, (from-sector, target).
    pub difat_oob: Option<(u32, u32)>,
    /// FAT sector IDs in DIFAT order.
    pub fat_sector_ids: Vec<u32>,
    /// Raw FAT entries, one per file sector (padded/truncated as needed).
    pub fat: Vec<u32>,
    /// Whether FAT reading was cut off because a DIFAT slot pointed OOB.
    pub fat_read_cut: bool,
    /// Directory slots in directory-chain order, with parse errors recorded.
    pub entries: Vec<RawEntry>,
    /// Stream IDs whose 128-byte slot could not be parsed.
    pub malformed_entries: Vec<(u32, u64, String)>,
    /// Whether the directory chain was cut off early (cycle/OOB/truncation).
    pub directory_chain_cut: bool,
    /// The number of directory sectors actually walked.
    pub directory_sector_count: u32,
    /// Directory sector IDs in chain order (as far as walkable).
    pub dir_sector_ids: Vec<u32>,
    /// MiniFAT sector IDs in chain order (as far as walkable).
    pub minifat_sector_ids: Vec<u32>,
    /// Raw MiniFAT entries.
    pub minifat: Vec<u32>,
    /// Whether reading the MiniFAT chain was cut off.
    pub minifat_read_cut: bool,
}

/// A finding plus the in-place byte patches that repair it (may be empty).
#[derive(Clone, Debug)]
pub(super) struct RawFinding {
    pub kind: CorruptionKind,
    pub table: Table,
    pub index: u32,
    pub stream_id: Option<u32>,
    pub byte_offset: u64,
    pub target: Option<u32>,
    pub detail: String,
    pub patches: Vec<(u64, Vec<u8>)>,
    /// True if this corruption cannot be repaired safely in place.
    pub repairable: bool,
}

impl RawFinding {
    fn finding(&self, id: usize) -> Finding {
        Finding {
            id,
            kind: self.kind,
            location: FindingLocation {
                table: self.table,
                index: self.index,
                stream_id: self.stream_id,
                byte_offset: self.byte_offset,
            },
            target: self.target,
            detail: self.detail.clone(),
        }
    }
}

fn u32le(value: u32) -> Vec<u8> {
    value.to_le_bytes().to_vec()
}

fn u64le(value: u64) -> Vec<u8> {
    value.to_le_bytes().to_vec()
}

/// Byte offset of FAT entry `sector` within the file.
pub(super) fn fat_entry_offset(sector_len: u64, fat_sector_ids: &[u32], sector: u32) -> Option<u64> {
    let entries_per_sector = sector_len / 4;
    let fat_sector_index = (sector / entries_per_sector as u32) as usize;
    let within = sector % entries_per_sector as u32;
    let fat_sector_id = *fat_sector_ids.get(fat_sector_index)?;
    Some((u64::from(fat_sector_id) + 1) * sector_len + u64::from(within) * 4)
}

/// Byte offset of MiniFAT entry `mini_sector`.
pub(super) fn minifat_entry_offset(
    sector_len: u64,
    minifat_sector_ids: &[u32],
    mini_sector: u32,
) -> Option<u64> {
    let entries_per_sector = sector_len / 4;
    let fat_sector_index = (mini_sector / entries_per_sector as u32) as usize;
    let within = mini_sector % entries_per_sector as u32;
    let sector_id = *minifat_sector_ids.get(fat_sector_index)?;
    Some((u64::from(sector_id) + 1) * sector_len + u64::from(within) * 4)
}

/// Byte offset of the `field` u32 within directory stream ID `stream_id`.
fn dir_field_offset(
    sector_len: u64,
    dir_sector_ids: &[u32],
    entries_per_sector: u32,
    stream_id: u32,
    field: u64,
) -> Option<u64> {
    let sector_index = (stream_id / entries_per_sector) as usize;
    let within = stream_id % entries_per_sector;
    let sector_id = (*dir_sector_ids.get(sector_index)?) as u64;
    Some(
        (sector_id + 1) * sector_len
            + u64::from(within) * consts::DIR_ENTRY_LEN as u64
            + field,
    )
}

fn is_data_entry(value: u32) -> bool {
    value <= consts::MAX_REGULAR_SECTOR
}

//===========================================================================//
// Parsing
//===========================================================================//

fn read_u32_at(data: &[u8], offset: u64) -> Option<u32> {
    let start = offset as usize;
    let bytes = data.get(start..start + 4)?;
    Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
}

/// Parses what can be parsed from `data`.  Returns `Err` only when there is
/// not enough structure to audit at all; otherwise returns the parsed view
/// even if parts of it had to be given up on.
pub(super) fn parse(data: &[u8]) -> std::io::Result<ParsedFile> {
    if (data.len() as u64) < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Cannot audit CFB input ({} bytes is smaller than the {} byte \
             header)",
            data.len(),
            consts::HEADER_LEN
        );
    }
    let mut header_cursor = &data[..consts::HEADER_LEN];
    let header = match Header::read_from(&mut header_cursor, Validation::Permissive) {
        Ok(header) => header,
        Err(err) => {
            invalid_data!("Cannot audit CFB input (invalid header: {err})");
        }
    };
    let sector_len = header.version.sector_len() as u64;
    if (data.len() as u64) < sector_len {
        invalid_data!(
            "Cannot audit CFB input ({} bytes is smaller than one {} byte \
             sector)",
            data.len(),
            sector_len
        );
    }
    let num_sectors = ((data.len() as u64 + sector_len - 1) / sector_len - 1)
        as u32;

    // ---- Walk the DIFAT chain, bounded by the file's sector count. ----
    let mut difat: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();
    let mut difat_sector_ids: Vec<u32> = Vec::new();
    let mut difat_cycle_from: Option<u32> = None;
    let mut difat_oob: Option<(u32, u32)> = None;
    let mut current = header.first_difat_sector;
    let mut seen = BTreeSet::new();
    while is_data_entry(current) {
        if current >= num_sectors {
            difat_oob = Some((
                difat_sector_ids.last().copied().unwrap_or(consts::END_OF_CHAIN),
                current,
            ));
            break;
        }
        if !seen.insert(current) {
            difat_cycle_from = difat_sector_ids.last().copied();
            break;
        }
        difat_sector_ids.push(current);
        let sector_start = (u64::from(current) + 1) * sector_len;
        let entries_per_sector = (sector_len / 4) as u32;
        for slot in 0..entries_per_sector - 1 {
            if let Some(value) =
                read_u32_at(data, sector_start + u64::from(slot) * 4)
            {
                difat.push(value);
            }
        }
        match read_u32_at(data, sector_start + sector_len - 4) {
            Some(next) => current = next,
            None => {
                difat_oob = Some((current, consts::INVALID_SECTOR));
                break;
            }
        }
    }
    // Drop the FREE_SECTOR tail padding, keeping any interior corruption.
    while difat.last() == Some(&consts::FREE_SECTOR) {
        difat.pop();
    }
    let mut fat_sector_ids = Vec::with_capacity(difat.len());
    for &sector in &difat {
        if is_data_entry(sector) {
            fat_sector_ids.push(sector);
        }
    }

    // ---- Read the FAT. ----
    let mut fat = Vec::new();
    let mut fat_read_cut = false;
    let entries_per_sector = (sector_len / 4) as u32;
    for &fat_sector in &fat_sector_ids {
        if fat_sector >= num_sectors {
            fat_read_cut = true;
            break;
        }
        let sector_start = (u64::from(fat_sector) + 1) * sector_len;
        for slot in 0..entries_per_sector {
            match read_u32_at(data, sector_start + u64::from(slot) * 4) {
                Some(value) => fat.push(value),
                None => {
                    fat_read_cut = true;
                    break;
                }
            }
        }
    }
    if fat.len() < num_sectors as usize {
        fat.resize(num_sectors as usize, consts::FREE_SECTOR);
    } else {
        fat.truncate(num_sectors as usize);
    }

    let parsed = ParsedFile {
        version: header.version,
        sector_len,
        num_sectors,
        num_fat_sectors_header: header.num_fat_sectors,
        num_difat_sectors_header: header.num_difat_sectors,
        num_minifat_sectors_header: header.num_minifat_sectors,
        first_dir_sector: header.first_dir_sector,
        first_minifat_sector: header.first_minifat_sector,
        difat,
        difat_sector_ids,
        difat_cycle_from,
        difat_oob,
        fat_sector_ids,
        fat,
        fat_read_cut,
        entries: Vec::new(),
        malformed_entries: Vec::new(),
        directory_chain_cut: false,
        directory_sector_count: 0,
        dir_sector_ids: Vec::new(),
        minifat_sector_ids: Vec::new(),
        minifat: Vec::new(),
        minifat_read_cut: false,
    };
    let mut parsed = parsed;

    read_directory(&mut parsed, data);
    read_minifat(&mut parsed, data);
    Ok(parsed)
}

//===========================================================================//
// Directory and MiniFAT reading
//===========================================================================//

/// Reads a single directory slot permissively; returns the parse error text
/// without the strict-only name/CLSID/timestamp rules of `DirEntry`.
fn read_raw_entry(
    data: &[u8],
    offset: u64,
    version: Version,
) -> Result<RawEntry, String> {
    let slot = data
        .get(offset as usize..offset as usize + consts::DIR_ENTRY_LEN)
        .ok_or_else(|| "directory slot runs past end of file".to_string())?;
    let mut cursor = &slot[..];
    let mut name_chars = [0u16; 32];
    for ch in name_chars.iter_mut() {
        *ch = cursor.read_le_u16().map_err(|e| e.to_string())?;
    }
    let name_len_bytes = cursor.read_le_u16().map_err(|e| e.to_string())?;
    if name_len_bytes > 64 || name_len_bytes % 2 != 0 {
        return Err(format!("invalid name length {name_len_bytes}"));
    }
    let name_len_chars = if name_len_bytes > 0 {
        (name_len_bytes / 2 - 1) as usize
    } else {
        0
    };
    let name = String::from_utf16(&name_chars[..name_len_chars])
        .map_err(|_| "name is not valid UTF-16".to_string())?;
    let mut type_byte = [0u8];
    use std::io::Read as _;
    cursor.read_exact(&mut type_byte).map_err(|e| e.to_string())?;
    let obj_type = ObjType::from_byte(type_byte[0])
        .ok_or_else(|| format!("invalid object type {}", type_byte[0]))?;
    let mut color_byte = [0u8];
    cursor.read_exact(&mut color_byte).map_err(|e| e.to_string())?;
    let left_sibling = cursor.read_le_u32().map_err(|e| e.to_string())?;
    let right_sibling = cursor.read_le_u32().map_err(|e| e.to_string())?;
    let child = cursor.read_le_u32().map_err(|e| e.to_string())?;
    // CLSID (16), state bits (4), timestamps (16): skipped, but bounded.
    let mut skipped = [0u8; 16 + 4 + 16];
    cursor.read_exact(&mut skipped).map_err(|e| e.to_string())?;
    let start_sector = cursor.read_le_u32().map_err(|e| e.to_string())?;
    let raw_stream_len = cursor.read_le_u64().map_err(|e| e.to_string())?;
    let stream_len = raw_stream_len & version.stream_len_mask();
    Ok(RawEntry {
        name,
        obj_type,
        child,
        left_sibling,
        right_sibling,
        start_sector,
        stream_len,
    })
}

/// Walks the directory chain from the header, recording every slot and every
/// way the chain or its slots can be damaged.
fn read_directory(
    parsed: &mut ParsedFile,
    data: &[u8],
) -> Vec<u32> {
    let sector_len = parsed.sector_len;
    let entries_per_sector =
        (parsed.sector_len / consts::DIR_ENTRY_LEN as u64) as u32;
    let mut current = parsed.first_dir_sector;
    let mut seen = BTreeSet::new();
    let mut dir_sector_ids: Vec<u32> = Vec::new();
    while is_data_entry(current) {
        if current >= parsed.num_sectors {
            parsed.directory_chain_cut = true;
            break;
        }
        if !seen.insert(current) {
            parsed.directory_chain_cut = true;
            break;
        }
        dir_sector_ids.push(current);
        let sector_start = (u64::from(current) + 1) * sector_len;
        for slot in 0..entries_per_sector {
            let stream_id =
                parsed.entries.len() as u32 + slot;
            let offset =
                sector_start + u64::from(slot) * consts::DIR_ENTRY_LEN as u64;
            match read_raw_entry(data, offset, parsed.version) {
                Ok(entry) => parsed.entries.push(entry),
                Err(message) => {
                    parsed.malformed_entries.push((stream_id, offset, message));
                    // Keep slot count aligned with stream IDs.
                    parsed.entries.push(RawEntry {
                        name: String::new(),
                        obj_type: ObjType::Unallocated,
                        child: consts::NO_STREAM,
                        left_sibling: consts::NO_STREAM,
                        right_sibling: consts::NO_STREAM,
                        start_sector: consts::END_OF_CHAIN,
                        stream_len: 0,
                    });
                }
            }
        }
        let fat_index = current as usize;
        let next = if fat_index < parsed.fat.len() {
            parsed.fat[fat_index]
        } else {
            consts::FREE_SECTOR
        };
        current = next;
    }
    // A chain that ends on a free/invalid marker (rather than END_OF_CHAIN)
    // is truncated: it did not end deliberately.
    if !parsed.directory_chain_cut
        && parsed.first_dir_sector != consts::END_OF_CHAIN
        && parsed.first_dir_sector != consts::FREE_SECTOR
        && !dir_sector_ids.is_empty()
    {
        let last = *dir_sector_ids.last().unwrap();
        if let Some(&entry) = parsed.fat.get(last as usize) {
            if entry != consts::END_OF_CHAIN {
                parsed.directory_chain_cut = true;
            }
        }
    }
    parsed.directory_sector_count = dir_sector_ids.len() as u32;
    parsed.dir_sector_ids = dir_sector_ids.clone();
    dir_sector_ids
}

/// Walks the MiniFAT chain (via the FAT) and reads its entries.
fn read_minifat(parsed: &mut ParsedFile, data: &[u8]) {
    let sector_len = parsed.sector_len;
    let entries_per_sector = (sector_len / 4) as u32;
    let mut current = parsed.first_minifat_sector;
    let mut seen = BTreeSet::new();
    let mut minifat_sector_ids: Vec<u32> = Vec::new();
    while is_data_entry(current) {
        if current >= parsed.num_sectors || !seen.insert(current) {
            parsed.minifat_read_cut = true;
            break;
        }
        minifat_sector_ids.push(current);
        let sector_start = (u64::from(current) + 1) * sector_len;
        for slot in 0..entries_per_sector {
            match read_u32_at(data, sector_start + u64::from(slot) * 4) {
                Some(value) => parsed.minifat.push(value),
                None => {
                    parsed.minifat_read_cut = true;
                    break;
                }
            }
        }
        let next = parsed.fat.get(current as usize).copied();
        match next {
            Some(next) if next == consts::END_OF_CHAIN => break,
            Some(next) => current = next,
            None => {
                parsed.minifat_read_cut = true;
                break;
            }
        }
    }
    parsed.minifat_sector_ids = minifat_sector_ids;
}
