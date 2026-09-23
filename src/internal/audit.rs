//! Opt-in structural auditing and read-only repair planning for the FAT,
//! DIFAT, MiniFAT, and directory chains of a Compound File Binary file.
//!
//! This module never opens or mutates a compound file: it works purely from
//! the input bytes.  Parsing the header reuses the production [`Header`]
//! parser; the rest of the analysis re-reads the allocation tables itself,
//! because it must keep going after corruption that makes the normal open
//! path fail early.  A repair [`Plan`] records byte-level edits together with
//! a digest of the planned input; [`Plan::apply`] refuses to write anything
//! unless the input still matches that digest.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::consts;
use crate::internal::Header;

// Header field offsets (MS-CFB 2.2), also used as first-violation locations.
const OFF_NUM_DIR_SECTORS: u64 = 40;
const OFF_NUM_FAT_SECTORS: u64 = 44;
const OFF_FIRST_DIR_SECTOR: u64 = 48;
const OFF_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFF_NUM_MINIFAT_SECTORS: u64 = 64;
const OFF_FIRST_DIFAT_SECTOR: u64 = 68;
const OFF_NUM_DIFAT_SECTORS: u64 = 72;
const OFF_DIFAT_ENTRIES_START: u64 = 76;
const DIR_ENTRY_OBJTYPE_OFF: u64 = 66;
const DIR_ENTRY_LEFT_OFF: u64 = 68;
const DIR_ENTRY_RIGHT_OFF: u64 = 72;
const DIR_ENTRY_CHILD_OFF: u64 = 76;
const DIR_ENTRY_START_OFF: u64 = 116;
const DIR_ENTRY_LEN_OFF: u64 = 120;

/// Which allocation structure a piece of damage was found in.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Layer {
    /// The Double-Indirect FAT (the chain of FAT-sector pointers).
    Difat,
    /// The File Allocation Table (sector chains).
    Fat,
    /// The MiniFAT (mini-sector chains inside the mini stream).
    MiniFat,
    /// The directory chain or the directory-entry tree.
    Directory,
}

/// The kind of allocation-chain damage.  The failure classes are kept
/// distinct so callers can tell cycles, out-of-bounds entries, duplicate
/// claims, orphans, and length inconsistencies apart.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Kind {
    /// A chain points back into a sector already on the same chain.
    Cycle,
    /// A chain entry or starting sector is out of range or invalid.
    OutOfBounds,
    /// Two distinct chains claim the same sector or mini-sector.
    DuplicateClaim,
    /// A usable sector/mini-sector is unreachable from any chain root.
    Orphan,
    /// A declared stream length disagrees with the reachable chain.
    LengthMismatch,
    /// The directory chain stops before all directory entries are present.
    TruncatedDirectory,
}

/// A single piece of damage evidence, located at the first offending byte.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Finding {
    /// Allocation structure the damage lives in.
    pub layer: Layer,
    /// Distinct failure class.
    pub kind: Kind,
    /// Byte offset of the first offending field in the input file.
    pub offset: u64,
    /// Human-readable evidence, with offending sector IDs and context.
    pub message: String,
}

impl Finding {
    fn new(
        layer: Layer,
        kind: Kind,
        offset: u64,
        message: String,
    ) -> Finding {
        Finding { layer, kind, offset, message }
    }
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} {:?} at byte {}: {}",
            self.layer, self.kind, self.offset, self.message
        )
    }
}

/// A single planned byte replacement, bound to the bytes on the planned input.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Edit {
    /// Absolute byte offset in the file.
    pub offset: u64,
    /// Bytes expected at that offset on the planned input.
    pub before: Vec<u8>,
    /// Bytes to write when applying the plan.
    pub after: Vec<u8>,
}

/// A read-only repair plan bound to one exact input via a digest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plan {
    /// Hex FNV-1a 128 digest of the input the plan was made for.
    pub precondition_digest: String,
    /// Ordered byte-level edits.
    pub edits: Vec<Edit>,
}

impl Plan {
    /// Returns the digest the input must still match for this plan to apply.
    pub fn precondition_digest(&self) -> &str {
        &self.precondition_digest
    }

    /// Returns the planned byte-level edits (never applied here).
    pub fn edits(&self) -> &[Edit] {
        &self.edits
    }
}

/// The result of an opt-in structural audit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Report {
    /// CFB version number (3 or 4).
    pub version: u16,
    /// Damage evidence, sorted by first-violation offset.
    pub findings: Vec<Finding>,
}

impl Report {
    /// Returns true if no damage was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
}

impl std::fmt::Display for Report {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_clean() {
            return write!(f, "CFB v{} audit: clean", self.version);
        }
        writeln!(
            f,
            "CFB v{} audit: {} finding(s):",
            self.version,
            self.findings.len()
        )?;
        for finding in self.findings.iter() {
            writeln!(f, "  - {}", finding)?;
        }
        Ok(())
    }
}

/// A report bundled with the repair plan computed for its input.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReportWithPlan {
    /// The audit report.
    pub report: Report,
    /// The repair plan, or `None` for a clean file.
    pub plan: Option<Plan>,
}

//===========================================================================//

fn u32le(data: &[u8], offset: u64) -> u32 {
    let index = offset as usize;
    u32::from_le_bytes([
        data[index],
        data[index + 1],
        data[index + 2],
        data[index + 3],
    ])
}

fn u64le(data: &[u8], offset: u64) -> u64 {
    let index = offset as usize;
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&data[index..index + 8]);
    u64::from_le_bytes(bytes)
}

fn is_special(value: u32) -> bool {
    value >= consts::MAX_REGULAR_SECTOR
}

fn is_regular_pointer(value: u32) -> bool {
    value <= consts::MAX_REGULAR_SECTOR
}

//===========================================================================//

/// Where a directory entry lives in the file.
#[derive(Clone, Copy)]
struct RawEntry {
    /// Stream ID (directory-entry index across the directory chain).
    stream_id: u32,
    /// Sector the entry is in.
    sector_id: u32,
    /// Offset of the entry's first byte.
    offset: u64,
}

/// A root claiming sectors through the FAT.  Walked in priority order; when
/// two chains claim the same sector, the earlier owner keeps it.
#[derive(Clone)]
struct Owner {
    /// Starting sector field offset (for start-field duplicate evidence).
    start_offset: u64,
    /// Declared stream length, if this owner has one.
    declared_len: Option<u64>,
    /// Allocation layer the owner belongs to.
    layer: Layer,
    /// Label for evidence messages.
    label: String,
}

struct Engine<'a> {
    data: &'a [u8],
    sector_len: u64,
    num_sectors: u32,

    // Working copies of the allocation tables, mutated to model repairs.
    fat: Vec<u32>,
    minifat: Vec<u32>,
    difat: Vec<u32>,

    // Header fields.
    first_dir_sector: u32,
    first_minifat_sector: u32,
    num_minifat_sectors: u32,
    hdr_num_dir_sectors: u32,
    hdr_num_fat_sectors: u32,
    hdr_num_difat_sectors: u32,
    first_difat_sector: u32,

    // Analysis state.
    findings: BTreeSet<Finding>,
    edits: BTreeMap<u64, Edit>,
    /// FAT sector ids claimed by the DIFAT (header + DIFAT chain).
    fat_sector_ids: BTreeSet<u32>,
    /// DIFAT sector ids in chain order.
    difat_sector_ids: Vec<u32>,
    /// Directory entries reached by the directory chain.
    dir_entries: Vec<RawEntry>,
    /// Directory sector ids in chain order.
    dir_sector_ids: Vec<u32>,
    /// MiniFAT sector ids in chain order.
    minifat_sector_ids: Vec<u32>,
}

impl<'a> Engine<'a> {
    fn sector_offset(&self, sector_id: u32, within: u64) -> u64 {
        (sector_id as u64 + 1) * self.sector_len + within
    }

    fn add_finding(&mut self, finding: Finding) {
        self.findings.insert(finding);
    }

    /// Records a planned 4-byte edit (a FAT/MiniFAT/DIFAT/header u32).
    fn edit_u32(&mut self, offset: u64, before: u32, after: u32) {
        if before == after {
            return;
        }
        self.edits.insert(
            offset,
            Edit {
                offset,
                before: before.to_le_bytes().to_vec(),
                after: after.to_le_bytes().to_vec(),
            },
        );
    }

    /// Records a planned 8-byte edit (a directory-entry stream length).
    fn edit_u64(&mut self, offset: u64, before: u64, after: u64) {
        if before == after {
            return;
        }
        self.edits.insert(
            offset,
            Edit {
                offset,
                before: before.to_le_bytes().to_vec(),
                after: after.to_le_bytes().to_vec(),
            },
        );
    }

    fn fat_slot_offset(&self, slot: u32) -> u64 {
        let entries_per_sector = self.sector_len / 4;
        let fat_sector =
            self.difat[(slot / entries_per_sector as u32) as usize];
        self.sector_offset(
            fat_sector,
            (slot % entries_per_sector as u32) as u64 * 4,
        )
    }

    fn minifat_slot_offset(&self, slot: u32) -> Option<u64> {
        let entries_per_sector = self.sector_len / 4;
        let sector_index = slot / entries_per_sector as u32;
        let sector_id =
            *self.minifat_sector_ids.get(sector_index as usize)?;
        Some(self.sector_offset(
            sector_id,
            (slot % entries_per_sector as u32) as u64 * 4,
        ))
    }

    fn dir_entry_offset(&self, stream_id: u32) -> u64 {
        let entries_per_sector = self.sector_len / 128;
        let sector_index = stream_id / entries_per_sector as u32;
        let sector_id = self.dir_sector_ids[sector_index as usize];
        self.sector_offset(
            sector_id,
            (stream_id % entries_per_sector as u32) as u64 * 128,
        )
    }
}
