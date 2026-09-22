//! Opt-in, read-only structural audit of a compound file.
//!
//! This module is reached only through the crate's public entry points:
//! [`crate::OpenOptions::audit_with`], [`crate::OpenOptions::audit`], and the
//! [`audit`] and [`audit_path`] free functions.  An audit never writes to its
//! input: it reads the whole file once, walks the DIFAT, FAT, MiniFAT,
//! directory chain and every stream chain, and records the first violation
//! it finds at each location as a [`Finding`].
//!
//! Findings stay classified into distinct corruption types: chains that
//! revisit a sector ([`CorruptionKind::Cycle`]), pointers past the end of an
//! allocation table ([`CorruptionKind::OutOfBounds`]), sectors claimed by two
//! chains ([`CorruptionKind::DoubleOccupancy`]), sectors that no structure
//! references ([`CorruptionKind::OrphanSector`]), and declared lengths or
//! counts that disagree with what the chains actually contain
//! ([`CorruptionKind::LengthMismatch`]).
//!
//! When every finding can be addressed, the report carries a [`RepairPlan`].
//! The plan records a [`RepairPlan::precondition_digest`] over the exact
//! input bytes; it may be applied only to bytes that still match that
//! digest.  Plan construction and [`RepairPlan::preview`] are both
//! read-only; [`RepairPlan::dry_run`] is guaranteed to write nothing, and
//! [`RepairPlan::apply_to`] either replaces the whole image atomically (with
//! rollback on mid-write failure) or leaves the destination untouched.

use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::mem::size_of;
use std::path::Path;

use fnv::FnvHashMap;

use crate::internal::consts;
use crate::internal::{Header, ObjType, Validation, Version};

//==========================================================================//
// File identity digest (FNV-1a, 64 bit).  This is a local, dependency-free
// implementation; it is used only to detect that bytes changed between the
// audit and the explicit apply, never as a cryptographic guarantee.

const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = FNV_OFFSET_BASIS;
    for &byte in bytes.iter() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

// Byte offsets of the chain-length fields in the 512-byte CFB header.
const HDR_NUM_DIR_SECTORS: usize = 40;
const HDR_NUM_FAT_SECTORS: usize = 44;
const HDR_FIRST_DIR_SECTOR: usize = 48;
const HDR_FIRST_MINIFAT_SECTOR: usize = 60;
const HDR_NUM_MINIFAT_SECTORS: usize = 64;
const HDR_FIRST_DIFAT_SECTOR: usize = 68;
const HDR_NUM_DIFAT_SECTORS: usize = 72;
const HDR_DIFAT_ENTRIES: usize = 76;

// Byte offsets of fields within a 128-byte directory entry.
const DIR_OBJ_TYPE: usize = 66;
const DIR_LEFT_SIBLING: usize = 68;
const DIR_RIGHT_SIBLING: usize = 72;
const DIR_CHILD: usize = 76;
const DIR_START_SECTOR: usize = 116;
const DIR_STREAM_LEN: usize = 120;

//==========================================================================//

/// Which of a compound file's allocation structures a finding applies to.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum CorruptionTable {
    /// The Double-Indirect File Allocation Table chain.
    Difat,
    /// The File Allocation Table.
    Fat,
    /// The MiniFAT that chains 64-byte mini sectors together.
    MiniFat,
    /// The directory chain (the sectors holding directory entries), or the
    /// sibling/child tree between those entries.
    Directory,
}

/// The distinct categories of corruption an audit can find.
///
/// Cycles, out-of-bounds pointers, double occupancy, orphan sectors and
/// length disagreements are reported separately rather than collapsed into a
/// single "corrupt" verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum CorruptionKind {
    /// Following a chain revisits a sector it already visited.
    Cycle,
    /// A table entry points past the end of the table or past the file.
    OutOfBounds,
    /// Two chains (or a chain and a table structure) claim the same sector.
    DoubleOccupancy,
    /// A sector is marked in use but no structure references it.
    OrphanSector,
    /// A declared stream length or chain/table count disagrees with what the
    /// chains actually provide.
    LengthMismatch,
    /// A directory entry cannot be parsed as the object type and layout the
    /// spec requires.
    MalformedEntry,
    /// A FAT entry uses the reserved `INVALID_SECTOR` (0xFFFFFFFB) value.
    InvalidEntry,
}

/// One piece of corruption evidence, with the first violating position and
/// enough context to explain it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// The allocation structure involved.
    pub table: CorruptionTable,
    /// The corruption category.
    pub kind: CorruptionKind,
    /// Byte offset into the file of the first offending field, when known.
    pub offset: Option<u64>,
    /// The sector or mini sector where the violation starts, when known.
    pub sector: Option<u32>,
    /// Human-readable context, never just a boolean verdict.
    pub detail: String,
}

impl Finding {
    fn new(
        table: CorruptionTable,
        kind: CorruptionKind,
        offset: Option<u64>,
        sector: Option<u32>,
        detail: impl Into<String>,
    ) -> Finding {
        Finding { table, kind, offset, sector, detail: detail.into() }
    }
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} / {:?}: {}",
            self.table, self.kind, self.detail
        )?;
        if let Some(offset) = self.offset {
            write!(f, " (first violating byte at offset {})", offset)?;
        }
        Ok(())
    }
}

//==========================================================================//

/// One byte-level edit in a read-only repair plan.
///
/// A step is a fixed-width little-endian overwrite (four bytes for table
/// slots and directory entry fields, eight bytes for declared stream
/// lengths) at a fixed offset.  All planned repairs are this shape, so the
/// repaired image always keeps the input's exact length: no truncation or
/// growth is needed to apply a plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    /// Absolute byte offset in the file.
    pub offset: u64,
    /// The original bytes (little endian) that the audit read.
    pub original: Vec<u8>,
    /// The replacement bytes (little endian).
    pub replacement: Vec<u8>,
    /// What this edit means semantically (e.g. "sever FAT edge 5 -> 6").
    pub rationale: String,
}

impl std::fmt::Display for RepairStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "offset {}: {} -> {} ({})",
            self.offset,
            hex_bytes(&self.original),
            hex_bytes(&self.replacement),
            self.rationale
        )
    }
}

fn hex_bytes(bytes: &[u8]) -> String {
    let mut out = String::from("0x");
    for byte in bytes {
        out.push_str(&format!("{:02X}", byte));
    }
    out
}

/// A read-only, precondition-gated repair plan.
///
/// The plan owns the fully-repaired image (`repaired`), which is produced by
/// applying the byte-level [`RepairStep`]s to a private copy of the audit
/// input.  Constructing a plan never touches the input file, and
/// [`RepairPlan::preview`] also performs no I/O on the input.  Applying a
/// plan is explicit and gated on the input bytes still matching
/// [`RepairPlan::precondition_digest`].
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition_digest: u64,
    steps: Vec<RepairStep>,
    repaired: Vec<u8>,
}

impl RepairPlan {
    /// The FNV-1a digest (rendered as 16 hex digits) of the exact bytes the
    /// plan was built for.  A plan can only be applied while this still
    /// matches the destination.
    pub fn precondition_digest(&self) -> String {
        format!("{:016x}", self.precondition_digest)
    }

    /// The individual byte-level edits, in ascending offset order.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }

    /// The complete repaired image.  This copies from an in-memory buffer and
    /// writes nothing to the audited file.
    pub fn preview(&self) -> Vec<u8> {
        self.repaired.clone()
    }

    /// Checks the precondition without writing anything.
    ///
    /// Returns an [`io::ErrorKind::InvalidInput`] error if the destination no
    /// longer matches [`RepairPlan::precondition_digest`]; such an error is
    /// repeatable and belongs to the crate's ordinary I/O error layering.
    pub fn dry_run<W: Read + Write + Seek>(
        &self,
        dest: &mut W,
    ) -> io::Result<()> {
        let current = read_all(dest)?;
        if fnv1a64(&current) != self.precondition_digest {
            invalid_input!(
                "repair plan precondition digest {} no longer matches the \
                 file; re-audit before applying",
                self.precondition_digest()
            );
        }
        Ok(())
    }

    /// Applies the plan to an in-place destination, but only if its bytes
    /// still match the precondition digest.
    ///
    /// The whole repaired image is written in one pass.  If a write fails
    /// partway through, the bytes written so far are restored from the audit
    /// snapshot before the error is returned, so a failed apply leaves the
    /// destination byte-for-byte unchanged.  A digest mismatch is rejected
    /// before any write.
    pub fn apply_to<W: Read + Write + Seek>(
        &self,
        dest: &mut W,
    ) -> io::Result<()> {
        let original = read_all(dest)?;
        if fnv1a64(&original) != self.precondition_digest {
            invalid_input!(
                "repair plan precondition digest {} no longer matches the \
                 file; re-audit before applying",
                self.precondition_digest()
            );
        }
        dest.seek(SeekFrom::Start(0))?;
        if let Err(write_err) = dest.write_all(&self.repaired) {
            // Best-effort rollback of every byte that the failed write may
            // have touched.  Failure to roll back is reported in the chain of
            // the original error rather than masked.
            let _ = dest.seek(SeekFrom::Start(0));
            if let Err(rollback_err) = dest.write_all(&original) {
                return Err(io::Error::new(
                    write_err.kind(),
                    format!(
                        "failed to apply repair: {write_err}; rollback also \
                         failed: {rollback_err}"
                    ),
                ));
            }
            return Err(write_err);
        }
        dest.flush()?;
        Ok(())
    }
}

//==========================================================================//

/// The result of an opt-in structural audit.
///
/// The report is a value with no shared or global state: every call to an
/// audit entry point builds a fresh report from a fresh full read of the
/// bytes, so one call can never carry a cache, counter, or temporary result
/// from a previous (including failed) call.
#[derive(Clone, Debug)]
pub struct AuditReport {
    /// Identity digest of the audited bytes, also used as the version tag on
    /// the derived plan.
    input_digest: u64,
    /// Length of the audited input in bytes.
    input_len: u64,
    version: Version,
    findings: Vec<Finding>,
    plan: Option<RepairPlan>,
}

impl AuditReport {
    /// The FNV-1a digest (16 hex digits) of the exact bytes audited.
    pub fn input_digest(&self) -> String {
        format!("{:016x}", self.input_digest)
    }

    /// Length in bytes of the audited input.
    pub fn input_len(&self) -> u64 {
        self.input_len
    }

    /// The CFB version declared by the header.
    pub fn version(&self) -> Version {
        self.version
    }

    /// All findings, sorted deterministically by structure, kind and first
    /// violating offset so that re-auditing identical bytes yields the same
    /// report regardless of call order or scheduling.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// True when no corruption was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// The read-only repair plan, present exactly when every finding can be
    /// repaired and the resulting image reopens under Strict validation.
    pub fn repair_plan(&self) -> Option<&RepairPlan> {
        self.plan.as_ref()
    }
}

//==========================================================================//

fn read_all<W: Read + Seek>(reader: &mut W) -> io::Result<Vec<u8>> {
    reader.seek(SeekFrom::Start(0))?;
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    Ok(data)
}

/// Audits an existing compound file at the given path without modifying it.
pub fn audit_path<P: AsRef<Path>>(path: P) -> io::Result<AuditReport> {
    crate::OpenOptions::new().audit_path(path)
}

/// Audits an existing compound file read from `inner` without modifying it.
pub fn audit<F: Read + Seek>(inner: F) -> io::Result<AuditReport> {
    crate::OpenOptions::new().audit_with(inner)
}

//==========================================================================//
// Parsed-once model of the file.
//
// The audit reuses the production header parser and the production file-size
// checks rather than re-implementing them; the raw parsing below only covers
// what the audit needs beyond what the production parser exposes.

#[derive(Clone, Debug)]
struct RawDirEntry {
    stream_id: u32,
    obj_type_byte: u8,
    obj_type: Option<ObjType>,
    name: String,
    left_sibling: u32,
    right_sibling: u32,
    child: u32,
    start_sector: u32,
    stream_len: u64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Owner {
    Difat,
    Fat,
    Directory,
    Minifat,
    MiniStream,
    /// A user-data stream; the value is its directory entry ID so that
    /// cross-chain findings can name both claimants.
    Stream(u32),
}

fn owner_label(owner: Owner) -> String {
    match owner {
        Owner::Difat => "the DIFAT chain".to_string(),
        Owner::Fat => "a FAT sector".to_string(),
        Owner::Directory => "the directory chain".to_string(),
        Owner::Minifat => "the MiniFAT chain".to_string(),
        Owner::MiniStream => "the mini stream".to_string(),
        Owner::Stream(id) => format!("stream at directory entry {id}"),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MiniOwner {
    MiniStream,
    Stream(u32),
}

/// Where following a table edge stopped, and how.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EdgeStop {
    End,
    Free,
    OutOfBounds,
    Cycle,
    DoubleClaim,
}

/// One pending table edit, recorded during the single analysis pass.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Patch {
    offset: usize,
    original: Vec<u8>,
    replacement: Vec<u8>,
    rationale: String,
}

#[derive(Clone, Debug)]
struct AuditEngine {
    data: Vec<u8>,
    version: Version,
    sector_len: usize,
    num_sectors: u32,
    header_fields: [u32; 8],
    difat_listed: Vec<u32>,
    /// Byte offset of each DIFAT-listed FAT sector reference.
    difat_list_loc: Vec<usize>,
    difat_chain: Vec<u32>,
    fat: Vec<u32>,
    /// Where each read FAT slot physically lives.
    fat_slot_sector: Vec<u32>,
    owners: FnvHashMap<u32, Owner>,
    dir_chain: Vec<u32>,
    dir_entries: Vec<RawDirEntry>,
    minifat: Vec<u32>,
    minifat_slot_sector: Vec<u32>,
    mini_owners: FnvHashMap<u32, MiniOwner>,
    findings: Vec<Finding>,
    patches: Vec<Patch>,
    repairable: bool,
}

fn u32_at(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(data[offset..offset + 4].try_into().unwrap())
}

fn u64_at(data: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(data[offset..offset + 8].try_into().unwrap())
}

impl AuditEngine {
    fn add_finding(&mut self, finding: Finding) {
        self.findings.push(finding);
    }

    fn note(&mut self, patch: Patch) {
        if let Some(existing) =
            self.patches.iter().find(|p| p.offset == patch.offset)
        {
            if existing.replacement != patch.replacement {
                // Two repairs disagree about one byte: this is an internal
                // invariant of the analysis, never user input.
                self.repairable = false;
            }
            return;
        }
        self.patches.push(patch);
    }

    fn fat_slot_offset(&self, sector_id: u32, slot: u32) -> usize {
        let entries_per_sector = self.sector_len / size_of::<u32>();
        let fat_sector_index = slot as usize / entries_per_sector;
        let index_within = slot as usize % entries_per_sector;
        let fat_sector = self.fat_slot_sector[fat_sector_index];
        let absolute = (fat_sector as usize + 1) * self.sector_len
            + index_within * 4;
        debug_assert_eq!(self.data[absolute..absolute + 4].len(), 4);
        let _ = sector_id;
        absolute
    }

    fn minifat_slot_offset(&self, slot: u32) -> usize {
        let entries_per_sector = self.sector_len / size_of::<u32>();
        let minifat_sector = self.minifat_slot_sector
            [(slot as usize) / entries_per_sector];
        let index_within = (slot as usize) % entries_per_sector;
        (minifat_sector as usize + 1) * self.sector_len + index_within * 4
    }

    fn dir_entry_offset(&self, stream_id: u32) -> usize {
        let entries_per_sector = self.version.dir_entries_per_sector();
        let dir_sector = self.dir_chain
            [(stream_id as usize) / entries_per_sector];
        let index_within = (stream_id as usize) % entries_per_sector;
        (dir_sector as usize + 1) * self.sector_len
            + index_within * consts::DIR_ENTRY_LEN
    }

    fn note_fat_slot(
        &mut self,
        slot: u32,
        new_value: u32,
        rationale: impl Into<String>,
    ) {
        let offset = self.fat_slot_offset(slot, slot);
        self.note(Patch {
            offset,
            original: u32_at(&self.data, offset).to_le_bytes().to_vec(),
            replacement: new_value.to_le_bytes().to_vec(),
            rationale: rationale.into(),
        });
        self.fat[slot as usize] = new_value;
    }

    fn note_minifat_slot(
        &mut self,
        slot: u32,
        new_value: u32,
        rationale: impl Into<String>,
    ) {
        let offset = self.minifat_slot_offset(slot);
        self.note(Patch {
            offset,
            original: u32_at(&self.data, offset).to_le_bytes().to_vec(),
            replacement: new_value.to_le_bytes().to_vec(),
            rationale: rationale.into(),
        });
        self.minifat[slot as usize] = new_value;
    }

    fn note_dir_field(
        &mut self,
        stream_id: u32,
        field_offset: usize,
        new_value: u32,
        rationale: impl Into<String>,
    ) {
        let base = self.dir_entry_offset(stream_id);
        let offset = base + field_offset;
        self.note(Patch {
            offset,
            original: u32_at(&self.data, offset).to_le_bytes().to_vec(),
            replacement: new_value.to_le_bytes().to_vec(),
            rationale: rationale.into(),
        });
        match field_offset {
            DIR_LEFT_SIBLING => {
                self.dir_entries[stream_id as usize].left_sibling = new_value
            }
            DIR_RIGHT_SIBLING => {
                self.dir_entries[stream_id as usize].right_sibling = new_value
            }
            DIR_CHILD => {
                self.dir_entries[stream_id as usize].child = new_value
            }
            DIR_START_SECTOR => {
                self.dir_entries[stream_id as usize].start_sector = new_value
            }
            _ => unreachable!(),
        }
    }

    fn note_dir_len(
        &mut self,
        stream_id: u32,
        new_len: u64,
        rationale: impl Into<String>,
    ) {
        let offset = self.dir_entry_offset(stream_id) + DIR_STREAM_LEN;
        self.note(Patch {
            offset,
            original: u64_at(&self.data, offset).to_le_bytes().to_vec(),
            replacement: new_len.to_le_bytes().to_vec(),
            rationale: rationale.into(),
        });
        self.dir_entries[stream_id as usize].stream_len = new_len;
    }

    fn note_header_u32(
        &mut self,
        offset: usize,
        new_value: u32,
        rationale: impl Into<String>,
    ) {
        self.note(Patch {
            offset,
            original: u32_at(&self.data, offset).to_le_bytes().to_vec(),
            replacement: new_value.to_le_bytes().to_vec(),
            rationale: rationale.into(),
        });
    }
}

//==========================================================================//
// Model construction.  Size checks mirror `CompoundFile::open_internal`, so
// an input too small/corrupt to hold a CFB header is rejected through the
// same InvalidData layering, before any audit runs.

fn audit_inner<F: Read + Seek>(mut inner: F) -> io::Result<AuditReport> {
    let inner_len = inner.seek(SeekFrom::End(0))?;
    if inner_len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            inner_len
        );
    }
    inner.seek(SeekFrom::Start(0))?;
    let header = Header::read_from(&mut inner, Validation::Permissive)?;
    let version = header.version;
    let sector_len = version.sector_len();
    if inner_len
        > (consts::MAX_REGULAR_SECTOR as u64 + 1) * (sector_len as u64)
    {
        invalid_data!(
            "Invalid CFB file ({} bytes is too large)",
            inner_len
        );
    }
    if inner_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            inner_len,
            sector_len
        );
    }
    let mut data = Vec::with_capacity(inner_len as usize);
    inner.seek(SeekFrom::Start(0))?;
    inner.read_to_end(&mut data)?;
    debug_assert_eq!(data.len() as u64, inner_len);
    let num_sectors = (inner_len / sector_len as u64) as u32 - 1;
    let input_digest = fnv1a64(&data);

    let header_fields = [
        u32_at(&data, HDR_NUM_DIR_SECTORS),
        u32_at(&data, HDR_NUM_FAT_SECTORS),
        u32_at(&data, HDR_FIRST_DIR_SECTOR),
        u32_at(&data, HDR_FIRST_MINIFAT_SECTOR),
        u32_at(&data, HDR_NUM_MINIFAT_SECTORS),
        u32_at(&data, HDR_FIRST_DIFAT_SECTOR),
        u32_at(&data, HDR_NUM_DIFAT_SECTORS),
        // slot 7 unused
        u32_at(&data, HDR_NUM_DIFAT_SECTORS),
    ];

    let mut engine = AuditEngine {
        data,
        version,
        sector_len,
        num_sectors,
        header_fields,
        difat_listed: Vec::new(),
        difat_list_loc: Vec::new(),
        difat_chain: Vec::new(),
        fat: Vec::new(),
        fat_slot_sector: Vec::new(),
        owners: FnvHashMap::default(),
        dir_chain: Vec::new(),
        dir_entries: Vec::new(),
        minifat: Vec::new(),
        minifat_slot_sector: Vec::new(),
        mini_owners: FnvHashMap::default(),
        findings: Vec::new(),
        patches: Vec::new(),
        repairable: true,
    };

    engine.read_difat(&header)?;
    engine.read_fat();
    engine.read_directory(&header);
    engine.read_minifat(&header);
    engine.analyze_chains();
    engine.scan_orphans_and_invalid();
    engine.check_tree();
    engine.check_header_counts(&header);

    let plan = engine.build_plan(input_digest);
    let mut findings = engine.findings;
    findings.sort_by(|a, b| {
        (a.table, a.kind, a.offset, a.sector, a.detail.as_str()).cmp(&(
            b.table,
            b.kind,
            b.offset,
            b.sector,
            b.detail.as_str(),
        ))
    });
    Ok(AuditReport {
        input_digest,
        input_len: inner_len,
        version,
        findings,
        plan,
    })
}

impl AuditEngine {
    /// Reads the DIFAT chain from the header and DIFAT sectors, recording
    /// cycles, out-of-bounds pointers and duplicated sector IDs as distinct
    /// findings instead of bailing out.
    fn read_difat(&mut self, header: &Header) -> io::Result<()> {
        // Header-embedded entries: the production parser already validated
        // that these are <= MAX_REGULAR_SECTOR.
        for (index, &listed) in header.initial_difat_entries.iter().enumerate() {
            if listed == consts::FREE_SECTOR {
                break;
            }
            self.difat_listed.push(listed);
            self.difat_list_loc.push(HDR_DIFAT_ENTRIES + index * 4);
        }

        let entries_per_difat_sector = self.sector_len / 4 - 1;
        let mut current = header.first_difat_sector;
        let mut visited = std::collections::HashSet::new();
        let mut declared_difat_sectors = 0u32;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            let offset_of_next = (current as usize + 1) * self.sector_len
                + entries_per_difat_sector * 4;
            if current > consts::MAX_REGULAR_SECTOR || current >= self.num_sectors
            {
                self.add_finding(Finding::new(
                    CorruptionTable::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(offset_of_next as u64),
                    Some(current),
                    format!(
                        "DIFAT chain references sector {}, but the file has \
                         only {} sectors",
                        current, self.num_sectors
                    ),
                ));
                break;
            }
            if !visited.insert(current) {
                self.add_finding(Finding::new(
                    CorruptionTable::Difat,
                    CorruptionKind::Cycle,
                    Some(offset_of_next as u64),
                    Some(current),
                    format!(
                        "DIFAT chain revisits sector {} instead of \
                         terminating",
                        current
                    ),
                ));
                // Sever the incoming edge inside the DIFAT sector: its last
                // four bytes must become END_OF_CHAIN.
                let prev = *self.difat_chain.last().unwrap();
                let prev_next_offset =
                    (prev as usize + 1) * self.sector_len
                        + entries_per_difat_sector * 4;
                self.note(Patch {
                    offset: prev_next_offset,
                    original: u32_at(&self.data, prev_next_offset)
                        .to_le_bytes()
                        .to_vec(),
                    replacement: consts::END_OF_CHAIN
                        .to_le_bytes()
                        .to_vec(),
                    rationale: format!(
                        "break DIFAT cycle by terminating chain after \
                         sector {prev}"
                    ),
                });
                break;
            }
            // The incoming edge that closes a loop lives either in the
            // header (when the DIFAT chain is a single self-referencing
            // sector) or in the previous DIFAT sector.
            self.note(Patch {
                offset: HDR_FIRST_DIFAT_SECTOR,
                original: u32_at(&self.data, HDR_FIRST_DIFAT_SECTOR)
                    .to_le_bytes()
                    .to_vec(),
                replacement: consts::END_OF_CHAIN.to_le_bytes().to_vec(),
                rationale: "break DIFAT cycle at its first sector"
                    .to_string(),
            });
            self.difat_chain.push(current);
            declared_difat_sectors += 1;
            let base = (current as usize + 1) * self.sector_len;
            for index in 0..entries_per_difat_sector {
                let entry = u32_at(&self.data, base + index * 4);
                if entry == consts::FREE_SECTOR {
                    continue;
                }
                if entry > consts::MAX_REGULAR_SECTOR {
                    self.add_finding(Finding::new(
                        CorruptionTable::Difat,
                        CorruptionKind::OutOfBounds,
                        Some((base + index * 4) as u64),
                        None,
                        format!(
                            "DIFAT sector {} refers to invalid sector index \
                             0x{:08X}",
                            current, entry
                        ),
                    ));
                    continue;
                }
                self.difat_listed.push(entry);
                self.difat_list_loc.push(base + index * 4);
            }
            current = u32_at(&self.data, offset_of_next);
        }

        if header.num_difat_sectors != declared_difat_sectors {
            self.add_finding(Finding::new(
                CorruptionTable::Difat,
                CorruptionKind::LengthMismatch,
                Some(HDR_NUM_DIFAT_SECTORS as u64),
                None,
                format!(
                    "header declares {} DIFAT sectors, but the chain \
                     contains {}",
                    header.num_difat_sectors, declared_difat_sectors
                ),
            ));
            self.note_header_u32(
                HDR_NUM_DIFAT_SECTORS,
                declared_difat_sectors,
                "correct DIFAT sector count to match chain",
            );
        }
        if header.first_difat_sector == consts::FREE_SECTOR {
            // Permissive parser normalizes FREE to EOC; nothing to repair.
        }
        Ok(())
    }

    /// Reads every FAT slot from the DIFAT-listed FAT sectors, applying the
    /// same end-of-FAT normalization as the production permissive parser.
    fn read_fat(&mut self) {
        let entries_per_sector = self.sector_len / size_of::<u32>();
        // The DIFAT chain sectors are marked in the FAT as DIFAT_SECTOR; they
        // are claimed before FAT sectors so that a listing overlapping the
        // DIFAT chain is reported as double occupancy rather than read twice.
        for &difat_sector in self.difat_chain.iter() {
            if difat_sector < self.num_sectors {
                self.owners.insert(difat_sector, Owner::Difat);
            }
        }
        let mut seen = std::collections::HashSet::new();
        for (index, &fat_sector) in self.difat_listed.iter().enumerate() {
            let loc = self.difat_list_loc[index];
            if fat_sector > consts::MAX_REGULAR_SECTOR
                || fat_sector >= self.num_sectors
            {
                self.add_finding(Finding::new(
                    CorruptionTable::Difat,
                    CorruptionKind::OutOfBounds,
                    Some(loc as u64),
                    Some(fat_sector),
                    format!(
                        "DIFAT lists sector {} as a FAT sector, but the file \
                         has only {} sectors",
                        fat_sector, self.num_sectors
                    ),
                ));
                self.note(Patch {
                    offset: loc,
                    original: u32_at(&self.data, loc).to_le_bytes().to_vec(),
                    replacement: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                    rationale: format!(
                        "drop out-of-bounds FAT sector listing {fat_sector}"
                    ),
                });
                continue;
            }
            if !seen.insert(fat_sector) {
                self.add_finding(Finding::new(
                    CorruptionTable::Difat,
                    CorruptionKind::DoubleOccupancy,
                    Some(loc as u64),
                    Some(fat_sector),
                    format!(
                        "DIFAT lists sector {} as a FAT sector more than once",
                        fat_sector
                    ),
                ));
                self.note(Patch {
                    offset: loc,
                    original: u32_at(&self.data, loc).to_le_bytes().to_vec(),
                    replacement: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                    rationale: format!(
                        "drop duplicate FAT sector listing {fat_sector}"
                    ),
                });
                continue;
            }
            if let Some(existing) = self.claim_sector(fat_sector, Owner::Fat) {
                self.add_finding(Finding::new(
                    CorruptionTable::Fat,
                    CorruptionKind::DoubleOccupancy,
                    Some(loc as u64),
                    Some(fat_sector),
                    format!(
                        "sector {} is marked as a FAT sector but is already \
                         claimed by {}",
                        fat_sector,
                        owner_label(existing)
                    ),
                ));
                self.note(Patch {
                    offset: loc,
                    original: u32_at(&self.data, loc).to_le_bytes().to_vec(),
                    replacement: consts::FREE_SECTOR.to_le_bytes().to_vec(),
                    rationale: format!(
                        "drop FAT listing for sector already claimed by {}",
                        owner_label(existing)
                    ),
                });
                continue;
            }
            let base = (fat_sector as usize + 1) * self.sector_len;
            for slot_index in 0..entries_per_sector {
                self.fat.push(u32_at(
                    &self.data,
                    base + slot_index * size_of::<u32>(),
                ));
                self.fat_slot_sector.push(fat_sector);
            }
        }
        // Mirror the permissive open path's stripping/padding.
        while (self.fat.len() as u32) > self.num_sectors {
            match *self.fat.last().unwrap() {
                0 | consts::DIFAT_SECTOR | consts::FAT_SECTOR
                | consts::FREE_SECTOR => {
                    self.fat.pop();
                    self.fat_slot_sector.pop();
                }
                _ => break,
            }
        }
        while (self.fat.len() as u32) > self.num_sectors
            && *self.fat.last().unwrap() == consts::FREE_SECTOR
        {
            self.fat.pop();
            self.fat_slot_sector.pop();
        }
        while (self.fat.len() as u32) < self.num_sectors {
            // Missing slots are treated as FREE exactly like the open path;
            // they have no on-disk location, so there is nothing to patch.
            self.fat.push(consts::FREE_SECTOR);
            self.fat_slot_sector.push(u32::MAX);
        }
    }

    /// Walks the directory chain and permissively parses every entry.
    fn read_directory(&mut self, header: &Header) {
        let (chain, stop) = self.walk_fat_chain(
            header.first_dir_sector,
            Owner::Directory,
            CorruptionTable::Directory,
            StartRef::Header(HDR_FIRST_DIR_SECTOR),
        );
        self.dir_chain = chain;
        if stop == EdgeStop::End && header.version == Version::V4 {
            let actual = self.dir_chain.len() as u32;
            if header.num_dir_sectors != actual {
                self.add_finding(Finding::new(
                    CorruptionTable::Directory,
                    CorruptionKind::LengthMismatch,
                    Some(HDR_NUM_DIR_SECTORS as u64),
                    None,
                    format!(
                        "header declares {} directory sectors, but the chain \
                         contains {}",
                        header.num_dir_sectors, actual
                    ),
                ));
                self.note_header_u32(
                    HDR_NUM_DIR_SECTORS,
                    actual,
                    "correct directory sector count to match chain",
                );
            }
        }
        let entries_per_sector = self.version.dir_entries_per_sector();
        let mut stream_id: u32 = 0;
        for &sector_id in self.dir_chain.iter() {
            let base = (sector_id as usize + 1) * self.sector_len;
            for index in 0..entries_per_sector {
                let offset = base + index * consts::DIR_ENTRY_LEN;
                let raw = self.parse_raw_dir_entry(stream_id, offset);
                self.dir_entries.push(raw);
                stream_id += 1;
            }
        }
    }

    /// Permissionless directory-entry decode, used only to locate streams for
    /// the audit.  The production `DirEntry::read_from` remains the
    /// authoritative parser and is also used to verify every repaired image.
    fn parse_raw_dir_entry(
        &self,
        stream_id: u32,
        offset: usize,
    ) -> RawDirEntry {
        let bytes = &self.data[offset..offset + consts::DIR_ENTRY_LEN];
        let name_len_byte =
            u16::from_le_bytes([bytes[64], bytes[65]]) as usize;
        let mut name = String::new();
        if name_len_byte <= 64 {
            let chars = name_len_byte / 2;
            let mut units = Vec::with_capacity(chars);
            for index in 0..chars.saturating_sub(0) {
                let unit = u16::from_le_bytes([
                    bytes[2 * index],
                    bytes[2 * index + 1],
                ]);
                units.push(unit);
            }
            // The length includes the terminating null; drop it if present.
            if units.last() == Some(&0) {
                units.pop();
            }
            name = String::from_utf16_lossy(&units);
        }
        let obj_type_byte = bytes[DIR_OBJ_TYPE];
        let obj_type = ObjType::from_byte(obj_type_byte);
        RawDirEntry {
            stream_id,
            obj_type_byte,
            obj_type,
            name,
            left_sibling: u32_at(bytes, DIR_LEFT_SIBLING),
            right_sibling: u32_at(bytes, DIR_RIGHT_SIBLING),
            child: u32_at(bytes, DIR_CHILD),
            start_sector: u32_at(bytes, DIR_START_SECTOR),
            stream_len: u64_at(bytes, DIR_STREAM_LEN)
                & self.version.stream_len_mask(),
        }
    }

    /// Reads the MiniFAT from the sectors named by its FAT chain.
    fn read_minifat(&mut self, header: &Header) {
        let (chain, stop) = self.walk_fat_chain(
            header.first_minifat_sector,
            Owner::Minifat,
            CorruptionTable::MiniFat,
            StartRef::Header(HDR_FIRST_MINIFAT_SECTOR),
        );
        let _ = stop;
        let entries_per_sector = self.sector_len / size_of::<u32>();
        for &sector_id in chain.iter() {
            let base = (sector_id as usize + 1) * self.sector_len;
            for index in 0..entries_per_sector {
                self.minifat
                    .push(u32_at(&self.data, base + index * size_of::<u32>()));
                self.minifat_slot_sector.push(sector_id);
            }
        }
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            self.minifat.pop();
            self.minifat_slot_sector.pop();
        }
        if header.num_minifat_sectors as usize != chain.len() {
            self.add_finding(Finding::new(
                CorruptionTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(HDR_NUM_MINIFAT_SECTORS as u64),
                None,
                format!(
                    "header declares {} MiniFAT sectors, but the chain \
                     contains {}",
                    header.num_minifat_sectors,
                    chain.len()
                ),
            ));
            self.note_header_u32(
                HDR_NUM_MINIFAT_SECTORS,
                chain.len() as u32,
                "correct MiniFAT sector count to match chain",
            );
        }
    }
}

//==========================================================================//
// Chain walking, shared by every FAT-based structure (directory, MiniFAT,
// mini stream and user streams).  The walk is the same single algorithm for
// all of them; only the owner identity and reported table differ.

#[derive(Clone, Copy, Debug)]
enum StartRef {
    Header(usize),
    DirField(u32, usize),
}

impl StartRef {
    fn offset(&self, engine: &AuditEngine) -> usize {
        match self {
            StartRef::Header(offset) => *offset,
            StartRef::DirField(stream_id, field) => {
                engine.dir_entry_offset(*stream_id) + *field
            }
        }
    }
}

impl AuditEngine {
    fn claim_sector(
        &mut self,
        sector: u32,
        owner: Owner,
    ) -> Option<Owner> {
        match self.owners.get(&sector).copied() {
            Some(existing) if existing == owner => None,
            Some(existing) => Some(existing),
            None => {
                self.owners.insert(sector, owner);
                None
            }
        }
    }

    /// Follows FAT edges from `start`, recording the first violation and the
    /// repair edge for each corruption type.  Mutations (edge severing) are
    /// applied to the in-memory FAT through [`Self::note_fat_slot`], so the
    /// repaired image is synthesized from the same walk that produced the
    /// evidence.
    fn walk_fat_chain(
        &mut self,
        start: u32,
        owner: Owner,
        table: CorruptionTable,
        start_ref: StartRef,
    ) -> (Vec<u32>, EdgeStop) {
        self.walk_table_chain(
            start,
            owner,
            table,
            start_ref,
            /*mini=*/ false,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_table_chain(
        &mut self,
        start: u32,
        owner: Owner,
        table: CorruptionTable,
        start_ref: StartRef,
        mini: bool,
    ) -> (Vec<u32>, EdgeStop) {
        let table_len = if mini {
            self.minifat.len() as u32
        } else {
            self.fat.len() as u32
        };
        let start_offset = start_ref.offset(self);
        if start == consts::END_OF_CHAIN {
            return (Vec::new(), EdgeStop::End);
        }
        let bad_start = |engine: &mut AuditEngine, kind, detail: String| {
            engine.add_finding(Finding::new(
                table,
                kind,
                Some(start_offset as u64),
                Some(start),
                detail,
            ));
            match start_ref {
                StartRef::Header(offset) => engine.note_header_u32(
                    offset,
                    consts::END_OF_CHAIN,
                    "terminate chain with no valid start",
                ),
                StartRef::DirField(stream_id, field) => engine.note_dir_field(
                    stream_id,
                    field,
                    consts::END_OF_CHAIN,
                    "terminate chain with no valid start",
                ),
            }
        };
        if start == consts::FREE_SECTOR {
            bad_start(
                self,
                CorruptionKind::OutOfBounds,
                format!(
                    "{} starts at FREE_SECTOR instead of a real sector",
                    owner_label(owner)
                ),
            );
            return (Vec::new(), EdgeStop::Free);
        }
        if start > consts::MAX_REGULAR_SECTOR || start >= table_len {
            bad_start(
                self,
                CorruptionKind::OutOfBounds,
                format!(
                    "{} starts at sector {}, but the {} has only {} entries",
                    owner_label(owner),
                    start,
                    if mini { "MiniFAT" } else { "FAT" },
                    table_len
                ),
            );
            return (Vec::new(), EdgeStop::OutOfBounds);
        }

        let mut chain = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut current = start;
        loop {
            let next_value = if mini {
                self.minifat[current as usize]
            } else {
                self.fat[current as usize]
            };
            visited.insert(current);
            let mini_owner = MiniOwner::from_owner(owner);
            if let Some(other) = if mini {
                match self.mini_owners.get(&current).copied() {
                    Some(existing) if existing == mini_owner => None,
                    Some(other) => Some(other.label()),
                    None => {
                        self.mini_owners.insert(current, mini_owner);
                        None
                    }
                }
            } else {
                self.claim_sector(current, owner).map(owner_label)
            } {
                let offset = self.edge_offset(current, mini);
                self.add_finding(Finding::new(
                    table,
                    CorruptionKind::DoubleOccupancy,
                    Some(offset as u64),
                    Some(current),
                    format!(
                        "sector {} is claimed by both {} and {}",
                        current,
                        owner_label(owner),
                        other
                    ),
                ));
                self.sever_edge(current, mini, owner);
                return (chain, EdgeStop::DoubleClaim);
            }
            chain.push(current);

            if next_value == consts::END_OF_CHAIN {
                return (chain, EdgeStop::End);
            }
            if next_value == consts::FREE_SECTOR {
                let offset = self.edge_offset(current, mini);
                self.add_finding(Finding::new(
                    table,
                    CorruptionKind::OutOfBounds,
                    Some(offset as u64),
                    Some(next_value),
                    format!(
                        "{} ends early: sector {} points to FREE_SECTOR, \
                         truncating the chain",
                        owner_label(owner),
                        current
                    ),
                ));
                self.sever_edge(current, mini, owner);
                return (chain, EdgeStop::Free);
            }
            if next_value > consts::MAX_REGULAR_SECTOR
                || next_value >= table_len
            {
                let offset = self.edge_offset(current, mini);
                self.add_finding(Finding::new(
                    table,
                    CorruptionKind::OutOfBounds,
                    Some(offset as u64),
                    Some(next_value),
                    format!(
                        "{}: sector {} points to {}, past the end of the {} \
                         ({} entries)",
                        owner_label(owner),
                        current,
                        next_value,
                        if mini { "MiniFAT" } else { "FAT" },
                        table_len
                    ),
                ));
                self.sever_edge(current, mini, owner);
                return (chain, EdgeStop::OutOfBounds);
            }
            if visited.contains(&next_value) {
                let offset = self.edge_offset(current, mini);
                self.add_finding(Finding::new(
                    table,
                    CorruptionKind::Cycle,
                    Some(offset as u64),
                    Some(next_value),
                    format!(
                        "{} loops back to sector {} instead of terminating",
                        owner_label(owner),
                        next_value
                    ),
                ));
                self.sever_edge(current, mini, owner);
                return (chain, EdgeStop::Cycle);
            }
            current = next_value;
        }
    }

    fn edge_offset(&self, from_sector: u32, mini: bool) -> usize {
        if mini {
            self.minifat_slot_offset(from_sector)
        } else {
            self.fat_slot_offset(from_sector, from_sector)
        }
    }

    fn sever_edge(&mut self, from_sector: u32, mini: bool, owner: Owner) {
        let _ = owner;
        if mini {
            self.note_minifat_slot(
                from_sector,
                consts::END_OF_CHAIN,
                format!("sever MiniFAT edge out of sector {from_sector}"),
            );
        } else {
            self.note_fat_slot(
                from_sector,
                consts::END_OF_CHAIN,
                format!("sever FAT edge out of sector {from_sector}"),
            );
        }
    }
}

impl MiniOwner {
    fn from_owner(owner: Owner) -> MiniOwner {
        match owner {
            Owner::MiniStream => MiniOwner::MiniStream,
            Owner::Stream(id) => MiniOwner::Stream(id),
            other => panic!("non-mini owner {other:?} in mini chain"),
        }
    }

    fn label(&self) -> String {
        match self {
            MiniOwner::MiniStream => "the mini stream".to_string(),
            MiniOwner::Stream(id) => {
                format!("stream at directory entry {id}")
            }
        }
    }
}

//==========================================================================//
// Stream-level analysis: mini stream chain, every user stream, declared
// length checks, orphan scans, and the sibling/child tree.

impl AuditEngine {
    fn analyze_chains(&mut self) {
        if self.dir_entries.is_empty() {
            self.add_finding(Finding::new(
                CorruptionTable::Directory,
                CorruptionKind::MalformedEntry,
                Some(0),
                None,
                "the directory chain contains no root entry".to_string(),
            ));
            self.repairable = false;
            return;
        }
        let root_id = consts::ROOT_STREAM_ID;
        let root_type = self.dir_entries[0].obj_type;
        if root_type != Some(ObjType::Root) {
            self.add_finding(Finding::new(
                CorruptionTable::Directory,
                CorruptionKind::MalformedEntry,
                Some((self.dir_entry_offset(root_id) + DIR_OBJ_TYPE) as u64),
                None,
                format!(
                    "root directory entry has object type {} instead of \
                     Root (5)",
                    self.dir_entries[0].obj_type_byte
                ),
            ));
            self.repairable = false;
            return;
        }

        let root_len = self.dir_entries[0].stream_len;
        if root_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            let offset = self.dir_entry_offset(0) + DIR_STREAM_LEN;
            let clamped = root_len
                - (root_len % consts::MINI_SECTOR_LEN as u64);
            self.add_finding(Finding::new(
                CorruptionTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(offset as u64),
                None,
                format!(
                    "root entry declares a mini stream of {} bytes, which is \
                     not a multiple of {}",
                    root_len, consts::MINI_SECTOR_LEN
                ),
            ));
            self.note_dir_len(
                0,
                clamped,
                "round mini stream length down to a whole mini sector",
            );
        }

        // Walk the mini stream (root's regular-FAT chain) before any mini
        // user stream, so a stream whose mini sector collides with it is the
        // second claimant.
        let root_start = self.dir_entries[0].start_sector;
        let (mini_stream_sectors, _mini_stop) = self.walk_fat_chain(
            root_start,
            Owner::MiniStream,
            CorruptionTable::MiniFat,
            StartRef::DirField(0, DIR_START_SECTOR),
        );
        let mini_capacity =
            (mini_stream_sectors.len() as u64) * (self.sector_len as u64);
        let declared_root_len = self.dir_entries[0].stream_len;
        if declared_root_len > mini_capacity {
            let offset = self.dir_entry_offset(0) + DIR_STREAM_LEN;
            self.add_finding(Finding::new(
                CorruptionTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(offset as u64),
                None,
                format!(
                    "root entry declares a mini stream of {} bytes, but its \
                     chain provides only {}",
                    declared_root_len, mini_capacity
                ),
            ));
            self.note_dir_len(
                0,
                mini_capacity,
                "clamp declared mini stream length to chain capacity",
            );
        }

        // The MiniFAT may extend no further than the mini stream.
        let mini_sector_capacity =
            mini_capacity / consts::MINI_SECTOR_LEN as u64;
        if (self.minifat.len() as u64) > mini_sector_capacity {
            let excess = self.minifat.len() as u64 - mini_sector_capacity;
            self.add_finding(Finding::new(
                CorruptionTable::MiniFat,
                CorruptionKind::LengthMismatch,
                Some(HDR_NUM_MINIFAT_SECTORS as u64),
                None,
                format!(
                    "MiniFAT has {} entries, but the mini stream holds only \
                     {} mini sectors",
                    self.minifat.len(),
                    mini_sector_capacity
                ),
            ));
            // Mark the unreachable tail entries FREE; the production parser
            // strips trailing FREE entries on read.
            let keep = mini_sector_capacity as usize;
            for slot in keep..self.minifat.len() {
                self.note_minifat_slot(
                    slot as u32,
                    consts::FREE_SECTOR,
                    format!(
                        "drop {} MiniFAT entries past the end of the mini \
                         stream",
                        excess
                    ),
                );
            }
        }

        // Walk every user stream in directory-entry order so that double
        // occupancy between two streams resolves deterministically (the lower
        // stream ID keeps the shared sector).
        let num_entries = self.dir_entries.len();
        for stream_id in 1..num_entries as u32 {
            let entry = self.dir_entries[stream_id as usize].clone();
            if entry.obj_type != Some(ObjType::Stream) {
                continue;
            }
            let name_label = if entry.name.is_empty() {
                format!("directory entry {stream_id}")
            } else {
                format!("directory entry {stream_id} ({:?})", entry.name)
            };
            let in_mini =
                entry.stream_len < consts::MINI_STREAM_CUTOFF as u64;
            if in_mini {
                let (sectors, stop) = self.walk_mini_chain(
                    entry.start_sector,
                    Owner::Stream(stream_id),
                    CorruptionTable::MiniFat,
                    StartRef::DirField(stream_id, DIR_START_SECTOR),
                );
                if stop != EdgeStop::End {
                    // A severed chain cannot carry the declared length; clamp
                    // to the sectors still reachable.
                    let capacity =
                        (sectors.len() as u64)
                            * consts::MINI_SECTOR_LEN as u64;
                    if entry.stream_len > capacity {
                        let offset = self.dir_entry_offset(stream_id)
                            + DIR_STREAM_LEN;
                        self.add_finding(Finding::new(
                            CorruptionTable::MiniFat,
                            CorruptionKind::LengthMismatch,
                            Some(offset as u64),
                            None,
                            format!(
                                "stream at {} declares {} bytes, but its \
                                 mini chain provides only {}",
                                name_label, entry.stream_len, capacity
                            ),
                        ));
                        self.note_dir_len(
                            stream_id,
                            capacity,
                            "clamp declared length to surviving mini chain",
                        );
                    }
                }
            } else {
                let (sectors, stop) = self.walk_fat_chain(
                    entry.start_sector,
                    Owner::Stream(stream_id),
                    CorruptionTable::Fat,
                    StartRef::DirField(stream_id, DIR_START_SECTOR),
                );
                let capacity =
                    (sectors.len() as u64) * (self.sector_len as u64);
                if entry.stream_len > capacity
                    || stop != EdgeStop::End
                        && entry.stream_len > capacity
                {
                    let offset = self.dir_entry_offset(stream_id)
                        + DIR_STREAM_LEN;
                    self.add_finding(Finding::new(
                        CorruptionTable::Fat,
                        CorruptionKind::LengthMismatch,
                        Some(offset as u64),
                        None,
                        format!(
                            "stream at {} declares {} bytes, but its chain \
                             provides only {}",
                            name_label, entry.stream_len, capacity
                        ),
                    ));
                    self.note_dir_len(
                        stream_id,
                        capacity,
                        "clamp declared length to surviving chain capacity",
                    );
                }
            }
        }
    }
}

impl AuditEngine {
    /// Scans every FAT and MiniFAT slot not already dealt with by a chain
    /// walk: orphaned in-use sectors, reserved INVALID_SECTOR entries, and
    /// mini sectors that no mini chain references.
    fn scan_orphans_and_invalid(&mut self) {
        for (slot, &entry) in self.fat.iter().enumerate() {
            let slot = slot as u32;
            if slot >= self.num_sectors {
                continue;
            }
            if entry <= consts::MAX_REGULAR_SECTOR {
                if !self.owners.contains_key(&slot) {
                    // A normal sector marked as linked by some edge but never
                    // walked is reachable only as a pointee; chain walks claim
                    // pointees as they follow edges, so anything left here is
                    // either a predecessor-less orphan or a duplicate.
                    let offset = self.fat_slot_offset(slot, slot);
                    let claimed_by_next =
                        self.owners.contains_key(&entry);
                    let _ = claimed_by_next;
                    self.add_finding(Finding::new(
                        CorruptionTable::Fat,
                        CorruptionKind::OrphanSector,
                        Some(offset as u64),
                        Some(slot),
                        format!(
                            "sector {} is in use (points to {}) but is not \
                             reachable from DIFAT, directory, MiniFAT, mini \
                             stream or any stream chain",
                            slot, entry
                        ),
                    ));
                    self.note_fat_slot(
                        slot,
                        consts::FREE_SECTOR,
                        format!("free orphaned FAT sector {slot}"),
                    );
                }
            } else if entry == consts::INVALID_SECTOR {
                let offset = self.fat_slot_offset(slot, slot);
                if !self.owners.contains_key(&slot) {
                    self.add_finding(Finding::new(
                        CorruptionTable::Fat,
                        CorruptionKind::InvalidEntry,
                        Some(offset as u64),
                        Some(slot),
                        format!(
                            "FAT entry for sector {} uses reserved value \
                             0x{:08X}",
                            slot, entry
                        ),
                    ));
                    self.note_fat_slot(
                        slot,
                        consts::FREE_SECTOR,
                        format!("replace reserved FAT entry at {slot}"),
                    );
                }
            } else if entry == consts::FAT_SECTOR
                || entry == consts::DIFAT_SECTOR
            {
                // Listed DIFAT/FAT sectors are claimed during read_fat; a
                // sector carrying a table marker that no listing references
                // is orphaned.
                if !self.owners.contains_key(&slot) {
                    let offset = self.fat_slot_offset(slot, slot);
                    self.add_finding(Finding::new(
                        CorruptionTable::Fat,
                        CorruptionKind::OrphanSector,
                        Some(offset as u64),
                        Some(slot),
                        format!(
                            "sector {} carries a table marker (0x{:08X}) but \
                             is not referenced by the DIFAT",
                            slot, entry
                        ),
                    ));
                    self.note_fat_slot(
                        slot,
                        consts::FREE_SECTOR,
                        format!(
                            "free unreferenced table marker at sector {slot}"
                        ),
                    );
                }
            }
        }

        // MiniFAT: every valid mini sector that no mini chain reaches is an
        // orphan; invalid pointers are reported and severed even when the
        // slot is unreachable, since the production validator checks all
        // MiniFAT slots on open.
        for (slot, &entry) in self.minifat.iter().enumerate() {
            let slot = slot as u32;
            let offset = self.minifat_slot_offset(slot);
            if entry <= consts::MAX_REGULAR_SECTOR {
                if entry >= self.minifat.len() as u32 {
                    if !self.mini_owners.contains_key(&slot) {
                        self.add_finding(Finding::new(
                            CorruptionTable::MiniFat,
                            CorruptionKind::OutOfBounds,
                            Some(offset as u64),
                            Some(slot),
                            format!(
                                "mini sector {} points to {}, past the end of \
                                 the MiniFAT ({} entries)",
                                slot, entry, self.minifat.len()
                            ),
                        ));
                        self.note_minifat_slot(
                            slot,
                            consts::END_OF_CHAIN,
                            format!(
                                "terminate mini sector {slot} pointing past \
                                 the MiniFAT"
                            ),
                        );
                    }
                } else if !self.mini_owners.contains_key(&slot) {
                    self.add_finding(Finding::new(
                        CorruptionTable::MiniFat,
                        CorruptionKind::OrphanSector,
                        Some(offset as u64),
                        Some(slot),
                        format!(
                            "mini sector {} is in use (points to {}) but no \
                             stream chain reaches it",
                            slot, entry
                        ),
                    ));
                    self.note_minifat_slot(
                        slot,
                        consts::FREE_SECTOR,
                        format!("free orphaned mini sector {slot}"),
                    );
                }
            } else if entry == consts::INVALID_SECTOR
                && !self.mini_owners.contains_key(&slot)
            {
                self.add_finding(Finding::new(
                    CorruptionTable::MiniFat,
                    CorruptionKind::InvalidEntry,
                    Some(offset as u64),
                    Some(slot),
                    format!(
                        "MiniFAT entry for mini sector {} uses reserved \
                         value 0x{:08X}",
                        slot, entry
                    ),
                ));
                self.note_minifat_slot(
                    slot,
                    consts::FREE_SECTOR,
                    format!("replace reserved MiniFAT entry at {slot}"),
                );
            }
        }
    }

    /// Walks the directory sibling/child tree from the root, reporting
    /// loops, dangling references and out-of-range child fields with the
    /// entry that introduced them.
    fn check_tree(&mut self) {
        if self.dir_entries.is_empty()
            || self.dir_entries[0].obj_type != Some(ObjType::Root)
        {
            return;
        }
        let mut visited = std::collections::HashSet::new();
        // (entry id, parent id)
        let mut stack = vec![(consts::ROOT_STREAM_ID, consts::ROOT_STREAM_ID)];
        while let Some((stream_id, parent_id)) = stack.pop() {
            if !visited.insert(stream_id) {
                let offset =
                    self.dir_entry_offset(parent_id) + DIR_CHILD;
                self.add_finding(Finding::new(
                    CorruptionTable::Directory,
                    CorruptionKind::Cycle,
                    Some(offset as u64),
                    Some(stream_id),
                    format!(
                        "directory entry {} is reachable through a loop in \
                         the sibling/child tree",
                        stream_id
                    ),
                ));
                continue;
            }
            let entry = self.dir_entries[stream_id as usize].clone();
            for (field, value, label) in [
                (DIR_LEFT_SIBLING, entry.left_sibling, "left sibling"),
                (DIR_RIGHT_SIBLING, entry.right_sibling, "right sibling"),
                (DIR_CHILD, entry.child, "child"),
            ] {
                if value == consts::NO_STREAM {
                    continue;
                }
                let offset = self.dir_entry_offset(stream_id) + field;
                if value > consts::MAX_REGULAR_STREAM_ID
                    || value as usize >= self.dir_entries.len()
                {
                    self.add_finding(Finding::new(
                        CorruptionTable::Directory,
                        CorruptionKind::OutOfBounds,
                        Some(offset as u64),
                        Some(value),
                        format!(
                            "directory entry {} {} references {}, but only \
                             {} entries are reachable through the directory \
                             chain",
                            stream_id, label, value, self.dir_entries.len()
                        ),
                    ));
                    self.note_dir_field(
                        stream_id,
                        field,
                        consts::NO_STREAM,
                        format!(
                            "clear dangling {label} reference from entry \
                             {stream_id}"
                        ),
                    );
                    continue;
                }
                let referenced = &self.dir_entries[value as usize];
                if referenced.obj_type == Some(ObjType::Unallocated)
                    || referenced.obj_type.is_none()
                {
                    self.add_finding(Finding::new(
                        CorruptionTable::Directory,
                        CorruptionKind::OutOfBounds,
                        Some(offset as u64),
                        Some(value),
                        format!(
                            "directory entry {} {} references unallocated \
                             entry {}",
                            stream_id, label, value
                        ),
                    ));
                    self.note_dir_field(
                        stream_id,
                        field,
                        consts::NO_STREAM,
                        format!(
                            "clear {label} reference to unallocated entry \
                             {value}"
                        ),
                    );
                    continue;
                }
                stack.push((value, stream_id));
            }
        }
    }

    /// Checks the header FAT-sector count after the DIFAT has been parsed and
    /// out-of-range listings dropped.
    fn check_header_counts(&mut self, _header: &Header) {
        // The repaired number of FAT sectors is the number of distinct,
        // in-range sectors the DIFAT chain lists.
        let mut listed = std::collections::BTreeSet::new();
        for &sector in self.difat_listed.iter() {
            if sector < self.num_sectors {
                listed.insert(sector);
            }
        }
        let actual = listed.len() as u32;
        let declared = u32_at(&self.data, HDR_NUM_FAT_SECTORS);
        if declared != actual {
            self.add_finding(Finding::new(
                CorruptionTable::Difat,
                CorruptionKind::LengthMismatch,
                Some(HDR_NUM_FAT_SECTORS as u64),
                None,
                format!(
                    "header declares {} FAT sectors, but the DIFAT lists {}",
                    declared, actual
                ),
            ));
            self.note_header_u32(
                HDR_NUM_FAT_SECTORS,
                actual,
                "correct FAT sector count to match DIFAT",
            );
        }
    }
}
