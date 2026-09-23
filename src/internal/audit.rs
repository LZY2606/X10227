//! Opt-in structural audit of a compound file, producing corruption evidence
//! for the FAT, DIFAT, MiniFAT, and directory chain together with a
//! read-only repair plan.
//!
//! The audit is read-only and stateless: every call builds its own tables
//! from the bytes of the input, so no cache, counter, or chain list from a
//! previous call (successful or failed) can leak into the next one.  The
//! repair plan is only a description; applying it requires the caller to do
//! so explicitly, after re-checking a digest of the bytes the plan was made
//! from, and a dry-run application never writes a single byte.

use std::fmt;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::mem::size_of;
use std::path::Path;

use fnv::FnvHashMap;

use crate::internal::path::compare_names;
use crate::internal::{consts, DirEntry, Header, ObjType, Validation, Version};
use crate::{ReadLeNumber, WriteLeNumber};

//===========================================================================//
// Public evidence and plan types
//===========================================================================//

/// Which allocation structure a piece of corruption evidence is about.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DefectTable {
    /// The double-indirect FAT (the chain of FAT-sector pointers).
    Difat,
    /// The file allocation table (regular-sector chains).
    Fat,
    /// The directory chain and the sibling trees stored within it.
    Directory,
    /// The mini-sector allocation table.
    MiniFat,
}

impl DefectTable {
    fn label(self) -> &'static str {
        match self {
            DefectTable::Difat => "DIFAT",
            DefectTable::Fat => "FAT",
            DefectTable::Directory => "directory",
            DefectTable::MiniFat => "MiniFAT",
        }
    }
}

/// The category of a corruption finding.  The distinct allocation-table
/// failure shapes are kept separate, exactly as the CFB spec describes them.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DefectKind {
    /// A chain revisits a sector it has already used (a cycle/loop).
    Cycle,
    /// A pointer targets an index outside the table or file.
    OutOfBounds,
    /// A sector is claimed by more than one chain (crossed chains).
    DoubleClaim,
    /// A sector is reachable by no chain at all (an orphan).
    Orphan,
    /// A declared length or count disagrees with what the table holds
    /// (e.g. a stream longer than its chain, or a wrong header count).
    LengthMismatch,
    /// A chain ends before all of its data is reachable (truncation).
    Truncated,
    /// A table entry or directory slot cannot be interpreted at all.
    InvalidEntry,
}

impl DefectKind {
    fn label(self) -> &'static str {
        match self {
            DefectKind::Cycle => "cycle",
            DefectKind::OutOfBounds => "out of bounds",
            DefectKind::DoubleClaim => "double claim",
            DefectKind::Orphan => "orphan",
            DefectKind::LengthMismatch => "declared length mismatch",
            DefectKind::Truncated => "truncated chain",
            DefectKind::InvalidEntry => "invalid entry",
        }
    }
}

/// One piece of corruption evidence, recorded at the first position where the
/// violation becomes certain, together with enough context to act on it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Defect {
    /// The allocation structure involved.
    pub table: DefectTable,
    /// The category of the violation.
    pub kind: DefectKind,
    /// The first violating index: a sector id, a mini-sector id, or a
    /// directory-entry stream id, depending on the table.
    pub index: u64,
    /// Human-readable context naming the chain or entry involved and the
    /// exact first violating position.
    pub detail: String,
}

impl fmt::Display for Defect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}: {} (index {})",
            self.table.label(),
            self.kind.label(),
            self.detail,
            self.index,
        )
    }
}

impl Defect {
    fn new(
        table: DefectTable,
        kind: DefectKind,
        index: u64,
        detail: String,
    ) -> Defect {
        Defect { table, kind, index, detail }
    }
}

/// A short, stable identity for the exact bytes a [`RepairPlan`] was derived
/// from.  A plan can only be applied when the current bytes still hash to
/// this digest.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct AuditDigest([u8; 8]);

impl AuditDigest {
    /// Returns the digest as fixed-width hexadecimal.
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(16);
        for byte in self.0.iter() {
            use std::fmt::Write as _;
            write!(out, "{byte:02x}").unwrap();
        }
        out
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

fn fnv1a_64(bytes: &[u8]) -> [u8; 8] {
    let mut hash: u64 = 0xcbf29ce484222325;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash.to_le_bytes()
}

/// Describes one edit of the read-only repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    /// The structure this edit fixes.
    pub table: DefectTable,
    /// The violation category this edit resolves.
    pub kind: DefectKind,
    /// A deterministic, zero-based position among the plan's edits.
    pub sequence: usize,
    /// What the edit does, naming the exact indices involved.
    pub action: String,
}

impl fmt::Display for RepairStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "#{} [{} {}] {}",
            self.sequence,
            self.table.label(),
            self.kind.label(),
            self.action,
        )
    }
}

/// The result of an opt-in structural audit: the corruption evidence and the
/// read-only repair plan derived from it.
#[derive(Clone, Debug)]
pub struct AuditReport {
    pub(crate) version: Version,
    pub(crate) file_len: u64,
    pub(crate) digest: AuditDigest,
    pub(crate) defects: Vec<Defect>,
    /// Structural findings are reported at every validation level; strict
    /// header-count findings are added only under strict validation.
    pub(crate) strict: bool,
    pub(crate) steps: Vec<RepairStep>,
    pub(crate) repairable: bool,
}

impl AuditReport {
    /// The CFB version of the audited file.
    pub fn version(&self) -> Version {
        self.version
    }

    /// The length, in bytes, of the audited file.
    pub fn file_len(&self) -> u64 {
        self.file_len
    }

    /// True when no corruption of any kind was found.
    pub fn is_clean(&self) -> bool {
        self.defects.is_empty()
    }

    /// The digest of the exact bytes that were audited.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// All findings, in a deterministic order (by structure, then category,
    /// then first violating position).
    pub fn defects(&self) -> &[Defect] {
        &self.defects
    }

    /// Just the findings in one allocation structure.
    pub fn defects_in(&self, table: DefectTable) -> Vec<&Defect> {
        self.defects.iter().filter(|d| d.table == table).collect()
    }

    /// The read-only repair plan.  It is always present, even for a clean
    /// file (then it is empty) and for files whose damage cannot be repaired
    /// automatically (then [`RepairPlan::repairable`] is false).
    pub fn plan(&self) -> RepairPlan {
        RepairPlan {
            version: self.version,
            digest: self.digest,
            steps: self.steps.clone(),
            repairable: self.repairable,
        }
    }
}

/// A read-only description of how to repair the file an [`AuditReport`] was
/// made from.  Nothing is repaired until the plan is applied explicitly, and
/// application first verifies that the input bytes still match
/// [`RepairPlan::digest`].
#[derive(Clone, Debug)]
pub struct RepairPlan {
    pub(crate) version: Version,
    pub(crate) digest: AuditDigest,
    pub(crate) steps: Vec<RepairStep>,
    pub(crate) repairable: bool,
}

impl RepairPlan {
    /// The digest of the bytes the plan was derived from.  Application
    /// refuses to run unless the current bytes still match it.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// True when every finding has an automatic repair.
    pub fn repairable(&self) -> bool {
        self.repairable
    }

    /// The ordered edits that applying the plan makes.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }
}

/// What an explicit plan application should do with its repaired output.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ApplyMode {
    /// Compute the repaired bytes and checks, but never write them
    /// anywhere.  This performs no writes at all.
    DryRun,
    /// Write the repaired file out.
    Commit,
}

/// The result of applying a [`RepairPlan`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ApplyOutcome {
    /// Whether bytes were actually written (false only for a dry run).
    pub wrote: bool,
    /// The length, in bytes, that the repaired file has (or would have).
    pub repaired_len: u64,
}

//===========================================================================//
// Internal analysis model
//===========================================================================//

/// A directory slot: either a parsed entry or the raw bytes with the parse
/// error recorded.
struct Slot {
    entry: Option<DirEntry>,
    /// `Some(message)` when this slot cannot be parsed even permissively.
    parse_error: Option<String>,
}

/// Which named chain owns a sector (or mini sector).  Double-claim evidence
/// can therefore name both chains involved.
#[derive(Clone, PartialEq, Eq)]
enum Owner {
    FatSector,
    DifatSector,
    Directory,
    MiniFat,
    MiniStream,
    /// A data stream, by directory-entry stream id.
    Stream(u32),
}

impl Owner {
    fn label(&self) -> String {
        match self {
            Owner::FatSector => "FAT sector".to_string(),
            Owner::DifatSector => "DIFAT sector".to_string(),
            Owner::Directory => "directory chain".to_string(),
            Owner::MiniFat => "MiniFAT chain".to_string(),
            Owner::MiniStream => "mini stream".to_string(),
            Owner::Stream(id) => format!("stream entry {id}"),
        }
    }
}

/// Everything the audit reads from one file.  It is local to a single call:
/// constructed, used, and dropped within [`audit_reader`], so there is no way
/// for one invocation to observe another's state.
struct AuditModel {
    version: Version,
    sector_len: usize,
    data: Vec<u8>,
    header: Header,
    num_sectors: u32,
    /// The DIFAT chain's sector ids in order.
    difat_sector_ids: Vec<u32>,
    /// FAT-sector ids in DIFAT order (header entries then DIFAT sectors).
    difat: Vec<u32>,
    /// One FAT entry per file sector (padded with FREE_SECTOR).
    fat: Vec<u32>,
    /// Directory slots in directory-chain order.
    slots: Vec<Slot>,
    /// The directory sector ids in chain order.
    dir_sector_ids: Vec<u32>,
    /// MiniFAT entries (trailing FREE_SECTOR stripped).
    minifat: Vec<u32>,
    defects: Vec<Defect>,
}

impl AuditModel {
    fn sector_bytes(&self, sector_id: u32) -> Option<&[u8]> {
        let start = (sector_id as u64 + 1) * self.sector_len as u64;
        let end = start + self.sector_len as u64;
        if end <= self.data.len() as u64 {
            Some(&self.data[start as usize..end as usize])
        } else {
            None
        }
    }

    fn read_u32(&self, offset: usize) -> Option<u32> {
        let bytes = self.data.get(offset..offset + 4)?;
        Some(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn record(
        &mut self,
        table: DefectTable,
        kind: DefectKind,
        index: u64,
        detail: String,
    ) {
        self.defects.push(Defect::new(table, kind, index, detail));
    }

    /// Has this exact finding already been recorded?  Used for findings that
    /// more than one pass can reach (e.g. a shared sector seen from both
    /// chains), so the evidence never double-counts.
    fn has(&self, table: DefectTable, kind: DefectKind, index: u64) -> bool {
        self.defects
            .iter()
            .any(|d| d.table == table && d.kind == kind && d.index == index)
    }

    fn dedup_and_sort(&mut self) {
        // Sort by (table, kind, index, detail) for a deterministic order
        // regardless of traversal scheduling, then drop exact duplicates.
        self.defects.sort_by(|a, b| {
            (a.table as u8, a.kind as u8, a.index, &a.detail).cmp(&(
                b.table as u8,
                b.kind as u8,
                b.index,
                &b.detail,
            ))
        });
        self.defects.dedup();
    }
}

//===========================================================================//
// Loading
//===========================================================================//

/// Audits a compound file from a seekable reader, read-only.  Mirrors the
/// parsing stages of `CompoundFile::open_internal` (the same `Header`,
/// `DirEntry`, and FAT/DIFAT layout code), but records evidence instead of
/// returning at the first structural failure.
pub(crate) fn audit_reader<F: Read + Seek>(
    mut inner: F,
    validation: Validation,
) -> io::Result<AuditReport> {
    let inner_len = inner.seek(SeekFrom::End(0))?;
    if inner_len < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            inner_len
        );
    }
    // Read just enough to learn the version, then read the whole file.  The
    // audit never writes, so a single private buffer is all the state there
    // is.
    inner.seek(SeekFrom::Start(0))?;
    let mut header_prefix = [0u8; 512];
    inner.read_exact(&mut header_prefix)?;
    let version_number =
        u16::from_le_bytes([header_prefix[26], header_prefix[27]]);
    let version = match Version::from_number(version_number) {
        Some(version) => version,
        None => invalid_data!(
            "CFB version {} is not supported",
            version_number
        ),
    };
    let sector_len = version.sector_len();
    if inner_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            inner_len,
            sector_len
        );
    }
    if inner_len
        > (consts::MAX_REGULAR_SECTOR as u64 + 1) * (sector_len as u64)
    {
        invalid_data!(
            "Invalid CFB file ({} bytes is too large)",
            inner_len
        );
    }
    let mut data = Vec::with_capacity(inner_len as usize);
    inner.seek(SeekFrom::Start(0))?;
    inner.take(inner_len).read_to_end(&mut data)?;

    // Re-parse the full header with the same production code the open path
    // uses, so audit and open agree on every field.
    let header = match Header::read_from(
        &mut &data[..consts::HEADER_LEN],
        validation,
    ) {
        Ok(header) => header,
        Err(err) => return Err(err),
    };
    let num_sectors =
        (inner_len / sector_len as u64) as u32 - 1;

    let mut model = AuditModel {
        version,
        sector_len,
        data,
        header,
        num_sectors,
        difat_sector_ids: Vec::new(),
        difat: Vec::new(),
        fat: Vec::new(),
        slots: Vec::new(),
        dir_sector_ids: Vec::new(),
        minifat: Vec::new(),
        defects: Vec::new(),
    };

    model.load_difat(validation);
    model.load_fat(validation);
    model.load_directory(validation);
    model.load_minifat(validation);
    model.analyze(validation);
    model.dedup_and_sort();

    let digest = AuditDigest(fnv1a_64(&model.data));
    let mut steps = Vec::new();
    let repairable = model.build_plan(&mut steps);

    Ok(AuditReport {
        version,
        file_len: inner_len,
        digest,
        defects: model.defects,
        strict: validation.is_strict(),
        steps,
        repairable,
    })
}

impl AuditModel {
    fn sector_range(&self, sector_id: u32) -> Option<(usize, usize)> {
        let start = (sector_id as usize + 1) * self.sector_len;
        let end = start + self.sector_len;
        if sector_id <= consts::MAX_REGULAR_SECTOR && end <= self.data.len() {
            Some((start, end))
        } else {
            None
        }
    }

    /// Loads the DIFAT chain and the ordered list of FAT sectors, recording
    /// DIFAT evidence instead of aborting.
    fn load_difat(&mut self, validation: Validation) {
        let entries_per_difat_sector = self.sector_len / size_of::<u32>();
        self.difat
            .extend_from_slice(&self.header.initial_difat_entries);
        let mut seen = FnvHashMap::<u32, u32>::default();
        let mut current = self.header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.record(
                    DefectTable::Difat,
                    DefectKind::OutOfBounds,
                    current as u64,
                    format!(
                        "DIFAT chain next pointer is sector {current}, but \
                         file has only {} sectors",
                        self.num_sectors
                    ),
                );
                return;
            }
            if let Some(&first) = seen.get(&current) {
                self.record(
                    DefectTable::Difat,
                    DefectKind::Cycle,
                    current as u64,
                    format!(
                        "DIFAT chain revisits sector {current}, first used \
                         after sector {first}"
                    ),
                );
                return;
            }
            seen.insert(current, *self.difat_sector_ids.last().unwrap_or(&0));
            self.difat_sector_ids.push(current);
            let (start, end) = self.sector_range(current).unwrap();
            let sector = &self.data[start..end];
            for i in 0..entries_per_difat_sector - 1 {
                let next = u32::from_le_bytes([
                    sector[4 * i],
                    sector[4 * i + 1],
                    sector[4 * i + 2],
                    sector[4 * i + 3],
                ]);
                if next != consts::FREE_SECTOR
                    && next > consts::MAX_REGULAR_SECTOR
                {
                    self.record(
                        DefectTable::Difat,
                        DefectKind::InvalidEntry,
                        next as u64,
                        format!(
                            "DIFAT sector {current} entry {} refers to \
                             invalid sector index 0x{next:08X}",
                            i
                        ),
                    );
                } else {
                    self.difat.push(next);
                }
            }
            let offset = end - 4;
            current = u32::from_le_bytes([
                self.data[offset],
                self.data[offset + 1],
                self.data[offset + 2],
                self.data[offset + 3],
            ]);
            if validation.is_strict() && current == consts::FREE_SECTOR {
                self.record(
                    DefectTable::Difat,
                    DefectKind::InvalidEntry,
                    current as u64,
                    "DIFAT chain terminates with FREE_SECTOR instead of \
                     END_OF_CHAIN"
                        .to_string(),
                );
                return;
            }
        }

        // Mirror open_internal's permissive repair of zero-padded DIFAT
        // sectors (issue #41): only strip trailing zeroes beyond the header
        // entries.
        if !validation.is_strict() {
            while self.difat.len()
                > consts::NUM_DIFAT_ENTRIES_IN_HEADER
                && self.difat.len() > self.header.num_fat_sectors as usize
                && self.difat.last() == Some(&0)
            {
                self.difat.pop();
            }
        }
        while self.difat.last() == Some(&consts::FREE_SECTOR) {
            self.difat.pop();
        }

        if validation.is_strict()
            && self.header.num_difat_sectors as usize
                != self.difat_sector_ids.len()
        {
            self.record(
                DefectTable::Difat,
                DefectKind::LengthMismatch,
                self.header.num_difat_sectors as u64,
                format!(
                    "header num_difat_sectors is {}, but the DIFAT chain \
                     has {} sectors",
                    self.header.num_difat_sectors,
                    self.difat_sector_ids.len()
                ),
            );
        }
        if validation.is_strict()
            && self.header.num_fat_sectors as usize != self.difat.len()
        {
            self.record(
                DefectTable::Difat,
                DefectKind::LengthMismatch,
                self.header.num_fat_sectors as u64,
                format!(
                    "header num_fat_sectors is {}, but the DIFAT lists {} \
                     FAT sectors",
                    self.header.num_fat_sectors,
                    self.difat.len()
                ),
            );
        }
    }

    /// Loads every FAT sector listed by the DIFAT and pads/truncates to one
    /// entry per file sector, recording evidence along the way.
    fn load_fat(&mut self, validation: Validation) {
        let entries_per_sector = self.sector_len / size_of::<u32>();
        for &sector_index in self.difat.iter() {
            if sector_index >= self.num_sectors {
                self.record(
                    DefectTable::Difat,
                    DefectKind::OutOfBounds,
                    sector_index as u64,
                    format!(
                        "DIFAT lists FAT sector {sector_index}, but file has \
                         only {} sectors",
                        self.num_sectors
                    ),
                );
                continue;
            }
            if let Some((start, end)) = self.sector_range(sector_index) {
                let sector = &self.data[start..end];
                for i in 0..entries_per_sector {
                    let entry = u32::from_le_bytes([
                        sector[4 * i],
                        sector[4 * i + 1],
                        sector[4 * i + 2],
                        sector[4 * i + 3],
                    ]);
                    self.fat.push(entry);
                }
            }
        }
        if !validation.is_strict() {
            while self.fat.len() > self.num_sectors as usize {
                match self.fat.last() {
                    Some(&0)
                    | Some(&consts::DIFAT_SECTOR)
                    | Some(&consts::FAT_SECTOR)
                    | Some(&consts::FREE_SECTOR) => {
                        self.fat.pop();
                    }
                    _ => break,
                }
            }
        }
        while self.fat.len() > self.num_sectors as usize
            && self.fat.last() == Some(&consts::FREE_SECTOR)
        {
            self.fat.pop();
        }
        if self.fat.len() > self.num_sectors as usize {
            self.record(
                DefectTable::Fat,
                DefectKind::LengthMismatch,
                self.num_sectors as u64,
                format!(
                    "FAT has {} entries, but file has only {} sectors",
                    self.fat.len(),
                    self.num_sectors
                ),
            );
        }
        while self.fat.len() < self.num_sectors as usize {
            self.fat.push(consts::FREE_SECTOR);
        }
    }
}

impl AuditModel {
    /// Follows a regular-sector chain through the raw FAT, stopping at the
    /// first out-of-bounds edge or cycle and recording evidence there.  This
    /// is the same edge classification the open path uses in
    /// `Allocator::next`/`Chain::new`, but non-fatal so later stages can run.
    fn follow_fat(&mut self, start: u32, context: &str) -> Vec<u32> {
        let mut ids = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return ids;
        }
        let mut current = start;
        let mut seen = FnvHashMap::<u32, u32>::default();
        loop {
            ids.push(current);
            let next = match self.fat.get(current as usize).copied() {
                Some(next) => next,
                None => {
                    if !self.has(
                        DefectTable::Fat,
                        DefectKind::OutOfBounds,
                        current as u64,
                    ) {
                        self.record(
                            DefectTable::Fat,
                            DefectKind::OutOfBounds,
                            current as u64,
                            format!(
                                "{context}: chain reaches sector {current}, \
                                 which has no FAT entry"
                            ),
                        );
                    }
                    break;
                }
            };
            match next {
                consts::END_OF_CHAIN => break,
                consts::FREE_SECTOR => {
                    if !self.has(
                        DefectTable::Fat,
                        DefectKind::InvalidEntry,
                        current as u64,
                    ) {
                        self.record(
                            DefectTable::Fat,
                            DefectKind::InvalidEntry,
                            current as u64,
                            format!(
                                "{context}: sector {current} is marked FREE \
                                 while it is part of a chain"
                            ),
                        );
                    }
                    break;
                }
                _ if next > consts::MAX_REGULAR_SECTOR
                    || next as usize >= self.fat.len() =>
                {
                    if !self.has(
                        DefectTable::Fat,
                        DefectKind::OutOfBounds,
                        next as u64,
                    ) {
                        self.record(
                            DefectTable::Fat,
                            DefectKind::OutOfBounds,
                            next as u64,
                            format!(
                                "{context}: sector {current} points to sector \
                                 {next}, outside the FAT"
                            ),
                        );
                    }
                    break;
                }
                _ => {}
            }
            if seen.contains_key(&next) {
                if !self.has(
                    DefectTable::Fat,
                    DefectKind::Cycle,
                    next as u64,
                ) {
                    self.record(
                        DefectTable::Fat,
                        DefectKind::Cycle,
                        next as u64,
                        format!(
                            "{context}: sector {current} points back to \
                             sector {next}, which the chain already visited"
                        ),
                    );
                }
                break;
            }
            seen.insert(next, current);
            current = next;
        }
        ids
    }

    /// Loads the directory chain slots.  Directory-chain problems (first
    /// sector missing, unparseable slots) are recorded here; FAT-level chain
    /// problems at those sectors are recorded by [`follow_fat`].
    fn load_directory(&mut self, validation: Validation) {
        let first = self.header.first_dir_sector;
        if first == consts::END_OF_CHAIN || first == consts::FREE_SECTOR {
            // No directory chain at all: the root entry is missing.
            self.record(
                DefectTable::Directory,
                DefectKind::Truncated,
                first as u64,
                "directory chain is empty, so the root entry is missing"
                    .to_string(),
            );
            return;
        }
        if first > consts::MAX_REGULAR_SECTOR || first >= self.num_sectors {
            self.record(
                DefectTable::Directory,
                DefectKind::OutOfBounds,
                first as u64,
                format!(
                    "first directory sector is {first}, but the file has \
                     only {} sectors",
                    self.num_sectors
                ),
            );
            return;
        }
        let ids = self.follow_fat(first, "directory chain");
        let entries_per_sector = self.version.dir_entries_per_sector();
        for sector_id in ids.iter().copied() {
            let (start, _end) = match self.sector_range(sector_id) {
                Some(range) => range,
                None => continue,
            };
            for slot_index in 0..entries_per_sector {
                let slot_start = start + slot_index * consts::DIR_ENTRY_LEN;
                let bytes =
                    &self.data[slot_start..slot_start + consts::DIR_ENTRY_LEN];
                match DirEntry::read_from(
                    &mut &bytes[..],
                    self.version,
                    // The audit always parses permissively here so that one
                    // bad slot does not hide the rest; strict-only
                    // directory-entry complaints are re-checked in `analyze`.
                    Validation::Permissive,
                ) {
                    Ok(entry) => {
                        self.slots.push(Slot { entry: Some(entry), parse_error: None });
                    }
                    Err(err) => {
                        let stream_id = self.slots.len() as u32;
                        self.record(
                            DefectTable::Directory,
                            DefectKind::InvalidEntry,
                            stream_id as u64,
                            format!(
                                "directory entry {stream_id} in sector \
                                 {sector_id} cannot be parsed: {err}"
                            ),
                        );
                        self.slots
                            .push(Slot { entry: None, parse_error: Some(err.to_string()) });
                    }
                }
            }
        }
        self.dir_sector_ids = ids;

        if validation.is_strict()
            && self.version == Version::V4
            && self.header.num_dir_sectors as usize
                != self.dir_sector_ids.len()
        {
            self.record(
                DefectTable::Directory,
                DefectKind::LengthMismatch,
                self.header.num_dir_sectors as u64,
                format!(
                    "header num_dir_sectors is {}, but the directory chain \
                     has {} sectors",
                    self.header.num_dir_sectors,
                    self.dir_sector_ids.len()
                ),
            );
        }
    }

    /// Loads the raw MiniFAT entries by following the MiniFAT chain.
    fn load_minifat(&mut self, validation: Validation) {
        let first = self.header.first_minifat_sector;
        if first == consts::END_OF_CHAIN || first == consts::FREE_SECTOR {
            if validation.is_strict()
                && self.header.num_minifat_sectors != 0
            {
                self.record(
                    DefectTable::MiniFat,
                    DefectKind::LengthMismatch,
                    self.header.num_minifat_sectors as u64,
                    format!(
                        "header num_minifat_sectors is {}, but there is no \
                         MiniFAT chain",
                        self.header.num_minifat_sectors
                    ),
                );
            }
            return;
        }
        let ids = self.follow_fat(first, "MiniFAT chain");
        let entries_per_sector = self.sector_len / size_of::<u32>();
        for sector_id in ids.iter().copied() {
            if let Some((start, end)) = self.sector_range(sector_id) {
                let sector = &self.data[start..end];
                for i in 0..entries_per_sector {
                    let entry = u32::from_le_bytes([
                        sector[4 * i],
                        sector[4 * i + 1],
                        sector[4 * i + 2],
                        sector[4 * i + 3],
                    ]);
                    self.minifat.push(entry);
                }
            }
        }
        let chain_sectors = ids.len() as u32;
        if validation.is_strict()
            && self.header.num_minifat_sectors != chain_sectors
        {
            self.record(
                DefectTable::MiniFat,
                DefectKind::LengthMismatch,
                self.header.num_minifat_sectors as u64,
                format!(
                    "header num_minifat_sectors is {}, but the MiniFAT chain \
                     has {} sectors",
                    self.header.num_minifat_sectors,
                    chain_sectors
                ),
            );
        }
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            self.minifat.pop();
        }
    }
}

impl AuditModel {
    fn slot(&self, stream_id: u32) -> Option<&Slot> {
        self.slots.get(stream_id as usize)
    }

    fn entry(&self, stream_id: u32) -> Option<&DirEntry> {
        self.slot(stream_id).and_then(|slot| slot.entry.as_ref())
    }

    /// Runs all cross-table analyses.
    fn analyze(&mut self, validation: Validation) {
        let difat_marked = self.analyze_fat_marks(validation);
        let minifat_sectors = if self.header.first_minifat_sector
            != consts::END_OF_CHAIN
            && self.header.first_minifat_sector != consts::FREE_SECTOR
        {
            self.follow_fat(
                self.header.first_minifat_sector,
                "MiniFAT chain",
            )
        } else {
            Vec::new()
        };
        let ministream_sectors = {
            let start = self
                .entry(consts::ROOT_STREAM_ID)
                .map(|e| e.start_sector)
                .unwrap_or(consts::END_OF_CHAIN);
            if start != consts::END_OF_CHAIN && start != consts::FREE_SECTOR {
                self.follow_fat(start, "mini stream")
            } else {
                Vec::new()
            }
        };

        // Assign FAT ownership in a fixed, scheduling-independent order; a
        // sector claimed by two distinct roots is one DoubleClaim.
        let mut owners: FnvHashMap<u32, Owner> = FnvHashMap::default();
        for id in self.difat.iter().copied() {
            if difat_marked.contains(&id) {
                owners.insert(id, Owner::FatSector);
            }
        }
        for &id in self.difat_sector_ids.iter() {
            owners.insert(id, Owner::DifatSector);
        }
        for &id in self.dir_sector_ids.iter() {
            self.claim_fat_sector(id, &mut owners, &Owner::Directory);
        }
        for &id in minifat_sectors.iter() {
            self.claim_fat_sector(id, &mut owners, &Owner::MiniFat);
        }
        for &id in ministream_sectors.iter() {
            self.claim_fat_sector(id, &mut owners, &Owner::MiniStream);
        }

        // Walk every stream's chain and check its declared length.
        self.analyze_stream_chains(&mut owners);

        // Orphans: regular sectors nobody owns.
        self.find_fat_orphans(&owners);

        // Directory tree shape and MiniFAT structure.
        let stream_chain_sectors = self.analyze_directory_tree(validation);
        self.analyze_minifat(
            validation,
            &ministream_sectors,
            stream_chain_sectors,
        );
    }

    /// Records FAT-marking and static pointer evidence, and returns the set
    /// of sector ids that genuinely hold a FAT sector.
    fn analyze_fat_marks(
        &mut self,
        validation: Validation,
    ) -> Vec<u32> {
        for &difat_sector in self.difat_sector_ids.iter() {
            match self.fat.get(difat_sector as usize).copied() {
                Some(mark) if mark == consts::DIFAT_SECTOR => {}
                Some(_) => {
                    if validation.is_strict() {
                        self.record(
                            DefectTable::Difat,
                            DefectKind::InvalidEntry,
                            difat_sector as u64,
                            format!(
                                "DIFAT sector {difat_sector} is not marked \
                                 DIFAT_SECTOR in the FAT"
                            ),
                        );
                    }
                }
                None => {}
            }
        }
        let mut fat_sector_ids = Vec::new();
        for &fat_sector in self.difat.iter() {
            match self.fat.get(fat_sector as usize).copied() {
                Some(mark) if mark == consts::FAT_SECTOR => {
                    fat_sector_ids.push(fat_sector);
                }
                Some(_) => {
                    if validation.is_strict() {
                        self.record(
                            DefectTable::Fat,
                            DefectKind::InvalidEntry,
                            fat_sector as u64,
                            format!(
                                "FAT sector {fat_sector} is not marked \
                                 FAT_SECTOR in the FAT"
                            ),
                        );
                    }
                    fat_sector_ids.push(fat_sector);
                }
                None => {}
            }
        }
        // Static pointer scan: out-of-range numeric pointers and sectors
        // pointed at twice.  Scanning the whole table (not just reachable
        // chains) keeps the result independent of visit order.
        let mut pointees: FnvHashMap<u32, u32> = FnvHashMap::default();
        for (from, &to) in self.fat.iter().enumerate() {
            let from = from as u32;
            if to == consts::INVALID_SECTOR {
                self.record(
                    DefectTable::Fat,
                    DefectKind::InvalidEntry,
                    from as u64,
                    format!("FAT entry of sector {from} is INVALID_SECTOR"),
                );
            } else if to <= consts::MAX_REGULAR_SECTOR {
                if to as usize >= self.fat.len() {
                    self.record(
                        DefectTable::Fat,
                        DefectKind::OutOfBounds,
                        to as u64,
                        format!(
                            "sector {from} points to sector {to}, but the FAT \
                             has only {} entries",
                            self.fat.len()
                        ),
                    );
                } else if let Some(&first_from) = pointees.get(&to) {
                    self.record(
                        DefectTable::Fat,
                        DefectKind::DoubleClaim,
                        to as u64,
                        format!(
                            "sector {to} is pointed to by both sector \
                             {first_from} and sector {from}"
                        ),
                    );
                } else {
                    pointees.insert(to, from);
                }
            }
        }
        fat_sector_ids
    }

    fn claim_fat_sector(
        &mut self,
        id: u32,
        owners: &mut FnvHashMap<u32, Owner>,
        claimant: &Owner,
    ) {
        if id as usize >= self.fat.len() {
            return;
        }
        match owners.get(&id).cloned() {
            Some(existing) if &existing != claimant => {
                self.record(
                    DefectTable::Fat,
                    DefectKind::DoubleClaim,
                    id as u64,
                    format!(
                        "sector {id} is claimed by both the {} and the {}",
                        existing.label(),
                        claimant.label()
                    ),
                );
            }
            _ => {
                owners.insert(id, claimant.clone());
            }
        }
    }

    fn analyze_stream_chains(&mut self, owners: &mut FnvHashMap<u32, Owner>) {
        // Iterate by stream id for determinism.
        let stream_ids: Vec<u32> = (0..self.slots.len() as u32).collect();
        for stream_id in stream_ids {
            let (obj_type, start_sector, stream_len) = {
                let Some(entry) = self.entry(stream_id) else { continue };
                (entry.obj_type, entry.start_sector, entry.stream_len)
            };
            if obj_type == ObjType::Storage {
                if start_sector != 0 {
                    self.record(
                        DefectTable::Directory,
                        DefectKind::InvalidEntry,
                        stream_id as u64,
                        format!(
                            "storage entry {stream_id} has non-zero starting \
                             sector {start_sector}"
                        ),
                    );
                }
                continue;
            }
            if obj_type != ObjType::Stream {
                continue;
            }
            if stream_len == 0 {
                continue;
            }
            let ids = if stream_len < consts::MINI_STREAM_CUTOFF as u64 {
                // Mini streams are checked against the MiniFAT later.
                continue;
            } else {
                if start_sector == consts::END_OF_CHAIN
                    || start_sector == consts::FREE_SECTOR
                {
                    self.record(
                        DefectTable::Directory,
                        DefectKind::LengthMismatch,
                        stream_id as u64,
                        format!(
                            "stream entry {stream_id} declares {} bytes but \
                             has no starting sector",
                            stream_len
                        ),
                    );
                    continue;
                }
                let ids = self.follow_fat(
                    start_sector,
                    &format!("stream entry {stream_id}"),
                );
                for &id in ids.iter() {
                    let claimant = Owner::Stream(stream_id);
                    self.claim_fat_sector(id, owners, &claimant);
                }
                ids
            };
            let capacity = ids.len() as u64 * self.sector_len as u64;
            if stream_len > capacity {
                self.record(
                    DefectTable::Directory,
                    DefectKind::LengthMismatch,
                    stream_id as u64,
                    format!(
                        "stream entry {stream_id} declares {} bytes, but its \
                         FAT chain starting at {start_sector} holds only {} \
                         bytes",
                        stream_len, capacity
                    ),
                );
            }
        }
    }

    fn find_fat_orphans(&mut self, owners: &FnvHashMap<u32, Owner>) {
        let mut index = 0u32;
        while index < self.fat.len() as u32 {
            let entry = self.fat[index as usize];
            let unowned = !owners.contains_key(&index)
                && entry != consts::FREE_SECTOR
                && entry != consts::FAT_SECTOR
                && entry != consts::DIFAT_SECTOR;
            if unowned {
                let start = index;
                let mut count = 0u64;
                while index < self.fat.len() as u32
                    && !owners.contains_key(&index)
                    && self.fat[index as usize] != consts::FREE_SECTOR
                    && self.fat[index as usize] != consts::FAT_SECTOR
                    && self.fat[index as usize] != consts::DIFAT_SECTOR
                {
                    count += 1;
                    index += 1;
                }
                self.record(
                    DefectTable::Fat,
                    DefectKind::Orphan,
                    start as u64,
                    format!(
                        "{count} unreachable sector(s) starting at sector \
                         {start} are not part of any FAT chain"
                    ),
                );
            } else {
                index += 1;
            }
        }
    }
}
