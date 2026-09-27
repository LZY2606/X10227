//! Opt-in structural auditing of compound files.
//!
//! Unlike normal opening, auditing never mutates the input and never rejects a
//! file merely because its allocation tables are damaged.  It walks the FAT,
//! DIFAT, MiniFAT, and directory chains as laid out in the file, records each
//! piece of damage as a separate [`Finding`] (keeping cycles, out-of-bounds
//! links, double allocation, orphan sectors, and declared-length
//! disagreements apart), and produces a read-only [`RepairPlan`].
//!
//! Applying a plan requires an explicit [`RepairPlan::apply`] call with a
//! writer.  The plan carries a digest of the bytes it was computed from; if
//! the input changed after auditing, application is refused without writing
//! a single byte.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hasher;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::sync::atomic::{AtomicU64, Ordering};

use fnv::FnvHasher;

use crate::internal::{consts, DirEntry, Header, ObjType, Validation, Version};

//===========================================================================//

/// Which of a compound file's allocation structures a finding concerns.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Table {
    /// The File Allocation Table chains.
    Fat,
    /// The Double-Indirect FAT chain and its FAT-sector pointers.
    Difat,
    /// The MiniFAT chains (mini-stream allocation).
    Minifat,
    /// The directory entry chain.
    Directory,
}

impl Table {
    fn as_str(self) -> &'static str {
        match self {
            Table::Fat => "FAT",
            Table::Difat => "DIFAT",
            Table::Minifat => "MiniFAT",
            Table::Directory => "directory chain",
        }
    }
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The kind of structural damage recorded in a [`Finding`].
///
/// The variants keep the five failure classes apart: a cycle is not reported
/// as an out-of-bounds link, a sector claimed by two chains is not an orphan,
/// and a length disagreement is separate from the chain damage behind it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Corruption {
    /// A chain points back to a sector already seen in the same chain.
    Cycle,
    /// An entry points outside the table/file or misuses a sentinel.
    OutOfBounds,
    /// The same sector is claimed by more than one allocation chain.
    DoubleAllocation,
    /// A sector is neither reachable from any chain nor marked free/reserved.
    OrphanSector,
    /// A declared length does not match the sectors the chain provides.
    LengthMismatch,
    /// A table entry holds the reserved INVALIDSECT marker.
    InvalidEntry,
    /// The directory chain ends before all declared entries are walked.
    TruncatedDirectory,
    /// A header count field does not match the structure it describes.
    HeaderCountMismatch,
}

impl Corruption {
    fn as_str(self) -> &'static str {
        match self {
            Corruption::Cycle => "cycle",
            Corruption::OutOfBounds => "out-of-bounds link",
            Corruption::DoubleAllocation => "double allocation",
            Corruption::OrphanSector => "orphan sector",
            Corruption::LengthMismatch => "declared length mismatch",
            Corruption::InvalidEntry => "invalid table entry",
            Corruption::TruncatedDirectory => "truncated directory chain",
            Corruption::HeaderCountMismatch => "header count mismatch",
        }
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One piece of damage evidence, located at the first offending position.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// The allocation structure the damage is in.
    pub table: Table,
    /// What kind of damage this is.
    pub corruption: Corruption,
    /// The index of the offending table entry, or the first orphan sector id.
    pub offset: u64,
    /// Sector or mini-sector ids reached, including the offending id last.
    pub context: Vec<u64>,
    /// Human-readable description of the violation.
    pub message: String,
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}: {} at offset {}",
            self.table, self.corruption, self.offset
        )?;
        if !self.context.is_empty() {
            write!(f, " (sectors {:?})", self.context)?;
        }
        write!(f, ": {}", self.message)
    }
}

/// A digest of the bytes a plan was computed from (a content fingerprint).
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AuditDigest(u64);

impl AuditDigest {
    /// The 64-bit fingerprint value.
    pub fn value(self) -> u64 {
        self.0
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

/// The result of an opt-in structural audit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuditReport {
    version: Version,
    audit_id: u64,
    digest: AuditDigest,
    file_len: u64,
    findings: Vec<Finding>,
    edits: Vec<Edit>,
}

static NEXT_AUDIT_ID: AtomicU64 = AtomicU64::new(1);

impl AuditReport {
    /// All damage findings in stable order (table, then offset, then kind).
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// True if no damage was found in any allocation structure.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// The content fingerprint of the audited bytes.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// The unique id of this audit run.
    pub fn audit_id(&self) -> u64 {
        self.audit_id
    }

    /// Produces the read-only repair plan.
    pub fn plan(&self) -> RepairPlan {
        let mut steps = Vec::with_capacity(self.findings.len());
        for finding in self.findings.iter() {
            let key = (
                table_rank(finding.table),
                finding.offset,
                corruption_rank(finding.corruption),
            );
            let edit = self
                .edits
                .iter()
                .find(|edit| edit.key == key)
                .cloned()
                .unwrap_or(Edit {
                    key,
                    file_offset: u64::MAX,
                    bytes: Vec::new(),
                });
            steps.push(RepairStep {
                finding: finding.clone(),
                description: step_description(finding),
                edit,
            });
        }
        RepairPlan {
            digest: self.digest,
            expected_len: self.file_len,
            audit_id: self.audit_id,
            steps,
        }
    }
}

fn step_description(finding: &Finding) -> String {
    match finding.corruption {
        Corruption::Cycle => format!(
            "Break the {} cycle by writing END_OF_CHAIN at the entry that \
             points back.",
            finding.table
        ),
        Corruption::OutOfBounds => format!(
            "Sever the dangling {} link with END_OF_CHAIN.",
            finding.table
        ),
        Corruption::DoubleAllocation => format!(
            "Keep the first owner of the contested sector and write \
             END_OF_CHAIN in the later {} chain.",
            finding.table
        ),
        Corruption::OrphanSector => {
            "Mark the unreachable sector as FREESECT in the FAT.".to_string()
        }
        Corruption::LengthMismatch => format!(
            "Update the declared length to match the reachable sectors of \
             the {} chain.",
            finding.table
        ),
        Corruption::InvalidEntry => {
            "Replace the reserved INVALIDSECT marker with FREESECT."
                .to_string()
        }
        Corruption::TruncatedDirectory => {
            "Set the header directory-sector count to the actual chain \
             length."
                .to_string()
        }
        Corruption::HeaderCountMismatch => {
            "Set the header count field to the actual chain length."
                .to_string()
        }
    }
}

/// One byte edit, keyed by the finding it resolves.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Edit {
    key: (u8, u64, u8),
    file_offset: u64,
    bytes: Vec<u8>,
}

/// One step of a read-only repair plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    /// The finding this step repairs.
    pub finding: Finding,
    /// What the step does, in human-readable terms.
    pub description: String,
    edit: Edit,
}

/// Why applying a [`RepairPlan`] was refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PlanMismatch {
    /// The current digest no longer matches the audit digest.
    DigestChanged,
    /// The file's length differs from when it was audited.
    LengthChanged,
}

impl fmt::Display for PlanMismatch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PlanMismatch::DigestChanged => f.write_str(
                "the file changed after the audit (digest mismatch)",
            ),
            PlanMismatch::LengthChanged => f.write_str(
                "the file length changed after the audit",
            ),
        }
    }
}

/// A read-only repair plan produced by [`AuditReport::plan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPlan {
    digest: AuditDigest,
    expected_len: u64,
    audit_id: u64,
    steps: Vec<RepairStep>,
}

impl RepairPlan {
    /// The ordered repair steps.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }

    /// The audit digest required for the plan to still apply.
    pub fn prerequisite_digest(&self) -> AuditDigest {
        self.digest
    }

    /// The id of the audit run that produced this plan.
    pub fn audit_id(&self) -> u64 {
        self.audit_id
    }

    /// Summarizes prerequisites and intended changes without writing.
    pub fn summary(&self) -> String {
        let mut out = format!(
            "Repair plan (audit {}, prerequisite digest {}): {} step(s)",
            self.audit_id,
            self.digest,
            self.steps.len()
        );
        for (index, step) in self.steps.iter().enumerate() {
            out.push_str(&format!("\n  {}. {}", index + 1, step.description));
        }
        out
    }

    /// Applies the plan only while the writer still contains the audited
    /// bytes.  Nothing is written on a digest mismatch.
    ///
    /// If a write fails midway, edits already made are rolled back in
    /// reverse order, so a failed application leaves the file byte-identical
    /// to its pre-apply state.
    pub fn apply<W: Read + Write + Seek>(
        &self,
        writer: &mut W,
    ) -> io::Result<()> {
        self.check_prerequisites(writer)?;
        let mut applied: Vec<Edit> = Vec::new();
        if let Err(write_err) = self.write_edits(writer, &mut applied) {
            if let Err(rollback_err) = self.rollback(writer, &mut applied) {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!(
                        "repair write failed ({write_err}) and rollback also \
                         failed ({rollback_err}); file may be damaged"
                    ),
                ));
            }
            return Err(write_err);
        }
        writer.flush()?;
        Ok(())
    }

    fn check_prerequisites<W: Read + Seek>(
        &self,
        reader: &mut W,
    ) -> io::Result<()> {
        let len = reader.seek(SeekFrom::End(0))?;
        if len != self.expected_len {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                PlanMismatch::LengthChanged.to_string(),
            ));
        }
        let digest = hash_reader(reader)?;
        if AuditDigest(digest) != self.digest {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                PlanMismatch::DigestChanged.to_string(),
            ));
        }
        Ok(())
    }

    fn write_edits<W: Read + Write + Seek>(
        &self,
        writer: &mut W,
        applied: &mut Vec<Edit>,
    ) -> io::Result<()> {
        for step in self.steps.iter() {
            if step.edit.file_offset == u64::MAX {
                continue;
            }
            let mut original = vec![0u8; step.edit.bytes.len()];
            writer.seek(SeekFrom::Start(step.edit.file_offset))?;
            writer.read_exact(&mut original)?;
            writer.seek(SeekFrom::Start(step.edit.file_offset))?;
            writer.write_all(&step.edit.bytes)?;
            applied.push(Edit {
                key: step.edit.key,
                file_offset: step.edit.file_offset,
                bytes: original,
            });
        }
        Ok(())
    }

    fn rollback<W: Write + Seek>(
        &self,
        writer: &mut W,
        applied: &mut Vec<Edit>,
    ) -> io::Result<()> {
        while let Some(edit) = applied.pop() {
            writer.seek(SeekFrom::Start(edit.file_offset))?;
            writer.write_all(&edit.bytes)?;
        }
        writer.flush()
    }
}

//===========================================================================//

const HEADER_NUM_DIR_SECTORS_OFFSET: u64 = 0x28;
const HEADER_NUM_FAT_SECTORS_OFFSET: u64 = 0x2c;
const HEADER_NUM_MINIFAT_SECTORS_OFFSET: u64 = 0x40;
const HEADER_NUM_DIFAT_SECTORS_OFFSET: u64 = 0x48;
const DIR_ENTRY_STREAM_LEN_OFFSET: u64 = 120;

/// Tables as laid out in the file, before interpretation.
struct RawFile {
    version: Version,
    sector_len: u64,
    file_len: u64,
    num_sectors: u32,
    header: Header,
    fat: Vec<u32>,
    difat_chain: Vec<u32>,
    difat_entries: Vec<u32>,
    dir_chain: Vec<u32>,
    dir_entries: Vec<(u32, DirEntry)>,
    minifat: Vec<u32>,
    minifat_chain: Vec<u32>,
}

/// Audits the compound file in `reader` without modifying it.
///
/// Shared implementation behind the public entry points
/// [`crate::OpenOptions::audit_with`] and [`crate::audit`].
pub(crate) fn audit_reader<F: Read + Seek>(
    mut reader: F,
) -> io::Result<AuditReport> {
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    audit_bytes(&data)
}

fn audit_bytes(data: &[u8]) -> io::Result<AuditReport> {
    let mut auditor = Auditor::new(data)?;
    auditor.collect();
    Ok(auditor.finish())
}

fn hash_bytes(data: &[u8]) -> u64 {
    let mut hasher = FnvHasher::default();
    hasher.write(data);
    hasher.finish()
}

fn hash_reader<R: Read + Seek>(reader: &mut R) -> io::Result<u64> {
    reader.seek(SeekFrom::Start(0))?;
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    Ok(hash_bytes(&data))
}

fn read_u32(data: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes([
        data[offset],
        data[offset + 1],
        data[offset + 2],
        data[offset + 3],
    ])
}

fn valid_sector(sector: u32, num_sectors: u32) -> bool {
    sector <= consts::MAX_REGULAR_SECTOR && sector < num_sectors
}

fn entries_per_fat_sector(sector_len: u64) -> u32 {
    (sector_len / 4) as u32
}

/// File offset of the FAT cell describing `sector`.
fn fat_cell_offset(sector: u32, sector_len: u64, fat_sectors: &[u32]) -> u64 {
    let per_sector = entries_per_fat_sector(sector_len);
    let fat_sector_index = sector / per_sector;
    let within = sector % per_sector;
    let fat_sector = fat_sectors[fat_sector_index as usize];
    (u64::from(fat_sector) + 1) * sector_len + u64::from(within) * 4
}

/// File offset of the MiniFAT cell describing `mini_sector`.
fn minifat_cell_offset(
    mini_sector: u32,
    sector_len: u64,
    minifat_chain: &[u32],
) -> u64 {
    let per_sector = entries_per_fat_sector(sector_len);
    let fat_sector =
        minifat_chain[(mini_sector / per_sector) as usize];
    let within = mini_sector % per_sector;
    (u64::from(fat_sector) + 1) * sector_len + u64::from(within) * 4
}

/// File offset of a directory-entry field.
fn dir_entry_field_offset(
    stream_id: u32,
    entries_per_sector: u32,
    dir_chain: &[u32],
    sector_len: u64,
    field_offset: u64,
) -> u64 {
    let sector = dir_chain[(stream_id / entries_per_sector) as usize];
    let slot = stream_id % entries_per_sector;
    (u64::from(sector) + 1) * sector_len
        + u64::from(slot) * consts::DIR_ENTRY_LEN as u64
        + field_offset
}

struct Auditor<'a> {
    data: &'a [u8],
    raw: RawFile,
    findings: Vec<Finding>,
    /// Collapsed edits keyed by finding offset.
    edits: HashMap<(u8, u64, u8), Edit>,
    /// FAT sector -> first chain that claims it.
    fat_claimed: HashMap<u32, ChainOwner>,
    /// FAT sectors reserved for FAT or DIFAT (never orphans or stream claims).
    reserved: HashSet<u32>,
}

#[derive(Clone, Copy)]
struct ChainOwner {
    start: u32,
}

impl<'a> Auditor<'a> {
    fn new(data: &'a [u8]) -> io::Result<Self> {
        if data.len() < consts::HEADER_LEN {
            invalid_data!(
                "Invalid CFB file ({} bytes is too small)",
                data.len()
            );
        }
        let header = Header::read_from(
            &mut io::Cursor::new(data),
            Validation::Permissive,
        )?;
        let version = header.version;
        let sector_len = version.sector_len() as u64;
        let file_len = data.len() as u64;
        let num_sectors = (file_len / sector_len) as u32 - 1;

        let mut auditor = Auditor {
            data,
            raw: RawFile {
                version,
                sector_len,
                file_len,
                num_sectors,
                header,
                fat: Vec::new(),
                difat_chain: Vec::new(),
                difat_entries: Vec::new(),
                dir_chain: Vec::new(),
                dir_entries: Vec::new(),
                minifat: Vec::new(),
                minifat_chain: Vec::new(),
            },
            findings: Vec::new(),
            edits: HashMap::new(),
            fat_claimed: HashMap::new(),
            reserved: HashSet::new(),
        };
        auditor.read_difat_and_fat();
        Ok(auditor)
    }

    fn sector_bytes(&self, sector: u32) -> &'a [u8] {
        let start = (u64::from(sector) + 1) * self.raw.sector_len;
        let end = (start + self.raw.sector_len).min(self.data.len() as u64);
        &self.data[start as usize..end as usize]
    }

    fn record(
        &mut self,
        table: Table,
        corruption: Corruption,
        offset: u64,
        context: Vec<u64>,
        message: String,
    ) {
        self.findings.push(Finding {
            table,
            corruption,
            offset,
            context,
            message,
        });
    }

    fn set_edit(
        &mut self,
        table: Table,
        finding_offset: u64,
        corruption: Corruption,
        file_offset: u64,
        bytes: Vec<u8>,
    ) {
        let key = (
            table_rank(table),
            finding_offset,
            corruption_rank(corruption),
        );
        self.edits.insert(key, Edit { key, file_offset, bytes });
    }

    fn set_fat_cell_edit(
        &mut self,
        table: Table,
        corruption: Corruption,
        sector: u32,
        value: u32,
    ) {
        let file_offset = fat_cell_offset(
            sector,
            self.raw.sector_len,
            &self.raw.difat_entries,
        );
        self.set_edit(
            table,
            u64::from(sector),
            corruption,
            file_offset,
            value.to_le_bytes().to_vec(),
        );
    }

    /// Reads the DIFAT chain and the FAT sectors it names, recording
    /// structural damage rather than failing.
    fn read_difat_and_fat(&mut self) {
        let sector_len = self.raw.sector_len as usize;
        let entries_per_difat_sector = sector_len / 4 - 1;

        for &entry in self.raw.header.initial_difat_entries.iter() {
            if entry == consts::FREE_SECTOR {
                break;
            }
            self.raw.difat_entries.push(entry);
        }

        let mut next = self.raw.header.first_difat_sector;
        let mut seen = HashSet::new();
        while next != consts::END_OF_CHAIN && next != consts::FREE_SECTOR {
            let current = next;
            if !valid_sector(current, self.raw.num_sectors) {
                self.record(
                    Table::Difat,
                    Corruption::OutOfBounds,
                    self.raw.difat_chain.len() as u64,
                    self.raw
                        .difat_chain
                        .iter()
                        .chain(Some(&current))
                        .map(|&s| u64::from(s))
                        .collect(),
                    format!(
                        "DIFAT chain reaches sector {current}, but the file \
                         has only {} sectors",
                        self.raw.num_sectors
                    ),
                );
                self.sever_difat_tail();
                break;
            }
            if !seen.insert(current) {
                self.record(
                    Table::Difat,
                    Corruption::Cycle,
                    self.raw.difat_chain.len() as u64,
                    self.raw
                        .difat_chain
                        .iter()
                        .chain(Some(&current))
                        .map(|&s| u64::from(s))
                        .collect(),
                    format!("DIFAT chain revisits sector {current}"),
                );
                self.sever_difat_tail();
                break;
            }
            self.raw.difat_chain.push(current);
            let bytes = self.sector_bytes(current);
            for slot in 0..entries_per_difat_sector {
                let entry = read_u32(bytes, slot * 4);
                if entry != consts::FREE_SECTOR {
                    self.raw.difat_entries.push(entry);
                }
            }
            next = read_u32(bytes, entries_per_difat_sector * 4);
        }

        for &fat_sector in self.raw.difat_entries.clone().iter() {
            if !valid_sector(fat_sector, self.raw.num_sectors) {
                self.record(
                    Table::Difat,
                    Corruption::OutOfBounds,
                    u64::from(fat_sector),
                    vec![u64::from(fat_sector)],
                    format!(
                        "DIFAT names FAT sector {fat_sector}, but the file \
                         has only {} sectors",
                        self.raw.num_sectors
                    ),
                );
                continue;
            }
            let bytes = self.sector_bytes(fat_sector);
            for slot in 0..sector_len / 4 {
                self.raw.fat.push(read_u32(bytes, slot * 4));
            }
        }
        let num_sectors = self.raw.num_sectors as usize;
        if self.raw.fat.len() < num_sectors {
            self.raw.fat.resize(num_sectors, consts::FREE_SECTOR);
        } else {
            self.raw.fat.truncate(num_sectors);
        }

        // FAT and DIFAT sectors are reserved; ignore their cell values for
        // ownership/orphan purposes.
        for &sector in self.raw.difat_entries.clone().iter() {
            if valid_sector(sector, self.raw.num_sectors) {
                self.reserved.insert(sector);
            }
        }
        for &sector in self.raw.difat_chain.iter() {
            self.reserved.insert(sector);
        }
    }

    fn sever_difat_tail(&mut self) {
        if let Some(&last) = self.raw.difat_chain.last() {
            let offset =
                (u64::from(last) + 1) * self.raw.sector_len
                    + self.raw.sector_len - 4;
            self.set_edit(
                Table::Difat,
                self.raw.difat_chain.len() as u64 - 1,
                Corruption::OutOfBounds,
                offset,
                consts::END_OF_CHAIN.to_le_bytes().to_vec(),
            );
            // A cyclic tail is also severed at the same last pointer.
            self.set_edit(
                Table::Difat,
                self.raw.difat_chain.len() as u64 - 1,
                Corruption::Cycle,
                offset,
                consts::END_OF_CHAIN.to_le_bytes().to_vec(),
            );
        }
    }

    fn fat_cell(&self, sector: u32) -> u32 {
        self.raw
            .fat
            .get(sector as usize)
            .copied()
            .unwrap_or(consts::FREE_SECTOR)
    }
}

//===========================================================================//

/// What a FAT chain is used for.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Anchor {
    Directory,
    Minifat,
    Stream(u32),
}

impl Anchor {
    fn table(self) -> Table {
        match self {
            Anchor::Directory => Table::Directory,
            Anchor::Minifat => Table::Fat,
            Anchor::Stream(_) => Table::Fat,
        }
    }
}

/// Result of walking one allocation chain.
struct WalkedChain {
    sectors: Vec<u32>,
}

impl<'a> Auditor<'a> {
    /// Walks a FAT chain, classifying damage, claiming sectors, and recording
    /// the repair edit for the first damaged edge.
    fn walk_fat_chain(&mut self, start: u32, anchor: Anchor) -> WalkedChain {
        let table = anchor.table();
        let mut sectors = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return WalkedChain { sectors };
        }
        let mut current = start;
        loop {
            if sectors.contains(&current) {
                let mut context =
                    sectors.iter().map(|&s| u64::from(s)).collect::<Vec<_>>();
                context.push(u64::from(current));
                let offender = *sectors.last().unwrap();
                self.record(
                    table,
                    Corruption::Cycle,
                    u64::from(offender),
                    context,
                    format!(
                        "chain starting at sector {start} loops back to \
                         sector {current}"
                    ),
                );
                self.set_fat_cell_edit(table, Corruption::Cycle, offender, consts::END_OF_CHAIN);
                return WalkedChain { sectors };
            }
            if !valid_sector(current, self.raw.num_sectors) {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(current)))
                    .collect();
                let offender = sectors.last().copied();
                self.record(
                    table,
                    Corruption::OutOfBounds,
                    u64::from(offender.unwrap_or(current)),
                    context,
                    format!(
                        "chain starting at sector {start} reaches sector \
                         {current}, outside the {} sectors of the file",
                        self.raw.num_sectors
                    ),
                );
                if let Some(offender) = offender {
                    self.set_fat_cell_edit(table, Corruption::OutOfBounds, offender, consts::END_OF_CHAIN);
                }
                return WalkedChain { sectors };
            }
            // Claim ownership (only stream chains are cross-checked; the
            // table chains walk first and never overlap them in a valid file).
            let contested = if let Anchor::Stream(_) = anchor {
                match self.fat_claimed.get(&current).copied() {
                    Some(owner) if owner.start != start => Some(owner),
                    _ => {
                        self.fat_claimed
                            .insert(current, ChainOwner { start });
                        None
                    }
                }
            } else {
                self.fat_claimed
                    .entry(current)
                    .or_insert(ChainOwner { start });
                None
            };
            if let Some(owner) = contested {
                let mut context =
                    sectors.iter().map(|&s| u64::from(s)).collect::<Vec<_>>();
                context.push(u64::from(owner.start));
                let offender = if sectors.len() >= 2 {
                    sectors[sectors.len() - 2]
                } else {
                    current
                };
                self.record(
                    Table::Fat,
                    Corruption::DoubleAllocation,
                    u64::from(offender),
                    context,
                    format!(
                        "sector {current} is already claimed by the chain \
                         starting at sector {}",
                        owner.start
                    ),
                );
                // Keep the first owner; detach this chain before the shared
                // sector by ending it at the predecessor.
                if sectors.len() >= 2 {
                    self.set_fat_cell_edit(Table::Fat, Corruption::DoubleAllocation, offender, consts::END_OF_CHAIN);
                }
                sectors.pop();
                return WalkedChain { sectors };
            }
            sectors.push(current);

            let next = self.fat_cell(current);
            if next == consts::END_OF_CHAIN {
                return WalkedChain { sectors };
            }
            if next == consts::INVALID_SECTOR {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(next)))
                    .collect();
                self.record(
                    table,
                    Corruption::InvalidEntry,
                    u64::from(current),
                    context,
                    format!(
                        "FAT entry for sector {current} is the reserved \
                         INVALIDSECT marker"
                    ),
                );
                self.set_fat_cell_edit(table, Corruption::InvalidEntry, current, consts::FREE_SECTOR);
                return WalkedChain { sectors };
            }
            if next == consts::FREE_SECTOR
                || next > consts::MAX_REGULAR_SECTOR
                || next >= self.raw.num_sectors
            {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(next)))
                    .collect();
                self.record(
                    table,
                    Corruption::OutOfBounds,
                    u64::from(current),
                    context,
                    format!(
                        "FAT entry for sector {current} points to {next}, \
                         which is not a valid sector in this file"
                    ),
                );
                self.set_fat_cell_edit(table, Corruption::OutOfBounds, current, consts::END_OF_CHAIN);
                return WalkedChain { sectors };
            }
            current = next;
        }
    }
}

//===========================================================================//

impl<'a> Auditor<'a> {
    /// Runs the full audit in a fixed order so findings are deterministic.
    fn collect(&mut self) {
        // 1. Table chains first (their sectors are claimed before streams):
        //    the directory chain, then the MiniFAT chain.
        let dir_walked = self.walk_fat_chain(
            self.raw.header.first_dir_sector,
            Anchor::Directory,
        );
        self.raw.dir_chain = dir_walked.sectors;
        self.parse_dir_entries();

        let minifat_start = match self.raw.header.first_minifat_sector {
            consts::FREE_SECTOR => consts::END_OF_CHAIN,
            start => start,
        };
        let minifat_walked =
            self.walk_fat_chain(minifat_start, Anchor::Minifat);
        self.raw.minifat_chain = minifat_walked.sectors;
        self.read_minifat_entries();

        // 2. The root entry's mini stream chain (regular FAT chain).
        let root_entry = self
            .raw
            .dir_entries
            .iter()
            .find(|(id, _)| *id == 0)
            .map(|(_, entry)| entry.clone());
        let mut mini_stream_chain: Vec<u32> = Vec::new();
        if let Some(root) = root_entry.as_ref() {
            let walked = self.walk_fat_chain(
                root.start_sector,
                Anchor::Stream(consts::ROOT_STREAM_ID),
            );
            mini_stream_chain = walked.sectors;
        }

        // 3. Every declared stream chain, recording length mismatches.
        let entries = self.raw.dir_entries.clone();
        for (stream_id, entry) in entries.iter() {
            match entry.obj_type {
                ObjType::Stream => {
                    self.audit_named_stream(
                        *stream_id,
                        entry,
                        &mini_stream_chain,
                    );
                }
                ObjType::Root => {
                    self.audit_root_stream(entry, &mini_stream_chain);
                }
                _ => {}
            }
        }

        // 4. Global FAT issues: INVALIDSECT cells and orphan sectors.
        self.audit_fat_globals();

        // 5. Header counts vs. actual chains.
        self.audit_header_counts();
    }

    fn parse_dir_entries(&mut self) {
        let entries_per_sector =
            self.raw.version.dir_entries_per_sector() as u32;
        let chain = self.raw.dir_chain.clone();
        for (chain_index, sector) in chain.iter().enumerate() {
            let bytes = self.sector_bytes(*sector);
            for slot in 0..entries_per_sector {
                let start = slot as usize * consts::DIR_ENTRY_LEN;
                let entry_bytes =
                    &bytes[start..start + consts::DIR_ENTRY_LEN];
                let stream_id =
                    chain_index as u32 * entries_per_sector + slot;
                match DirEntry::read_from(
                    &mut io::Cursor::new(entry_bytes),
                    self.raw.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => {
                        self.raw.dir_entries.push((stream_id, entry));
                    }
                    Err(error) => self.record(
                        Table::Directory,
                        Corruption::InvalidEntry,
                        u64::from(stream_id),
                        vec![u64::from(*sector), u64::from(slot)],
                        format!(
                            "directory entry {stream_id} (sector {sector}) \
                             is unreadable: {error}"
                        ),
                    ),
                }
            }
        }
    }

    fn read_minifat_entries(&mut self) {
        for sector in self.raw.minifat_chain.clone().iter() {
            let bytes = self.sector_bytes(*sector);
            for slot in 0..self.raw.sector_len as usize / 4 {
                self.raw.minifat.push(read_u32(bytes, slot * 4));
            }
        }
        while self.raw.minifat.last() == Some(&consts::FREE_SECTOR) {
            self.raw.minifat.pop();
        }
    }

    /// Audits a regular or mini stream's chain against its declared length.
    fn audit_named_stream(
        &mut self,
        stream_id: u32,
        entry: &DirEntry,
        mini_stream_chain: &[u32],
    ) {
        let is_mini = entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
            && entry.start_sector != consts::END_OF_CHAIN
            && entry.stream_len > 0;
        if is_mini {
            let sectors =
                self.walk_mini_chain(stream_id, entry.start_sector, entry);
            let available =
                sectors.len() as u64 * consts::MINI_SECTOR_LEN as u64;
            if available < entry.stream_len {
                self.record_length_mismatch(
                    Table::Minifat,
                    stream_id,
                    entry,
                    available,
                    true,
                    mini_stream_chain,
                );
            }
        } else if entry.start_sector != consts::END_OF_CHAIN
            || entry.stream_len > 0
        {
            let walked =
                self.walk_fat_chain(entry.start_sector, Anchor::Stream(stream_id));
            let available =
                walked.sectors.len() as u64 * self.raw.sector_len;
            if entry.stream_len > available {
                self.record_length_mismatch(
                    Table::Fat,
                    stream_id,
                    entry,
                    available,
                    false,
                    mini_stream_chain,
                );
            }
        }
    }

    fn audit_root_stream(&mut self, entry: &DirEntry, mini_stream_chain: &[u32]) {
        // The root stream must be a regular FAT chain; its declared length is
        // the size of the mini stream.
        let available =
            mini_stream_chain.len() as u64 * self.raw.sector_len;
        if entry.stream_len > available {
            self.record_length_mismatch(
                Table::Fat,
                consts::ROOT_STREAM_ID,
                entry,
                available,
                false,
                mini_stream_chain,
            );
        }
    }

    fn record_length_mismatch(
        &mut self,
        table: Table,
        stream_id: u32,
        entry: &DirEntry,
        available: u64,
        is_mini: bool,
        mini_stream_chain: &[u32],
    ) {
        let context = match table {
            Table::Minifat => vec![
                u64::from(entry.start_sector),
                entry.stream_len,
                available,
            ],
            _ => vec![u64::from(entry.start_sector), entry.stream_len, available],
        };
        self.record(
            table,
            Corruption::LengthMismatch,
            u64::from(stream_id),
            context,
            format!(
                "stream {} declares {} bytes but its chain provides only \
                 {} bytes",
                entry.name, entry.stream_len, available
            ),
        );
        // Repair: shrink the declared length to what is reachable.
        let new_len = entry.stream_len.min(available);
        let offset = if is_mini || table == Table::Minifat {
            self.dir_entry_offset(stream_id, DIR_ENTRY_STREAM_LEN_OFFSET)
        } else {
            self.dir_entry_offset(stream_id, DIR_ENTRY_STREAM_LEN_OFFSET)
        };
        let _ = mini_stream_chain;
        self.set_edit(
            table,
            u64::from(stream_id),
            Corruption::LengthMismatch,
            offset,
            new_len.to_le_bytes().to_vec(),
        );
    }

    fn dir_entry_offset(&self, stream_id: u32, field_offset: u64) -> u64 {
        let entries_per_sector =
            self.raw.version.dir_entries_per_sector() as u32;
        dir_entry_field_offset(
            stream_id,
            entries_per_sector,
            &self.raw.dir_chain,
            self.raw.sector_len,
            field_offset,
        )
    }
}

//===========================================================================//

impl<'a> Auditor<'a> {
    /// Walks a MiniFAT chain, classifying cycles/out-of-bounds/double
    /// allocation and checking every reached mini sector against the root
    /// mini stream's capacity.
    fn walk_mini_chain(
        &mut self,
        stream_id: u32,
        start: u32,
        entry: &DirEntry,
    ) -> Vec<u32> {
        let mut sectors = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return sectors;
        }
        let root_stream_len = self
            .raw
            .dir_entries
            .iter()
            .find(|(id, _)| *id == 0)
            .map(|(_, root)| root.stream_len)
            .unwrap_or(0);
        let mini_capacity =
            (root_stream_len / consts::MINI_SECTOR_LEN as u64) as u32;
        let mut current = start;
        let mut seen_starts: HashMap<u32, u32> = HashMap::new();
        loop {
            if sectors.contains(&current) {
                let mut context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .collect::<Vec<_>>();
                context.push(u64::from(current));
                let offender = *sectors.last().unwrap();
                self.record(
                    Table::Minifat,
                    Corruption::Cycle,
                    u64::from(offender),
                    context,
                    format!(
                        "mini chain of stream {} loops back to mini sector \
                         {current}",
                        entry.name
                    ),
                );
                self.set_minifat_cell_edit(Corruption::Cycle, offender, consts::END_OF_CHAIN);
                return sectors;
            }
            if current as usize >= self.raw.minifat.len()
                || current >= mini_capacity
            {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(current)))
                    .collect();
                let offender = sectors.last().copied();
                self.record(
                    Table::Minifat,
                    Corruption::OutOfBounds,
                    u64::from(offender.unwrap_or(current)),
                    context,
                    format!(
                        "mini chain of stream {} reaches mini sector \
                         {current}, outside the MiniFAT ({} entries) or the \
                         root mini stream ({} mini sectors)",
                        entry.name,
                        self.raw.minifat.len(),
                        mini_capacity
                    ),
                );
                if let Some(offender) = offender {
                    self.set_minifat_cell_edit(Corruption::OutOfBounds, offender, consts::END_OF_CHAIN);
                }
                return sectors;
            }
            // Cross-chain double allocation of mini sectors.
            if let Some(&other_stream) = seen_starts.get(&current) {
                if other_stream != stream_id {
                    let mut context = sectors
                        .iter()
                        .map(|&s| u64::from(s))
                        .collect::<Vec<_>>();
                    context.push(u64::from(other_stream));
                    let offender = if sectors.len() >= 2 {
                        sectors[sectors.len() - 2]
                    } else {
                        current
                    };
                    self.record(
                        Table::Minifat,
                        Corruption::DoubleAllocation,
                        u64::from(offender),
                        context,
                        format!(
                            "mini sector {current} is shared with stream id \
                             {other_stream}"
                        ),
                    );
                    if sectors.len() >= 2 {
                        self.set_minifat_cell_edit(
                            Corruption::DoubleAllocation,
                            offender,
                            consts::END_OF_CHAIN,
                        );
                    }
                    sectors.pop();
                    return sectors;
                }
            } else {
                seen_starts.insert(current, stream_id);
            }
            sectors.push(current);
            let next = self.raw.minifat[current as usize];
            if next == consts::END_OF_CHAIN {
                return sectors;
            }
            if next == consts::INVALID_SECTOR {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(next)))
                    .collect();
                self.record(
                    Table::Minifat,
                    Corruption::InvalidEntry,
                    u64::from(current),
                    context,
                    format!(
                        "MiniFAT entry for mini sector {current} is the \
                         reserved INVALIDSECT marker"
                    ),
                );
                self.set_minifat_cell_edit(Corruption::InvalidEntry, current, consts::FREE_SECTOR);
                return sectors;
            }
            if next == consts::FREE_SECTOR || next > consts::MAX_REGULAR_SECTOR
            {
                let context = sectors
                    .iter()
                    .map(|&s| u64::from(s))
                    .chain(Some(u64::from(next)))
                    .collect();
                self.record(
                    Table::Minifat,
                    Corruption::OutOfBounds,
                    u64::from(current),
                    context,
                    format!(
                        "MiniFAT entry for mini sector {current} is \
                         0x{next:08X}, not a valid mini sector"
                    ),
                );
                self.set_minifat_cell_edit(Corruption::OutOfBounds, current, consts::END_OF_CHAIN);
                return sectors;
            }
            current = next;
        }
    }

    fn set_minifat_cell_edit(
        &mut self,
        corruption: Corruption,
        mini_sector: u32,
        value: u32,
    ) {
        if self.raw.minifat_chain.is_empty() {
            return;
        }
        let offset = minifat_cell_offset(
            mini_sector,
            self.raw.sector_len,
            &self.raw.minifat_chain,
        );
        self.set_edit(
            Table::Minifat,
            u64::from(mini_sector),
            corruption,
            offset,
            value.to_le_bytes().to_vec(),
        );
    }

    /// Scans every FAT cell for INVALIDSECT markers and every sector for
    /// orphan status.
    fn audit_fat_globals(&mut self) {
        let num = self.raw.num_sectors;
        for sector in 0..num {
            let cell = self.fat_cell(sector);
            if cell == consts::INVALID_SECTOR
                && !self.reserved.contains(&sector)
            {
                self.record(
                    Table::Fat,
                    Corruption::InvalidEntry,
                    u64::from(sector),
                    vec![u64::from(sector)],
                    format!(
                        "FAT entry for sector {sector} is the reserved \
                         INVALIDSECT marker"
                    ),
                );
                let offset = fat_cell_offset(
                    sector,
                    self.raw.sector_len,
                    &self.raw.difat_entries,
                );
                self.set_edit(
                    Table::Fat,
                    u64::from(sector),
                    Corruption::InvalidEntry,
                    offset,
                    consts::FREE_SECTOR.to_le_bytes().to_vec(),
                );
            }
        }
        for sector in 0..num {
            if self.reserved.contains(&sector) {
                continue;
            }
            let claimed = self.fat_claimed.contains_key(&sector);
            let cell = self.fat_cell(sector);
            if !claimed
                && cell != consts::FREE_SECTOR
                && cell != consts::FAT_SECTOR
                && cell != consts::DIFAT_SECTOR
            {
                self.record(
                    Table::Fat,
                    Corruption::OrphanSector,
                    u64::from(sector),
                    vec![u64::from(sector), u64::from(cell)],
                    format!(
                        "sector {sector} is neither reachable from any chain \
                         nor marked FREESECT (its FAT entry is 0x{cell:08X})"
                    ),
                );
                let offset = fat_cell_offset(
                    sector,
                    self.raw.sector_len,
                    &self.raw.difat_entries,
                );
                self.set_edit(
                    Table::Fat,
                    u64::from(sector),
                    Corruption::OrphanSector,
                    offset,
                    consts::FREE_SECTOR.to_le_bytes().to_vec(),
                );
            }
        }
    }
}

//===========================================================================//

impl<'a> Auditor<'a> {
    fn audit_header_counts(&mut self) {
        let header = self.raw.header.clone();

        // V4 records the number of directory sectors; V3 requires zero.
        if self.raw.version == Version::V4 {
            let actual = self.raw.dir_chain.len() as u32;
            if header.num_dir_sectors != actual {
                self.record(
                    Table::Directory,
                    Corruption::TruncatedDirectory,
                    0,
                    vec![u64::from(header.num_dir_sectors), u64::from(actual)],
                    format!(
                        "header declares {} directory sector(s), but the \
                         directory chain has {actual}",
                        header.num_dir_sectors
                    ),
                );
                self.set_edit(
                    Table::Directory,
                    0,
                    Corruption::TruncatedDirectory,
                    HEADER_NUM_DIR_SECTORS_OFFSET,
                    actual.to_le_bytes().to_vec(),
                );
            }
        } else if header.num_dir_sectors != 0 {
            self.record(
                Table::Directory,
                Corruption::HeaderCountMismatch,
                0,
                vec![u64::from(header.num_dir_sectors), 0],
                "V3 header must declare zero directory sectors".to_string(),
            );
            self.set_edit(
                Table::Directory,
                0,
                Corruption::HeaderCountMismatch,
                HEADER_NUM_DIR_SECTORS_OFFSET,
                0u32.to_le_bytes().to_vec(),
            );
        }

        let actual_fat = self.raw.difat_entries.len() as u32;
        if header.num_fat_sectors != actual_fat {
            self.record(
                Table::Difat,
                Corruption::HeaderCountMismatch,
                1,
                vec![u64::from(header.num_fat_sectors), u64::from(actual_fat)],
                format!(
                    "header declares {} FAT sector(s), but the DIFAT lists \
                     {actual_fat}",
                    header.num_fat_sectors
                ),
            );
            self.set_edit(
                Table::Difat,
                1,
                Corruption::HeaderCountMismatch,
                HEADER_NUM_FAT_SECTORS_OFFSET,
                actual_fat.to_le_bytes().to_vec(),
            );
        }

        let actual_minifat = self.raw.minifat_chain.len() as u32;
        if header.first_minifat_sector != consts::END_OF_CHAIN
            && header.first_minifat_sector != consts::FREE_SECTOR
            && header.num_minifat_sectors != actual_minifat
        {
            self.record(
                Table::Minifat,
                Corruption::HeaderCountMismatch,
                2,
                vec![
                    u64::from(header.num_minifat_sectors),
                    u64::from(actual_minifat),
                ],
                format!(
                    "header declares {} MiniFAT sector(s), but the MiniFAT \
                     chain has {actual_minifat}",
                    header.num_minifat_sectors
                ),
            );
            self.set_edit(
                Table::Minifat,
                2,
                Corruption::HeaderCountMismatch,
                HEADER_NUM_MINIFAT_SECTORS_OFFSET,
                actual_minifat.to_le_bytes().to_vec(),
            );
        }

        let actual_difat = self.raw.difat_chain.len() as u32;
        if header.num_difat_sectors != actual_difat {
            self.record(
                Table::Difat,
                Corruption::HeaderCountMismatch,
                3,
                vec![
                    u64::from(header.num_difat_sectors),
                    u64::from(actual_difat),
                ],
                format!(
                    "header declares {} DIFAT sector(s), but the DIFAT chain \
                     has {actual_difat}",
                    header.num_difat_sectors
                ),
            );
            self.set_edit(
                Table::Difat,
                3,
                Corruption::HeaderCountMismatch,
                HEADER_NUM_DIFAT_SECTORS_OFFSET,
                actual_difat.to_le_bytes().to_vec(),
            );
        }
    }

    fn finish(mut self) -> AuditReport {
        // Deterministic, stable ordering: table, then offset, then kind.
        self.findings.sort_by(|a, b| {
            (table_rank(a.table), a.offset, corruption_rank(a.corruption))
                .cmp(&(
                    table_rank(b.table),
                    b.offset,
                    corruption_rank(b.corruption),
                ))
                .then_with(|| a.message.cmp(&b.message))
        });
        self.findings.dedup();
        let mut edits: Vec<Edit> = self.edits.into_values().collect();
        edits.sort_by_key(|edit| edit.key);
        let digest = AuditDigest(hash_bytes(self.data));
        AuditReport {
            version: self.raw.version,
            audit_id: NEXT_AUDIT_ID.fetch_add(1, Ordering::Relaxed),
            digest,
            file_len: self.raw.file_len,
            findings: self.findings,
            edits,
        }
    }
}

fn table_rank(table: Table) -> u8 {
    match table {
        Table::Fat => 0,
        Table::Difat => 1,
        Table::Minifat => 2,
        Table::Directory => 3,
    }
}

fn corruption_rank(corruption: Corruption) -> u8 {
    match corruption {
        Corruption::Cycle => 0,
        Corruption::OutOfBounds => 1,
        Corruption::DoubleAllocation => 2,
        Corruption::OrphanSector => 3,
        Corruption::LengthMismatch => 4,
        Corruption::InvalidEntry => 5,
        Corruption::TruncatedDirectory => 6,
        Corruption::HeaderCountMismatch => 7,
    }
}
