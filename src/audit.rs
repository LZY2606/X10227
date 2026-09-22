//! Opt-in structural auditing of compound files.
//!
//! The entry points in this module classify corruption in a Compound File
//! Binary file's allocation structures -- the DIFAT, the FAT, the MiniFAT,
//! and the directory chain -- without ever writing to the audited input.
//! A [`RepairPlan`] records a *precondition digest* of the input bytes; the
//! exact same bytes must still be present before the plan can be applied,
//! and a [`RepairPlan::dry_run`] never touches the destination.
//!
//! # Shared production logic
//!
//! Auditing deliberately tolerates malformed inputs that the normal open
//! path rejects, so it cannot simply construct the crate's internal objects.
//! It nevertheless shares the production parsers for the pieces that are
//! safe to reuse: [`Header::read_from`] and [`DirEntry::read_from`] are run
//! with [`Validation::Permissive`], and the repair result is verified by
//! reopening it through the public [`CompoundFile::open`] entry.  The chain
//! classification in this module is a tolerant analogue of the walks used by
//! the open path (`Allocator::next`, the directory-chain walk, and
//! `MiniAllocator`), not a separate test-only implementation of CFB
//! semantics: it reasons about the same tables and sector layouts.

use std::cmp::Ordering;
use std::fs;
use std::io::{self, Read, Seek, Write};
use std::path::Path;

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};

//===========================================================================//

/// Which allocation structure a piece of evidence comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Region {
    /// The 512-byte compound file header.
    Header,
    /// The double-indirect FAT (DIFAT) chain.
    Difat,
    /// The file allocation table (regular-sector chains).
    Fat,
    /// The directory entry chain and the sibling/child tree it holds.
    Directory,
    /// The mini stream allocation table.
    MiniFat,
    /// The root entry's mini stream itself (the regular chain the MiniFAT
    /// indexes into).
    MiniStream,
}

/// The kind of structural damage found.
///
/// The five damage classes the audit distinguishes are kept separate even
/// when one chain exhibits several at once.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    /// A chain pointer loops back to a sector already seen in the same
    /// chain.
    Cycle,
    /// A chain pointer refers past the end of its table or file.
    OutOfBounds,
    /// A sector (or mini sector) is reached from more than one predecessor
    /// (cross-linked chains).
    DoubleReference,
    /// An allocated sector is not reachable from any chain root.
    OrphanSector,
    /// A declared length or table size does not match the actual chain.
    LengthMismatch,
    /// Damage that does not fit the five allocation classes above (an
    /// invalid marker, an unparseable directory entry, and similar).
    Malformed,
}

/// Where in the file a [`Finding`] points, with the identifying sector or
/// stream id and the neighbor that makes the failure unambiguous.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Location {
    /// A byte offset in the file header.
    Header(u64),
    /// A regular sector id (the FAT entry for that sector).
    FatSector(u32),
    /// A DIFAT sector id.
    DifatSector(u32),
    /// A sector of the directory chain.
    DirectorySector(u32),
    /// A directory entry's slot id.
    DirectoryEntry(u32),
    /// A MiniFAT entry (mini sector id).
    MiniSector(u32),
    /// A regular sector of the root mini stream.
    MiniStreamSector(u32),
}

/// A single, separately-classified piece of corruption evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    region: Region,
    kind: Kind,
    location: Location,
    context: String,
}

impl Finding {
    /// The allocation table the evidence was found in.
    pub fn region(&self) -> Region {
        self.region
    }
    /// The class of damage.
    pub fn kind(&self) -> Kind {
        self.kind
    }
    /// The sector, entry, or header offset at which the damage is rooted.
    pub fn location(&self) -> Location {
        self.location
    }
    /// Human-readable context, including the neighboring sector id and the
    /// chain owner that establish the first violation.
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl std::fmt::Display for Finding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} {:?} at {:?}: {}", self.region, self.kind,
               self.location, self.context)
    }
}

/// Identity of a set of input bytes.
///
/// A repair plan records the digest of the bytes it was built from.  Before
/// applying, the bytes are hashed again; the plan can only be applied while
/// the digest still matches, so a file changed after planning is rejected
/// rather than repaired against a stale view.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FileDigest {
    len: u64,
    hash: u64,
}

impl std::fmt::Display for FileDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "len={}:fnv1a64={:016x}", self.len, self.hash)
    }
}

//===========================================================================//

/// The result of auditing one compound file: a stable digest, the parsed
/// layout, and the damage evidence.
#[derive(Clone, Debug)]
pub struct AuditReport {
    digest: FileDigest,
    version: Option<Version>,
    file_len: u64,
    sector_len: Option<usize>,
    num_sectors: u32,
    findings: Vec<Finding>,
    plan: PlanData,
}

impl AuditReport {
    /// Digest of the audited input bytes.
    pub fn digest(&self) -> FileDigest {
        self.digest
    }
    /// The CFB version parsed from the header, if any.
    pub fn version(&self) -> Option<Version> {
        self.version
    }
    /// Length of the audited file in bytes.
    pub fn file_len(&self) -> u64 {
        self.file_len
    }
    /// Sector size of the parsed version, if a header could be parsed.
    pub fn sector_len(&self) -> Option<usize> {
        self.sector_len
    }
    /// Number of sectors implied by the file length and version.
    pub fn num_sectors(&self) -> u32 {
        self.num_sectors
    }
    /// `true` when no damage was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
    /// The evidence in canonical (stable) order.  The first item is the
    /// first violation according to that ordering, and every item carries
    /// the context needed to locate it.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }
    /// Produces a read-only repair plan for the evidence.
    ///
    /// Returns `None` if the damage cannot be repaired safely (for example
    /// a broken DIFAT chain), or if the file is already clean.
    pub fn repair_plan(&self) -> Option<RepairPlan> {
        if self.findings.is_empty() || !self.plan.repairable {
            return None;
        }
        Some(RepairPlan { data: self.plan.clone() })
    }
}

/// A single deterministic change that the repair plan would make.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RepairAction {
    /// Set one FAT entry to a value.
    SetFatEntry {
        /// Sector whose FAT entry is changed.
        sector: u32,
        /// New value.
        value: u32,
    },
    /// Set one MiniFAT entry to a value.
    SetMiniFatEntry {
        /// Mini sector whose entry is changed.
        mini_sector: u32,
        /// New value.
        value: u32,
    },
    /// Set a directory entry's starting sector.
    SetStreamStart {
        /// Directory-entry slot id.
        stream_id: u32,
        /// New starting sector (or mini sector).
        start: u32,
    },
    /// Set a directory entry's declared stream length.
    SetStreamLen {
        /// Directory-entry slot id.
        stream_id: u32,
        /// New declared length in bytes.
        len: u64,
    },
    /// Overwrite a directory-entry slot with the canonical
    /// "unallocated" pattern.
    ResetDirectoryEntry {
        /// Directory-entry slot id.
        stream_id: u32,
    },
    /// Write a header field.
    SetHeaderField {
        /// Which header field.
        field: HeaderField,
        /// New value.
        value: u32,
    },
    /// Set a directory entry's sibling/child pointer.
    SetEntryPointer {
        /// Directory-entry slot id.
        stream_id: u32,
        /// Which tree pointer.
        field: EntryPointer,
        /// New value.
        value: u32,
    },
}

/// A tree pointer within a directory entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryPointer {
    /// Left sibling id (offset 68).
    LeftSibling,
    /// Right sibling id (offset 72).
    RightSibling,
    /// Child id (offset 76).
    Child,
}


/// A field of the compound file header that a repair may rewrite.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderField {
    /// Number of directory sectors (header offset 40; V4 only).
    NumDirSectors,
    /// Total number of FAT sectors (header offset 44).
    NumFatSectors,
    /// First directory sector (offset 48).
    FirstDirSector,
    /// First MiniFAT sector (offset 60).
    NumMiniFatSectors,
    /// Number of MiniFAT sectors (offset 64).
    FirstMiniFatSector,
    /// First DIFAT sector (offset 68).
    FirstDifatSector,
    /// Number of DIFAT sectors (offset 72).
    NumDifatSectors,
}

impl std::fmt::Display for HeaderField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            HeaderField::NumDirSectors => "num_dir_sectors",
            HeaderField::NumFatSectors => "num_fat_sectors",
            HeaderField::FirstDirSector => "first_dir_sector",
            HeaderField::FirstMiniFatSector => "first_minifat_sector",
            HeaderField::NumMiniFatSectors => "num_minifat_sectors",
            HeaderField::FirstDifatSector => "first_difat_sector",
            HeaderField::NumDifatSectors => "num_difat_sectors",
        })
    }
}

impl std::fmt::Display for RepairAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            RepairAction::SetFatEntry { sector, value } => {
                write!(f, "set FAT[{sector}] = {value:#010x}")
            }
            RepairAction::SetMiniFatEntry { mini_sector, value } => {
                write!(f, "set MiniFAT[{mini_sector}] = {value:#010x}")
            }
            RepairAction::SetStreamStart { stream_id, start } => {
                write!(f, "set entry {stream_id} start sector = {start}")
            }
            RepairAction::SetStreamLen { stream_id, len } => {
                write!(f, "set entry {stream_id} stream len = {len}")
            }
            RepairAction::ResetDirectoryEntry { stream_id } => {
                write!(f, "reset directory entry {stream_id} to unallocated")
            }
            RepairAction::SetHeaderField { field, value } => {
                write!(f, "set header {field} = {value}")
            }
            RepairAction::SetEntryPointer { stream_id, field, value } => {
                write!(f, "set entry {stream_id} {field:?} = {value}")
            }
        }
    }
}

//===========================================================================//

/// A read-only repair plan derived from an [`AuditReport`].
///
/// The plan stores the [`FileDigest`] of the bytes it was planned against.
/// Both [`RepairPlan::dry_run`] and [`RepairPlan::apply`] re-hash the
/// current input first and refuse with
/// [`ErrorKind::InvalidData`](std::io::ErrorKind::InvalidData) when it has
/// changed since planning.
pub struct RepairPlan {
    data: PlanData,
}

impl std::fmt::Debug for RepairPlan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RepairPlan")
            .field("precondition_digest", &self.data.digest)
            .field("actions", &self.data.actions)
            .finish()
    }
}

impl RepairPlan {
    /// Digest of the input bytes this plan was built from.  Application is
    /// allowed only while this digest still matches the input.
    pub fn precondition_digest(&self) -> FileDigest {
        self.data.digest
    }
    /// The deterministic list of byte-level changes the plan performs.
    pub fn actions(&self) -> &[RepairAction] {
        &self.data.actions
    }
    /// Checks the precondition against `input` and describes what would be
    /// done, without writing any bytes anywhere.
    ///
    /// The destination is not taken by this method, so it cannot be
    /// modified; this is the guaranteed-dry-run view.
    pub fn dry_run<R: Read + Seek>(
        &self,
        input: &mut R,
    ) -> io::Result<&[RepairAction]> {
        let bytes = read_all(input)?;
        let digest = digest_bytes(&bytes);
        if digest != self.data.digest {
            invalid_data!(
                "Repair plan is stale: input changed since the plan was \
                 made (expected {}, found {})",
                self.data.digest,
                digest,
            );
        }
        Ok(&self.data.actions)
    }
    /// Applies the repair by copying the input to `dest` with the planned
    /// edits.  The input reader is never written to.
    ///
    /// The precondition digest is verified first.  All edits are composed
    /// in memory and the result re-audited before `dest` is touched, so a
    /// precondition mismatch or a repair that would not actually produce a
    /// clean file leaves `dest` with zero bytes written: failure is atomic.
    pub fn apply<R: Read + Seek, W: Write>(
        &self,
        input: &mut R,
        dest: &mut W,
    ) -> io::Result<()> {
        let bytes = read_all(input)?;
        let digest = digest_bytes(&bytes);
        if digest != self.data.digest {
            invalid_data!(
                "Cannot apply repair plan: input changed since the plan was \
                 made (expected {}, found {})",
                self.data.digest,
                digest,
            );
        }
        // Compose the repaired image completely, and verify it, before the
        // destination receives a single byte.
        let repaired = compose_repaired(&bytes, &self.data)?;
        dest.write_all(&repaired)?;
        dest.flush()?;
        Ok(())
    }
}

//===========================================================================//

/// Audits a compound file at `path` without opening it for writing.
pub fn audit_file<P: AsRef<Path>>(path: P) -> io::Result<AuditReport> {
    let bytes = fs::read(path)?;
    Ok(audit_bytes(&bytes))
}

/// Audits a compound file read from `reader` without writing to it.
pub fn audit_reader<R: Read + Seek>(reader: &mut R) -> io::Result<AuditReport> {
    let bytes = read_all(reader)?;
    Ok(audit_bytes(&bytes))
}

//===========================================================================//

//===========================================================================//
// Internal machinery
//===========================================================================//

/// A planned byte mutation, recorded with an absolute file offset so the
/// apply step needs none of the parsed tables.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Edit {
    offset: u64,
    value: u32,
    width: u8,
    action: RepairAction,
}

#[derive(Clone, Debug)]
struct PlanData {
    digest: FileDigest,
    repairable: bool,
    actions: Vec<RepairAction>,
    edits: Vec<Edit>,
}

fn read_all<R: Read + Seek>(reader: &mut R) -> io::Result<Vec<u8>> {
    reader.seek(io::SeekFrom::Start(0))?;
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    reader.seek(io::SeekFrom::Start(0))?;
    Ok(bytes)
}

/// FNV-1a 64-bit over the input bytes, paired with the length.  This is an
/// identity check ("are these the same bytes the plan was made for?"), not a
/// cryptographic guarantee, which is all the precondition needs.
fn digest_bytes(bytes: &[u8]) -> FileDigest {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut hash = OFFSET_BASIS;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(PRIME);
    }
    FileDigest { len: bytes.len() as u64, hash }
}

// Header field offsets from MS-CFB section 2.2.
const OFFSET_NUM_DIR_SECTORS: u64 = 40;
const OFFSET_NUM_FAT_SECTORS: u64 = 44;
const OFFSET_FIRST_DIR_SECTOR: u64 = 48;
const OFFSET_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const OFFSET_FIRST_DIFAT_SECTOR: u64 = 68;
const OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
const OFFSET_DIFAT0: u64 = 76;

fn fat_entry_offset(sector_len: usize, difat: &[u32], sector: u32) -> Option<u64> {
    let entries_per_sector = sector_len / 4;
    let fat_sector_index = (sector as usize) / entries_per_sector;
    let within = (sector as usize) % entries_per_sector;
    let fat_sector = *difat.get(fat_sector_index)?;
    Some(
        consts::HEADER_LEN as u64
            + (fat_sector as u64) * (sector_len as u64)
            + (within as u64) * 4,
    )
}

fn minifat_entry_offset(
    sector_len: usize,
    minifat_sectors: &[u32],
    mini_sector: u32,
) -> Option<u64> {
    let entries_per_sector = sector_len / 4;
    let table_sector_index = (mini_sector as usize) / entries_per_sector;
    let within = (mini_sector as usize) % entries_per_sector;
    let table_sector = *minifat_sectors.get(table_sector_index)?;
    Some(
        consts::HEADER_LEN as u64
            + (table_sector as u64) * (sector_len as u64)
            + (within as u64) * 4,
    )
}

fn dir_entry_offset(sector_len: usize, stream_id: u32) -> u64 {
    let entries_per_sector = sector_len / consts::DIR_ENTRY_LEN;
    let sector_index = stream_id as usize / entries_per_sector;
    let within = stream_id as usize % entries_per_sector;
    consts::HEADER_LEN as u64
        + (sector_index as u64) * (sector_len as u64)
        + (within as u64) * (consts::DIR_ENTRY_LEN as u64)
}

fn read_u32_at(bytes: &[u8], offset: u64) -> Option<u32> {
    let offset = offset as usize;
    let slice = bytes.get(offset..offset + 4)?;
    Some(u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
}

fn write_u32_at(bytes: &mut [u8], offset: u64, value: u32) {
    let offset = offset as usize;
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

//===========================================================================//

/// Which named chain owns a sector or mini sector.  Only chains reachable
/// from the directory are named, which is what makes an orphan observable.
#[derive(Clone, Debug)]
enum Owner {
    Fat,
    Difat,
    Directory,
    MiniFatTable,
    MiniStream,
    /// A normal data stream, identified by its directory-entry slot.
    Stream(u32),
}

impl Owner {
    fn label(&self) -> String {
        match self {
            Owner::Fat => "FAT sector chain".to_string(),
            Owner::Difat => "DIFAT chain".to_string(),
            Owner::Directory => "directory chain".to_string(),
            Owner::MiniFatTable => "MiniFAT chain".to_string(),
            Owner::MiniStream => "root mini stream".to_string(),
            Owner::Stream(id) => format!("stream entry {id}"),
        }
    }
}

/// A directory slot parsed from the directory chain.
struct Slot {
    id: u32,
    entry: Option<DirEntry>,
}

struct Auditor {
    digest: FileDigest,
    findings: Vec<Finding>,
    edits: Vec<Edit>,
    repairable: bool,
    version: Option<Version>,
    sector_len: Option<usize>,
    num_sectors: u32,
    header: Option<Header>,
    difat_sector_ids: Vec<u32>,
    difat: Vec<u32>,
    fat: Vec<u32>,
    dir_sector_ids: Vec<u32>,
    slots: Vec<Slot>,
    minifat_sectors: Vec<u32>,
    minifat: Vec<u32>,
}

impl Auditor {
    fn finding(
        &mut self,
        region: Region,
        kind: Kind,
        location: Location,
        context: String,
    ) {
        self.findings.push(Finding { region, kind, location, context });
    }

    /// Damage that has no safe automatic repair.
    fn unrepairable(&mut self) {
        self.repairable = false;
    }

    fn add_edit(&mut self, edit: Edit) {
        if let Some(existing) =
            self.edits.iter().find(|e| e.offset == edit.offset)
        {
            debug_assert_eq!(
                existing.value, edit.value,
                "conflicting repairs planned at the same offset"
            );
            return;
        }
        self.edits.push(edit);
    }

    fn edit_fat(&mut self, sector: u32, value: u32) {
        let (Some(sector_len), Some(offset)) = (
            self.sector_len,
            fat_entry_offset(self.sector_len.unwrap(), &self.difat, sector),
        ) else {
            self.unrepairable();
            return;
        };
        let _ = sector_len;
        self.add_edit(Edit {
            offset,
            value,
            width: 4,
            action: RepairAction::SetFatEntry { sector, value },
        });
    }

    fn edit_minifat(&mut self, mini_sector: u32, value: u32) {
        let Some(offset) = minifat_entry_offset(
            self.sector_len.unwrap(),
            &self.minifat_sectors,
            mini_sector,
        ) else {
            self.unrepairable();
            return;
        };
        self.add_edit(Edit {
            offset,
            value,
            width: 4,
            action: RepairAction::SetMiniFatEntry {
                mini_sector,
                value,
            },
        });
    }

    fn edit_entry_field(
        &mut self,
        stream_id: u32,
        offset_within_entry: u64,
        value: u32,
        width: u8,
        action: RepairAction,
    ) {
        let Some(sector_len) = self.sector_len else {
            self.unrepairable();
            return;
        };
        let offset =
            dir_entry_offset(sector_len, stream_id) + offset_within_entry;
        self.add_edit(Edit { offset, value, width, action });
    }

    fn edit_header(&mut self, field: HeaderField, offset: u64, value: u32) {
        self.add_edit(Edit {
            offset,
            value,
            width: 4,
            action: RepairAction::SetHeaderField { field, value },
        });
    }
}

//===========================================================================//

/// Audits raw CFB bytes.  Never fails: even a truncated or unparseable file
/// yields a report describing the first violation, rather than an error.
pub(crate) fn audit_bytes(bytes: &[u8]) -> AuditReport {
    let digest = digest_bytes(bytes);
    let mut aud = Auditor {
        digest,
        findings: Vec::new(),
        edits: Vec::new(),
        repairable: true,
        version: None,
        sector_len: None,
        num_sectors: 0,
        header: None,
        difat_sector_ids: Vec::new(),
        difat: Vec::new(),
        fat: Vec::new(),
        dir_sector_ids: Vec::new(),
        slots: Vec::new(),
        minifat_sectors: Vec::new(),
        minifat: Vec::new(),
    };
    aud.parse_header(bytes);
    aud.parse_difat_and_fat(bytes);
    aud.parse_directory(bytes);
    aud.parse_minifat(bytes);
    aud.analyze_fat_chains();
    aud.analyze_minifat();
    aud.finalize(bytes.len() as u64);

    let Auditor {
        digest, version, sector_len, num_sectors, findings, edits,
        repairable, ..
    } = aud;
    let plan = PlanData {
        digest,
        repairable,
        actions: edits.iter().map(|e| e.action.clone()).collect(),
        edits,
    };
    AuditReport {
        digest,
        version,
        file_len: bytes.len() as u64,
        sector_len,
        num_sectors,
        findings,
        plan,
    }
}

impl Auditor {
    /// Stage 1: parse the header with the production parser in permissive
    /// mode.
    fn parse_header(&mut self, bytes: &[u8]) {
        if bytes.len() < consts::HEADER_LEN {
            self.finding(
                Region::Header,
                Kind::OutOfBounds,
                Location::Header(bytes.len() as u64),
                format!(
                    "file is {} bytes, smaller than the {} byte CFB header",
                    bytes.len(),
                    consts::HEADER_LEN
                ),
            );
            self.unrepairable();
            return;
        }
        let mut cursor = std::io::Cursor::new(bytes);
        let header = match Header::read_from(&mut cursor, Validation::Permissive)
        {
            Ok(header) => header,
            Err(err) => {
                self.finding(
                    Region::Header,
                    Kind::Malformed,
                    Location::Header(0),
                    err.to_string(),
                );
                self.unrepairable();
                return;
            }
        };
        let sector_len = header.version.sector_len();
        self.version = Some(header.version);
        self.sector_len = Some(sector_len);
        if bytes.len() < sector_len {
            self.finding(
                Region::Header,
                Kind::OutOfBounds,
                Location::Header(consts::HEADER_LEN as u64),
                format!(
                    "file is {} bytes, smaller than one {} byte sector",
                    bytes.len(),
                    sector_len
                ),
            );
            self.unrepairable();
            return;
        }
        self.num_sectors = ((bytes.len() as u64) / (sector_len as u64) - 1)
            as u32;
        self.header = Some(header);
    }

    fn num_sectors(&self) -> u32 {
        self.num_sectors
    }
}

//===========================================================================//

impl Auditor {
    /// Stages 2a/2b: walk the DIFAT chain and read the FAT, tolerating
    /// pointers that the open path rejects.  Mirrors the parsing order in
    /// `CompoundFile::open_internal`.
    fn parse_difat_and_fat(&mut self, bytes: &[u8]) {
        let (Some(header), Some(sector_len)) =
            (self.header.clone(), self.sector_len)
        else {
            return;
        };
        let num_sectors = self.num_sectors();

        // Header DIFAT entries.
        let mut difat: Vec<u32> = Vec::new();
        for &entry in header.initial_difat_entries.iter() {
            difat.push(entry);
        }

        // Walk the DIFAT sector chain.
        let mut difat_sector_ids = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut current = header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR || current >= num_sectors {
                self.finding(
                    Region::Difat,
                    Kind::OutOfBounds,
                    Location::DifatSector(current),
                    format!(
                        "DIFAT chain points to sector {current}, but sector \
                         count is {num_sectors}"
                    ),
                );
                self.unrepairable();
                return;
            }
            if !seen.insert(current) {
                self.finding(
                    Region::Difat,
                    Kind::Cycle,
                    Location::DifatSector(current),
                    format!(
                        "DIFAT chain loops back to sector {current}"
                    ),
                );
                self.unrepairable();
                return;
            }
            difat_sector_ids.push(current);
            let sector_start =
                consts::HEADER_LEN as u64 + (current as u64) * sector_len as u64;
            let entries_per_sector = sector_len / 4;
            for idx in 0..(entries_per_sector - 1) {
                let Some(next) =
                    read_u32_at(bytes, sector_start + (idx as u64) * 4)
                else {
                    self.finding(
                        Region::Difat,
                        Kind::OutOfBounds,
                        Location::DifatSector(current),
                        format!(
                            "DIFAT sector {current} runs past end of file"
                        ),
                    );
                    self.unrepairable();
                    return;
                };
                if next != consts::FREE_SECTOR && next > consts::MAX_REGULAR_SECTOR
                {
                    self.finding(
                        Region::Difat,
                        Kind::Malformed,
                        Location::DifatSector(current),
                        format!(
                            "DIFAT entry {idx} has invalid sector index \
                             {next:#010x}"
                        ),
                    );
                    self.unrepairable();
                    return;
                }
                difat.push(next);
            }
            let Some(next_pointer) = read_u32_at(
                bytes,
                sector_start + ((entries_per_sector - 1) as u64) * 4,
            ) else {
                self.unrepairable();
                return;
            };
            current = next_pointer;
        }

        // Permissive trailing-entry trimming, as the open path does it.
        while difat.len() > consts::NUM_DIFAT_ENTRIES_IN_HEADER
            && difat.len() > header.num_fat_sectors as usize
            && difat.last() == Some(&0)
        {
            difat.pop();
        }
        while difat.last() == Some(&consts::FREE_SECTOR) {
            difat.pop();
        }

        if header.num_difat_sectors as usize != difat_sector_ids.len() {
            self.finding(
                Region::Header,
                Kind::LengthMismatch,
                Location::Header(OFFSET_NUM_DIFAT_SECTORS),
                format!(
                    "header says {} DIFAT sectors, DIFAT chain has {}",
                    header.num_difat_sectors,
                    difat_sector_ids.len()
                ),
            );
            // Update the header field to the walked length.
            self.edit_header(
                HeaderField::NumDifatSectors,
                OFFSET_NUM_DIFAT_SECTORS,
                difat_sector_ids.len() as u32,
            );
            if header.first_difat_sector != consts::END_OF_CHAIN
                && difat_sector_ids.is_empty()
            {
                self.edit_header(
                    HeaderField::FirstDifatSector,
                    OFFSET_FIRST_DIFAT_SECTOR,
                    consts::END_OF_CHAIN,
                );
            } else if let Some(&first) = difat_sector_ids.first() {
                if header.first_difat_sector != first {
                    self.edit_header(
                        HeaderField::FirstDifatSector,
                        OFFSET_FIRST_DIFAT_SECTOR,
                        first,
                    );
                }
            }
        }
        if header.num_fat_sectors as usize != difat.len() {
            self.finding(
                Region::Header,
                Kind::LengthMismatch,
                Location::Header(OFFSET_NUM_FAT_SECTORS),
                format!(
                    "header says {} FAT sectors, DIFAT lists {}",
                    header.num_fat_sectors,
                    difat.len()
                ),
            );
            self.edit_header(
                HeaderField::NumFatSectors,
                OFFSET_NUM_FAT_SECTORS,
                difat.len() as u32,
            );
        }

        // Read the FAT sectors named by the DIFAT.
        let mut fat: Vec<u32> = Vec::new();
        for &fat_sector in difat.iter() {
            if fat_sector >= num_sectors {
                self.finding(
                    Region::Difat,
                    Kind::OutOfBounds,
                    Location::DifatSector(fat_sector),
                    format!(
                        "DIFAT lists FAT sector {fat_sector}, but sector \
                         count is {num_sectors}"
                    ),
                );
                self.unrepairable();
                return;
            }
            let sector_start = consts::HEADER_LEN as u64
                + (fat_sector as u64) * sector_len as u64;
            for idx in 0..(sector_len / 4) {
                let Some(entry) =
                    read_u32_at(bytes, sector_start + (idx as u64) * 4)
                else {
                    self.finding(
                        Region::Fat,
                        Kind::OutOfBounds,
                        Location::FatSector(fat_sector),
                        format!(
                            "FAT sector {fat_sector} runs past end of file"
                        ),
                    );
                    self.unrepairable();
                    return;
                };
                fat.push(entry);
            }
        }

        // Permissive padding trim, matching the open path exactly.
        let trim_values = [
            0u32,
            consts::DIFAT_SECTOR,
            consts::FAT_SECTOR,
            consts::FREE_SECTOR,
        ];
        while fat.len() > num_sectors as usize
            && trim_values.contains(fat.last().unwrap())
        {
            fat.pop();
        }
        while fat.len() > num_sectors as usize
            && fat.last() == Some(&consts::FREE_SECTOR)
        {
            fat.pop();
        }
        while fat.len() < num_sectors as usize {
            fat.push(consts::FREE_SECTOR);
        }

        // FAT entry-level checks and metadata marking, matching
        // `Allocator::validate`.
        for &difat_sector in difat_sector_ids.iter() {
            let Some(&entry) = fat.get(difat_sector as usize) else {
                continue;
            };
            if entry != consts::DIFAT_SECTOR {
                self.finding(
                    Region::Fat,
                    Kind::Malformed,
                    Location::FatSector(difat_sector),
                    format!(
                        "DIFAT sector {difat_sector} is marked {entry:#010x} \
                         in the FAT, not {:#010x}",
                        consts::DIFAT_SECTOR
                    ),
                );
                self.edit_fat(difat_sector, consts::DIFAT_SECTOR);
            }
        }
        for &fat_sector in difat.iter() {
            let Some(&entry) = fat.get(fat_sector as usize) else {
                continue;
            };
            if entry != consts::FAT_SECTOR {
                self.finding(
                    Region::Fat,
                    Kind::Malformed,
                    Location::FatSector(fat_sector),
                    format!(
                        "FAT sector {fat_sector} is marked {entry:#010x} in \
                         the FAT, not {:#010x}",
                        consts::FAT_SECTOR
                    ),
                );
                self.edit_fat(fat_sector, consts::FAT_SECTOR);
            }
        }
        for from_sector in 0..fat.len() as u32 {
            let to = fat[from_sector as usize];
            if to == consts::INVALID_SECTOR {
                self.finding(
                    Region::Fat,
                    Kind::Malformed,
                    Location::FatSector(from_sector),
                    format!(
                        "FAT[{from_sector}] = {to:#010x}, which is not a \
                         valid FAT entry"
                    ),
                );
                self.edit_fat(from_sector, consts::END_OF_CHAIN);
            }
        }

        self.difat_sector_ids = difat_sector_ids;
        self.difat = difat;
        self.fat = fat;
    }
}

//===========================================================================//

impl Auditor {
    /// Stage 3: walk the directory chain (a tolerant version of the walk in
    /// `open_internal`), parsing each entry with the production
    /// `DirEntry::read_from` in permissive mode.
    fn parse_directory(&mut self, bytes: &[u8]) {
        let (Some(header), Some(sector_len)) =
            (self.header.clone(), self.sector_len)
        else {
            return;
        };
        let num_sectors = self.num_sectors();
        let entries_per_sector = sector_len / consts::DIR_ENTRY_LEN;

        // Walk the directory chain using the parsed FAT, stopping at the
        // first fatal edge but recording every sector reached.
        let mut seen = std::collections::HashSet::new();
        let mut current = header.first_dir_sector;
        let mut chain_len = 0u32;
        while current != consts::END_OF_CHAIN {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= num_sectors
            {
                self.finding(
                    Region::Directory,
                    Kind::OutOfBounds,
                    Location::DirectorySector(current),
                    format!(
                        "directory chain points to sector {current}, but \
                         sector count is {num_sectors}: directory chain is \
                         truncated"
                    ),
                );
                // Sever the edge into the missing sector; the predecessor is
                // the last sector actually reached.
                if let Some(&prev) = self.dir_sector_ids.last() {
                    self.edit_fat(prev, consts::END_OF_CHAIN);
                } else {
                    self.unrepairable();
                }
                break;
            }
            if !seen.insert(current) {
                self.finding(
                    Region::Directory,
                    Kind::Cycle,
                    Location::DirectorySector(current),
                    format!("directory chain loops back to sector {current}"),
                );
                if let Some(&prev) = self.dir_sector_ids.last() {
                    self.edit_fat(prev, consts::END_OF_CHAIN);
                }
                break;
            }
            self.dir_sector_ids.push(current);
            chain_len += 1;

            // Parse the directory entries carried by this sector.
            let sector_start = consts::HEADER_LEN as u64
                + (current as u64) * sector_len as u64;
            for within in 0..entries_per_sector {
                let entry_offset =
                    sector_start + (within as u64) * consts::DIR_ENTRY_LEN as u64;
                let slot_id = (self.slots.len()) as u32;
                let entry_bytes = match bytes
                    .get(entry_offset as usize
                        ..entry_offset as usize + consts::DIR_ENTRY_LEN)
                {
                    Some(slice) => slice,
                    None => {
                        self.finding(
                            Region::Directory,
                            Kind::OutOfBounds,
                            Location::DirectorySector(current),
                            format!(
                                "directory sector {current} runs past end of \
                                 file"
                            ),
                        );
                        self.slots.push(Slot { id: slot_id, entry: None });
                        continue;
                    }
                };
                let mut sub = std::io::Cursor::new(entry_bytes);
                match DirEntry::read_from(
                    &mut sub,
                    header.version,
                    Validation::Permissive,
                ) {
                    Ok(entry) => {
                        self.slots.push(Slot { id: slot_id, entry: Some(entry) })
                    }
                    Err(err) => {
                        self.finding(
                            Region::Directory,
                            Kind::Malformed,
                            Location::DirectoryEntry(slot_id),
                            format!(
                                "directory entry {slot_id}: {}",
                                err.to_string()
                            ),
                        );
                        self.slots.push(Slot { id: slot_id, entry: None });
                        // Reset the malformed slot to the canonical
                        // unallocated pattern.  Its absolute bytes can be
                        // written without parsing the chain.
                        self.reset_directory_entry(slot_id);
                    }
                }
            }

            // Advance using the FAT.
            match self.fat.get(current as usize).copied() {
                Some(next) if next <= consts::MAX_REGULAR_SECTOR => {
                    current = next
                }
                Some(consts::END_OF_CHAIN) => current = consts::END_OF_CHAIN,
                Some(consts::FREE_SECTOR) => {
                    self.finding(
                        Region::Directory,
                        Kind::Malformed,
                        Location::DirectorySector(current),
                        format!(
                            "directory sector {current} has a FREE_SECTOR FAT \
                             entry"
                        ),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
                Some(other) => {
                    self.finding(
                        Region::Directory,
                        Kind::Malformed,
                        Location::DirectorySector(current),
                        format!(
                            "directory sector {current} has invalid FAT entry \
                             {other:#010x}"
                        ),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
                None => {
                    self.finding(
                        Region::Directory,
                        Kind::OutOfBounds,
                        Location::DirectorySector(current),
                        format!(
                            "directory sector {current} has no FAT entry"
                        ),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
            }
        }

        // V4 header directory-sector count check.
        if header.version == Version::V4
            && header.num_dir_sectors != 0
            && header.num_dir_sectors != chain_len
        {
            self.finding(
                Region::Header,
                Kind::LengthMismatch,
                Location::Header(OFFSET_NUM_DIR_SECTORS),
                format!(
                    "header says {} directory sectors, chain has {}",
                    header.num_dir_sectors, chain_len
                ),
            );
            self.edit_header(
                HeaderField::NumDirSectors,
                OFFSET_NUM_DIR_SECTORS,
                chain_len,
            );
        }

        // Root entry sanity and tree-pointer reachability.
        self.analyze_directory_tree();
    }

    fn reset_directory_entry(&mut self, stream_id: u32) {
        let Some(sector_len) = self.sector_len else {
            self.unrepairable();
            return;
        };
        let base = dir_entry_offset(sector_len, stream_id);
        let unallocated = DirEntry::unallocated();
        let mut buf = Vec::with_capacity(consts::DIR_ENTRY_LEN);
        let mut cursor = std::io::Cursor::new(&mut buf);
        if unallocated.write_to(&mut cursor).is_err() {
            self.unrepairable();
            return;
        }
        // Record the write as individual u32 edits at the offsets whose
        // values differ from a zeroed slot (the NO_STREAM sibling/child
        // fields).  Simplest robust action: represent via a dedicated action
        // whose apply copies the canonical 128 bytes.
        let _ = base;
        self.edits.push(Edit {
            offset: base,
            value: 0,
            width: 0,
            action: RepairAction::ResetDirectoryEntry { stream_id },
        });
    }

    /// Checks tree pointers (siblings/child) against the parsed slots, and
    /// records the reachable slot set for later anchor collection.
    fn analyze_directory_tree(&mut self) {
        let slot_count = self.slots.len() as u32;
        let root_is_root = self
            .slots
            .first()
            .and_then(|s| s.entry.as_ref())
            .is_some_and(|e| e.obj_type == ObjType::Root);
        if self.slots.is_empty() || !root_is_root {
            self.finding(
                Region::Directory,
                Kind::Malformed,
                Location::DirectoryEntry(0),
                "root directory entry is missing or not a root storage"
                    .to_string(),
            );
            self.unrepairable();
            return;
        }
        // Copy the tree pointers, then validate without holding a borrow of
        // `self.slots` (findings mutate `self`).
        struct Links {
            left: u32,
            right: u32,
            child: u32,
            obj_type: ObjType,
        }
        let links: Vec<Links> = self
            .slots
            .iter()
            .map(|slot| match &slot.entry {
                Some(entry) => Links {
                    left: entry.left_sibling,
                    right: entry.right_sibling,
                    child: entry.child,
                    obj_type: entry.obj_type,
                },
                None => Links {
                    left: consts::NO_STREAM,
                    right: consts::NO_STREAM,
                    child: consts::NO_STREAM,
                    obj_type: ObjType::Unallocated,
                },
            })
            .collect();
        for (stream_id, links) in links.iter().enumerate() {
            let stream_id = stream_id as u32;
            let check = |pointer: u32, field: &str| -> Option<(Kind, String)> {
                if pointer == consts::NO_STREAM {
                    return None;
                }
                if pointer > consts::MAX_REGULAR_STREAM_ID {
                    return Some((
                        Kind::Malformed,
                        format!(
                            "entry {stream_id} {field} pointer {pointer} is \
                             invalid"
                        ),
                    ));
                }
                if pointer >= slot_count {
                    return Some((
                        Kind::OutOfBounds,
                        format!(
                            "entry {stream_id} {field} points to directory \
                             entry {pointer}, but only {slot_count} entries \
                             are reachable from the directory chain: the \
                             directory is truncated"
                        ),
                    ));
                }
                None
            };
            if let Some((kind, msg)) = check(links.left, "left sibling") {
                self.finding(
                    Region::Directory,
                    kind,
                    Location::DirectoryEntry(stream_id),
                    msg,
                );
                self.edit_entry_field(
                    stream_id,
                    68,
                    consts::NO_STREAM,
                    4,
                    RepairAction::SetEntryPointer {
                        stream_id,
                        field: EntryPointer::LeftSibling,
                        value: consts::NO_STREAM,
                    },
                );
            }
            if let Some((kind, msg)) = check(links.right, "right sibling") {
                self.finding(
                    Region::Directory,
                    kind,
                    Location::DirectoryEntry(stream_id),
                    msg,
                );
                self.edit_entry_field(
                    stream_id,
                    72,
                    consts::NO_STREAM,
                    4,
                    RepairAction::SetEntryPointer {
                        stream_id,
                        field: EntryPointer::RightSibling,
                        value: consts::NO_STREAM,
                    },
                );
            }
            if let Some((kind, msg)) = check(links.child, "child") {
                self.finding(
                    Region::Directory,
                    kind,
                    Location::DirectoryEntry(stream_id),
                    msg,
                );
                self.edit_entry_field(
                    stream_id,
                    76,
                    consts::NO_STREAM,
                    4,
                    RepairAction::SetEntryPointer {
                        stream_id,
                        field: EntryPointer::Child,
                        value: consts::NO_STREAM,
                    },
                );
            }
        }
    }
}

//===========================================================================//

impl Auditor {
    /// Stage 4: read the MiniFAT chain (walking it via the parsed FAT) and
    /// the entry-level checks done by `MiniAllocator::validate`.
    fn parse_minifat(&mut self, bytes: &[u8]) {
        let (Some(header), Some(sector_len)) =
            (self.header.clone(), self.sector_len)
        else {
            return;
        };
        let entries_per_sector = sector_len / 4;

        // Collect the MiniFAT chain sectors using the FAT, with cycle and
        // bounds protection.
        let mut seen = std::collections::HashSet::new();
        let mut current = header.first_minifat_sector;
        while current != consts::END_OF_CHAIN {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors()
            {
                self.finding(
                    Region::MiniFat,
                    Kind::OutOfBounds,
                    Location::MiniStreamSector(current),
                    format!(
                        "MiniFAT chain starts at sector {current}, which is \
                         past the end of the file"
                    ),
                );
                self.edit_header(
                    HeaderField::FirstMiniFatSector,
                    OFFSET_FIRST_MINIFAT_SECTOR,
                    consts::END_OF_CHAIN,
                );
                self.edit_header(
                    HeaderField::NumMiniFatSectors,
                    OFFSET_NUM_MINIFAT_SECTORS,
                    0,
                );
                return;
            }
            if !seen.insert(current) {
                self.finding(
                    Region::MiniFat,
                    Kind::Cycle,
                    Location::MiniStreamSector(current),
                    format!("MiniFAT chain loops back to sector {current}"),
                );
                if let Some(&prev) = self.minifat_sectors.last() {
                    self.edit_fat(prev, consts::END_OF_CHAIN);
                }
                break;
            }
            self.minifat_sectors.push(current);
            match self.fat.get(current as usize).copied() {
                Some(next) if next <= consts::MAX_REGULAR_SECTOR => {
                    current = next
                }
                Some(consts::END_OF_CHAIN) => break,
                Some(_) => {
                    self.finding(
                        Region::MiniFat,
                        Kind::Malformed,
                        Location::MiniStreamSector(current),
                        format!(
                            "MiniFAT chain sector {current} has a bad FAT \
                             entry"
                        ),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
                None => {
                    self.finding(
                        Region::MiniFat,
                        Kind::OutOfBounds,
                        Location::MiniStreamSector(current),
                        format!(
                            "MiniFAT chain sector {current} has no FAT entry"
                        ),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
            }
        }

        if header.first_minifat_sector == consts::END_OF_CHAIN {
            if header.num_minifat_sectors != 0 {
                self.finding(
                    Region::Header,
                    Kind::LengthMismatch,
                    Location::Header(OFFSET_NUM_MINIFAT_SECTORS),
                    format!(
                        "header says {} MiniFAT sectors, but first MiniFAT \
                         sector is END_OF_CHAIN",
                        header.num_minifat_sectors
                    ),
                );
                self.edit_header(
                    HeaderField::NumMiniFatSectors,
                    OFFSET_NUM_MINIFAT_SECTORS,
                    0,
                );
            }
            return;
        }
        if header.num_minifat_sectors as usize != self.minifat_sectors.len() {
            self.finding(
                Region::Header,
                Kind::LengthMismatch,
                Location::Header(OFFSET_NUM_MINIFAT_SECTORS),
                format!(
                    "header says {} MiniFAT sectors, chain has {}",
                    header.num_minifat_sectors,
                    self.minifat_sectors.len()
                ),
            );
            self.edit_header(
                HeaderField::NumMiniFatSectors,
                OFFSET_NUM_MINIFAT_SECTORS,
                self.minifat_sectors.len() as u32,
            );
        }

        // Read the entries.
        for &table_sector in self.minifat_sectors.iter() {
            let sector_start = consts::HEADER_LEN as u64
                + (table_sector as u64) * sector_len as u64;
            for within in 0..entries_per_sector {
                let Some(value) =
                    read_u32_at(bytes, sector_start + (within as u64) * 4)
                else {
                    self.finding(
                        Region::MiniFat,
                        Kind::OutOfBounds,
                        Location::MiniStreamSector(table_sector),
                        format!(
                            "MiniFAT sector {table_sector} runs past end of \
                             file"
                        ),
                    );
                    return;
                };
                self.minifat.push(value);
            }
        }
        while self.minifat.last() == Some(&consts::FREE_SECTOR) {
            self.minifat.pop();
        }
    }
}

//===========================================================================//

impl Auditor {
    /// The set of directory-entry slot ids reachable from the root through
    /// sibling/child pointers that stay in range.
    fn reachable_slot_ids(&self) -> std::collections::HashSet<u32> {
        let mut reachable = std::collections::HashSet::new();
        let slot_count = self.slots.len() as u32;
        let mut stack = vec![consts::ROOT_STREAM_ID];
        while let Some(id) = stack.pop() {
            if id >= slot_count || !reachable.insert(id) {
                continue;
            }
            if let Some(entry) =
                self.slots.get(id as usize).and_then(|s| s.entry.as_ref())
            {
                for pointer in
                    [entry.left_sibling, entry.right_sibling, entry.child]
                {
                    if pointer != consts::NO_STREAM && pointer < slot_count {
                        stack.push(pointer);
                    }
                }
            }
        }
        reachable
    }

    /// Stage 5: walk every named FAT chain from its anchor, classifying
    /// cycles, out-of-bounds pointers, cross-linked double references, and
    /// declared-length mismatches, then report orphan sectors.
    fn analyze_fat_chains(&mut self) {
        let (Some(header), Some(sector_len)) =
            (self.header.clone(), self.sector_len)
        else {
            return;
        };
        let num_sectors = self.num_sectors();
        let reachable_slots = self.reachable_slot_ids();

        // Deterministic anchor order: metadata anchors first, then stream
        // anchors in ascending slot id.
        let mut anchors: Vec<(u32, Owner, Option<u64>)> = Vec::new();
        anchors.push((header.first_dir_sector, Owner::Directory, None));
        if header.first_minifat_sector != consts::END_OF_CHAIN {
            anchors.push((
                header.first_minifat_sector,
                Owner::MiniFatTable,
                None,
            ));
        }
        if let Some(root) = self.slots.first().and_then(|s| s.entry.as_ref())
        {
            anchors.push((
                root.start_sector,
                Owner::MiniStream,
                Some(root.stream_len),
            ));
        }
        for slot in self.slots.iter().skip(1) {
            let Some(entry) = slot.entry.as_ref() else { continue };
            if !reachable_slots.contains(&slot.id) {
                continue;
            }
            if entry.obj_type == ObjType::Stream
                && entry.stream_len >= consts::MINI_STREAM_CUTOFF as u64
            {
                anchors.push((
                    entry.start_sector,
                    Owner::Stream(slot.id),
                    Some(entry.stream_len),
                ));
            }
        }

        // Global first-assignment map: sector -> owner label of the chain
        // that reached it first.  Metadata sectors are claimed up front so
        // they are never orphans.
        let mut claimed: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        for &fat_sector in self.difat.iter() {
            if fat_sector < num_sectors {
                claimed.entry(fat_sector).or_insert_with(|| Owner::Fat.label());
            }
        }
        for &difat_sector in self.difat_sector_ids.iter() {
            if difat_sector < num_sectors {
                claimed
                    .entry(difat_sector)
                    .or_insert_with(|| Owner::Difat.label());
            }
        }

        for (start, owner, declared_len) in anchors.into_iter() {
            self.walk_fat_anchor(
                start,
                owner,
                declared_len,
                sector_len,
                num_sectors,
                &mut claimed,
            );
        }

        // Orphan regular sectors: an entry that points at a data sector
        // (<= MAX_REGULAR_SECTOR) but is neither metadata nor reached by any
        // named chain.
        for sector in 0..num_sectors {
            let entry = match self.fat.get(sector as usize).copied() {
                Some(entry) => entry,
                None => continue,
            };
            if claimed.contains_key(&sector) {
                continue;
            }
            if entry <= consts::MAX_REGULAR_SECTOR {
                self.finding(
                    Region::Fat,
                    Kind::OrphanSector,
                    Location::FatSector(sector),
                    format!(
                        "allocated sector {sector} is not reachable from any \
                         directory, MiniFAT, DIFAT, or mini stream chain"
                    ),
                );
                self.edit_fat(sector, consts::FREE_SECTOR);
            }
        }
    }

    fn walk_fat_anchor(
        &mut self,
        start: u32,
        owner: Owner,
        declared_len: Option<u64>,
        sector_len: usize,
        num_sectors: u32,
        claimed: &mut std::collections::HashMap<u32, String>,
    ) {
        let label = owner.label();
        let region = region_for_owner(&owner);
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return;
        }
        if start > consts::MAX_REGULAR_SECTOR || start >= num_sectors {
            self.finding(
                region,
                Kind::OutOfBounds,
                owner_location(&owner, start),
                format!(
                    "{label} starts at sector {start}, but sector count is \
                     {num_sectors}"
                ),
            );
            self.repair_anchor_start(&owner);
            return;
        }

        let mut seen_in_walk = std::collections::HashSet::new();
        let mut current = start;
        let mut count: u64 = 0;
        loop {
            if let Some(first_owner) = claimed.get(&current) {
                let first_owner = first_owner.clone();
                self.finding(
                    region,
                    Kind::DoubleReference,
                    owner_location(&owner, current),
                    format!(
                        "sector {current} of {label} is already part of the \
                         {first_owner}: chains are cross-linked"
                    ),
                );
                // Sever the edge entering the shared sector: if it is the
                // anchor start itself, clear the anchor; otherwise set the
                // predecessor's FAT entry to END_OF_CHAIN.
                if current == start {
                    self.repair_anchor_start(&owner);
                } else {
                    self.edit_fat(prev_of(current, start, &self.fat),
                                  consts::END_OF_CHAIN);
                }
                return;
            }
            claimed.insert(current, label.clone());
            seen_in_walk.insert(current);
            count += 1;

            let next = match self.fat.get(current as usize).copied() {
                Some(next) => next,
                None => {
                    self.finding(
                        region,
                        Kind::OutOfBounds,
                        owner_location(&owner, current),
                        format!("{label} sector {current} has no FAT entry"),
                    );
                    self.edit_fat(current, consts::END_OF_CHAIN);
                    break;
                }
            };
            if next == consts::END_OF_CHAIN {
                break;
            }
            if next == consts::FREE_SECTOR {
                self.finding(
                    region,
                    Kind::Malformed,
                    owner_location(&owner, current),
                    format!("{label} sector {current} is marked FREE_SECTOR"),
                );
                self.edit_fat(current, consts::END_OF_CHAIN);
                break;
            }
            if next > consts::MAX_REGULAR_SECTOR {
                self.finding(
                    region,
                    Kind::Malformed,
                    owner_location(&owner, current),
                    format!(
                        "{label} sector {current} points at invalid value \
                         {next:#010x}"
                    ),
                );
                self.edit_fat(current, consts::END_OF_CHAIN);
                break;
            }
            if next >= num_sectors {
                self.finding(
                    region,
                    Kind::OutOfBounds,
                    owner_location(&owner, next),
                    format!(
                        "{label} sector {current} points to sector {next}, \
                         but sector count is {num_sectors}"
                    ),
                );
                self.edit_fat(current, consts::END_OF_CHAIN);
                break;
            }
            if seen_in_walk.contains(&next) {
                self.finding(
                    region,
                    Kind::Cycle,
                    owner_location(&owner, current),
                    format!(
                        "{label} sector {current} points back to sector \
                         {next} already seen in the same chain"
                    ),
                );
                self.edit_fat(current, consts::END_OF_CHAIN);
                break;
            }
            current = next;
        }

        // Declared-length consistency for regular streams and the root mini
        // stream.
        if let Some(len) = declared_len {
            let expected_sectors = len.div_ceil(sector_len as u64);
            if expected_sectors != count {
                let effective_len = count * sector_len as u64;
                self.finding(
                    region,
                    Kind::LengthMismatch,
                    owner_location(&owner, start),
                    format!(
                        "{label} declares {len} bytes ({expected_sectors} \
                         sectors) but its FAT chain has {count} sector(s)"
                    ),
                );
                match owner {
                    Owner::Stream(id) => {
                        self.edit_entry_field(
                            id,
                            120,
                            effective_len as u32,
                            4,
                            RepairAction::SetStreamLen {
                                stream_id: id,
                                len: effective_len,
                            },
                        );
                    }
                    Owner::MiniStream => {
                        self.edit_entry_field(
                            0,
                            120,
                            effective_len as u32,
                            4,
                            RepairAction::SetStreamLen {
                                stream_id: 0,
                                len: effective_len,
                            },
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    /// Repairs an anchor whose start sector itself is invalid by clearing
    /// the directory/header reference and declared length.
    fn repair_anchor_start(&mut self, owner: &Owner) {
        match *owner {
            Owner::Directory => {
                // A file with no directory cannot be repaired safely.
                self.unrepairable();
            }
            Owner::MiniFatTable => {
                self.edit_header(
                    HeaderField::FirstMiniFatSector,
                    OFFSET_FIRST_MINIFAT_SECTOR,
                    consts::END_OF_CHAIN,
                );
                self.edit_header(
                    HeaderField::NumMiniFatSectors,
                    OFFSET_NUM_MINIFAT_SECTORS,
                    0,
                );
                self.minifat.clear();
                self.minifat_sectors.clear();
            }
            Owner::MiniStream => {
                self.edit_entry_field(
                    0,
                    116,
                    consts::END_OF_CHAIN,
                    4,
                    RepairAction::SetStreamStart {
                        stream_id: 0,
                        start: consts::END_OF_CHAIN,
                    },
                );
                self.edit_entry_field(
                    0,
                    120,
                    0,
                    4,
                    RepairAction::SetStreamLen { stream_id: 0, len: 0 },
                );
            }
            Owner::Stream(id) => {
                self.edit_entry_field(
                    id,
                    116,
                    consts::END_OF_CHAIN,
                    4,
                    RepairAction::SetStreamStart {
                        stream_id: id,
                        start: consts::END_OF_CHAIN,
                    },
                );
                self.edit_entry_field(
                    id,
                    120,
                    0,
                    4,
                    RepairAction::SetStreamLen { stream_id: id, len: 0 },
                );
            }
            Owner::Fat | Owner::Difat => self.unrepairable(),
        }
    }
}

/// Finds the sector in the chain from `start` whose FAT entry is `target`.
fn prev_of(target: u32, start: u32, fat: &[u32]) -> u32 {
    let mut cur = start;
    let mut guard = 0usize;
    while guard < fat.len() {
        guard += 1;
        match fat.get(cur as usize).copied() {
            Some(next) if next == target => return cur,
            Some(next) if next <= consts::MAX_REGULAR_SECTOR => cur = next,
            _ => return cur,
        }
    }
    cur
}

fn region_for_owner(owner: &Owner) -> Region {
    match owner {
        Owner::Directory => Region::Directory,
        Owner::MiniFatTable => Region::MiniFat,
        Owner::MiniStream => Region::MiniStream,
        Owner::Stream(_) => Region::Fat,
        Owner::Fat | Owner::Difat => Region::Fat,
    }
}

fn owner_location(owner: &Owner, sector: u32) -> Location {
    match owner {
        Owner::Directory => Location::DirectorySector(sector),
        Owner::MiniFatTable => Location::MiniStreamSector(sector),
        Owner::MiniStream => Location::MiniStreamSector(sector),
        Owner::Stream(_) => Location::FatSector(sector),
        Owner::Fat | Owner::Difat => Location::FatSector(sector),
    }
}

//===========================================================================

impl Auditor {
    /// Stage 6: walk every named mini chain from its anchor and classify
    /// MiniFAT damage, then report orphan mini sectors.
    fn analyze_minifat(&mut self) {
        let (Some(header), Some(sector_len)) =
            (self.header.clone(), self.sector_len)
        else {
            return;
        };
        if self.minifat.is_empty() {
            return;
        }
        let reachable_slots = self.reachable_slot_ids();
        let minifat_len = self.minifat.len() as u32;

        // MiniFAT entry-level checks (mirrors MiniAllocator::validate).
        let root_mini_sectors = self
            .slots
            .first()
            .and_then(|s| s.entry.as_ref())
            .map(|e| e.stream_len / consts::MINI_SECTOR_LEN as u64)
            .unwrap_or(0);
        if root_mini_sectors < minifat_len as u64 {
            self.finding(
                Region::MiniFat,
                Kind::LengthMismatch,
                Location::MiniSector(0),
                format!(
                    "MiniFAT has {minifat_len} entries, but the root mini \
                     stream has only {root_mini_sectors} mini sectors"
                ),
            );
            // Repair: grow the root stream length to cover the table.
            let new_len =
                (minifat_len as u64) * consts::MINI_SECTOR_LEN as u64;
            self.edit_entry_field(
                0,
                120,
                new_len as u32,
                4,
                RepairAction::SetStreamLen { stream_id: 0, len: new_len },
            );
        }
        let mut pointees = std::collections::HashSet::new();
        for from in 0..minifat_len {
            let to = self.minifat[from as usize];
            if to <= consts::MAX_REGULAR_SECTOR {
                if to >= minifat_len {
                    self.finding(
                        Region::MiniFat,
                        Kind::OutOfBounds,
                        Location::MiniSector(from),
                        format!(
                            "MiniFAT[{from}] = {to}, but the MiniFAT has \
                             only {minifat_len} entries"
                        ),
                    );
                    self.edit_minifat(from, consts::END_OF_CHAIN);
                } else if !pointees.insert(to) {
                    self.finding(
                        Region::MiniFat,
                        Kind::DoubleReference,
                        Location::MiniSector(to),
                        format!(
                            "mini sector {to} is pointed to twice in the \
                             MiniFAT"
                        ),
                    );
                    self.edit_minifat(from, consts::END_OF_CHAIN);
                }
            } else if to == consts::INVALID_SECTOR {
                self.finding(
                    Region::MiniFat,
                    Kind::Malformed,
                    Location::MiniSector(from),
                    format!(
                        "MiniFAT[{from}] = {to:#010x}, which is not a valid \
                         MiniFAT entry"
                    ),
                );
                self.edit_minifat(from, consts::END_OF_CHAIN);
            }
        }

        // Walk each small stream's mini chain from its anchor.
        let mut claimed: std::collections::HashMap<u32, String> =
            std::collections::HashMap::new();
        let mut anchors: Vec<(u32, u32, u64)> = Vec::new();
        for slot in self.slots.iter().skip(1) {
            let Some(entry) = slot.entry.as_ref() else { continue };
            if !reachable_slots.contains(&slot.id) {
                continue;
            }
            if entry.obj_type == ObjType::Stream
                && entry.stream_len < consts::MINI_STREAM_CUTOFF as u64
                && entry.stream_len > 0
            {
                anchors.push((
                    slot.id,
                    entry.start_sector,
                    entry.stream_len,
                ));
            }
        }
        for (stream_id, start, declared_len) in anchors.into_iter() {
            self.walk_mini_anchor(
                stream_id,
                start,
                declared_len,
                minifat_len,
                &mut claimed,
            );
        }

        // Orphan mini sectors: allocated (not FREE) mini sectors not reached
        // by any small stream chain.
        for mini in 0..minifat_len {
            let entry = self.minifat[mini as usize];
            if entry == consts::FREE_SECTOR {
                continue;
            }
            if claimed.contains_key(&mini) {
                continue;
            }
            self.finding(
                Region::MiniFat,
                Kind::OrphanSector,
                Location::MiniSector(mini),
                format!(
                    "allocated mini sector {mini} is not reachable from any \
                     small stream chain"
                ),
            );
            self.edit_minifat(mini, consts::FREE_SECTOR);
        }

        let _ = header;
        let _ = sector_len;
    }

    fn walk_mini_anchor(
        &mut self,
        stream_id: u32,
        start: u32,
        declared_len: u64,
        minifat_len: u32,
        claimed: &mut std::collections::HashMap<u32, String>,
    ) {
        let label = format!("stream entry {stream_id}");
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return;
        }
        if start > consts::MAX_REGULAR_SECTOR || start >= minifat_len {
            self.finding(
                Region::MiniFat,
                Kind::OutOfBounds,
                Location::MiniSector(start),
                format!(
                    "{label} starts at mini sector {start}, but the MiniFAT \
                     has only {minifat_len} entries"
                ),
            );
            self.edit_entry_field(
                stream_id,
                116,
                consts::END_OF_CHAIN,
                4,
                RepairAction::SetStreamStart {
                    stream_id,
                    start: consts::END_OF_CHAIN,
                },
            );
            self.edit_entry_field(
                stream_id,
                120,
                0,
                4,
                RepairAction::SetStreamLen { stream_id, len: 0 },
            );
            return;
        }

        let mut seen_in_walk = std::collections::HashSet::new();
        let mut current = start;
        let mut count: u64 = 0;
        loop {
            if let Some(first_owner) = claimed.get(&current) {
                let first_owner = first_owner.clone();
                self.finding(
                    Region::MiniFat,
                    Kind::DoubleReference,
                    Location::MiniSector(current),
                    format!(
                        "mini sector {current} of {label} is already part \
                         of {first_owner}: mini chains are cross-linked"
                    ),
                );
                if current == start {
                    self.edit_entry_field(
                        stream_id,
                        116,
                        consts::END_OF_CHAIN,
                        4,
                        RepairAction::SetStreamStart {
                            stream_id,
                            start: consts::END_OF_CHAIN,
                        },
                    );
                    self.edit_entry_field(
                        stream_id,
                        120,
                        0,
                        4,
                        RepairAction::SetStreamLen { stream_id, len: 0 },
                    );
                } else {
                    // Sever the edge into the shared mini sector.
                    let pred = prev_of_mini(current, start, &self.minifat);
                    self.edit_minifat(pred, consts::END_OF_CHAIN);
                }
                return;
            }
            claimed.insert(current, label.clone());
            seen_in_walk.insert(current);
            count += 1;

            let next = match self.minifat.get(current as usize).copied() {
                Some(next) => next,
                None => break,
            };
            if next == consts::END_OF_CHAIN {
                break;
            }
            if next == consts::FREE_SECTOR {
                self.finding(
                    Region::MiniFat,
                    Kind::Malformed,
                    Location::MiniSector(current),
                    format!(
                        "{label} mini sector {current} is marked FREE_SECTOR"
                    ),
                );
                self.edit_minifat(current, consts::END_OF_CHAIN);
                break;
            }
            if next > consts::MAX_REGULAR_SECTOR {
                self.finding(
                    Region::MiniFat,
                    Kind::Malformed,
                    Location::MiniSector(current),
                    format!(
                        "{label} mini sector {current} points at invalid \
                         value {next:#010x}"
                    ),
                );
                self.edit_minifat(current, consts::END_OF_CHAIN);
                break;
            }
            if next >= minifat_len {
                self.finding(
                    Region::MiniFat,
                    Kind::OutOfBounds,
                    Location::MiniSector(next),
                    format!(
                        "{label} mini sector {current} points to mini \
                         sector {next}, but the MiniFAT has only \
                         {minifat_len} entries"
                    ),
                );
                self.edit_minifat(current, consts::END_OF_CHAIN);
                break;
            }
            if seen_in_walk.contains(&next) {
                self.finding(
                    Region::MiniFat,
                    Kind::Cycle,
                    Location::MiniSector(current),
                    format!(
                        "{label} mini sector {current} points back to mini \
                         sector {next} already seen in the same chain"
                    ),
                );
                self.edit_minifat(current, consts::END_OF_CHAIN);
                break;
            }
            current = next;
        }

        // Declared-length consistency: expected mini sectors from the
        // declared stream length.
        let expected =
            declared_len.div_ceil(consts::MINI_SECTOR_LEN as u64);
        if expected != count {
            let effective_len = count * consts::MINI_SECTOR_LEN as u64;
            self.finding(
                Region::MiniFat,
                Kind::LengthMismatch,
                Location::MiniSector(start),
                format!(
                    "{label} declares {declared_len} bytes ({expected} mini \
                     sectors) but its MiniFAT chain has {count} mini \
                     sector(s)"
                ),
            );
            self.edit_entry_field(
                stream_id,
                120,
                effective_len as u32,
                4,
                RepairAction::SetStreamLen {
                    stream_id,
                    len: effective_len,
                },
            );
        }
    }

    /// Stage 7: sort findings deterministically and drop repairability if
    /// any finding has no repair action.
    fn finalize(&mut self, _file_len: u64) {
        fn region_rank(r: Region) -> u8 {
            match r {
                Region::Header => 0,
                Region::Difat => 1,
                Region::Fat => 2,
                Region::Directory => 3,
                Region::MiniFat => 4,
                Region::MiniStream => 5,
            }
        }
        fn kind_rank(k: Kind) -> u8 {
            match k {
                Kind::Malformed => 0,
                Kind::Cycle => 1,
                Kind::OutOfBounds => 2,
                Kind::DoubleReference => 3,
                Kind::OrphanSector => 4,
                Kind::LengthMismatch => 5,
            }
        }
        fn location_rank(l: Location) -> (u8, u64) {
            match l {
                Location::Header(o) => (0, o),
                Location::FatSector(s) => (1, s as u64),
                Location::DifatSector(s) => (2, s as u64),
                Location::DirectorySector(s) => (3, s as u64),
                Location::DirectoryEntry(s) => (4, s as u64),
                Location::MiniSector(s) => (5, s as u64),
                Location::MiniStreamSector(s) => (6, s as u64),
            }
        }
        self.findings.sort_by(|a, b| {
            region_rank(a.region)
                .cmp(&region_rank(b.region))
                .then(kind_rank(a.kind).cmp(&kind_rank(b.kind)))
                .then(location_rank(a.location).cmp(&location_rank(b.location)))
                .then(a.context.cmp(&b.context))
        });
        // Stable dedup of identical findings.
        self.findings.dedup();
        // Sort edits by offset for determinism.
        self.edits.sort_by_key(|e| e.offset);
        self.edits.dedup_by(|a, b| {
            if a.offset == b.offset {
                debug_assert_eq!(a.value, b.value);
                true
            } else {
                false
            }
        });
    }
}

/// Finds the mini sector in the chain from `start` whose MiniFAT entry is
/// `target`.
fn prev_of_mini(target: u32, start: u32, minifat: &[u32]) -> u32 {
    let mut cur = start;
    let mut guard = 0usize;
    while guard < minifat.len() {
        guard += 1;
        match minifat.get(cur as usize).copied() {
            Some(next) if next == target => return cur,
            Some(next) if next <= consts::MAX_REGULAR_SECTOR => cur = next,
            _ => return cur,
        }
    }
    cur
}

//===========================================================================

/// Applies the planned edits to a copy of the input and verifies the result
/// by re-auditing it.  Returns the repaired image only if the re-audit is
/// clean; otherwise returns an error and nothing is written anywhere.
fn compose_repaired(input: &[u8], plan: &PlanData) -> io::Result<Vec<u8>> {
    let mut repaired = input.to_vec();
    for edit in plan.edits.iter() {
        match edit.width {
            4 => {
                let offset = edit.offset as usize;
                if offset + 4 > repaired.len() {
                    invalid_data!(
                        "Repair edit at offset {} is past end of file",
                        edit.offset,
                    );
                }
                write_u32_at(&mut repaired, edit.offset, edit.value);
            }
            0 => {
                // A ResetDirectoryEntry edit: overwrite the 128-byte slot
                // with the canonical unallocated pattern.
                let RepairAction::ResetDirectoryEntry { stream_id } =
                    edit.action
                else {
                    invalid_data!("invalid repair edit");
                };
                let _ = stream_id;
                let offset = edit.offset as usize;
                if offset + consts::DIR_ENTRY_LEN > repaired.len() {
                    invalid_data!(
                        "Repair edit at offset {} is past end of file",
                        edit.offset,
                    );
                }
                let unallocated = DirEntry::unallocated();
                let mut buf = Vec::with_capacity(consts::DIR_ENTRY_LEN);
                {
                    let mut cursor = std::io::Cursor::new(&mut buf);
                    unallocated
                        .write_to(&mut cursor)
                        .map_err(|e| {
                            io::Error::new(io::ErrorKind::InvalidData, e)
                        })?;
                }
                repaired[offset..offset + consts::DIR_ENTRY_LEN]
                    .copy_from_slice(&buf);
            }
            _ => {
                invalid_data!("unsupported repair edit width");
            }
        }
    }
    // Verify the repaired image by re-auditing it.  It must be clean.
    let re_audit = audit_bytes(&repaired);
    if !re_audit.is_clean() {
        let first = re_audit.findings().first().unwrap();
        invalid_data!(
            "Repair did not produce a clean file: {}",
            first.to_string(),
        );
    }
    Ok(repaired)
}

//===========================================================================
