//! Opt-in, read-only structural audit of a compound file.
//!
//! The audit never opens a compound file for mutation: it parses the raw
//! bytes of a CFB image and reports concrete evidence of corruption in the
//! four allocation structures (FAT, DIFAT, MiniFAT, and the directory chain),
//! along with a read-only [`RepairPlan`].  A plan carries a digest of the
//! bytes it was built for; applying it is an explicit, separate step that
//! first re-checks the digest, so a plan goes stale if the file changes.
//!
//! Enter through [`crate::OpenOptions::audit`] or
//! [`crate::OpenOptions::audit_with`]; the ordinary `open`/`open_rw`/
//! `create` entry points are unaffected.

use std::fmt;
use std::fs;
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

//===========================================================================//

/// Which allocation table a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Table {
    /// The File Allocation Table and the sector chains built from it.
    Fat,
    /// The Double-Indirect FAT (the chain of FAT-sector locations).
    Difat,
    /// The Mini Allocation Table and mini chains inside the mini stream.
    MiniFat,
    /// The chain of directory sectors and the directory entries it holds.
    Directory,
    /// Counters and first-sector pointers stored in the file header.
    Header,
}

impl Table {
    fn as_str(self) -> &'static str {
        match self {
            Table::Fat => "FAT",
            Table::Difat => "DIFAT",
            Table::MiniFat => "MiniFAT",
            Table::Directory => "directory chain",
            Table::Header => "header",
        }
    }
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

//===========================================================================//

/// What a directory entry's sector chain belongs to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ChainOwner {
    /// The root entry's mini stream.
    MiniStream,
    /// The MiniFAT chain.
    MiniFat,
    /// The named stream with the given directory-entry stream ID.
    Stream(u32),
}

impl fmt::Display for ChainOwner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ChainOwner::MiniStream => f.write_str("root mini stream"),
            ChainOwner::MiniFat => f.write_str("MiniFAT"),
            ChainOwner::Stream(id) => write!(f, "stream dir entry {}", id),
        }
    }
}

//===========================================================================//

/// A classified corruption, with enough context to point at the first
/// violating byte rather than merely saying the file is bad.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Corruption {
    /// A chain loops back onto itself.  `at` is the sector already visited,
    /// `edge_from` is the cell whose pointer closes the loop.
    Cycle {
        /// Which table the chain lives in.
        table: Table,
        /// Sector at which the repeated visit occurs.
        at: u32,
        /// Cell whose pointer closes the cycle.
        edge_from: u32,
        /// What the chain belongs to, when it was reached from an owner.
        owner: Option<ChainOwner>,
    },
    /// A pointer names a sector/mini-sector that does not exist.
    OutOfBounds {
        /// Which table holds the bad pointer.
        table: Table,
        /// The cell containing the bad pointer.
        edge_from: u32,
        /// The pointer value itself.
        target: u32,
        /// What the chain belongs to, when it was reached from an owner.
        owner: Option<ChainOwner>,
    },
    /// Two chains claim the same sector, or a chain runs into a sector the
    /// file already assigns to the FAT/DIFAT/directory.
    CrossLinked {
        /// Which table the conflicting chains live in.
        table: Table,
        /// The cell whose pointer enters the already-owned sector.
        edge_from: u32,
        /// The sector claimed twice.
        target: u32,
        /// What the entering chain belongs to, when known.
        owner: Option<ChainOwner>,
    },
    /// A sector or mini-sector that is neither marked free nor reachable
    /// from any structure.
    Orphan {
        /// Which table the unreachable cell lives in.
        table: Table,
        /// The unreachable sector/mini-sector id.
        sector: u32,
    },
    /// A directory-entry pointer (sibling or child) cannot be followed
    /// because the directory chain ends before that entry exists, or points
    /// at an unallocated entry slot.
    TruncatedDirectory {
        /// The directory entry holding the bad pointer.
        entry_stream_id: u32,
        /// The field the bad pointer was read from.
        field: DirectoryField,
        /// The pointer value itself.
        target: u32,
        /// Number of entries reachable along the directory chain.
        available_entries: u32,
    },
    /// A stream or mini stream's declared length disagrees with the bytes
    /// its chain can actually supply.
    DeclaredLengthMismatch {
        /// What the chain belongs to.
        owner: ChainOwner,
        /// Length declared by the directory entry/header.
        declared: u64,
        /// Bytes reachable through the chain.
        reachable: u64,
    },
    /// A counter or first-sector pointer in the header does not match the
    /// structures found on disk.
    HeaderCountMismatch {
        /// The header field that disagrees with the file.
        field: HeaderField,
        /// Value stored in the header.
        declared: u64,
        /// Value implied by the structures on disk.
        actual: u64,
    },
}

/// A pointer field within a directory entry.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DirectoryField {
    /// `left_sibling_id`
    LeftSibling,
    /// `right_sibling_id`
    RightSibling,
    /// `child_id`
    Child,
}

impl fmt::Display for DirectoryField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            DirectoryField::LeftSibling => "left_sibling_id",
            DirectoryField::RightSibling => "right_sibling_id",
            DirectoryField::Child => "child_id",
        })
    }
}

/// A numeric field in the CFB header.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HeaderField {
    /// `number_of_fat_sectors`
    NumFatSectors,
    /// `first_dir_sector` / the directory chain length vs
    /// `number_of_directory_sectors` (V4 only)
    NumDirSectors,
    /// `first_minifat_sector` / `number_of_minifat_sectors`
    NumMiniFatSectors,
    /// `first_difat_sector` / `number_of_difat_sectors`
    NumDifatSectors,
}

impl fmt::Display for HeaderField {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            HeaderField::NumFatSectors => "number_of_fat_sectors",
            HeaderField::NumDirSectors => "number_of_directory_sectors",
            HeaderField::NumMiniFatSectors => "number_of_minifat_sectors",
            HeaderField::NumDifatSectors => "number_of_difat_sectors",
        })
    }
}

impl Corruption {
    /// Which allocation table this piece of evidence concerns.
    pub fn table(&self) -> Table {
        match self {
            Corruption::Cycle { table, .. }
            | Corruption::OutOfBounds { table, .. }
            | Corruption::CrossLinked { table, .. }
            | Corruption::Orphan { table, .. } => *table,
            Corruption::TruncatedDirectory { .. } => Table::Directory,
            Corruption::DeclaredLengthMismatch { .. } => Table::Fat,
            Corruption::HeaderCountMismatch { .. } => Table::Header,
        }
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Corruption::Cycle { table, at, edge_from, owner } => write!(
                f,
                "{} chain cycles: sector {} points back to already-visited \
                 sector {}{}",
                table,
                edge_from,
                at,
                owner_suffix(owner.as_ref())
            ),
            Corruption::OutOfBounds { table, edge_from, target, owner } => {
                write!(
                    f,
                    "{} cell {} points to out-of-range sector {}{}",
                    table,
                    edge_from,
                    format_sector(*target),
                    owner_suffix(owner.as_ref())
                )
            }
            Corruption::CrossLinked { table, edge_from, target, owner } => {
                write!(
                    f,
                    "{} cross-linked chain: cell {} enters sector {} already \
                     claimed by another structure{}",
                    table,
                    edge_from,
                    target,
                    owner_suffix(owner.as_ref())
                )
            }
            Corruption::Orphan { table, sector } => write!(
                f,
                "{} sector {} is neither marked free nor reachable",
                table, sector
            ),
            Corruption::TruncatedDirectory {
                entry_stream_id,
                field,
                target,
                available_entries,
            } => write!(
                f,
                "directory entry {} field {} points to entry {}, but only {} \
                 entries are reachable along the directory chain",
                entry_stream_id, field, target, available_entries
            ),
            Corruption::DeclaredLengthMismatch { owner, declared, reachable } => {
                write!(
                    f,
                    "{} declares {} bytes but its chain supplies {}",
                    owner, declared, reachable
                )
            }
            Corruption::HeaderCountMismatch { field, declared, actual } => {
                write!(
                    f,
                    "header {} is {} but the on-disk structure implies {}",
                    field, declared, actual
                )
            }
        }
    }
}

fn owner_suffix(owner: Option<&ChainOwner>) -> String {
    match owner {
        Some(owner) => format!(" (chain of {})", owner),
        None => String::new(),
    }
}

fn format_sector(value: u32) -> String {
    if value == u32::MAX {
        "FREE_SECTOR (0xFFFFFFFF)".to_string()
    } else {
        format!("{} (0x{:08X})", value, value)
    }
}

//===========================================================================//

/// One piece of corruption evidence: a classified [`Corruption`] plus the
/// byte offset in the image where the violating pointer/length lives.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Finding {
    corruption: Corruption,
    /// Byte offset of the first violating field within the image, when it can
    /// be located.
    offset: Option<u64>,
}

impl Finding {
    pub(crate) fn new(corruption: Corruption, offset: Option<u64>) -> Finding {
        Finding { corruption, offset }
    }

    /// The classified corruption.
    pub fn corruption(&self) -> &Corruption {
        &self.corruption
    }

    /// Byte offset of the violating field in the image, if locatable.
    pub fn offset(&self) -> Option<u64> {
        self.offset
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.offset {
            Some(offset) => {
                write!(f, "at byte offset {}: {}", offset, self.corruption)
            }
            None => fmt::Display::fmt(&self.corruption, f),
        }
    }
}

//===========================================================================//

/// The result of a read-only structural audit.
#[derive(Clone, Debug)]
pub struct AuditReport {
    findings: Vec<Finding>,
    /// Deduplicated byte patches that a repair would apply.
    patches: Vec<Patch>,
    /// Precondition digest of the image that was audited.
    digest: u64,
    /// Length of the audited image in bytes.
    file_len: u64,
}

impl AuditReport {
    /// All findings, in a deterministic order: by table (FAT, DIFAT, MiniFAT,
    /// directory, header) and then by byte offset/cell, so the first element
    /// is always the first violation a repair would touch.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// True when no corruption was found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// Digest of the exact bytes this report was produced for.
    pub fn digest(&self) -> u64 {
        self.digest
    }

    /// Builds a read-only repair plan from this report.  Constructing the
    /// plan never writes anything.
    pub fn repair_plan(&self) -> RepairPlan {
        RepairPlan {
            digest: self.digest,
            file_len: self.file_len,
            patches: self.patches.clone(),
            findings: self.findings.clone(),
        }
    }
}

impl AuditReport {
    pub(crate) fn from_parts(
        findings: Vec<Finding>,
        digest: u64,
        file_len: u64,
    ) -> AuditReport {
        AuditReport { findings, patches: Vec::new(), digest, file_len }
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.findings.is_empty() {
            return writeln!(
                f,
                "structure audit: clean (digest {:016x})",
                self.digest
            );
        }
        writeln!(
            f,
            "structure audit: {} finding(s) (digest {:016x})",
            self.findings.len(),
            self.digest
        )?;
        for finding in &self.findings {
            writeln!(f, "  - {}", finding)?;
        }
        Ok(())
    }
}

//===========================================================================//

/// A single in-place byte change that a repair would make.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Patch {
    pub(crate) offset: u64,
    pub(crate) original: Vec<u8>,
    pub(crate) replacement: Vec<u8>,
}

impl Patch {
    /// Byte offset at which the patch starts.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// The bytes currently expected at the offset.
    pub fn original_bytes(&self) -> &[u8] {
        &self.original
    }

    /// The bytes the repair would write.
    pub fn replacement_bytes(&self) -> &[u8] {
        &self.replacement
    }
}

//===========================================================================//

/// A read-only repair plan, carrying the precondition digest of the image it
/// was computed for.  Nothing is written until an explicit apply call, and
/// even then the digest must still match.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    digest: u64,
    file_len: u64,
    patches: Vec<Patch>,
    findings: Vec<Finding>,
}

impl RepairPlan {
    /// The precondition digest.  `apply_*` succeeds only when the current
    /// image still hashes to this value.
    pub fn precondition_digest(&self) -> u64 {
        self.digest
    }

    /// The findings the plan was built from.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// The in-place patches the plan would apply, sorted by offset.
    pub fn patches(&self) -> &[Patch] {
        &self.patches
    }

    /// Checks the precondition against an in-memory image without writing.
    pub fn matches_image(&self, image: &[u8]) -> bool {
        image.len() as u64 == self.file_len
            && digest_bytes(image) == self.digest
    }

    /// Returns the repaired image without touching the original bytes.  This
    /// is the dry run: it takes `&self` and needs no writer, so it cannot
    /// emit any bytes anywhere.
    pub fn dry_run(&self, current_image: &[u8]) -> io::Result<Vec<u8>> {
        self.check_precondition(current_image.len() as u64, current_image)?;
        let mut repaired = current_image.to_vec();
        for patch in &self.patches {
            let start = patch.offset as usize;
            let end = start + patch.replacement.len();
            if end > repaired.len()
                || repaired[start..end] != patch.original[..]
            {
                invalid_data!(
                    "Repair plan is stale: bytes at offset {} changed since \
                     the audit",
                    patch.offset
                );
            }
            repaired[start..end].copy_from_slice(&patch.replacement);
        }
        Ok(repaired)
    }

    /// Applies the plan to a seekable, writable image.
    ///
    /// The current contents are first fully re-read and checked against the
    /// precondition digest; a mismatch returns
    /// [`ErrorKind::InvalidData`] without writing.  If a write fails partway
    /// through, every patch already written is rolled back from the bytes
    /// captured before the first write, leaving the image byte-identical to
    /// what it was on entry.
    pub fn apply_to<W: Read + Write + Seek>(
        &self,
        writer: &mut W,
    ) -> io::Result<()> {
        let len = writer.seek(SeekFrom::End(0))?;
        writer.seek(SeekFrom::Start(0))?;
        let mut current = vec![0u8; len as usize];
        writer.read_exact(&mut current)?;
        // Validate everything before the first write.
        let repaired = self.dry_run(&current)?;
        // Apply, tracking how many patches landed so a failure can roll back.
        writer.seek(SeekFrom::Start(0))?;
        for (index, patch) in self.patches.iter().enumerate() {
            if let Err(error) = writer
                .seek(SeekFrom::Start(patch.offset))
                .and_then(|_| writer.write_all(&patch.replacement))
            {
                let _ = rollback(writer, &self.patches[..index], &current);
                return Err(error);
            }
        }
        writer.flush()?;
        let _ = repaired;
        Ok(())
    }

    /// Applies the plan to a file on disk atomically: the repaired image is
    /// staged in a sibling temporary file and renamed over the original only
    /// after every write succeeds.  Any staging error removes the temporary
    /// file and leaves the original untouched.
    pub fn apply_to_path<P: AsRef<Path>>(&self, path: P) -> io::Result<()> {
        let path = path.as_ref();
        let current = fs::read(path)?;
        let repaired = self.dry_run(&current)?;
        let dir = path.parent().unwrap_or_else(|| Path::new("."));
        let mut temp = tempfile_in(dir)?;
        let result = temp.file.write_all(&repaired).and_then(|_| temp.file.sync_all());
        if let Err(error) = result {
            let _ = fs::remove_file(&temp.path);
            return Err(error);
        }
        // Rename over the destination atomically on both Unix and Windows.
        fs::rename(temp.path.clone(), path).map_err(|error| {
            let _ = fs::remove_file(&temp.path);
            error
        })
    }

    fn check_precondition(
        &self,
        current_len: u64,
        current: &[u8],
    ) -> io::Result<()> {
        if current_len != self.file_len {
            invalid_data!(
                "Repair plan precondition failed: file length changed (was \
                 {}, now {})",
                self.file_len,
                current_len
            );
        }
        let current_digest = digest_bytes(current);
        if current_digest != self.digest {
            invalid_data!(
                "Repair plan precondition failed: digest changed (was \
                 {:016x}, now {:016x}); re-audit before applying",
                self.digest,
                current_digest
            );
        }
        Ok(())
    }
}

fn rollback<W: Write + Seek>(
    writer: &mut W,
    applied: &[Patch],
    original: &[u8],
) -> io::Result<()> {
    for patch in applied.iter().rev() {
        let start = patch.offset as usize;
        let end = start + patch.original.len();
        writer.seek(SeekFrom::Start(patch.offset))?;
        writer.write_all(&original[start..end])?;
    }
    writer.flush()
}

struct NamedTemp {
    path: std::path::PathBuf,
    file: fs::File,
}

fn tempfile_in(dir: &Path) -> io::Result<NamedTemp> {
    // Avoid pulling in a new dependency: the temp name uses the process id
    // and a fine-grained timestamp, and rename/remove handle any clash.
    use std::time::SystemTime;
    let nanos = SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    for attempt in 0..16u32 {
        let path = dir.join(format!(
            ".cfb-repair-{}-{}-{}.tmp",
            std::process::id(),
            nanos,
            attempt
        ));
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(file) => return Ok(NamedTemp { path, file }),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                continue
            }
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::Other,
        "could not create repair staging file",
    ))
}

//===========================================================================//

/// FNV-1a 64-bit digest of the image bytes.  This is a stable, dependency-free
/// fingerprint used only to detect that the planned-on bytes are still the
/// bytes on disk; it is not a cryptographic hash.
pub(crate) fn digest_bytes(bytes: &[u8]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;
    let mut hash = OFFSET_BASIS;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}
