//! Opt-in structural audit of a compound file, producing corruption evidence
//! and a read-only repair plan.
//!
//! The audit never writes to the audited input: every table is read once into
//! an in-memory [`AuditImage`], analyzed, and (if asked for) turned into a
//! [`RepairPlan`].  A plan is bound to a digest of the bytes it was made for;
//! [`RepairPlan::apply`] refuses to touch a file whose digest no longer
//! matches.  Each call starts from a fresh image, so there is no cache,
//! counter, or global configuration that can leak between calls.

use std::collections::BTreeSet;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

use fnv::FnvHashSet;

use crate::internal::consts;
use crate::internal::{Header, Sectors, Validation, Version};

//===========================================================================//

/// Which allocation structure of a compound file a corruption lives in.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorruptionLayer {
    /// The Double-Indirect File Allocation Table (the DIFAT sector chain and
    /// the list of FAT sectors).
    Difat,
    /// The File Allocation Table and the regular-sector chains it describes.
    Fat,
    /// The chain of directory sectors.
    Directory,
    /// The MiniFAT and the mini stream (root entry) chains.
    MiniFat,
}

/// The kind of corruption found at one location.
///
/// The kinds are intentionally kept separate even when they coexist in one
/// chain, so that a caller can tell a loop from an out-of-bounds pointer, a
/// doubly-claimed sector, an orphaned sector, or a length that disagrees with
/// the chain.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorruptionKind {
    /// A chain points back to a sector already visited by that same chain.
    Loop,
    /// A pointer names a sector/mini sector past the end of the file or
    /// table.
    OutOfBounds,
    /// Two different chain roots (or two points in a chain) claim the same
    /// sector.
    DuplicateOccupancy,
    /// A sector is marked as allocated in a table but no chain reaches it.
    OrphanSector,
    /// A header field or directory entry's declared length disagrees with the
    /// chain it names.
    DeclaredLengthMismatch,
    /// A table entry holds a value the spec reserves or forbids.
    InvalidEntry,
    /// The directory chain ends before all directory entries have been seen.
    Truncated,
}

/// One piece of corruption evidence: where it is, what it is, and enough
/// context to understand it without the file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// The allocation structure containing the corruption.
    pub layer: CorruptionLayer,
    /// The kind of corruption.
    pub kind: CorruptionKind,
    /// The first offending location, expressed within its structure (e.g. a
    /// FAT entry index, a sector id, or a directory entry index).  This is the
    /// first violation encountered in a fixed, deterministic traversal order.
    pub location: u32,
    /// Human-readable context for the violation.
    pub detail: String,
}

impl Finding {
    fn new(
        layer: CorruptionLayer,
        kind: CorruptionKind,
        location: u32,
        detail: String,
    ) -> Finding {
        Finding { layer, kind, location, detail }
    }
}

//===========================================================================//

/// An identity for the exact bytes a [`RepairPlan`] was derived from.
///
/// The digest is a tagged 64-bit FNV-1a hash of the whole input.  It is the
/// plan's precondition: the plan may only be applied when the current digest
/// still matches.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct AuditDigest(u64);

impl AuditDigest {
    fn of_bytes(bytes: &[u8]) -> AuditDigest {
        // 64-bit FNV-1a, with a domain tag mixed in so the digest is specific
        // to this precondition use rather than a bare FNV of the bytes.
        const OFFSET: u64 = 0xcbf29ce484222325;
        const PRIME: u64 = 0x100000001b3;
        let mut hash = OFFSET;
        for &byte in b"cfb-audit-v1\0" {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(PRIME);
        }
        for &byte in bytes {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(PRIME);
        }
        AuditDigest(hash)
    }

    /// Returns the digest as 16 lowercase hexadecimal digits.
    pub fn as_hex(&self) -> String {
        format!("{:016x}", self.0)
    }
}

//===========================================================================//

/// One byte-level operation in a [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairOp {
    /// Absolute byte offset into the file.
    pub offset: u64,
    /// The bytes expected to be there when the plan was made.
    pub before: Vec<u8>,
    /// The bytes to write there.
    pub after: Vec<u8>,
    /// What this op repairs, for human inspection.
    pub note: String,
}

/// A read-only repair plan: a digest of the bytes it was derived from plus the
/// concrete byte operations a successful repair consists of.
///
/// The plan never owns the file.  [`RepairPlan::dry_run`] reports the ops
/// without writing anything; [`RepairPlan::apply`] writes them atomically and
/// only while the digest still matches.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition: AuditDigest,
    ops: Vec<RepairOp>,
    findings: Vec<Finding>,
}

impl RepairPlan {
    /// The digest of the bytes this plan was made from.  Applying the plan is
    /// permitted only while the file's digest still equals this.
    pub fn precondition(&self) -> AuditDigest {
        self.precondition
    }

    /// The byte operations the repair would perform, in write order.
    pub fn ops(&self) -> &[RepairOp] {
        &self.ops
    }

    /// The corruption findings the plan repairs, in deterministic order.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// Reports the operations that would be applied and returns the digest of
    /// the bytes currently in `inner`, without writing a single byte.
    pub fn dry_run<F: Read + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<(AuditDigest, &[RepairOp])> {
        let digest = current_digest(inner)?;
        Ok((digest, &self.ops))
    }
}

fn current_digest<F: Read + Seek>(inner: &mut F) -> io::Result<AuditDigest> {
    let len = inner.seek(SeekFrom::End(0))?;
    inner.seek(SeekFrom::Start(0))?;
    let mut bytes = Vec::with_capacity(len as usize);
    inner.read_to_end(&mut bytes)?;
    inner.seek(SeekFrom::Start(0))?;
    Ok(AuditDigest::of_bytes(&bytes))
}

fn stale_error(digest: AuditDigest, precondition: AuditDigest) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidInput,
        format!(
            "Repair plan is stale: current digest is {} but the plan was \
             made for {}",
            digest.as_hex(),
            precondition.as_hex()
        ),
    )
}

//===========================================================================//

/// The result of an opt-in structural audit.
///
/// Holds the corruption evidence as ordered [`Finding`]s and, when the
/// corruption is repairable, a [`RepairPlan`].  The audit itself never modifies
/// the input; see [`AuditReport::apply_repair`].
#[derive(Debug)]
pub struct AuditReport<F> {
    inner: F,
    findings: Vec<Finding>,
    plan: Option<RepairPlan>,
}

impl<F> AuditReport<F> {
    /// The corruption findings, sorted by layer, kind, and location, with no
    /// duplicates.  Empty means the audited bytes satisfy the structural
    /// invariants the audit checks.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// Returns true if the audit found no corruption.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// The read-only repair plan, if one could be derived.  Even when present,
    /// nothing is written until [`AuditReport::apply_repair`] is called.
    pub fn repair_plan(&self) -> Option<&RepairPlan> {
        self.plan.as_ref()
    }

    /// Consumes the report and gives back the underlying reader/writer.
    /// Auditing never writes, so it is exactly as it was before the audit.
    pub fn into_inner(self) -> F {
        self.inner
    }
}

impl<F: Read + Seek> AuditReport<F> {
    /// Computes the digest of the bytes currently in the audited file and
    /// returns whether the plan could still be applied.  This writes nothing.
    pub fn plan_is_current(
        &mut self,
    ) -> io::Result<Option<(AuditDigest, bool)>> {
        match self.plan.as_ref() {
            None => Ok(None),
            Some(plan) => {
                let digest = current_digest(&mut self.inner)?;
                Ok(Some((digest, digest == plan.precondition())))
            }
        }
    }

    /// Runs the plan's dry run against the audited file: the operations that
    /// would be applied are returned, but no bytes are written.
    pub fn dry_run(&mut self) -> io::Result<Option<(AuditDigest, &[RepairOp])>> {
        match self.plan.as_ref() {
            None => Ok(None),
            Some(plan) => Ok(Some(plan.dry_run(&mut self.inner)?)),
        }
    }
}

impl<F: Read + Write + Seek> AuditReport<F> {
    /// Applies the repair plan explicitly.
    ///
    /// The plan is applied only when the file's current digest equals the
    /// plan's precondition; a file that changed since the audit produces an
    /// [`io::ErrorKind::InvalidInput`] error with no writes.  The write phase
    /// is atomic with respect to failures: each touched region is backed up
    /// first, and any write error restores every prior region before the
    /// error is returned, so a failed apply leaves the input byte-for-byte
    /// unchanged and the report remains usable for an identical retry.  On
    /// success the report's own evidence is replaced by a fresh audit of the
    /// repaired bytes, which carries no state from this attempt.
    pub fn apply_repair(&mut self) -> io::Result<usize> {
        let plan = match self.plan.as_ref() {
            Some(plan) => plan.clone(),
            None => invalid_input!("Audit found no repairable corruption"),
        };
        let digest = current_digest(&mut self.inner)?;
        if digest != plan.precondition {
            return Err(stale_error(digest, plan.precondition));
        }
        // Commit phase with backup/rollback.  All ops have been computed up
        // front; the only failures here are I/O failures, every one of which
        // is recoverable by restoring the saved regions.
        let mut backups: Vec<(u64, Vec<u8>)> = Vec::new();
        if let Err(error) =
            commit_ops(&mut self.inner, &plan.ops, &mut backups)
        {
            if let Err(rollback_error) =
                rollback_ops(&mut self.inner, &backups)
            {
                panic!(
                    "Repair commit failed ({error}) and rollback also failed                      ({rollback_error})"
                );
            }
            return Err(error);
        }
        self.inner.flush()?;
        let applied = plan.ops.len();
        // Replace this report's evidence wholesale with a fresh audit derived
        // only from the repaired bytes, so no counter, cache, or plan from the
        // attempt can survive into subsequent calls.
        let fresh = analyze_from_reader(&mut self.inner)?;
        self.findings = fresh.findings;
        self.plan = fresh.plan;
        Ok(applied)
    }
}

fn commit_ops<F: Read + Write + Seek>(
    inner: &mut F,
    ops: &[RepairOp],
    backups: &mut Vec<(u64, Vec<u8>)>,
) -> io::Result<()> {
    for op in ops {
        let mut before = vec![0u8; op.before.len()];
        inner.seek(SeekFrom::Start(op.offset))?;
        inner.read_exact(&mut before)?;
        if before != op.before {
            invalid_input!(
                "Repair plan precondition violated at byte {}: expected {:x?}, \
                 found {:x?}",
                op.offset,
                op.before,
                before
            );
        }
        backups.push((op.offset, before));
        inner.seek(SeekFrom::Start(op.offset))?;
        inner.write_all(&op.after)?;
    }
    Ok(())
}

fn rollback_ops<F: Read + Write + Seek>(
    inner: &mut F,
    backups: &[(u64, Vec<u8>)],
) -> io::Result<()> {
    for (offset, before) in backups.iter().rev() {
        inner.seek(SeekFrom::Start(*offset))?;
        inner.write_all(before)?;
    }
    inner.flush()?;
    Ok(())
}

//===========================================================================//
// Parsed directory slot: only the fields the audit reasons about.

#[derive(Clone, Debug)]
struct RawEntry {
    obj_type: u8,
    left_sibling: u32,
    right_sibling: u32,
    child: u32,
    start_sector: u32,
    stream_len: u64,
}

impl RawEntry {
    fn parse(slot: &[u8]) -> RawEntry {
        let u32at = |off: usize| {
            u32::from_le_bytes([
                slot[off],
                slot[off + 1],
                slot[off + 2],
                slot[off + 3],
            ])
        };
        RawEntry {
            obj_type: slot[66],
            left_sibling: u32at(68),
            right_sibling: u32at(72),
            child: u32at(76),
            start_sector: u32at(116),
            stream_len: u64::from_le_bytes([
                slot[120], slot[121], slot[122], slot[123], slot[124],
                slot[125], slot[126], slot[127],
            ]),
        }
    }
}

//===========================================================================//
// Edge outcome of following one table link.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Edge {
    End,
    Next(u32),
    OutOfBounds,
    Invalid,
}

fn fat_edge(fat: &[u32], from: u32, num_sectors: u32) -> Edge {
    let index = from as usize;
    if index >= fat.len() {
        return Edge::OutOfBounds;
    }
    match fat[index] {
        consts::END_OF_CHAIN | consts::FREE_SECTOR => Edge::End,
        consts::INVALID_SECTOR | consts::FAT_SECTOR | consts::DIFAT_SECTOR => {
            Edge::Invalid
        }
        next => {
            if next >= num_sectors {
                Edge::OutOfBounds
            } else {
                Edge::Next(next)
            }
        }
    }
}

fn mini_edge(minifat: &[u32], from: u32) -> Edge {
    let index = from as usize;
    if index >= minifat.len() {
        return Edge::OutOfBounds;
    }
    match minifat[index] {
        consts::END_OF_CHAIN | consts::FREE_SECTOR => Edge::End,
        consts::INVALID_SECTOR | consts::FAT_SECTOR | consts::DIFAT_SECTOR => {
            Edge::Invalid
        }
        next => {
            if next as usize >= minifat.len() {
                Edge::OutOfBounds
            } else {
                Edge::Next(next)
            }
        }
    }
}

//===========================================================================//

struct AuditImage {
    parse_findings: Vec<Finding>,
    version: Version,
    sector_len: u32,
    num_sectors: u32,
    header: Header,
    difat_chain: Vec<u32>,
    difat_ok: bool,
    fat_sector_ids: Vec<u32>,
    fat: Vec<u32>,
    dir_chain: Vec<u32>,
    dir_ok: bool,
    entries: Vec<RawEntry>,
    minifat_chain: Vec<u32>,
    minifat_ok: bool,
    minifat: Vec<u32>,
}

fn u32s(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

fn sector_bytes<'a>(bytes: &'a [u8], sector_len: u32, sector: u32) -> &'a [u8] {
    let start = ((sector as u64 + 1) * sector_len as u64) as usize;
    &bytes[start..start + sector_len as usize]
}

/// Parses the audit image.  A hard header failure (wrong magic, unknown
/// version, bad byte-order mark) is returned as an error, exactly as the
/// ordinary open path does; table corruption never errors, it is collected.
fn parse_image(bytes: &[u8]) -> io::Result<AuditImage> {
    if bytes.len() < consts::HEADER_LEN {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            bytes.len()
        );
    }
    let mut cursor = Cursor::new(bytes);
    // Same header parser the open path uses, under Permissive validation: the
    // audit must be able to get far enough to report table damage rather than
    // reject the file.
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let sector_len = header.version.sector_len() as u32;
    if (bytes.len() as u64) < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            bytes.len(),
            sector_len
        );
    }
    let num_sectors = (bytes.len() as u32 / sector_len) - 1;
    let entries_per_sector = sector_len / 4;
    let mut findings_buf: Vec<Finding> = Vec::new();

    // ---- DIFAT: same traversal order and trimming as the open path. ----
    let mut difat_list: Vec<u32> =
        header.initial_difat_entries.iter().copied().collect();
    let mut difat_chain: Vec<u32> = Vec::new();
    let mut difat_ok = true;
    {
        let mut seen = FnvHashSet::default();
        let mut current = header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Difat,
                    CorruptionKind::InvalidEntry,
                    current,
                    format!("DIFAT chain includes invalid sector {current}"),
                ));
                difat_ok = false;
                break;
            } else if current >= num_sectors {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Difat,
                    CorruptionKind::OutOfBounds,
                    current,
                    format!(
                        "DIFAT chain includes sector {current}, but sector \
                         count is only {num_sectors}"
                    ),
                ));
                difat_ok = false;
                break;
            }
            if !seen.insert(current) {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Difat,
                    CorruptionKind::Loop,
                    current,
                    format!(
                        "DIFAT chain revisits sector {current}, forming a loop"
                    ),
                ));
                difat_ok = false;
                break;
            }
            difat_chain.push(current);
            let sector = sector_bytes(bytes, sector_len, current);
            for i in 0..(entries_per_sector - 1) {
                let next = u32::from_le_bytes([
                    sector[4 * i],
                    sector[4 * i + 1],
                    sector[4 * i + 2],
                    sector[4 * i + 3],
                ]);
                if next != consts::FREE_SECTOR
                    && next > consts::MAX_REGULAR_SECTOR
                {
                    findings_buf.push(Finding::new(
                        CorruptionLayer::Difat,
                        CorruptionKind::InvalidEntry,
                        next,
                        format!("DIFAT refers to invalid sector index {next}"),
                    ));
                    difat_ok = false;
                }
                difat_list.push(next);
            }
            let last = entries_per_sector - 1;
            current = u32::from_le_bytes([
                sector[4 * last],
                sector[4 * last + 1],
                sector[4 * last + 2],
                sector[4 * last + 3],
            ]);
        }
    }
    // Replicate the open path's permissive trimming of bogus padding.
    while difat_list.len() > consts::NUM_DIFAT_ENTRIES_IN_HEADER
        && difat_list.len() > header.num_fat_sectors as usize
        && difat_list.last() == Some(&0)
    {
        difat_list.pop();
    }
    while difat_list.last() == Some(&consts::FREE_SECTOR) {
        difat_list.pop();
    }

    // ---- FAT. ----
    let mut fat: Vec<u32> = Vec::new();
    for &fat_sector in difat_list.iter() {
        if fat_sector > consts::MAX_REGULAR_SECTOR {
            continue;
        }
        if fat_sector >= num_sectors {
            findings_buf.push(Finding::new(
                CorruptionLayer::Fat,
                CorruptionKind::OutOfBounds,
                fat_sector,
                format!(
                    "DIFAT lists FAT sector {fat_sector}, but sector count is \
                     only {num_sectors}"
                ),
            ));
            continue;
        }
        fat.extend(u32s(sector_bytes(bytes, sector_len, fat_sector)));
    }
    // Same permissive normalization the open path performs.
    while fat.len() > num_sectors as usize {
        if matches!(
            fat.last(),
            Some(&0)
                | Some(&consts::DIFAT_SECTOR)
                | Some(&consts::FAT_SECTOR)
                | Some(&consts::FREE_SECTOR)
        ) {
            fat.pop();
        } else {
            break;
        }
    }
    while fat.len() < num_sectors as usize {
        fat.push(consts::FREE_SECTOR);
    }
    let fat_sector_ids = difat_list
        .iter()
        .copied()
        .filter(|&s| s < num_sectors)
        .collect::<Vec<u32>>();

    // ---- Directory chain. ----
    let mut dir_chain: Vec<u32> = Vec::new();
    let mut entries: Vec<RawEntry> = Vec::new();
    let mut dir_ok = true;
    {
        let mut current = header.first_dir_sector;
        let mut seen = FnvHashSet::default();
        if current == consts::END_OF_CHAIN || current == consts::FREE_SECTOR {
            findings_buf.push(Finding::new(
                CorruptionLayer::Directory,
                CorruptionKind::Truncated,
                current,
                "directory chain is empty, so the root entry is missing"
                    .to_string(),
            ));
            dir_ok = false;
        }
        while dir_ok
            && current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Directory,
                    CorruptionKind::InvalidEntry,
                    current,
                    format!(
                        "directory chain includes invalid sector {current}"
                    ),
                ));
                dir_ok = false;
                break;
            } else if current >= num_sectors {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Directory,
                    CorruptionKind::Truncated,
                    current,
                    format!(
                        "directory chain names sector {current}, but sector \
                         count is only {num_sectors}"
                    ),
                ));
                dir_ok = false;
                break;
            }
            if !seen.insert(current) {
                findings_buf.push(Finding::new(
                    CorruptionLayer::Directory,
                    CorruptionKind::Loop,
                    current,
                    format!(
                        "directory chain revisits sector {current}, forming a \
                         loop"
                    ),
                ));
                dir_ok = false;
                break;
            }
            dir_chain.push(current);
            let sector = sector_bytes(bytes, sector_len, current);
            for slot_index in 0..header.version.dir_entries_per_sector() {
                let start = slot_index * consts::DIR_ENTRY_LEN;
                entries.push(RawEntry::parse(
                    &sector[start..start + consts::DIR_ENTRY_LEN],
                ));
            }
            match fat_edge(&fat, current, num_sectors) {
                Edge::End => break,
                Edge::Next(next) => current = next,
                Edge::OutOfBounds => {
                    findings_buf.push(Finding::new(
                        CorruptionLayer::Directory,
                        CorruptionKind::Truncated,
                        current,
                        format!(
                            "directory chain ends at sector {current} with a \
                             pointer past the end of the file"
                        ),
                    ));
                    dir_ok = false;
                }
                Edge::Invalid => {
                    findings_buf.push(Finding::new(
                        CorruptionLayer::Directory,
                        CorruptionKind::InvalidEntry,
                        current,
                        format!(
                            "FAT entry {current} on the directory chain holds \
                             a reserved value"
                        ),
                    ));
                    dir_ok = false;
                }
            }
        }
    }

    // ---- MiniFAT chain. ----
    let mut minifat_chain: Vec<u32> = Vec::new();
    let mut minifat_ok = true;
    {
        let mut current = header.first_minifat_sector;
        let mut seen = FnvHashSet::default();
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= num_sectors
            {
                findings_buf.push(Finding::new(
                    CorruptionLayer::MiniFat,
                    CorruptionKind::OutOfBounds,
                    current,
                    format!(
                        "MiniFAT chain starts at sector {current}, but sector \
                         count is only {num_sectors}"
                    ),
                ));
                minifat_ok = false;
                break;
            }
            if !seen.insert(current) {
                findings_buf.push(Finding::new(
                    CorruptionLayer::MiniFat,
                    CorruptionKind::Loop,
                    current,
                    format!(
                        "MiniFAT chain revisits sector {current}, forming a \
                         loop"
                    ),
                ));
                minifat_ok = false;
                break;
            }
            minifat_chain.push(current);
            match fat_edge(&fat, current, num_sectors) {
                Edge::End => break,
                Edge::Next(next) => current = next,
                Edge::OutOfBounds => {
                    findings_buf.push(Finding::new(
                        CorruptionLayer::MiniFat,
                        CorruptionKind::Truncated,
                        current,
                        format!(
                            "MiniFAT chain ends at sector {current} with a \
                             pointer past the end of the file"
                        ),
                    ));
                    minifat_ok = false;
                }
                Edge::Invalid => {
                    findings_buf.push(Finding::new(
                        CorruptionLayer::MiniFat,
                        CorruptionKind::InvalidEntry,
                        current,
                        format!(
                            "FAT entry {current} on the MiniFAT chain holds a \
                             reserved value"
                        ),
                    ));
                    minifat_ok = false;
                }
            }
        }
    }
    let mut minifat: Vec<u32> = Vec::new();
    for &sector in minifat_chain.iter() {
        minifat.extend(u32s(sector_bytes(bytes, sector_len, sector)));
    }
    while minifat.last() == Some(&consts::FREE_SECTOR) {
        minifat.pop();
    }

    // Stash the early findings on the image so the analysis pass can combine
    // them with the findings that need parsed entries.
    Ok(AuditImage {
        parse_findings: findings_buf,
        version: header.version,
        sector_len,
        num_sectors,
        header,
        difat_chain,
        difat_ok,
        fat_sector_ids,
        fat,
        dir_chain,
        dir_ok,
        entries,
        minifat_chain,
        minifat_ok,
        minifat,
    })
}

//===========================================================================//

