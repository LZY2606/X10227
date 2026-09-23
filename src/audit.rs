//! Opt-in, strictly read-only structural audits of Compound File Binary
//! files.
//!
//! Unlike opening a compound file (which repairs some damage on the fly so
//! that data can still be read), an [`AuditReport`] does not touch the input
//! at all.  It enumerates separate [`Corruption`] evidence for each of the
//! four allocation structures (FAT, DIFAT, MiniFAT, and the directory
//! chain), classifies every problem by the distinct structural invariant it
//! violates (cycles, out-of-bounds references, double allocation, orphan
//! sectors, declared-length mismatches, ...), and derives a
//! [`RepairPlan`] of deterministic byte-level edits.
//!
//! The repair plan records a prerequisite [`AuditDigest`] of the audited
//! bytes.  [`RepairPlan::apply_to`] refuses to write anything unless the
//! source bytes still hash to that digest, and it builds the entire repaired
//! image in memory before touching the destination, so a failure at any
//! point leaves no half-written state behind.  A plan can also be checked
//! with [`RepairPlan::dry_run`], which never performs any I/O at all.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

use fnv::FnvHashSet;

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::ReadLeNumber;

// Header field offsets (MS-CFB section 2.2).
const OFFSET_NUM_DIR_SECTORS: u64 = 40;
const OFFSET_NUM_FAT_SECTORS: u64 = 44;
const OFFSET_FIRST_DIR_SECTOR: u64 = 48;
const OFFSET_FIRST_MINIFAT_SECTOR: u64 = 60;
const OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const OFFSET_FIRST_DIFAT_SECTOR: u64 = 68;
const OFFSET_NUM_DIFAT_SECTORS: u64 = 72;
const OFFSET_DIFAT_START: u64 = 76;

// Directory-entry field offsets within a 128-byte entry (MS-CFB 2.6.6).
const OFFSET_DIR_START_SECTOR: usize = 116;
const OFFSET_DIR_STREAM_LEN: usize = 120;

const MINI_SECTORS_PER_4096_SECTOR: u32 = 64;

//===========================================================================//

/// Which CFB allocation structure a piece of [`Corruption`] evidence was
/// found in.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Component {
    /// The Double-Indirect FAT (the chain locating the FAT sectors).
    Difat,
    /// The File Allocation Table (the regular-sector chains).
    Fat,
    /// The directory chain and the sibling/child trees within it.
    DirectoryChain,
    /// The MiniFAT and the mini stream it allocates out of.
    MiniFat,
}

impl Component {
    fn label(self) -> &'static str {
        match self {
            Component::Difat => "DIFAT",
            Component::Fat => "FAT",
            Component::DirectoryChain => "directory chain",
            Component::MiniFat => "MiniFAT",
        }
    }
}

impl fmt::Display for Component {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// The distinct structural invariant that a piece of [`Corruption`]
/// violates.
///
/// The five invariants called out by the format's recovery semantics --
/// cycles, out-of-bounds references, double allocation (crossed chains),
/// orphan sectors, and declared-length mismatches -- are always reported
/// separately, so a caller never has to disambiguate a generic "bad chain"
/// error.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum CorruptionKind {
    /// A chain reaches a sector it already visited.
    Cycle,
    /// A pointer names a sector (or mini sector) that does not exist.
    OutOfBounds,
    /// The same sector is reachable from two different chains.
    DoubleAllocation,
    /// An allocated sector is not reachable from any chain.
    OrphanSector,
    /// A declared length or sector count does not match the actual chain.
    DeclaredLengthMismatch,
    /// A FAT/DIFAT entry holds a reserved/illegal value.
    InvalidValue,
}

impl CorruptionKind {
    fn label(self) -> &'static str {
        match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DoubleAllocation => "double allocation",
            CorruptionKind::OrphanSector => "orphan sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared length mismatch"
            }
            CorruptionKind::InvalidValue => "invalid reserved value",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// One concrete piece of corruption evidence: the structure it is in, the
/// invariant it violates, where it was first observed, and a human-readable
/// description of the surrounding context.
#[derive(Clone, Debug)]
pub struct Corruption {
    component: Component,
    kind: CorruptionKind,
    /// A machine-independent description of the first offending position.
    location: String,
    /// The human-readable context around that position.
    detail: String,
}

impl Corruption {
    /// The allocation structure containing this problem.
    pub fn component(&self) -> Component {
        self.component
    }
    /// The structural invariant this problem violates.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }
    /// The first position at which the violation was observed (e.g.
    /// `"FAT[7]"` or `"directory entry 2 (/foo)"`).
    pub fn location(&self) -> &str {
        &self.location
    }
    /// The context around the first violation, with the concrete sector IDs
    /// and lengths involved.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} at {} ({})",
            self.component.label(),
            self.kind.label(),
            self.location,
            self.detail
        )
    }
}

//===========================================================================//

/// An FNV-1a 64-bit digest of the exact bytes an audit was computed from.
///
/// The digest is part of the [`RepairPlan`] contract: a plan only applies
/// when the source bytes still produce the same digest, so any change to the
/// file after planning is detected before a single byte is written.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct AuditDigest(u64);

impl AuditDigest {
    /// The digest as 16 lowercase hexadecimal digits.
    pub fn to_hex(self) -> String {
        format!("{:016x}", self.0)
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_hex())
    }
}

fn digest_bytes(data: &[u8]) -> AuditDigest {
    // FNV-1a 64-bit, seeded with the length so that trailing bytes can never
    // be confused with absent bytes.
    let mut hash: u64 = 0xcbf29ce484222325;
    for &byte in (data.len() as u64).to_le_bytes().iter().chain(data.iter()) {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    AuditDigest(hash)
}

//===========================================================================//

/// One deterministic byte replacement proposed by a [`RepairPlan`].
#[derive(Clone, Debug)]
pub struct RepairStep {
    offset: u64,
    old_bytes: Vec<u8>,
    new_bytes: Vec<u8>,
    description: String,
}

impl RepairStep {
    /// The byte offset in the file that this step rewrites.
    pub fn offset(&self) -> u64 {
        self.offset
    }
    /// The bytes expected at that offset when the plan is applied.
    pub fn expected_bytes(&self) -> &[u8] {
        &self.old_bytes
    }
    /// The bytes to write at that offset.
    pub fn replacement_bytes(&self) -> &[u8] {
        &self.new_bytes
    }
    /// A human-readable description of the edit.
    pub fn description(&self) -> &str {
        &self.description
    }
}

impl fmt::Display for RepairStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "at byte {}: {}",
            self.offset, self.description
        )
    }
}

/// A read-only repair plan derived from an [`AuditReport`].
///
/// The plan is a pure value: it owns no handles, threads, caches, or files.
/// Every step is a fixed-width byte replacement, and the recorded
/// [`AuditDigest`] pins the exact input the plan was computed from.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    digest: AuditDigest,
    source_len: usize,
    steps: Vec<RepairStep>,
    unfixable: Vec<String>,
}

impl RepairPlan {
    /// The prerequisite digest of the source bytes.  Application is refused
    /// unless the source still matches this.
    pub fn prerequisite_digest(&self) -> AuditDigest {
        self.digest
    }
    /// The byte-level edits that would be made, in ascending offset order.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }
    /// True only when every reported corruption has a deterministic repair.
    pub fn fully_repairable(&self) -> bool {
        self.unfixable.is_empty()
    }
    /// Locations of findings whose damage cannot be repaired by rewriting
    /// existing bytes (for example a chain whose sector is beyond EOF).
    pub fn unfixable_findings(&self) -> &[String] {
        &self.unfixable
    }

    /// Checks that the plan would apply to `source` without performing any
    /// writes.
    ///
    /// This performs no I/O beyond reading the source: it verifies the
    /// prerequisite digest and every expected byte, then reports `Ok(true)`
    /// if the plan is applicable.  A dry run can never write a single byte.
    pub fn dry_run<F: Read + Seek>(&self, source: &mut F) -> io::Result<bool> {
        let mut data = Vec::new();
        source.seek(SeekFrom::Start(0))?;
        source.read_to_end(&mut data)?;
        if digest_bytes(&data) != self.digest || data.len() != self.source_len
        {
            return Ok(false);
        }
        for step in self.steps.iter() {
            let start = step.offset as usize;
            if start + step.old_bytes.len() > data.len()
                || &data[start..start + step.old_bytes.len()]
                    != step.old_bytes.as_slice()
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Applies the plan, writing a fully repaired copy to `dest`.
    ///
    /// The source is opened only for reading and seeking, and is never
    /// modified.  The method:
    ///
    /// 1. Refuses with [`io::ErrorKind::InvalidInput`] unless the source
    ///    still matches the plan's prerequisite digest.
    /// 2. Refuses with [`io::ErrorKind::InvalidData`] if any finding has no
    ///    deterministic repair, so a partial repair can never be produced.
    /// 3. Builds the complete repaired image in memory, re-audits it to prove
    ///    it is clean, and only then writes it out.
    ///
    /// If any step fails (including a write error to `dest`), neither the
    /// source nor the destination is left half-updated: the destination is
    /// truncated to zero bytes before the error is returned.
    pub fn apply_to<F, W>(&self, source: &mut F, mut dest: W) -> io::Result<()>
    where
        F: Read + Seek,
        W: Read + Write + Seek,
    {
        if !self.fully_repairable() {
            invalid_input!(
                "repair plan has unfixable findings: {}",
                self.unfixable.join("; ")
            );
        }
        let mut data = Vec::new();
        source.seek(SeekFrom::Start(0))?;
        source.read_to_end(&mut data)?;
        if digest_bytes(&data) != self.digest || data.len() != self.source_len
        {
            invalid_input!(
                "source no longer matches the repair plan's prerequisite \
                 digest {}; audit and re-plan before applying",
                self.digest
            );
        }
        for step in self.steps.iter() {
            let start = step.offset as usize;
            let end = start + step.old_bytes.len();
            if end > data.len() {
                invalid_data!(
                    "repair step at byte {} is beyond the {}-byte file",
                    step.offset,
                    data.len()
                );
            }
            if data[start..end] != step.old_bytes[..] {
                invalid_input!(
                    "byte {} has changed since the repair plan was made",
                    step.offset
                );
            }
            data[start..end].copy_from_slice(&step.new_bytes);
        }
        // The repaired image must itself be structurally clean; this shares
        // the production audit logic, so a plan cannot self-certify.
        let repaired_digest = digest_bytes(&data);
        let report = audit_bytes(&data, Validation::Permissive)?;
        if !report.is_clean() {
            invalid_data!(
                "aborting repair: repaired file still shows {}",
                report
                    .corruptions()
                    .first()
                    .map(|c| c.to_string())
                    .unwrap_or_else(|| "corruption".to_string())
            );
        }
        // Publish the result as a single whole-file write, so the
        // destination never observes a partial image.
        if let Err(error) = (|| -> io::Result<()> {
            dest.seek(SeekFrom::Start(0))?;
            dest.set_len(0)?;
            dest.write_all(&data)?;
            dest.flush()?;
            // Guarantee no caller can mistake a trailing stale tail for
            // repaired data.
            dest.seek(SeekFrom::End(0))?;
            debug_assert_eq!(
                dest.stream_position()? as usize,
                data.len()
            );
            debug_assert_ne!(repaired_digest, self.digest);
            let _ = repaired_digest;
            Ok(())
        })() {
            // Roll back any partial destination state before propagating.
            let _ = dest.seek(SeekFrom::Start(0));
            let _ = dest.set_len(0);
            return Err(error);
        }
        Ok(())
    }
}

impl fmt::Display for RepairPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "read-only repair plan (prerequisite digest {})",
            self.digest
        )?;
        for step in self.steps.iter() {
            writeln!(f, "  - {step}")?;
        }
        for finding in self.unfixable.iter() {
            writeln!(f, "  - NO AUTOMATIC REPAIR: {finding}")?;
        }
        Ok(())
    }
}

//===========================================================================//

#[derive(Clone)]
struct Edit {
    old_bytes: Vec<u8>,
    new_bytes: Vec<u8>,
    description: String,
}

/// The result of an opt-in structural audit: separate evidence for every
/// distinct problem found in the FAT, DIFAT, MiniFAT, and directory chain,
/// plus a read-only [`RepairPlan`].
#[derive(Clone)]
pub struct AuditReport {
    digest: AuditDigest,
    version: Version,
    corruptions: Vec<Corruption>,
    edits: BTreeMap<u64, Edit>,
    unfixable: Vec<String>,
}

impl AuditReport {
    /// The version of the audited compound file.
    pub fn version(&self) -> Version {
        self.version
    }
    /// The digest of the exact bytes that were audited.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }
    /// Returns true if no corruption was found.
    pub fn is_clean(&self) -> bool {
        self.corruptions.is_empty()
    }
    /// The corruption evidence, sorted deterministically by structure,
    /// invariant, and first-offending position.
    pub fn corruptions(&self) -> &[Corruption] {
        &self.corruptions
    }
    /// Returns true if evidence of the given invariant was found.
    pub fn has_kind(&self, kind: CorruptionKind) -> bool {
        self.corruptions.iter().any(|c| c.kind == kind)
    }
    /// Derives the read-only repair plan for this report.
    pub fn repair_plan(&self) -> RepairPlan {
        let steps = self
            .edits
            .iter()
            .map(|(offset, edit)| RepairStep {
                offset: *offset,
                old_bytes: edit.old_bytes.clone(),
                new_bytes: edit.new_bytes.clone(),
                description: edit.description.clone(),
            })
            .collect();
        RepairPlan {
            digest: self.digest,
            source_len: self.source_len,
            steps,
            unfixable: self.unfixable.clone(),
        }
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_clean() {
            return writeln!(f, "CFB audit: clean ({})", self.digest);
        }
        writeln!(
            f,
            "CFB audit: {} finding(s) ({})",
            self.corruptions.len(),
            self.digest
        )?;
        for corruption in self.corruptions.iter() {
            writeln!(f, "  - {corruption}")?;
        }
        Ok(())
    }
}

//===========================================================================//

#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Difat,
    Fat,
    DirectoryChain,
    MiniFatChain,
    MiniStream,
    Stream,
}

#[derive(Clone)]
struct OwnerInfo {
    owner: Owner,
    label: String,
}

struct FatChain {
    sids: Vec<u32>,
    /// True if the walk had to stop for a structural fault rather than
    /// reaching END_OF_CHAIN cleanly.
    fault: bool,
}

struct Engine<'a> {
    data: &'a [u8],
    version: Version,
    sector_len: usize,
    num_sectors: u32,
    validation: Validation,
    findings: Vec<Corruption>,
    edits: BTreeMap<u64, Edit>,
    unfixable: Vec<String>,
}

impl<'a> Engine<'a> {
    fn u32le(slice: &[u8], offset: usize) -> u32 {
        u32::from_le_bytes([
            slice[offset],
            slice[offset + 1],
            slice[offset + 2],
            slice[offset + 3],
        ])
    }

    fn u64le(slice: &[u8], offset: usize) -> u64 {
        u64::from_le_bytes([
            slice[offset],
            slice[offset + 1],
            slice[offset + 2],
            slice[offset + 3],
            slice[offset + 4],
            slice[offset + 5],
            slice[offset + 6],
            slice[offset + 7],
        ])
    }

    fn sector_offset(&self, sid: u32, index: usize) -> usize {
        consts::HEADER_LEN
            + sid as usize * self.sector_len
            + index
    }

    fn sector_slice(&self, sid: u32) -> Option<&'a [u8]> {
        if sid >= self.num_sectors {
            return None;
        }
        let start = consts::HEADER_LEN + sid as usize * self.sector_len;
        self.data.get(start..start + self.sector_len)
    }

    fn fat_entry_offset(&self, fat_sectors: &[u32], index: usize) -> Option<u64> {
        let per = self.sector_len / 4;
        let fat_sector = fat_sectors.get(index / per)?;
        Some(self.sector_offset(*fat_sector, (index % per) * 4) as u64)
    }

    fn add(
        &mut self,
        component: Component,
        kind: CorruptionKind,
        location: String,
        detail: String,
    ) {
        self.findings.push(Corruption {
            component,
            kind,
            location,
            detail,
        });
    }

    fn add_unfixable(
        &mut self,
        component: Component,
        kind: CorruptionKind,
        location: String,
        detail: String,
    ) {
        self.add(component, kind, location.clone(), detail);
        self.unfixable.push(location);
    }

    /// Records a fixed-width replacement.  Each offset has exactly one
    /// authoritative edit; the first proposal wins, which keeps the edits a
    /// deterministic function of the findings.
    fn edit(
        &mut self,
        offset: u64,
        new_bytes: Vec<u8>,
        description: String,
    ) {
        let start = offset as usize;
        let old_bytes = self
            .data
            .get(start..start + new_bytes.len())
            .map(|slice| slice.to_vec())
            .unwrap_or_default();
        self.edits.entry(offset).or_insert(Edit {
            old_bytes,
            new_bytes,
            description,
        });
    }

    fn edit_u32(&mut self, offset: u64, new_value: u32, description: String) {
        self.edit(offset, new_value.to_le_bytes().to_vec(), description);
    }

    fn edit_u64(&mut self, offset: u64, new_value: u64, description: String) {
        self.edit(offset, new_value.to_le_bytes().to_vec(), description);
    }

    // ------------------------------------------------------------------ //
    // DIFAT and FAT parsing.
    // ------------------------------------------------------------------ //

    /// Walks the DIFAT sector chain independently of the FAT (the DIFAT
    /// links its own sectors through their last u32).
    fn read_difat(
        &mut self,
        header: &Header,
    ) -> (Vec<u32>, Vec<u32>) {
        let mut difat = Vec::new();
        let mut difat_sector_ids = Vec::new();
        // DIFAT entries stored in the header array.
        for (index, &sid) in header
            .initial_difat_entries
            .iter()
            .take_while(|&&sid| sid != consts::FREE_SECTOR)
            .enumerate()
        {
            if sid >= self.num_sectors {
                self.add_unfixable(
                    Component::Difat,
                    CorruptionKind::OutOfBounds,
                    format!("header DIFAT entry {index}"),
                    format!(
                        "DIFAT lists FAT sector {sid}, but file has only {} \
                         sectors",
                        self.num_sectors
                    ),
                );
            } else if difat.contains(&sid) {
                self.add(
                    Component::Difat,
                    CorruptionKind::DoubleAllocation,
                    format!("header DIFAT entry {index}"),
                    format!("FAT sector {sid} is listed more than once in the \
                             DIFAT"),
                );
                let offset = OFFSET_DIFAT_START + 4 * index as u64;
                self.edit_u32(
                    offset,
                    consts::FREE_SECTOR,
                    format!("drop duplicate DIFAT entry for FAT sector {sid}"),
                );
            } else {
                difat.push(sid);
            }
        }

        let mut current = header.first_difat_sector;
        let mut seen = FnvHashSet::default();
        let mut position = 0usize;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            if current > consts::MAX_REGULAR_SECTOR
                || current >= self.num_sectors
            {
                self.add_unfixable(
                    Component::Difat,
                    CorruptionKind::OutOfBounds,
                    format!("DIFAT chain sector {position}"),
                    format!(
                        "DIFAT chain continues at sector {current}, but file \
                         has only {} sectors",
                        self.num_sectors
                    ),
                );
                break;
            }
            if !seen.insert(current) {
                self.add(
                    Component::Difat,
                    CorruptionKind::Cycle,
                    format!("DIFAT sector {current}"),
                    "DIFAT sector chain revisits a sector".to_string(),
                );
                break;
            }
            difat_sector_ids.push(current);
            let Some(sector) = self.sector_slice(current) else {
                break;
            };
            let entries_per_sector = self.sector_len / 4 - 1;
            for index in 0..entries_per_sector {
                let sid = Self::u32le(sector, 4 * index);
                if sid == consts::FREE_SECTOR {
                    continue;
                }
                if sid > consts::MAX_REGULAR_SECTOR {
                    let offset = self.sector_offset(current, 4 * index) as u64;
                    self.add(
                        Component::Difat,
                        CorruptionKind::InvalidValue,
                        format!("DIFAT sector {current} entry {index}"),
                        format!("DIFAT entry is 0x{sid:08X}"),
                    );
                    self.edit_u32(
                        offset,
                        consts::FREE_SECTOR,
                        format!("clear reserved DIFAT entry 0x{sid:08X}"),
                    );
                } else if sid >= self.num_sectors {
                    self.add_unfixable(
                        Component::Difat,
                        CorruptionKind::OutOfBounds,
                        format!("DIFAT sector {current} entry {index}"),
                        format!(
                            "DIFAT lists FAT sector {sid}, but file has only \
                             {} sectors",
                            self.num_sectors
                        ),
                    );
                } else if difat.contains(&sid) {
                    self.add(
                        Component::Difat,
                        CorruptionKind::DoubleAllocation,
                        format!("DIFAT sector {current} entry {index}"),
                        format!(
                            "FAT sector {sid} is listed more than once in the \
                             DIFAT"
                        ),
                    );
                    let offset = self.sector_offset(current, 4 * index) as u64;
                    self.edit_u32(
                        offset,
                        consts::FREE_SECTOR,
                        format!("drop duplicate DIFAT entry for FAT sector {sid}"),
                    );
                } else {
                    difat.push(sid);
                }
            }
            current = Self::u32le(sector, self.sector_len - 4);
            position += 1;
            if self.validation.is_strict() && current == consts::FREE_SECTOR {
                self.add(
                    Component::Difat,
                    CorruptionKind::InvalidValue,
                    format!("DIFAT sector {current}"),
                    "DIFAT chain terminates with FREE_SECTOR instead of \
                     END_OF_CHAIN"
                        .to_string(),
                );
            }
        }

        if header.num_difat_sectors as usize != difat_sector_ids.len() {
            self.add(
                Component::Difat,
                CorruptionKind::DeclaredLengthMismatch,
                "header num_difat_sectors".to_string(),
                format!(
                    "header declares {} DIFAT sectors, but the chain has {}",
                    header.num_difat_sectors,
                    difat_sector_ids.len()
                ),
            );
            self.edit_u32(
                OFFSET_NUM_DIFAT_SECTORS,
                difat_sector_ids.len() as u32,
                "correct num_difat_sectors in header".to_string(),
            );
        }

        (difat, difat_sector_ids)
    }

    /// Reads the raw FAT sectors listed by the DIFAT.
    fn read_fat(&mut self, difat: &[u32]) -> Vec<u32> {
        let mut fat = Vec::new();
        for &sid in difat.iter() {
            let Some(sector) = self.sector_slice(sid) else {
                continue;
            };
            for index in 0..self.sector_len / 4 {
                fat.push(Self::u32le(sector, 4 * index));
            }
        }
        // A FAT longer than the file can't be repaired by fixed-width edits
        // (it would require removing sectors); flag it, with no edit.
        if fat.len() > self.num_sectors as usize {
            self.add_unfixable(
                Component::Fat,
                CorruptionKind::DeclaredLengthMismatch,
                "FAT".to_string(),
                format!(
                    "FAT has {} entries, but file has only {} sectors",
                    fat.len(),
                    self.num_sectors
                ),
            );
        }
        while fat.len() < self.num_sectors as usize {
            fat.push(consts::FREE_SECTOR);
        }
        fat
    }
}

impl<'a> Engine<'a> {
    // ------------------------------------------------------------------ //
    // FAT chain classification.
    // ------------------------------------------------------------------ //

    fn owner_label(info: &OwnerInfo) -> &str {
        &info.label
    }

    /// Records that a sector is in use by a chain.  Returns false when the
    /// sector already belongs to a different chain (a crossed chain), or to
    /// the same chain (a cycle).
    fn claim_fat_sector(
        owners: &mut Vec<Option<OwnerInfo>>,
        sid: u32,
        info: &OwnerInfo,
        local: &mut FnvHashSet<u32>,
        component: Component,
        location_prefix: &str,
        findings: &mut Vec<Corruption>,
    ) -> bool {
        if !local.insert(sid) {
            findings.push(Corruption {
                component,
                kind: CorruptionKind::Cycle,
                location: format!("{location_prefix}sector {sid}"),
                detail: "chain revisits one of its own sectors".to_string(),
            });
            return false;
        }
        if let Some(existing) = &owners[sid as usize] {
            findings.push(Corruption {
                component,
                kind: CorruptionKind::DoubleAllocation,
                location: format!("{location_prefix}sector {sid}"),
                detail: format!(
                    "sector {sid} is shared between {} and {}",
                    existing.label, info.label
                ),
            });
            return false;
        }
        owners[sid as usize] = Some(info.clone());
        true
    }

    /// Walks one regular FAT chain, returning the sectors reached in order
    /// and whether the walk terminated because of a structural fault.
    ///
    /// The five distinct failure modes are reported separately here: cycles
    /// and crossed chains via `claim_fat_sector`, out-of-bounds edges,
    /// reserved-value edges, and mid-chain FREE edges (a declared-length
    /// mismatch).
    fn walk_fat_chain(
        &mut self,
        fat: &[u32],
        owners: &mut Vec<Option<OwnerInfo>>,
        start: u32,
        info: OwnerInfo,
        component: Component,
    ) -> FatChain {
        let mut sids = Vec::new();
        if start == consts::END_OF_CHAIN || start == consts::FREE_SECTOR {
            return FatChain { sids, fault: false };
        }
        if start > consts::MAX_REGULAR_SECTOR || start as usize >= fat.len() {
            let mut findings = std::mem::take(&mut self.findings);
            findings.push(Corruption {
                component,
                kind: CorruptionKind::OutOfBounds,
                location: format!("{} start sector", info.label),
                detail: format!(
                    "chain starts at sector {start}, but FAT has {} entries",
                    fat.len()
                ),
            });
            self.findings = findings;
            self.unfixable.push(format!("{} start sector", info.label));
            return FatChain { sids, fault: true };
        }
        let mut local = FnvHashSet::default();
        let mut current = start;
        let mut fault = false;
        loop {
            let location_prefix = format!("{}: ", info.label);
            let mut claimed = false;
            {
                let mut findings = std::mem::take(&mut self.findings);
                claimed = Self::claim_fat_sector(
                    owners,
                    current,
                    &info,
                    &mut local,
                    component,
                    &location_prefix,
                    &mut findings,
                );
                self.findings = findings;
            }
            if !claimed {
                fault = true;
                break;
            }
            sids.push(current);
            let next = fat[current as usize];
            if next == consts::END_OF_CHAIN {
                break;
            } else if next == consts::FREE_SECTOR {
                self.add(
                    component,
                    CorruptionKind::DeclaredLengthMismatch,
                    format!("FAT[{current}]"),
                    format!(
                        "{} ends abruptly at sector {current}: FAT entry is \
                         FREE_SECTOR",
                        info.label
                    ),
                );
                if let Some(offset) = self.fat_entry_offset(self.fat_sectors, current as usize) {
                    self.edit_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!("terminate {} at sector {current}", info.label),
                    );
                }
                fault = true;
                break;
            } else if next == consts::INVALID_SECTOR
                || next == consts::DIFAT_SECTOR
                || next == consts::FAT_SECTOR
            {
                self.add(
                    component,
                    CorruptionKind::InvalidValue,
                    format!("FAT[{current}]"),
                    format!(
                        "{} follows a reserved FAT entry 0x{next:08X} at \
                         sector {current}",
                        info.label
                    ),
                );
                if let Some(offset) = self.fat_entry_offset(self.fat_sectors, current as usize) {
                    self.edit_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!("terminate {} at sector {current}", info.label),
                    );
                }
                fault = true;
                break;
            } else if next > consts::MAX_REGULAR_SECTOR
                || next as usize >= fat.len()
            {
                self.add(
                    component,
                    CorruptionKind::OutOfBounds,
                    format!("FAT[{current}]"),
                    format!(
                        "{} at sector {current} points to sector {next}, but \
                         FAT has {} entries",
                        info.label,
                        fat.len()
                    ),
                );
                if let Some(offset) = self.fat_entry_offset(self.fat_sectors, current as usize) {
                    self.edit_u32(
                        offset,
                        consts::END_OF_CHAIN,
                        format!("terminate {} at sector {current}", info.label),
                    );
                }
                fault = true;
                break;
            }
            if sids.len() > fat.len() {
                // Defensive bound; cycle detection normally stops first.
                fault = true;
                break;
            }
            current = next;
        }
        FatChain { sids, fault }
    }

    // ------------------------------------------------------------------ //
    // Orphan-sector sweep over the FAT.
    // ------------------------------------------------------------------ //

    /// After every legitimate chain has claimed its sectors, anything still
    /// marked with a regular FAT entry but claimed by nobody is orphaned.
    /// Contiguous orphan runs are reported as one finding, retaining the
    /// first sector ID as the first-offending position.
    fn sweep_fat_orphans(
        &mut self,
        fat: &[u32],
        owners: &[Option<OwnerInfo>],
    ) {
        let mut index = 0u32;
        while index < fat.len() as u32 {
            let entry = fat[index as usize];
            let unowned = owners[index as usize].is_none();
            let points_at_data =
                entry <= consts::MAX_REGULAR_SECTOR
                    && entry != consts::END_OF_CHAIN;
            let is_data_edge =
                entry == consts::END_OF_CHAIN || points_at_data;
            if !(unowned && is_data_edge) {
                index += 1;
                continue;
            }
            // Start of a contiguous orphan run; consume consecutive sectors.
            let start = index;
            let mut end = index;
            loop {
                let next = fat[end as usize];
                let regular =
                    next == consts::END_OF_CHAIN || next <= MAX_REGULAR_DATA;
                let last = next == consts::END_OF_CHAIN
                    || next as usize >= fat.len();
                if !regular {
                    break;
                }
                // Free this orphan's own entry.
                if let Some(offset) =
                    self.fat_entry_offset(self.fat_sectors, end as usize)
                {
                    self.edit_u32(
                        offset,
                        consts::FREE_SECTOR,
                        format!("mark orphan sector {end} as free"),
                    );
                }
                if last {
                    break;
                }
                let candidate = end + 1;
                if candidate as usize >= fat.len()
                    || owners[candidate as usize].is_some()
                {
                    break;
                }
                end = candidate;
            }
            let count = end - start + 1;
            self.add(
                Component::Fat,
                CorruptionKind::OrphanSector,
                format!("FAT sector {start}"),
                if count == 1 {
                    format!(
                        "sector {start} is marked allocated but is not \
                         reachable from any chain"
                    )
                } else {
                    format!(
                        "sectors {start}..={end} are marked allocated but are \
                         not reachable from any chain"
                    )
                },
            );
            index = end + 1;
        }
    }
}

const MAX_REGULAR_DATA: u32 = consts::MAX_REGULAR_SECTOR;
