//! Opt-in, read-only structural auditing of Compound File Binary allocation
//! tables.
//!
//! Unlike the normal open path, which aims to make the file usable and
//! repairs tolerated spec violations in memory, the auditor never mutates its
//! input.  It walks the same on-disk structures (reusing the production
//! [`Header`] and [`DirEntry`] parsers) and records every corruption it finds
//! as a separate piece of [`CorruptionEvidence`], then produces a read-only
//! [`RepairPlan`] that can only be applied to a byte-for-byte identical input.

use std::collections::BTreeMap;
use std::fmt;
use std::io::{self, Read, Seek, SeekFrom};
use std::mem::size_of;

use crate::internal::sha256::Sha256;
use crate::internal::{
    consts, DirEntry, Header, ObjType, Validation, Version,
};

// ========================================================================= //

/// Which of the four on-disk allocation structures a piece of evidence is
/// about.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AuditTable {
    /// The File Allocation Table (sector chains).
    Fat,
    /// The Double-Indirect FAT (the chain of sectors listing FAT sectors).
    Difat,
    /// The Mini FAT (mini-sector chains inside the root stream).
    MiniFat,
    /// The directory sector chain and its entries.
    Directory,
}

impl fmt::Display for AuditTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            AuditTable::Fat => "FAT",
            AuditTable::Difat => "DIFAT",
            AuditTable::MiniFat => "MiniFAT",
            AuditTable::Directory => "directory chain",
        })
    }
}

/// The kind of structural problem found.  The five kinds are always reported
/// separately, so a caller can tell a cycle apart from an out-of-bounds
/// pointer, a sector claimed by two chains, an unreachable sector, and a
/// declared length that does not match the actual chain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CorruptionKind {
    /// Following a chain visits a sector it has already visited.
    ChainCycle,
    /// A table entry or chain pointer references an index beyond the file or
    /// beyond the table.
    ChainOutOfBounds,
    /// The same sector is reachable from more than one chain.
    DuplicateOwnership,
    /// A sector that is marked in use cannot be reached from any chain root.
    OrphanSector,
    /// A length or sector count declared in a header or directory entry does
    /// not match what the allocation tables actually provide.
    DeclaredLengthMismatch,
}

impl CorruptionKind {
    /// A short, stable identifier for the kind, useful in test names and
    /// machine-readable output.
    pub fn identifier(self) -> &'static str {
        match self {
            CorruptionKind::ChainCycle => "chain_cycle",
            CorruptionKind::ChainOutOfBounds => "chain_out_of_bounds",
            CorruptionKind::DuplicateOwnership => "duplicate_ownership",
            CorruptionKind::OrphanSector => "orphan_sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared_length_mismatch"
            }
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CorruptionKind::ChainCycle => "cycle in allocation chain",
            CorruptionKind::ChainOutOfBounds => "pointer out of bounds",
            CorruptionKind::DuplicateOwnership => "sector owned twice",
            CorruptionKind::OrphanSector => "orphan in-use sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared length does not match allocation"
            }
        })
    }
}

// ========================================================================= //

/// One structural corruption, with the table it belongs to, the precise kind,
/// the byte offset of the first offending on-disk field, and enough context
/// to understand it without reopening the file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorruptionEvidence {
    table: AuditTable,
    kind: CorruptionKind,
    offset: u64,
    detail: String,
    /// The concrete byte changes that resolve this finding.  Evidence is
    /// descriptive; the plan is built from these, so a finding and its repair
    /// can never disagree.
    repairs: Vec<Patch>,
}

impl CorruptionEvidence {
    /// The allocation table this corruption lives in.
    pub fn table(&self) -> AuditTable {
        self.table
    }

    /// What kind of corruption this is.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }

    /// Byte offset within the file of the first offending field.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// A human-readable description carrying the first violation position and
    /// the relevant sector or entry indices.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl fmt::Display for CorruptionEvidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at byte {} in {}: {}",
            self.kind, self.offset, self.table, self.detail
        )
    }
}

// ========================================================================= //

/// The result of a read-only structural audit: the exact bytes audited, a
/// precondition fingerprint of them, and every corruption found (in a stable,
/// deterministic order).
#[derive(Clone, Debug)]
pub struct AuditReport {
    input_len: u64,
    precondition: [u8; 32],
    evidence: Vec<CorruptionEvidence>,
}

impl AuditReport {
    /// Length in bytes of the audited input.
    pub fn input_len(&self) -> u64 {
        self.input_len
    }

    /// The SHA-256 digest of the exact input bytes this report was computed
    /// from.  A [`RepairPlan`] derived from this report can only be applied
    /// while the input still has this digest.
    pub fn precondition_digest(&self) -> [u8; 32] {
        self.precondition
    }

    /// All corruptions found, in deterministic scan order.
    pub fn evidence(&self) -> &[CorruptionEvidence] {
        &self.evidence
    }

    /// True if the allocation structures are internally consistent.
    pub fn is_clean(&self) -> bool {
        self.evidence.is_empty()
    }

    /// Builds a read-only repair plan describing how the corruptions would be
    /// repaired.  Building the plan writes nothing; applying it is a separate,
    /// explicit step and is only accepted if the input digest still matches.
    pub fn plan(&self) -> RepairPlan {
        // Multiple findings may agree on the same field (e.g. two views of one
        // broken edge); merge by offset, keeping the first action and
        // dropping a later action that would write a different value.
        let mut merged: BTreeMap<u64, [u8; 4]> = BTreeMap::new();
        for finding in self.evidence.iter() {
            for patch in finding.repairs.iter() {
                merged.entry(patch.offset).or_insert(patch.bytes);
            }
        }
        RepairPlan {
            input_len: self.input_len,
            precondition: self.precondition,
            patches: merged
                .into_iter()
                .map(|(offset, bytes)| Patch { offset, bytes })
                .collect(),
        }
    }
}

// ========================================================================= //

/// A single 4-byte replacement at an absolute file offset.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Patch {
    offset: u64,
    bytes: [u8; 4],
}

/// A read-only repair plan.  It carries the precondition digest of the bytes
/// it was computed from; it can be applied only to input with that digest,
/// and applying it never modifies the input, instead producing repaired
/// bytes.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    input_len: u64,
    precondition: [u8; 32],
    patches: Vec<Patch>,
}

impl RepairPlan {
    /// The digest the input must still have for this plan to apply.
    pub fn precondition_digest(&self) -> [u8; 32] {
        self.precondition
    }

    /// The number of 4-byte fields the plan would change.
    pub fn num_changes(&self) -> usize {
        self.patches.len()
    }

    /// The file offsets the plan would write to, in ascending order.
    pub fn changed_offsets(&self) -> Vec<u64> {
        self.patches.iter().map(|patch| patch.offset).collect()
    }

    /// Applies the plan to `input`, returning freshly allocated repaired
    /// bytes.  The input slice is never modified.  If its digest no longer
    /// matches the precondition (the file changed after the plan was made),
    /// or any planned field moved, this fails atomically with
    /// [`io::ErrorKind::InvalidData`] and returns no partial result.
    pub fn apply_to_bytes(&self, input: &[u8]) -> io::Result<Vec<u8>> {
        let mut hasher = Sha256::default();
        hasher.update(input);
        if hasher.finish() != self.precondition || input.len() as u64
            != self.input_len
        {
            invalid_data!(
                "Cannot apply repair plan: the input changed since the plan \
                 was made (precondition digest no longer matches)"
            );
        }
        let mut repaired = input.to_vec();
        for patch in self.patches.iter() {
            let start = patch.offset as usize;
            if start + 4 > input.len() {
                invalid_data!(
                    "Cannot apply repair plan: planned offset {} is beyond \
                     the {} input bytes",
                    patch.offset,
                    input.len()
                );
            }
            repaired[start..start + 4].copy_from_slice(&patch.bytes);
        }
        Ok(repaired)
    }
}

// ========================================================================= //

/// Byte offset of the "next DIFAT sector" pointer at the end of DIFAT sector
/// `sector`.  The pointer is what closes a cycle, so it is the first
/// violating site for a DIFAT cycle.
fn difat_next_pointer_offset(sector: u32, sector_len: u64) -> u64 {
    (sector as u64 + 1) * sector_len + sector_len - 4
}

/// Special values returned for a table entry in `audit_entry`, mirroring the
/// FAT entry encoding.
enum EntryKind {
    Regular(u32),
    Free,
    EndOfChain,
    Fat,
    Difat,
    Invalid,
}

fn classify_entry(entry: u32) -> EntryKind {
    match entry {
        consts::FREE_SECTOR => EntryKind::Free,
        consts::END_OF_CHAIN => EntryKind::EndOfChain,
        consts::FAT_SECTOR => EntryKind::Fat,
        consts::DIFAT_SECTOR => EntryKind::Difat,
        consts::INVALID_SECTOR => EntryKind::Invalid,
        other if other > consts::MAX_REGULAR_SECTOR => EntryKind::Invalid,
        other => EntryKind::Regular(other),
    }
}

/// All the mutable state of one audit.  Everything is local: two audits on
/// the same input share no cache, counter, or temporary data.
struct Auditor {
    version: Version,
    sector_len: usize,
    /// The exact bytes of the file.
    data: Vec<u8>,
    num_sectors: u32,
    /// FAT entries exactly as read from the FAT sectors (never repaired in
    /// place, unlike the open path).
    fat: Vec<u32>,
    /// Sector IDs listed by the DIFAT as FAT sectors, in order, duplicates
    /// and out-of-range values included.
    difat_fat_sectors: Vec<u32>,
    /// Byte offset of each FAT entry that was successfully read.
    fat_offsets: Vec<u64>,
    /// Which sectors the DIFAT chain itself used (in order).
    difat_chain_sectors: Vec<u32>,
    findings: Vec<CorruptionEvidence>,
    /// Sectors reserved for FAT/DIFAT use.
    role_sectors: std::collections::BTreeSet<u32>,
    /// Sectors reached by walking FAT chains from real roots.
    fat_owned: std::collections::BTreeSet<u32>,
    /// Parsed directory entries: file offset and (if parseable) the entry.
    dir_entries: Vec<(u64, Option<DirEntry>)>,
    /// Sectors used by the directory chain, in order.
    dir_chain: Vec<u32>,
    /// MiniFAT entries (file offset, value), in order.
    minifat: Vec<(u64, u32)>,
    /// Mini sectors reached from mini-chain roots.
    mini_owned: std::collections::BTreeSet<u32>,
}

impl Auditor {
    fn u32_at(&self, offset: u64) -> Option<u32> {
        let start = offset as usize;
        let bytes = self.data.get(start..start + 4)?;
        Some(u32::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3],
        ]))
    }

    fn header_field_offset(header_field: u64) -> u64 {
        header_field
    }

    fn report(
        &mut self,
        table: AuditTable,
        kind: CorruptionKind,
        offset: u64,
        detail: String,
        repairs: Vec<Patch>,
    ) {
        self.findings.push(CorruptionEvidence {
            table,
            kind,
            offset,
            detail,
            repairs,
        });
    }

    /// Convenience for findings repaired by writing one 4-byte field.
    fn report_one(
        &mut self,
        table: AuditTable,
        kind: CorruptionKind,
        offset: u64,
        detail: String,
        value: u32,
    ) {
        self.report(
            table,
            kind,
            offset,
            detail,
            vec![Patch { offset, bytes: value.to_le_bytes() }],
        );
    }

    fn end_of_chain_patch(&self, offset: u64) -> Patch {
        Patch { offset, bytes: consts::END_OF_CHAIN.to_le_bytes() }
    }

    fn free_patch(&self, offset: u64) -> Patch {
        Patch { offset, bytes: consts::FREE_SECTOR.to_le_bytes() }
    }

    fn fat_offset(&self, sector_id: u32) -> Option<u64> {
        self.fat_offsets.get(sector_id as usize).copied()
    }

    // ----- DIFAT and FAT ------------------------------------------------- //

    fn read_difat_and_fat(&mut self, header: &Header) {
        let sector_len = self.sector_len as u64;
        // Walk the DIFAT sector chain, as open_internal does, but record
        // cycles and out-of-bounds pointers instead of aborting.
        let mut raw_difat: Vec<u32> =
            header.initial_difat_entries.to_vec();
        let mut seen = std::collections::BTreeSet::new();
        let mut current = header.first_difat_sector;
        while current != consts::END_OF_CHAIN
            && current != consts::FREE_SECTOR
        {
            let offset = difat_next_pointer_offset(current, sector_len);
            if current > consts::MAX_REGULAR_SECTOR || current >= self.num_sectors
            {
                self.report(
                    AuditTable::Difat,
                    CorruptionKind::ChainOutOfBounds,
                    offset,
                    format!(
                        "DIFAT chain points to sector {}, but the file has \
                         only {} sectors",
                        current, self.num_sectors
                    ),
                    vec![],
                );
                break;
            }
            if !seen.insert(current) {
                self.report(
                    AuditTable::Difat,
                    CorruptionKind::ChainCycle,
                    offset,
                    format!(
                        "DIFAT chain revisits sector {} instead of \
                         terminating",
                        current
                    ),
                    vec![Patch {
                        offset,
                        bytes: consts::END_OF_CHAIN.to_le_bytes(),
                    }],
                );
                break;
            }
            self.difat_chain_sectors.push(current);
            let sector_start = (current as u64 + 1) * sector_len;
            let entries_per_sector = self.sector_len / size_of::<u32>();
            for index in 0..entries_per_sector - 1 {
                let entry_offset =
                    sector_start + (index as u64) * 4;
                let Some(entry) = self.u32_at(entry_offset) else {
                    self.report(
                        AuditTable::Difat,
                        CorruptionKind::ChainOutOfBounds,
                        entry_offset,
                        format!(
                            "DIFAT sector {} runs past the end of the file",
                            current
                        ),
                        vec![],
                    );
                    break;
                };
                raw_difat.push(entry);
            }
            let next_offset = sector_start + sector_len - 4;
            current = match self.u32_at(next_offset) {
                Some(value) => value,
                None => {
                    self.report(
                        AuditTable::Difat,
                        CorruptionKind::ChainOutOfBounds,
                        next_offset,
                        format!(
                            "DIFAT sector {} has no next-chain pointer",
                            current
                        ),
                        vec![],
                    );
                    break;
                }
            };
        }
        if header.num_difat_sectors as usize != self.difat_chain_sectors.len()
        {
            self.report_one(
                AuditTable::Difat,
                CorruptionKind::DeclaredLengthMismatch,
                72,
                format!(
                    "header declares {} DIFAT sectors, but the DIFAT chain \
                     actually uses {}",
                    header.num_difat_sectors,
                    self.difat_chain_sectors.len()
                ),
                self.difat_chain_sectors.len() as u32,
            );
        }

        // Tolerate the same zero/FREE padding the open path tolerates, so a
        // file that opens fine is not flagged spuriously.
        while raw_difat.len()
            > consts::NUM_DIFAT_ENTRIES_IN_HEADER
            && raw_difat.len() > header.num_fat_sectors as usize
            && *raw_difat.last().unwrap() == 0
        {
            raw_difat.pop();
        }
        while raw_difat.last() == Some(&consts::FREE_SECTOR) {
            raw_difat.pop();
        }
        if header.num_fat_sectors as usize != raw_difat.len() {
            self.report_one(
                AuditTable::Difat,
                CorruptionKind::DeclaredLengthMismatch,
                44,
                format!(
                    "header declares {} FAT sectors, but the DIFAT lists {}",
                    header.num_fat_sectors,
                    raw_difat.len()
                ),
                raw_difat.len() as u32,
            );
        }

        // Read each listed FAT sector, recording exactly where each FAT entry
        // came from in the file.
        let entries_per_sector = self.sector_len / size_of::<u32>();
        for fat_sector in raw_difat.into_iter() {
            if fat_sector == consts::FREE_SECTOR {
                continue;
            }
            if fat_sector > consts::MAX_REGULAR_SECTOR
                || fat_sector >= self.num_sectors
            {
                let offset = self
                    .fat_offsets
                    .last()
                    .copied()
                    .unwrap_or(consts::HEADER_LEN as u64);
                self.report(
                    AuditTable::Difat,
                    CorruptionKind::ChainOutOfBounds,
                    offset,
                    format!(
                        "DIFAT lists FAT sector {}, but the file has only {} \
                         sectors",
                        fat_sector, self.num_sectors
                    ),
                    vec![],
                );
                continue;
            }
            self.difat_fat_sectors.push(fat_sector);
            let sector_start = (fat_sector as u64 + 1) * sector_len;
            for index in 0..entries_per_sector {
                let entry_offset = sector_start + (index as u64) * 4;
                match self.u32_at(entry_offset) {
                    Some(entry) => {
                        self.fat.push(entry);
                        self.fat_offsets.push(entry_offset);
                    }
                    None => break,
                }
            }
        }
        if (self.fat.len() as u32) > self.num_sectors {
            // Point at the first FAT entry beyond the file's sector count.
            let offending_offset =
                self.fat_offsets[self.num_sectors as usize];
            self.report(
                AuditTable::Fat,
                CorruptionKind::DeclaredLengthMismatch,
                offending_offset,
                format!(
                    "FAT has {} entries, but the file contains only {} \
                     sectors",
                    self.fat.len(),
                    self.num_sectors
                ),
                vec![],
            );
        }
    }

    /// FAT entry at `sector_id`, or `None` if the FAT itself does not cover
    /// that sector.
    fn fat_entry(&self, sector_id: u32) -> Option<u32> {
        self.fat.get(sector_id as usize).copied()
    }

    fn scan_fat_static(&mut self) {
        // Role sectors (the FAT sectors listed by the DIFAT and the sectors
        // of the DIFAT chain itself) are pre-owned by the tables, so a data
        // chain that runs into one is reported as duplicate ownership rather
        // than as a reachable sector.  All other FAT-level classification is
        // done by walking chains from their roots and by the orphan pass, so
        // every corrupt sector is reported exactly once with a single kind.
        for &sector_id in self.difat_fat_sectors.iter() {
            if sector_id < self.num_sectors {
                self.role_sectors.insert(sector_id);
            }
        }
        for &sector_id in self.difat_chain_sectors.iter() {
            self.role_sectors.insert(sector_id);
        }
    }

    /// Follows one FAT chain from `root`, recording cycles, pointers out of
    /// range, and sectors already owned by another chain.  `owner` labels the
    /// root in messages.  Returns the sectors reached (without repeats).
    fn walk_fat_chain(
        &mut self,
        root: u32,
        table: AuditTable,
        owner: &str,
    ) -> Vec<u32> {
        let mut reached = Vec::new();
        if root == consts::END_OF_CHAIN || root == consts::FREE_SECTOR {
            return reached;
        }
        if root > consts::MAX_REGULAR_SECTOR
            || root >= self.num_sectors
            || (root as usize) >= self.fat.len()
        {
            let offset = self.fat_offset(root).unwrap_or(0);
            self.report(
                table,
                CorruptionKind::ChainOutOfBounds,
                offset,
                format!(
                    "{} starts at sector 0x{:08X}, beyond the {} sectors in \
                     the file",
                    owner, root, self.num_sectors
                ),
                vec![],
            );
            return reached;
        }
        let mut current = root;
        let mut in_chain = std::collections::BTreeSet::new();
        loop {
            reached.push(current);
            in_chain.insert(current);
            self.fat_owned.insert(current);
            let edge_offset = self.fat_offset(current).unwrap_or(0);
            let Some(entry) = self.fat_entry(current) else {
                self.report(
                    table,
                    CorruptionKind::ChainOutOfBounds,
                    edge_offset,
                    format!(
                        "FAT has no entry for sector {} while walking {}",
                        current, owner
                    ),
                    vec![],
                );
                return reached;
            };
            let next = match classify_entry(entry) {
                EntryKind::EndOfChain => return reached,
                EntryKind::Free => {
                    self.report_one(
                        table,
                        CorruptionKind::ChainOutOfBounds,
                        edge_offset,
                        format!(
                            "{} ends in a FREE-sector marker at sector {} \
                             instead of END_OF_CHAIN",
                            owner, current
                        ),
                        consts::END_OF_CHAIN,
                    );
                    return reached;
                }
                EntryKind::Fat | EntryKind::Difat => {
                    self.report_one(
                        table,
                        CorruptionKind::DuplicateOwnership,
                        edge_offset,
                        format!(
                            "{} runs into table-reserved sector {} (FAT entry \
                             0x{:08X})",
                            owner, current, entry
                        ),
                        consts::END_OF_CHAIN,
                    );
                    return reached;
                }
                EntryKind::Invalid => {
                    self.report_one(
                        table,
                        CorruptionKind::ChainOutOfBounds,
                        edge_offset,
                        format!(
                            "{} hits reserved invalid FAT entry 0x{:08X} at \
                             sector {}",
                            owner, entry, current
                        ),
                        consts::END_OF_CHAIN,
                    );
                    return reached;
                }
                EntryKind::Regular(next) => next,
            };
            if next >= self.num_sectors || (next as usize) >= self.fat.len() {
                self.report_one(
                    table,
                    CorruptionKind::ChainOutOfBounds,
                    edge_offset,
                    format!(
                        "{}: sector {} points to {}, beyond the {} sectors in \
                         the file",
                        owner, current, next, self.num_sectors
                    ),
                    consts::END_OF_CHAIN,
                );
                return reached;
            }
            if in_chain.contains(&next) {
                self.report_one(
                    table,
                    CorruptionKind::ChainCycle,
                    edge_offset,
                    format!(
                        "{} loops back to sector {} (chain so far: {:?})",
                        owner, next, reached
                    ),
                    consts::END_OF_CHAIN,
                );
                return reached;
            }
            if self.fat_owned.contains(&next)
                && !self.role_sectors.contains(&next)
            {
                self.report_one(
                    table,
                    CorruptionKind::DuplicateOwnership,
                    edge_offset,
                    format!(
                        "{} crosses into sector {}, already claimed by \
                         another chain",
                        owner, next
                    ),
                    consts::END_OF_CHAIN,
                );
                return reached;
            }
            current = next;
        }
    }

    fn scan_fat_orphans(&mut self) {
        let limit = self.fat.len().min(self.num_sectors as usize);
        for sector_id in 0..limit as u32 {
            let entry = self.fat[sector_id as usize];
            if matches!(classify_entry(entry), EntryKind::Free) {
                continue;
            }
            if self.role_sectors.contains(&sector_id)
                || self.fat_owned.contains(&sector_id)
            {
                continue;
            }
            let offset = self.fat_offset(sector_id).unwrap_or(0);
            self.report_one(
                AuditTable::Fat,
                CorruptionKind::OrphanSector,
                offset,
                format!(
                    "sector {} is marked in use (FAT entry 0x{:08X}) but no \
                     allocation chain reaches it",
                    sector_id, entry
                ),
                consts::FREE_SECTOR,
            );
        }
    }

    // ----- Directory chain and entries ----------------------------------- //

    fn scan_directory(&mut self, header: &Header) {
        self.dir_chain = self.walk_fat_chain(
            header.first_dir_sector,
            AuditTable::Directory,
            "directory chain",
        );
        if self.version == Version::V4
            && header.num_dir_sectors as usize != self.dir_chain.len()
        {
            self.report_one(
                AuditTable::Directory,
                CorruptionKind::DeclaredLengthMismatch,
                40,
                format!(
                    "header declares {} directory sectors, but the directory \
                     chain uses {}",
                    header.num_dir_sectors,
                    self.dir_chain.len()
                ),
                self.dir_chain.len() as u32,
            );
        }
        let entries_per_sector = self.version.dir_entries_per_sector();
        let sector_len = self.sector_len as u64;
        for &sector_id in self.dir_chain.iter() {
            for slot in 0..entries_per_sector {
                let entry_offset = (sector_id as u64 + 1) * sector_len
                    + (slot as u64) * consts::DIR_ENTRY_LEN as u64;
                let parsed = self
                    .data
                    .get(entry_offset as usize
                        ..entry_offset as usize
                            + consts::DIR_ENTRY_LEN)
                    .and_then(|bytes| {
                        DirEntry::read_from(
                            &mut &bytes[..],
                            self.version,
                            Validation::Permissive,
                        )
                        .ok()
                    });
                self.dir_entries.push((entry_offset, parsed));
            }
        }
    }

    fn entry_name(entry: &DirEntry) -> String {
        if entry.name.is_empty() {
            "<unnamed>".to_string()
        } else {
            format!("{:?}", entry.name)
        }
    }

    // ----- MiniFAT ------------------------------------------------------- //

    fn scan_minifat(&mut self, header: &Header) {
        // Read the MiniFAT chain sectors from the FAT.
        let minifat_sectors = self.walk_fat_chain(
            header.first_minifat_sector,
            AuditTable::MiniFat,
            "MiniFAT chain",
        );
        if header.first_minifat_sector != consts::END_OF_CHAIN
            && header.num_minifat_sectors as usize
                != minifat_sectors.len()
        {
            self.report_one(
                AuditTable::MiniFat,
                CorruptionKind::DeclaredLengthMismatch,
                60,
                format!(
                    "header declares {} MiniFAT sectors, but the MiniFAT \
                     chain uses {}",
                    header.num_minifat_sectors,
                    minifat_sectors.len()
                ),
                minifat_sectors.len() as u32,
            );
        }
        let sector_len = self.sector_len as u64;
        for sector_id in minifat_sectors {
            let sector_start = (sector_id as u64 + 1) * sector_len;
            for slot in 0..(self.sector_len / size_of::<u32>()) {
                let entry_offset =
                    sector_start + (slot as u64) * 4;
                if let Some(entry) = self.u32_at(entry_offset) {
                    self.minifat.push((entry_offset, entry));
                }
            }
        }
        // Static check: reserved invalid values.
        for &(offset, entry) in self.minifat.iter() {
            if entry == consts::INVALID_SECTOR
                || (entry > consts::MAX_REGULAR_SECTOR
                    && entry != consts::FREE_SECTOR
                    && entry != consts::END_OF_CHAIN)
            {
                self.report_one(
                    AuditTable::MiniFat,
                    CorruptionKind::ChainOutOfBounds,
                    offset,
                    format!(
                        "MiniFAT entry is the reserved value 0x{:08X}",
                        entry
                    ),
                    consts::END_OF_CHAIN,
                );
            }
        }
    }

    fn mini_entry(&self, mini_sector: u32) -> Option<(u64, u32)> {
        self.minifat.get(mini_sector as usize).copied()
    }

    fn walk_mini_chain(
        &mut self,
        root: u32,
        owner: &str,
        start_field_offset: u64,
        length_field_offset: u64,
        declared_len: u64,
    ) {
        if root == consts::END_OF_CHAIN || root == consts::FREE_SECTOR {
            return;
        }
        if root > consts::MAX_REGULAR_SECTOR
            || (root as usize) >= self.minifat.len()
        {
            self.report(
                AuditTable::MiniFat,
                CorruptionKind::ChainOutOfBounds,
                length_field_offset - 8,
                format!(
                    "{} starts at mini sector 0x{:08X}, beyond the {} MiniFAT \
                     entries",
                    owner, root, self.minifat.len()
                ),
                vec![],
            );
            return;
        }
        let mut reached = Vec::new();
        let mut current = root;
        let mut in_chain = std::collections::BTreeSet::new();
        loop {
            reached.push(current);
            in_chain.insert(current);
            self.mini_owned.insert(current);
            let Some((edge_offset, entry)) = self.mini_entry(current) else {
                self.report(
                    AuditTable::MiniFat,
                    CorruptionKind::ChainOutOfBounds,
                    start_field_offset,
                    format!(
                        "MiniFAT has no entry for mini sector {} of {}",
                        current, owner
                    ),
                    vec![],
                );
                break;
            };
            let next = match classify_entry(entry) {
                EntryKind::EndOfChain => break,
                EntryKind::Free => {
                    self.report_one(
                        AuditTable::MiniFat,
                        CorruptionKind::ChainOutOfBounds,
                        edge_offset,
                        format!(
                            "{} ends in a FREE mini-sector marker at {} \
                             instead of END_OF_CHAIN",
                            owner, current
                        ),
                        consts::END_OF_CHAIN,
                    );
                    break;
                }
                EntryKind::Invalid => {
                    self.report_one(
                        AuditTable::MiniFat,
                        CorruptionKind::ChainOutOfBounds,
                        edge_offset,
                        format!(
                            "{} hits reserved MiniFAT entry 0x{:08X} at mini \
                             sector {}",
                            owner, entry, current
                        ),
                        consts::END_OF_CHAIN,
                    );
                    break;
                }
                EntryKind::Fat | EntryKind::Difat => {
                    self.report_one(
                        AuditTable::MiniFat,
                        CorruptionKind::ChainOutOfBounds,
                        edge_offset,
                        format!(
                            "{} hits a regular-FAT sentinel (0x{:08X}) in the                              MiniFAT at mini sector {}",
                            owner, entry, current
                        ),
                        consts::END_OF_CHAIN,
                    );
                    break;
                }
                EntryKind::Regular(next) => next,
            };
            if (next as usize) >= self.minifat.len() {
                self.report_one(
                    AuditTable::MiniFat,
                    CorruptionKind::ChainOutOfBounds,
                    edge_offset,
                    format!(
                        "{}: mini sector {} points to {}, beyond the {} \
                         MiniFAT entries",
                        owner, current, next, self.minifat.len()
                    ),
                    consts::END_OF_CHAIN,
                );
                break;
            }
            if in_chain.contains(&next) {
                self.report_one(
                    AuditTable::MiniFat,
                    CorruptionKind::ChainCycle,
                    edge_offset,
                    format!(
                        "{} mini chain loops back to mini sector {} (chain so \
                         far: {:?})",
                        owner, next, reached
                    ),
                    consts::END_OF_CHAIN,
                );
                break;
            }
            if self.mini_owned.contains(&next) {
                self.report_one(
                    AuditTable::MiniFat,
                    CorruptionKind::DuplicateOwnership,
                    edge_offset,
                    format!(
                        "{} mini chain crosses into mini sector {}, already \
                         claimed by another mini chain",
                        owner, next
                    ),
                    consts::END_OF_CHAIN,
                );
                break;
            }
            current = next;
        }
        self.check_declared_mini_length(
            owner,
            &reached,
            declared_len,
            length_field_offset,
        );
    }

    /// A declared stream length must fit inside the mini sectors its chain
    /// actually provides.
    fn check_declared_mini_length(
        &mut self,
        owner: &str,
        reached: &[u32],
        declared_len: u64,
        length_field_offset: u64,
    ) {
        let capacity =
            (reached.len() as u64) * consts::MINI_SECTOR_LEN as u64;
        if declared_len > capacity {
            let clamped = capacity;
            self.report_one(
                AuditTable::MiniFat,
                CorruptionKind::DeclaredLengthMismatch,
                length_field_offset,
                format!(
                    "{} declares {} bytes, but its mini chain provides only \
                     {} bytes across {} mini sector(s)",
                    owner, declared_len, capacity, reached.len()
                ),
                clamped as u32,
            );
        }
    }

    fn scan_mini_orphans(&mut self) {
        for (index, (offset, entry)) in self.minifat.iter().enumerate() {
            if matches!(classify_entry(*entry), EntryKind::Free) {
                continue;
            }
            if self.mini_owned.contains(&(index as u32)) {
                continue;
            }
            self.report_one(
                AuditTable::MiniFat,
                CorruptionKind::OrphanSector,
                *offset,
                format!(
                    "mini sector {} is marked in use (MiniFAT entry \
                     0x{:08X}) but no mini chain reaches it",
                    index, entry
                ),
                consts::FREE_SECTOR,
            );
        }
    }

    // ----- Orchestration ------------------------------------------------- //

    fn run(mut self, header: &Header) -> AuditReport {
        self.read_difat_and_fat(header);
        self.scan_fat_static();
        self.scan_directory(header);
        self.scan_minifat(header);

        // The directory entries are available now; derive all remaining
        // chain roots in a fixed order so output is stable.
        let mut root_entry: Option<(u64, DirEntry)> = None;
        let mut streams: Vec<(u64, DirEntry)> = Vec::new();
        for (offset, parsed) in self.dir_entries.iter() {
            let Some(entry) = parsed else { continue };
            match entry.obj_type {
                ObjType::Root => root_entry = Some((*offset, entry.clone())),
                ObjType::Stream => streams.push((*offset, entry.clone())),
                _ => {}
            }
        }
        let root_offset;
        let root_start;
        let root_len;
        match root_entry {
            Some((offset, entry)) => {
                root_offset = offset;
                root_start = entry.start_sector;
                root_len = entry.stream_len;
            }
            None => {
                // No parseable root entry: the directory chain finding (if
                // any) already describes why; nothing else to anchor.
                self.scan_fat_orphans();
                self.scan_mini_orphans();
                return self.finish();
            }
        }

        // Root stream (container of the mini stream) lives on a regular FAT
        // chain.  Its length must be a multiple of 64 and match the chain.
        let mini_stream_sectors =
            self.walk_fat_chain(root_start, AuditTable::Directory, "root stream");
        if root_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            let clamped = root_len - (root_len % consts::MINI_SECTOR_LEN as u64);
            self.report_one(
                AuditTable::MiniFat,
                CorruptionKind::DeclaredLengthMismatch,
                root_offset + 120,
                format!(
                    "root stream length {} is not a multiple of the {} byte \
                     mini sector size",
                    root_len, consts::MINI_SECTOR_LEN
                ),
                clamped as u32,
            );
        }
        let mini_stream_capacity =
            (mini_stream_sectors.len() as u64) * self.sector_len as u64;
        if root_len > mini_stream_capacity {
            self.report_one(
                AuditTable::MiniFat,
                CorruptionKind::DeclaredLengthMismatch,
                root_offset + 120,
                format!(
                    "root stream declares {} bytes, but its FAT chain holds \
                     only {} bytes across {} sector(s)",
                    root_len,
                    mini_stream_capacity,
                    mini_stream_sectors.len()
                ),
                mini_stream_capacity as u32,
            );
        }
        // The MiniFAT must not describe more mini sectors than the root
        // stream actually provides.
        let mini_sectors_available =
            root_len / consts::MINI_SECTOR_LEN as u64;
        if (self.minifat.len() as u64) > mini_sectors_available {
            if let Some((offset, _)) = self
                .minifat
                .get(mini_sectors_available as usize)
            {
                self.report_one(
                    AuditTable::MiniFat,
                    CorruptionKind::DeclaredLengthMismatch,
                    *offset,
                    format!(
                        "MiniFAT has {} entries, but the {} byte root stream \
                         provides only {} mini sector slots",
                        self.minifat.len(),
                        root_len,
                        mini_sectors_available
                    ),
                    self.minifat.len() as u32,
                );
            }
        }

        // Every stream entry anchors either a FAT chain (>= cutoff) or a mini
        // chain (smaller), in directory order.
        for (entry_offset, entry) in streams.iter() {
            let name = Self::entry_name(entry);
            let start_field_offset = entry_offset + 116;
            let length_field_offset = entry_offset + 120;
            let declared_len = entry.stream_len & self.version.stream_len_mask();
            if declared_len >= consts::MINI_STREAM_CUTOFF as u64 {
                let reached = self.walk_fat_chain(
                    entry.start_sector,
                    AuditTable::Fat,
                    &format!("stream {}", name),
                );
                let capacity =
                    (reached.len() as u64) * self.sector_len as u64;
                if declared_len > capacity {
                    self.report_one(
                        AuditTable::Fat,
                        CorruptionKind::DeclaredLengthMismatch,
                        length_field_offset,
                        format!(
                            "stream {} declares {} bytes, but its FAT chain \
                             holds only {} bytes across {} sector(s)",
                            name, declared_len, capacity, reached.len()
                        ),
                        capacity as u32,
                    );
                }
            } else {
                self.walk_mini_chain(
                    entry.start_sector,
                    &format!("stream {}", name),
                    start_field_offset,
                    length_field_offset,
                    declared_len,
                );
            }
        }

        self.scan_fat_orphans();
        self.scan_mini_orphans();
        self.finish()
    }

    fn finish(self) -> AuditReport {
        let Auditor {
            data,
            findings,
            ..
        } = self;
        let mut hasher = Sha256::default();
        hasher.update(&data);
        AuditReport {
            input_len: data.len() as u64,
            precondition: hasher.finish(),
            evidence: findings,
        }
    }
}

// ========================================================================= //

/// Audits the bytes of an already-loaded compound file.  The bytes are read
/// but never modified; see [`audit_with`] for the streaming entry point.
pub fn audit_bytes(data: &[u8]) -> io::Result<AuditReport> {
    if (data.len() as u64) < consts::HEADER_LEN as u64 {
        invalid_data!(
            "Invalid CFB file ({} bytes is too small)",
            data.len()
        );
    }
    let mut cursor = std::io::Cursor::new(data);
    let header = Header::read_from(&mut cursor, Validation::Permissive)?;
    let sector_len = header.version.sector_len();
    let inner_len = data.len() as u64;
    if inner_len < sector_len as u64 {
        invalid_data!(
            "Invalid CFB file (length of {} < sector length of {})",
            inner_len,
            sector_len
        );
    }
    let num_sectors =
        (inner_len / sector_len as u64).saturating_sub(1) as u32;
    let auditor = Auditor {
        version: header.version,
        sector_len,
        data: data.to_vec(),
        num_sectors,
        fat: Vec::new(),
        difat_fat_sectors: Vec::new(),
        fat_offsets: Vec::new(),
        difat_chain_sectors: Vec::new(),
        findings: Vec::new(),
        role_sectors: std::collections::BTreeSet::new(),
        fat_owned: std::collections::BTreeSet::new(),
        dir_entries: Vec::new(),
        dir_chain: Vec::new(),
        minifat: Vec::new(),
        mini_owned: std::collections::BTreeSet::new(),
    };
    Ok(auditor.run(&header))
}

/// Audits a compound file from a readable, seekable source without opening it
/// for mutation and without writing anything back.  The reader is consumed
/// only for reading: no bytes are ever written through it.
pub fn audit_with<F: Read + Seek>(mut inner: F) -> io::Result<AuditReport> {
    let inner_len = inner.seek(SeekFrom::End(0))?;
    inner.seek(SeekFrom::Start(0))?;
    if inner_len > (consts::MAX_REGULAR_SECTOR as u64 + 1) * 4096 {
        invalid_data!("Invalid CFB file ({} bytes is too large)", inner_len);
    }
    let mut data = Vec::with_capacity(inner_len as usize);
    // Read in bounded chunks so that a reader that fails partway through (for
    // example an injected, recoverable I/O error) fails the audit before any
    // analysis was done and leaves nothing cached: a retry starts fresh.
    let mut remaining = inner_len;
    let mut chunk = vec![0u8; 4096];
    while remaining > 0 {
        let take = std::cmp::min(remaining as usize, chunk.len());
        inner.read_exact(&mut chunk[..take])?;
        data.extend_from_slice(&chunk[..take]);
        remaining -= take as u64;
    }
    audit_bytes(&data)
}

// ========================================================================= //
