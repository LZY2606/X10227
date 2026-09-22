// Public data model for the opt-in structural audit.

use std::fmt;

/// Which of the CFB allocation structures a [`Finding`] concerns.
///
/// The audit examines four structures independently:
///
/// - the **DIFAT**, which lists the sectors holding the FAT,
/// - the **FAT**, which chains regular sectors (the directory chain, the
///   MiniFAT chain, the mini stream chain, and every large stream chain),
/// - the **MiniFAT**, which chains 64-byte mini sectors inside the root
///   stream, and
/// - the **directory chain**, reached from the header's first-directory
///   sector field.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[non_exhaustive]
pub enum Table {
    /// The double-indirect FAT: the header DIFAT array plus DIFAT sectors.
    Difat,
    /// The file allocation table.
    Fat,
    /// The mini file allocation table.
    MiniFat,
    /// The directory entry chain.
    Directory,
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Table::Difat => f.write_str("DIFAT"),
            Table::Fat => f.write_str("FAT"),
            Table::MiniFat => f.write_str("MiniFAT"),
            Table::Directory => f.write_str("directory chain"),
        }
    }
}

/// The kind of corruption found.
///
/// These categories are reported separately, even when several appear in the
/// same chain:
///
/// - [`Cycle`](CorruptionKind::Cycle): following the links revisits an
///   earlier sector,
/// - [`OutOfBounds`](CorruptionKind::OutOfBounds): a link targets a sector
///   index outside the file or outside the table,
/// - [`DoubleOccupancy`](CorruptionKind::DoubleOccupancy): one sector is the
///   successor of two distinct predecessors, i.e. two chains cross or merge,
/// - [`OrphanSector`](CorruptionKind::OrphanSector): a regular sector is
///   neither free nor reachable from any legitimate chain root,
/// - [`DeclaredLengthMismatch`](CorruptionKind::DeclaredLengthMismatch): a
///   header field or a directory entry's declared stream length disagrees
///   with what the allocation tables provide,
/// - [`TruncatedChain`](CorruptionKind::TruncatedChain): a chain that must
///   end with an end-of-chain marker instead stops early (in particular, the
///   directory chain runs out of sectors before reaching it), and
/// - [`MalformedEntry`](CorruptionKind::MalformedEntry): a directory slot
///   cannot be parsed even under permissive rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[non_exhaustive]
pub enum CorruptionKind {
    /// Following the links revisits an earlier sector.
    Cycle,
    /// A link points outside the file or outside its table.
    OutOfBounds,
    /// A sector has more than one predecessor.
    DoubleOccupancy,
    /// A non-free sector is reachable from no legitimate chain.
    OrphanSector,
    /// A declared length/count disagrees with the actual tables.
    DeclaredLengthMismatch,
    /// A chain that needs an end-of-chain marker stops early.
    TruncatedChain,
    /// A directory slot is structurally malformed.
    MalformedEntry,
}

impl CorruptionKind {
    /// A short, stable, machine-readable identifier for the kind.
    pub fn code(self) -> &'static str {
        match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out_of_bounds",
            CorruptionKind::DoubleOccupancy => "double_occupancy",
            CorruptionKind::OrphanSector => "orphan_sector",
            CorruptionKind::DeclaredLengthMismatch => "length_mismatch",
            CorruptionKind::TruncatedChain => "truncated_chain",
            CorruptionKind::MalformedEntry => "malformed_entry",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DoubleOccupancy => "double occupancy",
            CorruptionKind::OrphanSector => "orphan sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared length mismatch"
            }
            CorruptionKind::TruncatedChain => "truncated chain",
            CorruptionKind::MalformedEntry => "malformed directory entry",
        })
    }
}

/// Where a [`Finding`] is located, with both the logical table location and
/// the first offending byte offset in the file.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FindingLocation {
    /// The table structure the offending link lives in.
    pub table: Table,
    /// Index of the table entry or chain sector that holds the bad link.
    ///
    /// For the FAT and MiniFAT this is the entry's sector ID; for the DIFAT
    /// it is the sector holding the bad DIFAT slot; for the directory chain
    /// it is the sector that failed to read.
    pub index: u32,
    /// For findings about a directory entry, the stream ID (directory slot)
    /// involved; otherwise `None`.
    pub stream_id: Option<u32>,
    /// First byte offset of the offending field within the file, when known.
    pub byte_offset: u64,
}

impl fmt::Display for FindingLocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} entry {}", self.table, self.index)?;
        if let Some(stream_id) = self.stream_id {
            write!(f, " (directory stream ID {stream_id})")?;
        }
        write!(f, " at byte {}", self.byte_offset)
    }
}

/// A single piece of corruption evidence.
///
/// A finding preserves the first offending location (including its byte
/// offset) and enough context to understand and display it, rather than
/// collapsing the whole audit to a boolean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// A stable, zero-based index within the sorted [`AuditReport`].
    pub id: usize,
    /// The corruption category.
    pub kind: CorruptionKind,
    /// The location of the first offending field.
    pub location: FindingLocation,
    /// The referenced sector/mini-sector/stream ID, when there is one.
    pub target: Option<u32>,
    /// Human-readable detail, including the relevant counts or IDs.
    pub detail: String,
}

impl Finding {
    /// A one-line `kind code @ byte offset` description of the finding.
    pub fn summary_line(&self) -> String {
        match self.target {
            Some(target) => format!(
                "{}: {} -> sector {} at byte {}",
                self.kind.code(),
                self.location,
                target,
                self.location.byte_offset
            ),
            None => format!(
                "{}: {} at byte {}",
                self.kind.code(),
                self.location,
                self.location.byte_offset
            ),
        }
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "#{} [{}] {}: {}",
            self.id,
            self.kind.code(),
            self.location,
            self.detail
        )
    }
}
