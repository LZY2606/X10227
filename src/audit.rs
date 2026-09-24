//! Opt-in structural auditing of Compound File Binary (CFB) files.
//!
//! Unlike the normal open path, which parses a file eagerly and returns an
//! error at the *first* structural problem it encounters,
//! [`audit`] reads a compound file in one pass, never writes to it, and
//! collects a separate [`CorruptionFinding`] for every problem it can
//! diagnose across the four allocation structures: the FAT, the DIFAT, the
//! MiniFAT, and the directory chain.
//!
//! The audit returns a read-only [`RepairPlan`].  A plan records an
//! [`AuditDigest`] of the exact input bytes it was computed from;
//! [`RepairPlan::apply`] recomputes that digest first and refuses to write
//! anything when the input has changed.  [`RepairPlan::check`] performs the
//! same precondition checks without writing a single byte.
//!
//! # Reuse of the production parser
//!
//! The audit deliberately does not duplicate the format parser.  It parses
//! headers with [`crate::internal::Header::read_from`] and each directory
//! entry with [`crate::internal::DirEntry::read_from`] (the same functions
//! the normal open path in [`crate::CompoundFile`] uses), under
//! [`Validation::Permissive`].  The audit-only logic lives entirely in this
//! module: it builds the chain graph over the parsed tables and reasons about
//! ownership, which is precisely the extra analysis the open path does not
//! perform.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::io::{self, Cursor, Read, Seek, Write};

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};
use crate::ReadLeNumber;

//===========================================================================//

/// Which of a compound file's allocation tables a finding concerns.
///
/// The order of the variants is also the ordering used when findings are
/// sorted for stable output.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AllocationTable {
    /// The File Allocation Table, which chains regular sectors.
    Fat,
    /// The Double-Indirect File Allocation Table, which locates FAT sectors.
    Difat,
    /// The MiniFAT, which chains 64-byte mini sectors inside the mini stream.
    MiniFat,
    /// The chain of directory sectors and the directory-entry tree they hold.
    DirectoryChain,
}

impl AllocationTable {
    fn as_str(self) -> &'static str {
        match self {
            AllocationTable::Fat => "FAT",
            AllocationTable::Difat => "DIFAT",
            AllocationTable::MiniFat => "MiniFAT",
            AllocationTable::DirectoryChain => "directory chain",
        }
    }
}

impl fmt::Display for AllocationTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The kind of corruption a [`CorruptionFinding`] describes.
///
/// Cycles, out-of-bounds references, double ownership (crossed chains),
/// orphan sectors, and declared-length inconsistencies are always reported as
/// distinct kinds, so a caller can match on them individually.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorruptionKind {
    /// A chain reaches one of its own sectors again instead of terminating.
    Cycle,
    /// A pointer refers to a sector or entry index past the end of the table
    /// or file.
    OutOfBounds,
    /// Two distinct chains claim the same sector (crossed allocation chains).
    DoubleOwnership,
    /// An allocated sector or directory entry is not reachable from any chain
    /// root.
    OrphanSector,
    /// A length declared in a header or directory entry disagrees with the
    /// structure it actually describes.
    DeclaredLengthMismatch,
    /// A directory chain ends while still-referenced directory entries lie in
    /// the missing sectors.
    TruncatedDirectory,
    /// A table entry holds a reserved/invalid sentinel value or a directory
    /// entry is malformed.
    InvalidEntry,
}

impl CorruptionKind {
    fn as_str(self) -> &'static str {
        match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DoubleOwnership => {
                "sector claimed by multiple chains"
            }
            CorruptionKind::OrphanSector => "orphan sector",
            CorruptionKind::DeclaredLengthMismatch => {
                "declared length mismatch"
            }
            CorruptionKind::TruncatedDirectory => "truncated directory chain",
            CorruptionKind::InvalidEntry => "invalid entry",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One piece of evidence that a compound file is structurally corrupt.
///
/// A finding always records the allocation [`table`](Self::table) it was found
/// in, the [`kind`](Self::kind) of corruption, a deterministic
/// [`location`](Self::location) (the first offending sector, entry, or byte
/// index), and a human-readable [`context`](Self::context) string with the
/// necessary details.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorruptionFinding {
    table: AllocationTable,
    kind: CorruptionKind,
    location: u64,
    context: String,
}

impl CorruptionFinding {
    /// The allocation table this finding was produced from.
    pub fn table(&self) -> AllocationTable {
        self.table
    }

    /// What kind of corruption was found.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }

    /// The first offending sector, directory-entry, or byte index.
    pub fn location(&self) -> u64 {
        self.location
    }

    /// Human-readable details needed to understand the finding.
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl fmt::Display for CorruptionFinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} at {} ({})",
            self.table.as_str(),
            self.kind.as_str(),
            self.location,
            self.context
        )
    }
}
