//! Opt-in structural audit of a compound file.
//!
//! Unlike the normal open path, an audit does not *fail* on the first
//! malformed table entry.  It reads the file independently (but using the
//! same [`Header`](crate::internal::Header) and
//! [`DirEntry`](crate::internal::DirEntry) parsers as the production open
//! path) and collects separately classified damage evidence for the FAT,
//! DIFAT, MiniFAT and directory chains, then derives a read-only
//! [`RepairPlan`] of exact byte changes.
//!
//! The audit never mutates its input; repairing is an explicit second step
//! that first re-checks the plan's [`Fingerprint`] against the live bytes.
//! See [`audit`], [`audit_with`], [`OpenOptions::audit`](crate::OpenOptions::audit)
//! and [`OpenOptions::audit_with`](crate::OpenOptions::audit_with).
//!
//! # Example
//!
//! ```no_run
//! use cfb::audit;
//!
//! // Read-only inspection: `report` and its plan never touch the source.
//! let report = audit("suspect.cfb").unwrap();
//! for defect in report.defects() {
//!     println!("{}", defect);
//! }
//! // Explicit application; fails (and writes nothing) if the file changed.
//! if !report.plan().is_empty() {
//!     report.plan().apply_file("suspect.cfb").unwrap();
//! }
//! ```

use std::fs;
use std::io::{self, Read, Seek, Write};
use std::path::Path;

use fnv::FnvHashSet;

use crate::internal::consts;
use crate::internal::{DirEntry, Header, ObjType, Validation, Version};

//===========================================================================//
// Public types
//===========================================================================//

/// Which allocation structure a piece of damage lives in.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Region {
    /// The File Allocation Table and the chains it describes.
    Fat,
    /// The Double-Indirect FAT (the chain of FAT-sector directories).
    Difat,
    /// The Mini Stream Allocation Table.
    MiniFat,
    /// The directory entry chain as linked through the FAT.
    DirectoryChain,
    /// The sibling/child tree formed by directory entries.
    DirectoryTree,
    /// The mini stream (the root storage's stream that backs mini sectors).
    MiniStream,
}

impl Region {
    /// Short, stable name used in [`Defect`] messages and test assertions.
    pub fn as_str(self) -> &'static str {
        match self {
            Region::Fat => "FAT",
            Region::Difat => "DIFAT",
            Region::MiniFat => "MiniFAT",
            Region::DirectoryChain => "directory chain",
            Region::DirectoryTree => "directory tree",
            Region::MiniStream => "mini stream",
        }
    }
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The distinct categories of damage an audit distinguishes.
///
/// Cycles, out-of-bounds references, double ownership, orphan sectors and
/// declared-length disagreements are always reported separately: each
/// [`Defect`] has exactly one kind, even when several problems coexist.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum DefectKind {
    /// A chain entry points back to a sector already seen in that chain.
    Cycle,
    /// A chain entry points past the table end or uses an invalid marker.
    OutOfBounds,
    /// A sector or mini sector is claimed by more than one chain.
    DoubleOwner,
    /// A sector/mini sector is allocated but unreachable from any chain root.
    Orphan,
    /// A directory entry's declared length disagrees with its chain capacity.
    LengthMismatch,
    /// Any other structural problem (bad markers, dangling links, ...).
    Structural,
}

impl DefectKind {
    /// Short, stable name used in [`Defect`] messages and test assertions.
    pub fn as_str(self) -> &'static str {
        match self {
            DefectKind::Cycle => "cycle",
            DefectKind::OutOfBounds => "out-of-bounds",
            DefectKind::DoubleOwner => "double owner",
            DefectKind::Orphan => "orphan",
            DefectKind::LengthMismatch => "declared length mismatch",
            DefectKind::Structural => "structural",
        }
    }
}

impl std::fmt::Display for DefectKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A single, separately classified piece of damage found by an audit.
///
/// Records the first location where the violation was observed, not just a
/// boolean: [`Defect::region`], [`Defect::kind`], [`Defect::index`] and
/// [`Defect::detail`] identify exactly which table entry or directory slot
/// is wrong and why.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Defect {
    region: Region,
    kind: DefectKind,
    /// First violating table index / sector id / mini sector id / stream id.
    index: u64,
    detail: String,
}

impl Defect {
    /// The allocation structure the damage is in.
    pub fn region(&self) -> Region {
        self.region
    }
    /// The category of the damage.
    pub fn kind(&self) -> DefectKind {
        self.kind
    }
    /// The first violating index (FAT entry, sector, mini sector or stream).
    pub fn index(&self) -> u64 {
        self.index
    }
    /// Human-readable context for the first violation.
    pub fn detail(&self) -> &str {
        &self.detail
    }
}

impl std::fmt::Display for Defect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} at index {}: {}",
            self.region, self.kind, self.index, self.detail
        )
    }
}

/// Content identity of the bytes a plan was made from.
///
/// Covers both byte length and a hash of every byte, so truncation,
/// extension and in-place edits all invalidate it.  Every audit computes a
/// fresh fingerprint; nothing is carried over between calls.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Fingerprint {
    len: u64,
    hash: u64,
}

impl Fingerprint {
    /// Length, in bytes, of the audited input.
    pub fn len(&self) -> u64 {
        self.len
    }
    /// True for an empty input.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// 64-bit content hash (FNV-1a over the input bytes).
    pub fn hash(&self) -> u64 {
        self.hash
    }
}

impl std::fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} bytes, hash 0x{:016x}", self.len, self.hash)
    }
}

/// One concrete byte change in a [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RepairStep {
    offset: u64,
    before: Vec<u8>,
    after: Vec<u8>,
    why: String,
}

impl RepairStep {
    /// Absolute file offset this step rewrites.
    pub fn offset(&self) -> u64 {
        self.offset
    }
    /// Bytes present at the offset when the plan was made.
    pub fn before(&self) -> &[u8] {
        &self.before
    }
    /// Normalized bytes the step writes.
    pub fn after(&self) -> &[u8] {
        &self.after
    }
    /// Why the step is needed (references the defect it repairs).
    pub fn reason(&self) -> &str {
        &self.why
    }
}

impl std::fmt::Display for RepairStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "rewrite {} byte(s) at offset {} ({})",
            self.after.len(),
            self.offset,
            self.why
        )
    }
}

/// A read-only repair plan derived from an [`AuditReport`].
///
/// Stores only byte-identities and byte-changes; it never holds a write
/// handle.  Apply explicitly through [`RepairPlan::write_repaired_to`]
/// (writes a new copy) or [`RepairPlan::apply_file`] (atomically replaces a
/// path).  Both re-audit the live input and refuse to write unless the
/// [`Fingerprint`] still matches.  Building or holding the plan never
/// writes anything.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    precondition: Fingerprint,
    steps: Vec<RepairStep>,
}

impl RepairPlan {
    /// Fingerprint the input must still have for this plan to apply.
    pub fn precondition(&self) -> Fingerprint {
        self.precondition
    }
    /// Byte-level changes the plan would make, in ascending offset order.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }
    /// True when the plan contains no changes.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
    /// Number of distinct byte ranges the plan rewrites.
    pub fn len(&self) -> usize {
        self.steps.len()
    }
}

/// Result of an audit: the precondition fingerprint, all damage evidence and
/// the read-only repair plan.
#[derive(Clone, Debug)]
pub struct AuditReport {
    fingerprint: Fingerprint,
    version: Version,
    defects: Vec<Defect>,
    plan: RepairPlan,
}

impl AuditReport {
    /// Content identity of the audited bytes.
    pub fn fingerprint(&self) -> Fingerprint {
        self.fingerprint
    }
    /// CFB version recorded in the header.
    pub fn version(&self) -> Version {
        self.version
    }
    /// All defects in a stable order (region, then kind, then first index).
    pub fn defects(&self) -> &[Defect] {
        &self.defects
    }
    /// Defects restricted to one allocation structure.
    pub fn defects_in(&self, region: Region) -> Vec<&Defect> {
        self.defects.iter().filter(|d| d.region == region).collect()
    }
    /// True when no damage was found.
    pub fn is_clean(&self) -> bool {
        self.defects.is_empty()
    }
    /// The read-only repair plan (a no-op for a clean file).
    pub fn plan(&self) -> &RepairPlan {
        &self.plan
    }
}
