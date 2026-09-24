//! Opt-in structural auditing of compound files.
//!
//! The audit is a read-only analysis of a CFB image: it reports corruption
//! evidence for the DIFAT, FAT, directory chain, and MiniFAT, and it prepares
//! a [`RepairPlan`] describing exactly which bytes would change.  Auditing
//! never writes anything, and a plan can only be applied explicitly, and
//! only while a digest of the input still matches the digest recorded when
//! the plan was made.
//!
//! Entry points:
//! * [`audit_bytes`] / [`audit_reader`] audit an image without opening it.
//!   This is the only way to inspect files too damaged to open normally.
//! * [`crate::OpenOptions::audit_only`] audits through the standard open
//!   options, from a path or any reader.
//! * [`crate::CompoundFile::audit`] audits an already-open compound file.
//! * [`RepairPlan::dry_run`] returns the repaired image in memory; it never
//!   touches the input.
//! * [`crate::CompoundFile::apply_repair_plan`] applies a matching plan to a
//!   read-write compound file atomically.
//!
//! Each diagnosis is classified as one of [`Corruption`], so cycles,
//! out-of-bounds references, double occupancy, orphan sectors, and declared
//! length disagreements are always reported separately.

use std::fmt;
use std::io::{self, Read, Seek, SeekFrom, Write};

use crate::internal::audit_engine::{
    self, analyze_image, apply_patches_journaled, digest_bytes, read_all,
};

/// Which CFB allocation structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Table {
    /// The double-indirect FAT (header entries plus DIFAT sectors).
    Difat,
    /// The file allocation table.
    Fat,
    /// The directory entry chain and sibling/child tree.
    Directory,
    /// The mini-sector FAT.
    MiniFat,
}

impl From<audit_engine::AuditTable> for Table {
    fn from(table: audit_engine::AuditTable) -> Table {
        match table {
            audit_engine::AuditTable::Difat => Table::Difat,
            audit_engine::AuditTable::Fat => Table::Fat,
            audit_engine::AuditTable::Directory => Table::Directory,
            audit_engine::AuditTable::MiniFat => Table::MiniFat,
        }
    }
}

/// The category of a structural violation.  These variants are kept distinct
/// on purpose: a damaged chain can exhibit several at once and a caller may
/// want to react differently to each.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum Corruption {
    /// A chain loops back on itself.
    Cycle,
    /// A pointer names a sector or directory entry that does not exist.
    OutOfBounds,
    /// One sector is reachable from two different chains.
    DoubleOccupancy,
    /// An allocated sector is not reachable from any root.
    Orphan,
    /// A declared length (stream size, chain size in the header) disagrees
    /// with what the chains actually cover.
    LengthMismatch,
    /// A structure cannot be parsed at all.
    Malformed,
}

impl From<audit_engine::AuditCorruption> for Corruption {
    fn from(c: audit_engine::AuditCorruption) -> Corruption {
        match c {
            audit_engine::AuditCorruption::Cycle => Corruption::Cycle,
            audit_engine::AuditCorruption::OutOfBounds => {
                Corruption::OutOfBounds
            }
            audit_engine::AuditCorruption::DoubleOccupancy => {
                Corruption::DoubleOccupancy
            }
            audit_engine::AuditCorruption::Orphan => Corruption::Orphan,
            audit_engine::AuditCorruption::LengthMismatch => {
                Corruption::LengthMismatch
            }
            audit_engine::AuditCorruption::Malformed => Corruption::Malformed,
        }
    }
}

impl fmt::Display for Corruption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let table = match self {
            Corruption::Cycle => "cycle",
            Corruption::OutOfBounds => "out-of-bounds reference",
            Corruption::DoubleOccupancy => "double occupancy",
            Corruption::Orphan => "orphan sector",
            Corruption::LengthMismatch => "declared length mismatch",
            Corruption::Malformed => "malformed structure",
        };
        f.write_str(table)
    }
}

/// One diagnosed violation: its table, category, the first offending
/// location, and a sentence of context.  Findings are sorted by table, then
/// category, then location, so the first violation is stable across repeated
/// audits and across scheduling or iteration-order changes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    /// The damaged allocation structure.
    pub table: Table,
    /// What kind of violation it is.
    pub corruption: Corruption,
    /// First violating sector/entry index.
    pub location: u64,
    /// Human-readable context for the violation.
    pub detail: String,
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}: {} at index {}: {}",
            self.table,
            self.corruption,
            self.location,
            self.detail
        )
    }
}

impl From<audit_engine::RawFinding> for Finding {
    fn from(raw: audit_engine::RawFinding) -> Finding {
        Finding {
            table: raw.table.into(),
            corruption: raw.corruption.into(),
            location: raw.location,
            detail: raw.detail,
        }
    }
}

/// A fingerprint of the exact input bytes a plan was made for: an FNV-1a
/// (64-bit) hash and the byte length.  A plan can only be applied while the
/// input still has this digest.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct PrerequisiteDigest {
    /// FNV-1a 64-bit hash of the input.
    pub fnv1a_64: u64,
    /// Input length in bytes.
    pub len: u64,
}

impl PrerequisiteDigest {
    fn matches(&self, data: &[u8]) -> bool {
        digest_bytes(data) == (self.fnv1a_64, self.len)
    }
}

impl fmt::Display for PrerequisiteDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fnv1a64={:016x}/len={}", self.fnv1a_64, self.len)
    }
}

/// A read-only repair plan.  Carries the digest of the bytes it was derived
/// from; application checks that digest first and refuses a stale plan.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    source_digest: PrerequisiteDigest,
    target_digest: PrerequisiteDigest,
    patches: Vec<audit_engine::Patch>,
    repairable: bool,
    converged: bool,
    residual: Vec<Finding>,
}

impl RepairPlan {
    /// Digest of the input this plan was made for.  Application requires this
    /// digest to still match.
    pub fn prerequisite_digest(&self) -> PrerequisiteDigest {
        self.source_digest
    }

    /// Digest of the image the patches converge on.
    pub fn target_digest(&self) -> PrerequisiteDigest {
        self.target_digest
    }

    /// Number of byte patches the plan applies.
    pub fn num_patches(&self) -> usize {
        self.patches.len()
    }

    /// True iff the planned repairs converge on an image with no findings,
    /// using only fixed-width in-place patches.
    pub fn is_repairable(&self) -> bool {
        self.repairable
    }

    /// Findings that remain after the planned repairs (empty for a plan that
    /// converges).
    pub fn residual_findings(&self) -> &[Finding] {
        &self.residual
    }

    /// Produces the repaired image in memory and audits it again, without
    /// writing anything to the input.  Returns an error if the plan cannot
    /// converge.
    pub fn dry_run(&self, input: &[u8]) -> io::Result<AuditReport> {
        if !self.source_digest.matches(input) {
            return Err(stale_plan_error(self.source_digest, input));
        }
        let mut repaired = input.to_vec();
        for patch in self.patches.iter() {
            let start = patch.offset as usize;
            if start + patch.new_bytes.len() > repaired.len() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "repair plan references bytes beyond the input image",
                ));
            }
            repaired[start..start + patch.new_bytes.len()]
                .copy_from_slice(&patch.new_bytes);
        }
        let report = audit_bytes(&repaired)?;
        if !report.findings().is_empty() || !self.repairable {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "repair plan does not converge; residual findings: {}",
                    report
                        .findings()
                        .iter()
                        .map(|f| f.to_string())
                        .collect::<Vec<_>>()
                        .join("; ")
                ),
            ));
        }
        Ok(report)
    }
}

/// The result of an audit: every detected finding, plus a plan if the damage
/// can be repaired in place.
#[derive(Clone, Debug)]
pub struct AuditReport {
    findings: Vec<Finding>,
    plan: RepairPlan,
}

impl AuditReport {
    /// Every detected violation, sorted by table, category, then first
    /// violating location.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// True if no violations were detected.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// The read-only repair plan derived from this audit.
    pub fn repair_plan(&self) -> &RepairPlan {
        &self.plan
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.findings.is_empty() {
            return writeln!(f, "audit: clean");
        }
        writeln!(f, "audit: {} finding(s)", self.findings.len())?;
        for finding in &self.findings {
            writeln!(f, "  - {}", finding)?;
        }
        if self.plan.is_repairable() {
            writeln!(
                f,
                "repair plan: {} in-place patch(es), prerequisite {}",
                self.plan.num_patches(),
                self.plan.source_digest
            )
        } else {
            writeln!(f, "repair plan: not repairable in place")
        }
    }
}

fn report_from(data: &[u8]) -> io::Result<AuditReport> {
    let outcome = analyze_image(data)?;
    let source_digest = {
        let (hash, len) = digest_bytes(data);
        PrerequisiteDigest { fnv1a_64: hash, len }
    };
    let target_digest = PrerequisiteDigest {
        fnv1a_64: outcome.target_digest.0,
        len: outcome.target_digest.1,
    };
    let plan = RepairPlan {
        source_digest,
        target_digest,
        patches: outcome.patches,
        repairable: outcome.repairable,
        converged: outcome.converged,
        residual: outcome.findings.iter().cloned().map(Finding::from).collect(),
    };
    Ok(AuditReport {
        findings: outcome.findings.into_iter().map(Finding::from).collect(),
        plan,
    })
}

/// Audits an in-memory CFB image.  Never writes.
pub fn audit_bytes(data: &[u8]) -> io::Result<AuditReport> {
    report_from(data)
}

/// Audits a CFB image read from `reader` (the whole image is read into
/// memory).  Never writes to `reader`.
pub fn audit_reader<R: Read>(reader: &mut R) -> io::Result<AuditReport> {
    let data = read_all(reader)?;
    audit_bytes(&data)
}

fn stale_plan_error(digest: PrerequisiteDigest, current: &[u8]) -> io::Error {
    let (hash, len) = digest_bytes(current);
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "stale repair plan: prerequisite {} no longer matches current \
             image (fnv1a64={:016x}/len={})",
            digest, hash, len
        ),
    )
}

/// Applies a digest-gated plan to a read-write seekable target.  The target
/// is read in full first; if the digest does not match no bytes are written;
/// writes are journaled so a mid-way failure rolls back every earlier write.
pub(crate) fn apply_plan_to_writer<W>(
    writer: &mut W,
    plan: &RepairPlan,
) -> io::Result<PrerequisiteDigest>
where
    W: Read + Write + Seek,
{
    writer.seek(SeekFrom::Start(0))?;
    let data = read_all(writer)?;
    if !plan.source_digest.matches(&data) {
        return Err(stale_plan_error(plan.source_digest, &data));
    }
    if !plan.repairable {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "repair plan does not converge and cannot be applied",
        ));
    }
    writer.seek(SeekFrom::Start(0))?;
    apply_patches_journaled(writer, &plan.patches)?;
    writer.flush()?;
    // Re-read and verify the target digest before reporting success.
    writer.seek(SeekFrom::Start(0))?;
    let after = read_all(writer)?;
    let after_digest = {
        let (hash, len) = digest_bytes(&after);
        PrerequisiteDigest { fnv1a_64: hash, len }
    };
    if after_digest != plan.target_digest {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "applied repair did not produce the planned image",
        ));
    }
    Ok(after_digest)
}
