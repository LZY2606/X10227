//! The public shape of an audit: evidence, plans, and reports.

use std::fmt;
use std::io::{self, Read, Seek, Write};

use super::digest::AuditDigest;
use super::parse::{self, RawImage};
use super::repair;

/// Which CFB structure a piece of evidence concerns.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum Structure {
    /// The File Allocation Table chain (and the sector chains it describes).
    Fat,
    /// The Double-Indirect FAT that locates FAT sectors.
    Difat,
    /// The mini stream allocator.
    MiniFat,
    /// The chain of sectors holding directory entries.
    Directory,
}

impl Structure {
    /// A short, stable name used in test and report output.
    pub fn name(self) -> &'static str {
        match self {
            Structure::Fat => "FAT",
            Structure::Difat => "DIFAT",
            Structure::MiniFat => "MiniFAT",
            Structure::Directory => "directory chain",
        }
    }
}

impl fmt::Display for Structure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The kind of damage recorded for one [`Evidence`] item.
///
/// The variants deliberately distinguish conditions that can otherwise look
/// alike: a chain that enters a cycle, a pointer past the end of a table, a
/// sector claimed by two chains, an unreachable sector, and a stream whose
/// declared length disagrees with its chain.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum DamageKind {
    /// A chain pointer enters a sector already visited by the same chain.
    Cycle,
    /// A table entry points at a sector/mini sector that does not exist.
    OutOfBounds,
    /// A sector/mini sector is reachable from two different owners.
    DoubleOccupancy,
    /// An allocated-looking sector or mini sector is owned by no chain.
    Orphan,
    /// A directory entry's declared stream length disagrees with the sectors
    /// its chain provides.
    LengthMismatch,
}

impl DamageKind {
    /// A short, stable name used in test and report output.
    pub fn name(self) -> &'static str {
        match self {
            DamageKind::Cycle => "cycle",
            DamageKind::OutOfBounds => "out-of-bounds",
            DamageKind::DoubleOccupancy => "double occupancy",
            DamageKind::Orphan => "orphan",
            DamageKind::LengthMismatch => "declared length mismatch",
        }
    }
}

impl fmt::Display for DamageKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// One defect found during an audit.
///
/// `offset` is the first offending location, measured as a byte offset within
/// the input file whenever it can be determined (so callers can point at the
/// exact table entry), and `context` describes the chain or entry involved.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evidence {
    structure: Structure,
    kind: DamageKind,
    offset: Option<u64>,
    context: String,
}

impl Evidence {
    pub(crate) fn new(
        structure: Structure,
        kind: DamageKind,
        offset: Option<u64>,
        context: impl Into<String>,
    ) -> Evidence {
        Evidence { structure, kind, offset, context: context.into() }
    }

    /// The structure this defect was found in.
    pub fn structure(&self) -> Structure {
        self.structure
    }

    /// The kind of defect.
    pub fn kind(&self) -> DamageKind {
        self.kind
    }

    /// Byte offset of the first offending table entry or directory field in
    /// the audited file, if it has a fixed on-disk location.
    pub fn offset(&self) -> Option<u64> {
        self.offset
    }

    /// Human-readable context: which chain, sector, or stream is involved.
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl fmt::Display for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {} in {}", self.kind, self.context, self.structure)?;
        if let Some(offset) = self.offset {
            write!(f, " (file byte {})", offset)?;
        }
        Ok(())
    }
}

/// One action a repair would perform.  Returned as part of a [`RepairPlan`];
/// it only describes the action, it has not been applied to anything.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    index: usize,
    description: String,
}

impl RepairStep {
    pub(crate) fn new(index: usize, description: impl Into<String>) -> RepairStep {
        RepairStep { index, description: description.into() }
    }

    /// Position of this step within the plan (0-based).
    pub fn index(&self) -> usize {
        self.index
    }
}

impl fmt::Display for RepairStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}. {}", self.index + 1, self.description)
    }
}

/// A read-only description of how an audited file could be rebuilt.
///
/// A plan is bound to the exact input bytes it was produced from via
/// [`RepairPlan::digest`].  [`RepairPlan::apply_to`] refuses to run unless the
/// input still has that digest, so a plan can never be applied to a file that
/// changed after auditing.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    digest: AuditDigest,
    steps: Vec<String>,
}

impl RepairPlan {
    /// Identity of the input bytes this plan was computed for.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// The repair actions, in order.
    pub fn steps(&self) -> &[String] {
        &self.steps
    }

    /// Returns true if the plan would change nothing.
    pub fn is_noop(&self) -> bool {
        self.steps.is_empty()
    }

    /// Verifies that `input` is unchanged since the audit and returns the
    /// repaired image, without writing anywhere.
    ///
    /// This is the dry run: it only reads `input`, never writes.
    pub fn build<F: Read + Seek>(&self, input: F) -> io::Result<Vec<u8>> {
        let digest = AuditDigest::of_reader(input)?;
        if digest != self.digest {
            invalid_input!(
                "Cannot apply repair plan: the compound file has changed \
                 since the audit (expected {}, found {})",
                self.digest,
                digest
            );
        }
        repair::rebuild(&self.steps, digest)
    }

    /// Applies the plan to `dest`, but only if `input` is still the bytes the
    /// plan was made for.
    ///
    /// The repaired image is built entirely in memory and checked before
    /// `dest` is touched, so a failure while building (including an injected
    /// I/O failure) leaves `dest` and the input untouched.  After a successful
    /// return, `dest` contains a compacted, fully valid compound file holding
    /// all the recoverable storages and streams.
    pub fn apply_to<F: Read + Seek, W: Write + Seek>(
        &self,
        input: F,
        dest: &mut W,
    ) -> io::Result<()> {
        let image = self.build(input)?;
        dest.seek(io::SeekFrom::Start(0))?;
        dest.write_all(&image)?;
        dest.flush()?;
        Ok(())
    }
}

impl fmt::Display for RepairPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.steps.is_empty() {
            writeln!(f, "Repair plan: no changes needed (digest {})", self.digest)
        } else {
            writeln!(f, "Repair plan (for input digest {}):", self.digest)?;
            for (index, step) in self.steps.iter().enumerate() {
                writeln!(f, "  {}. {}", index + 1, step)?;
            }
            Ok(())
        }
    }
}

/// The result of auditing one compound file.
#[derive(Clone, Debug)]
pub struct AuditReport {
    digest: AuditDigest,
    evidence: Vec<Evidence>,
    plan: RepairPlan,
}

impl AuditReport {
    /// Identity of the audited input bytes.
    pub fn digest(&self) -> AuditDigest {
        self.digest
    }

    /// Every defect found, in a deterministic order.
    pub fn evidence(&self) -> &[Evidence] {
        &self.evidence
    }

    /// True if no structural defects were found.
    pub fn is_clean(&self) -> bool {
        self.evidence.is_empty()
    }

    /// The read-only repair plan for the audited input.
    pub fn plan(&self) -> &RepairPlan {
        &self.plan
    }
}

impl fmt::Display for AuditReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CFB audit (digest {}):", self.digest)?;
        if self.evidence.is_empty() {
            writeln!(f, "  no allocation-chain defects found")?;
        } else {
            for item in &self.evidence {
                writeln!(f, "  - {}", item)?;
            }
        }
        write!(f, "{}", self.plan)
    }
}

pub(super) fn audit_reader<F: Read + Seek>(
    mut reader: F,
    validation: crate::internal::Validation,
) -> io::Result<AuditReport> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    let digest = AuditDigest::of_bytes(&bytes);
    let raw = RawImage::parse(&bytes, validation)?;
    let (evidence, steps) = parse::collect(&raw);
    Ok(AuditReport {
        digest,
        evidence,
        plan: RepairPlan { digest, steps },
    })
}
