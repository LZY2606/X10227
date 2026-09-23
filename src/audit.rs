//! Opt-in structural auditing and read-only repair planning for compound
//! files.
//!
//! The audit is read-only: it parses the header, DIFAT, FAT, MiniFAT, and
//! directory chain of a compound file and reports corruption evidence
//! without modifying the input.  Evidence is grouped into distinct
//! categories (loops, out-of-bounds pointers, duplicate occupancy, orphan
//! sectors, and declared-length mismatches), each carrying the first
//! violating sector and human-readable context.
//!
//! From the evidence, the audit derives a [`RepairPlan`]: a read-only,
//! explicitly versioned description of the minimal byte edits that would
//! repair the file.  A plan records the digest of the exact input it was
//! computed from and only applies while that digest still matches;
//! [`RepairPlan::dry_run`] never writes any bytes.
//!
//! The audit reuses the crate's production header and directory-entry
//! parsers; it adds no separate parsing algorithm of its own.

use std::fmt;
use std::hash::Hasher;
use std::io::{self, Read, Seek, SeekFrom, Write};

use fnv::{FnvHashMap, FnvHashSet};

use crate::internal::{consts, DirEntry, Header, ObjType, Validation, Version};

// Byte offsets within the 512-byte CFB header.
const HEADER_OFFSET_NUM_DIR_SECTORS: u64 = 40;
const HEADER_OFFSET_NUM_FAT_SECTORS: u64 = 44;
const HEADER_OFFSET_NUM_MINIFAT_SECTORS: u64 = 64;
const HEADER_OFFSET_FIRST_DIFAT_SECTOR: u64 = 68;
const HEADER_OFFSET_NUM_DIFAT_SECTORS: u64 = 72;

// Byte offsets within a 128-byte directory entry.
const DIR_ENTRY_OFFSET_START_SECTOR: u64 = 116;
const DIR_ENTRY_OFFSET_STREAM_LEN: u64 = 120;

//===========================================================================//

//===========================================================================//

/// One proposed byte-level edit to a compound file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ByteEdit {
    offset: u64,
    before: Vec<u8>,
    after: Vec<u8>,
}

impl ByteEdit {
    /// Returns the file offset at which the edit starts.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Returns the bytes expected at that offset before the edit.
    pub fn before(&self) -> &[u8] {
        &self.before
    }

    /// Returns the bytes that would replace them.
    pub fn after(&self) -> &[u8] {
        &self.after
    }
}

/// One step of a [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    component: AuditComponent,
    description: String,
    edits: Vec<ByteEdit>,
}

impl RepairStep {
    fn new(
        component: AuditComponent,
        description: String,
        edits: Vec<ByteEdit>,
    ) -> RepairStep {
        debug_assert!(!edits.is_empty());
        RepairStep { component, description, edits }
    }

    /// Returns the component this repair targets.
    pub fn component(&self) -> AuditComponent {
        self.component
    }

    /// Returns a human-readable description of the repair.
    pub fn description(&self) -> &str {
        &self.description
    }

    /// Returns the byte edits that implement this repair.
    pub fn edits(&self) -> &[ByteEdit] {
        &self.edits
    }
}

//===========================================================================//

/// The result of auditing a compound file: its corruption evidence together
/// with a read-only [`RepairPlan`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuditReport {
    digest: u64,
    input_len: u64,
    diagnostics: Vec<Diagnostic>,
    steps: Vec<RepairStep>,
}

impl AuditReport {
    /// Returns the digest of the exact audited input.  This is the version
    /// identity of the audit: any derived plan can only be applied to an
    /// input with this same digest.
    pub fn digest(&self) -> u64 {
        self.digest
    }

    /// Returns the length in bytes of the audited input.
    pub fn input_len(&self) -> u64 {
        self.input_len
    }

    /// Returns the corruption evidence in deterministic order.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    /// Returns true if the audited file showed no structural problems.
    pub fn is_healthy(&self) -> bool {
        self.diagnostics.is_empty()
    }

    /// Derives a read-only repair plan from the audit.
    pub fn repair_plan(&self) -> RepairPlan {
        RepairPlan {
            digest: self.digest,
            input_len: self.input_len,
            steps: self.steps.clone(),
        }
    }
}

//===========================================================================//

/// A read-only repair plan produced by an [`AuditReport`].
///
/// The plan never writes bytes by itself.  It carries the digest of the
/// input it was planned against (its version identity); both
/// [`dry_run`](RepairPlan::dry_run) and [`apply`](RepairPlan::apply) refuse
/// an input whose digest no longer matches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPlan {
    digest: u64,
    input_len: u64,
    steps: Vec<RepairStep>,
}

impl RepairPlan {
    /// Returns the precondition digest recorded by the plan: the digest of
    /// the input the plan was computed from.
    pub fn precondition_digest(&self) -> u64 {
        self.digest
    }

    /// Returns the input length required by the plan.
    pub fn expected_input_len(&self) -> u64 {
        self.input_len
    }

 /// Returns the planned repair steps.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }

    /// Returns true if the plan performs no edits.
    pub fn is_noop(&self) -> bool {
        self.steps.is_empty()
    }

    /// Verifies the precondition digest and reports what would change,
    /// without writing a single byte.  The reader bound does not even allow
    /// writing.
    pub fn dry_run<F: Read + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<DryRunReport> {
        let data = read_all(inner)?;
        self.check_precondition(&data)?;
        let bytes_that_would_change = self
            .steps
            .iter()
            .flat_map(|step| step.edits.iter())
            .map(|edit| edit.after.len())
            .sum();
        Ok(DryRunReport {
            precondition_digest: self.digest,
            steps: self.steps.clone(),
            bytes_that_would_change,
        })
    }

    /// Applies the plan after verifying that the input digest still matches.
    ///
    /// All edits are composed against an in-memory copy and the repaired
    /// image is re-audited before any byte is committed, so any precondition
    /// or self-check failure returns without touching the input.  The
    /// commit itself is a single write of the complete repaired image.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        inner: &mut F,
    ) -> io::Result<ApplyReport> {
        let data = read_all(inner)?;
        self.check_precondition(&data)?;
        if self.steps.is_empty() {
            return Ok(ApplyReport { steps_applied: 0, bytes_written: 0 });
        }

        let mut image = data.clone();
        let mut steps_applied = 0usize;
        for step in &self.steps {
            for edit in &step.edits {
                let start = edit.offset as usize;
                let end = start + edit.after.len();
                let current = image.get(start..end);
                if current != Some(&edit.before[..]) {
                    invalid_data!(
                        "Repair precondition failed at offset {} (the bytes \
                         there do not match the audit)",
                        edit.offset
                    );
                }
                image[start..end].copy_from_slice(&edit.after);
            }
            steps_applied += 1;
        }

        // Self-check: the repaired image must no longer contain the kinds
        // of structural corruption this plan edits (loops, out-of-bounds
        // pointers, or duplicate occupancy).
        let reanalysis = analyze(&image)?;
        let unresolved: Vec<&Diagnostic> = reanalysis
            .diagnostics
            .iter()
            .filter(|diagnostic| {
                matches!(
                    diagnostic.kind,
                    DiagnosticKind::Loop
                        | DiagnosticKind::OutOfBounds
                        | DiagnosticKind::DuplicateOccupancy
                )
            })
            .collect();
        if !unresolved.is_empty() {
            invalid_data!(
                "Repair plan failed its self-check: {} structural \
                 problem(s) would remain (first: {})",
                unresolved.len(),
                unresolved[0]
            );
        }

        inner.seek(SeekFrom::Start(0))?;
        inner.write_all(&image)?;
        inner.flush()?;
        Ok(ApplyReport {
            steps_applied,
            bytes_written: image.len(),
        })
    }

    fn check_precondition(&self, data: &[u8]) -> io::Result<()> {
        if data.len() as u64 != self.input_len {
            invalid_input!(
                "Repair plan precondition failed: input is {} bytes, but \
                 the plan was made for a {} byte input",
                data.len(),
                self.input_len
            );
        }
        let digest = content_digest(data);
        if digest != self.digest {
            invalid_input!(
                "Repair plan precondition failed: input digest is \
                 {:016x}, but the plan requires {:016x}",
                digest,
                self.digest
            );
        }
        Ok(())
    }
}

impl fmt::Display for RepairPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Repair plan for input digest {:016x} ({} bytes), {} step(s):",
            self.digest,
            self.input_len,
            self.steps.len()
        )?;
        if self.steps.is_empty() {
            writeln!(f, "  (no repairs needed)")?;
        }
        for step in &self.steps {
            writeln!(f, "  - [{}] {}", step.component, step.description)?;
        }
        Ok(())
    }
}

/// The outcome of a successful [`RepairPlan::dry_run`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DryRunReport {
    precondition_digest: u64,
    steps: Vec<RepairStep>,
    bytes_that_would_change: usize,
}

impl DryRunReport {
    /// Returns the precondition digest that was verified.
    pub fn precondition_digest(&self) -> u64 {
        self.precondition_digest
    }

    /// Returns the steps the dry run would perform.
    pub fn steps(&self) -> &[RepairStep] {
        &self.steps
    }

    /// Returns how many bytes would be overwritten.
    pub fn bytes_that_would_change(&self) -> usize {
        self.bytes_that_would_change
    }
}

/// The outcome of a successful [`RepairPlan::apply`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ApplyReport {
    steps_applied: usize,
    bytes_written: usize,
}

impl ApplyReport {
    /// Returns how many repair steps were applied.
    pub fn steps_applied(&self) -> usize {
        self.steps_applied
    }

    /// Returns how many bytes were committed to the input.
    pub fn bytes_written(&self) -> usize {
        self.bytes_written
    }
}

//===========================================================================//

/// Audits a compound file image held in memory.
pub fn audit_bytes(data: &[u8]) -> io::Result<AuditReport> {
    analyze(data).map(|analysis| analysis.into_report())
}

/// Audits an existing compound file through any readable, seekable input
/// (for example a [`File`](std::fs::File) or a [`Cursor`](std::io::Cursor)).
/// The input is only read; it is never modified.
pub fn audit_reader<R: Read + Seek>(mut reader: R) -> io::Result<AuditReport> {
    let data = read_all(&mut reader)?;
    audit_bytes(&data)
}

fn read_all<R: Read + Seek>(reader: &mut R) -> io::Result<Vec<u8>> {
    reader.seek(SeekFrom::Start(0))?;
    let mut data = Vec::new();
    reader.read_to_end(&mut data)?;
    Ok(data)
}

//===========================================================================//

/// Which part of the compound file a [`Diagnostic`] concerns.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AuditComponent {
    /// The File Allocation Table (sector chains).
    Fat,
    /// The Double-Indirect File Allocation Table.
    Difat,
    /// The MiniFAT (mini sector chains inside the mini stream).
    MiniFat,
    /// The FAT chain that holds directory entries.
    DirectoryChain,
    /// The mini stream backed by the root storage entry.
    MiniStream,
}

impl fmt::Display for AuditComponent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            AuditComponent::Fat => "FAT",
            AuditComponent::Difat => "DIFAT",
            AuditComponent::MiniFat => "MiniFAT",
            AuditComponent::DirectoryChain => "directory chain",
            AuditComponent::MiniStream => "mini stream",
        };
        f.write_str(name)
    }
}

/// The category of a [`Diagnostic`].
///
/// The audit deliberately keeps these categories distinct: a chain
/// [`Loop`](DiagnosticKind::Loop), an
/// [`OutOfBounds`](DiagnosticKind::OutOfBounds) pointer, a
/// [`DuplicateOccupancy`](DiagnosticKind::DuplicateOccupancy) reference, an
/// [`OrphanSector`](DiagnosticKind::OrphanSector), and a
/// [`DeclaredLengthMismatch`](DiagnosticKind::DeclaredLengthMismatch) are
/// never merged into a single generic "malformed" result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DiagnosticKind {
    /// A chain follows a pointer back to a sector it already visited.
    Loop,
    /// A pointer targets a sector or mini sector that does not exist.
    OutOfBounds,
    /// One sector is claimed by more than one chain.
    DuplicateOccupancy,
    /// A sector is marked allocated but is unreachable from any chain head.
    OrphanSector,
    /// A header- or entry-declared length or count does not match reality.
    DeclaredLengthMismatch,
}

impl fmt::Display for DiagnosticKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            DiagnosticKind::Loop => "loop",
            DiagnosticKind::OutOfBounds => "out-of-bounds pointer",
            DiagnosticKind::DuplicateOccupancy => "duplicate occupancy",
            DiagnosticKind::OrphanSector => "orphan sector",
            DiagnosticKind::DeclaredLengthMismatch => {
                "declared length mismatch"
            }
        };
        f.write_str(name)
    }
}

//===========================================================================//

/// One piece of corruption evidence found while auditing a compound file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    component: AuditComponent,
    kind: DiagnosticKind,
    first_violating_sector: Option<u32>,
    message: String,
}

impl Diagnostic {
    fn new(
        component: AuditComponent,
        kind: DiagnosticKind,
        first_violating_sector: Option<u32>,
        message: String,
    ) -> Diagnostic {
        Diagnostic {
            component,
            kind,
            first_violating_sector,
            message,
        }
    }

    /// Returns the structural component the evidence is about.
    pub fn component(&self) -> AuditComponent {
        self.component
    }

    /// Returns the category of corruption.
    pub fn kind(&self) -> DiagnosticKind {
        self.kind
    }

    /// Returns the sector ID at which the first violation was observed, if
    /// any.  This is the target sector for duplicate and out-of-bounds
    /// pointers, and the revisited sector for loops.
    pub fn first_violating_sector(&self) -> Option<u32> {
        self.first_violating_sector
    }

    /// Returns human-readable context for the violation.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} in {}", self.kind, self.component)?;
        if let Some(sector) = self.first_violating_sector {
            write!(f, " at sector {}", sector)?;
        }
        write!(f, ": {}", self.message)
    }
}

//===========================================================================//
