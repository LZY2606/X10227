//! Opt-in structural auditing of compound files.
//!
//! The functions in [`crate::OpenOptions`] named `audit_with`,
//! `dry_run_repair_with`, and `apply_repair_with` analyze a compound file
//! without having to successfully open it first.  This makes them usable on
//! files whose allocation tables are damaged enough that
//! [`crate::CompoundFile::open`] rejects them.
//!
//! Auditing never writes to the input.  Repairing is a separate, explicit
//! step: an [`AuditReport`] describes what is wrong and proposes a read-only
//! [`RepairPlan`].  The plan records a [`Digest`] of the exact bytes it was
//! computed from; applying it fails without writing anything unless those
//! bytes still match.  A dry run performs every check of a real application
//! except the final write, so it too can never modify the input.
//!
//! All audit state is local to one call.  Reports from one audit carry no
//! caches, counters, or handles into the next one, and repeating an audit on
//! unchanged input yields an identical report regardless of call order.

use std::fmt;

/// Which CFB allocation structure a piece of evidence comes from.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum AuditTable {
    /// The File Allocation Table and its sector chains.
    Fat,
    /// The Double-Indirect FAT that locates FAT sectors.
    Difat,
    /// The mini-sector allocation table.
    MiniFat,
    /// The directory chain and the directory entries it contains.
    Directory,
}

impl fmt::Display for AuditTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AuditTable::Fat => f.write_str("FAT"),
            AuditTable::Difat => f.write_str("DIFAT"),
            AuditTable::MiniFat => f.write_str("MiniFAT"),
            AuditTable::Directory => f.write_str("directory"),
        }
    }
}

/// The kind of damage recorded in a [`Finding`].
///
/// These categories are intentionally distinct: a chain that loops back into
/// itself is not the same as one that runs past the end of a table, a sector
/// claimed by two chains is not the same as a sector claimed by none, and a
/// declared stream length that disagrees with its chain is reported on its
/// own.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CorruptionKind {
    /// A chain revisits a sector it has already visited.
    Cycle,
    /// A table entry points outside the table or past the end of the file.
    OutOfBounds,
    /// The same sector is reachable from two different chain roots.
    DuplicateOwner,
    /// An allocated sector is not reachable from any chain root.
    Orphan,
    /// A declared length disagrees with the sectors backing the object.
    LengthMismatch,
    /// The directory chain does not cover every referenced directory entry,
    /// or a header count disagrees with the actual number of sectors.
    Truncated,
}

impl CorruptionKind {
    fn as_str(self) -> &'static str {
        match self {
            CorruptionKind::Cycle => "cycle",
            CorruptionKind::OutOfBounds => "out-of-bounds reference",
            CorruptionKind::DuplicateOwner => "duplicate ownership",
            CorruptionKind::Orphan => "orphan sector",
            CorruptionKind::LengthMismatch => "declared length mismatch",
            CorruptionKind::Truncated => "truncated chain or count",
        }
    }
}

impl fmt::Display for CorruptionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// One piece of corruption evidence, located as precisely as the format
/// allows.
///
/// Every finding records the table involved, the kind of damage, the first
/// location at which it can be demonstrated, and a human-readable context
/// string.  The first-location field is a byte offset into the file when the
/// evidence is a table entry or directory field; otherwise it is a sector or
/// mini-sector number.  `context` says which it is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding {
    table: AuditTable,
    kind: CorruptionKind,
    location: u64,
    context: String,
}

impl Finding {
    /// Returns the table containing this finding.
    pub fn table(&self) -> AuditTable {
        self.table
    }

    /// Returns the kind of corruption.
    pub fn kind(&self) -> CorruptionKind {
        self.kind
    }

    /// Returns the first provable location of the finding; see the context
    /// for whether this is a file byte offset or a sector number.
    pub fn location(&self) -> u64 {
        self.location
    }

    /// Returns a description of where [`Finding::location`] points and what
    /// was found there.
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl fmt::Display for Finding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {} at {} ({})",
            self.table,
            self.kind,
            self.location,
            self.context
        )
    }
}

/// A content fingerprint of the audited bytes.
///
/// The digest covers the entire input.  A [`RepairPlan`] only applies when
/// the current bytes produce the same digest, so any change made after
/// planning invalidates the plan.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Digest(u64, u64);

impl Digest {
    /// Returns the two 64-bit halves of the fingerprint.
    pub fn parts(&self) -> (u64, u64) {
        (self.0, self.1)
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}{:016x}", self.0, self.1)
    }
}

/// One byte-level edit proposed by a [`RepairPlan`].
///
/// Patches are the only thing an application ever writes.  Each patch
/// replaces `bytes.len()` bytes at byte offset `offset`; the audit engine
/// only ever proposes to overwrite table entries or directory fields, never
/// to append or truncate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairPatch {
    offset: u64,
    bytes: Vec<u8>,
    reason: String,
}

impl RepairPatch {
    /// Returns the byte offset at which the patch starts.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Returns the bytes to write.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns why this patch is part of the plan.
    pub fn reason(&self) -> &str {
        &self.reason
    }
}

/// A read-only proposal for turning the audited bytes into a file the
/// normal open path accepts.
///
/// Construct a plan with [`AuditReport::repair_plan`].  It is inert on its
/// own: pass it to [`crate::OpenOptions::dry_run_repair_with`] or
/// [`crate::OpenOptions::apply_repair_with`] to make use of it.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    prerequisite_digest: Digest,
    patches: Vec<RepairPatch>,
    unrepairable: Vec<Finding>,
}

impl RepairPlan {
    /// Returns the digest the input must still have for this plan to apply.
    pub fn prerequisite_digest(&self) -> Digest {
        self.prerequisite_digest
    }

    /// Returns the proposed byte-level patches, in ascending offset order.
    pub fn patches(&self) -> &[RepairPatch] {
        &self.patches
    }

    /// Returns the findings for which no safe patch could be proposed.  If
    /// this is non-empty, applying the plan fails without writing, because a
    /// partial repair would leave the file half-fixed.
    pub fn unrepairable_findings(&self) -> &[Finding] {
        &self.unrepairable
    }

    /// Returns true if this plan can restore the file to an openable state.
    pub fn is_fully_repairable(&self) -> bool {
        self.unrepairable.is_empty()
    }
}

/// The result of an opt-in structural audit.
#[derive(Clone, Debug)]
pub struct AuditReport {
    digest: Digest,
    findings: Vec<Finding>,
    candidate_patches: Vec<RepairPatch>,
    /// The exact audited bytes, retained so `repair_plan` can verify its
    /// proposals against the same audit logic.  This is per-report state,
    /// not a cache shared between calls.
    input: Vec<u8>,
}

impl AuditReport {
    /// Returns the digest of the audited bytes.
    pub fn digest(&self) -> Digest {
        self.digest
    }

    /// Returns every finding, sorted by table, kind, and first location so
    /// that the same input always reports in the same order.
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    /// Returns true when no structural problems were found.
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }

    /// Returns just the findings of one table.
    pub fn findings_in(&self, table: AuditTable) -> Vec<&Finding> {
        self.findings.iter().filter(|f| f.table == table).collect()
    }

    /// Builds a read-only repair plan from this report.  Building the plan
    /// performs no I/O beyond the audit that already happened.
    pub fn repair_plan(&self) -> RepairPlan {
        crate::internal::audit_engine::build_repair_plan(self)
    }
}

/// The outcome of applying (or dry-running) a [`RepairPlan`].
#[derive(Debug)]
pub struct ApplyOutcome {
    prerequisite_digest: Digest,
    current_digest: Digest,
    patches_applied: usize,
    remaining_findings: Vec<Finding>,
}

impl ApplyOutcome {
    /// Returns the digest the plan required.
    pub fn prerequisite_digest(&self) -> Digest {
        self.prerequisite_digest
    }

    /// Returns the digest the target had when the plan was checked.  On a
    /// successful application this equals the prerequisite digest before the
    /// write and differs afterward.
    pub fn current_digest(&self) -> Digest {
        self.current_digest
    }

    /// Returns how many patches were (or would be) written.
    pub fn patches_applied(&self) -> usize {
        self.patches_applied
    }

    /// Returns the findings a fresh audit of the result reports.  A
    /// successful application leaves this empty.
    pub fn remaining_findings(&self) -> &[Finding] {
        &self.remaining_findings
    }
}

/// The order in which an audit visits chain roots.
///
/// The report is independent of this choice; it exists so callers (and the
/// crate's regression tests) can prove that reordering visits cannot change
/// which damage is detected or which finding comes first.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum AuditOrder {
    /// Visit roots in a fixed, table-defined order.
    #[default]
    Canonical,
    /// Visit the same roots in the reverse order.
    Reverse,
}

/// Points at which an audit or an application may deliberately fail to
/// demonstrate recovery.
///
/// Every checkpoint lies strictly before any byte is written, so a failure
/// there leaves the input untouched and the same call retried on unchanged
/// input produces the same result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AuditCheckpoint {
    /// After the header, DIFAT, and FAT have been read, before chains are
    /// walked.
    TablesLoaded,
    /// After all chains and the directory have been examined, before the
    /// report is finalized.
    ChainsExamined,
    /// When applying a plan: after the prerequisite digest and planned
    /// patches have been re-verified, immediately before the first byte
    /// would be written.
    BeforeWrite,
    /// When applying a plan: after the repaired bytes have been re-audited
    /// in memory, immediately before they are committed to the target.
    BeforeCommit,
}

impl AuditCheckpoint {
    fn as_str(self) -> &'static str {
        match self {
            AuditCheckpoint::TablesLoaded => "tables loaded",
            AuditCheckpoint::ChainsExamined => "chains examined",
            AuditCheckpoint::BeforeWrite => "before write",
            AuditCheckpoint::BeforeCommit => "before commit",
        }
    }
}

impl fmt::Display for AuditCheckpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Options controlling an opt-in structural audit.
#[derive(Clone, Debug, Default)]
pub struct AuditOptions {
    order: AuditOrder,
    failpoint: Option<AuditCheckpoint>,
}

impl AuditOptions {
    /// Creates options with default settings.
    pub fn new() -> Self {
        AuditOptions::default()
    }

    /// Sets the order in which chain roots are visited.
    pub fn order(mut self, order: AuditOrder) -> Self {
        self.order = order;
        self
    }

    /// Arranges for the audit or application to fail once at the given
    /// checkpoint with a retryable [`std::io::Error`].  The failure is
    /// injected before any write, leaves no state behind, and is not
    /// persistent: the next call without this option (or with a different
    /// checkpoint) runs normally.
    pub fn fail_once_at(mut self, checkpoint: AuditCheckpoint) -> Self {
        self.failpoint = Some(checkpoint);
        self
    }
}

//===========================================================================//
// Crate-internal constructors and accessors.  These are the seam through
// which the audit engine fills the public, read-only result types; they are
// not part of the documented API.

impl Finding {
    #[allow(dead_code)]
    pub(crate) fn new(
        table: AuditTable,
        kind: CorruptionKind,
        location: u64,
        context: String,
    ) -> Finding {
        Finding { table, kind, location, context }
    }
}

impl AuditReport {
    pub(crate) fn from_parts(
        digest: Digest,
        findings: Vec<Finding>,
        candidate_patches: Vec<RepairPatch>,
    ) -> AuditReport {
        AuditReport { digest, findings, candidate_patches, input: Vec::new() }
    }

    pub(crate) fn with_input(
        digest: Digest,
        findings: Vec<Finding>,
        candidate_patches: Vec<RepairPatch>,
        input: Vec<u8>,
    ) -> AuditReport {
        AuditReport { digest, findings, candidate_patches, input }
    }

    pub(crate) fn candidate_patches(&self) -> &[RepairPatch] {
        &self.candidate_patches
    }

    pub(crate) fn input_hint(&self) -> &[u8] {
        &self.input
    }
}

impl RepairPlan {
    pub(crate) fn from_parts(
        prerequisite_digest: Digest,
        patches: Vec<RepairPatch>,
        unrepairable: Vec<Finding>,
    ) -> RepairPlan {
        RepairPlan { prerequisite_digest, patches, unrepairable }
    }
}

impl ApplyOutcome {
    pub(crate) fn from_parts(
        prerequisite_digest: Digest,
        current_digest: Digest,
        patches_applied: usize,
        remaining_findings: Vec<Finding>,
    ) -> ApplyOutcome {
        ApplyOutcome {
            prerequisite_digest,
            current_digest,
            patches_applied,
            remaining_findings,
        }
    }
}
