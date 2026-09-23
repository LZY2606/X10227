//! Opt-in structural audit of compound files.
//!
//! Unlike [`open`](crate::open), auditing never fails on a damaged allocation
//! chain: it walks the raw on-disk structures tolerantly and collects
//! *evidence* about each problem instead of returning the first parse error.
//! The resulting [`AuditReport`] names the first violating sector (or stream
//! entry) and enough context to tell apart the five CFB corruption classes:
//! cycles, out-of-bounds links, double allocation (crossed chains), orphan
//! sectors, and declared-length mismatches.
//!
//! A report can produce a [`RepairPlan`].  The plan is bound to the audited
//! bytes by a content [`Digest`]; [`RepairPlan::apply`] refuses to touch a
//! file whose digest no longer matches.  Building a plan and calling
//! [`RepairPlan::preview`] never writes anything; writes happen only inside
//! `apply`, which journals every byte it changes and rolls the file back to
//! its original contents if any step fails.
//!
//! The audit reader deliberately reuses the same primitives as the production
//! open path ([`Header`](crate::internal::Header), [`Version`], the FAT/DIFAT
//! constants, and the MS-CFB sector/entry layouts); it does not contain a
//! second copy of the file format.

mod engine;
mod plan;

pub use engine::{ChainKind, ChainLayer, Evidence};
pub use plan::{ApplyOutcome, Digest, RepairPlan, RepairStep, RepairStepView};

use std::io::{Read, Seek};

/// Result of a structural audit: the content digest the evidence was computed
/// from, plus the (possibly empty) list of problems found.
///
/// The report is a plain snapshot: it holds no handles, threads, caches, or
/// global state.  Auditing the same bytes twice, in any order, yields
/// identical reports.
#[derive(Clone, Debug)]
pub struct AuditReport {
    pub(crate) digest: Digest,
    pub(crate) evidence: Vec<Evidence>,
}

impl AuditReport {
    /// Runs the opt-in structural audit over `reader`, starting with the same
    /// CFB header parsing as [`CompoundFile::open`](crate::CompoundFile::open)
    /// and then tolerantly walking FAT, DIFAT, MiniFAT, and directory chains.
    ///
    /// Damaged chains produce evidence; only unreadable headers (wrong magic,
    /// unsupported version, or a file smaller than a header) are rejected,
    /// using the same `InvalidData` error class as the normal open entry.
    pub fn new<F: Read + Seek>(reader: F) -> std::io::Result<AuditReport> {
        engine::audit(reader)
    }

    /// Content identity of the audited bytes.
    pub fn digest(&self) -> &Digest {
        &self.digest
    }

    /// Evidence collected during the audit, sorted deterministically by the
    /// first violating location.  Empty when the file has no chain damage.
    pub fn evidence(&self) -> &[Evidence] {
        &self.evidence
    }

    /// Returns true if no corruption was found.
    pub fn is_clean(&self) -> bool {
        self.evidence.is_empty()
    }

    /// Builds a read-only repair plan for all repairable evidence.
    ///
    /// This does not write anything; it only reads `reader` and refuses to
    /// build anything unless the reader's current digest still equals
    /// [`self.digest()`](AuditReport::digest), i.e. the file has not changed
    /// since the audit.  Use [`RepairPlan::apply`] to apply the steps
    /// explicitly.
    pub fn repair_plan<F: Read + Seek>(
        &self,
        reader: F,
    ) -> std::io::Result<RepairPlan> {
        engine::build_repair_plan(self, reader)
    }
}
