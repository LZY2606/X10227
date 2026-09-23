//! Opt-in structural audits of potentially corrupted compound files.
//!
//! Unlike opening a compound file with [`crate::CompoundFile::open`], which
//! has to be able to interpret a file to succeed, an audit never rejects a
//! file just because an allocation chain is malformed.  Instead it walks the
//! raw FAT, DIFAT, MiniFAT, and directory chains defensively, records each
//! piece of damage as a separate [`Evidence`] item (keeping the first
//! offending location and its context), and produces a read-only
//! [`RepairPlan`].
//!
//! The plan never touches the input: [`RepairPlan::apply_to`] first rebuilds
//! the repaired image entirely in memory (using the same production
//! read/write code path as [`crate::CompoundFile::copy_to`]) and only then
//! writes it out, after re-checking the input's [`AuditDigest`].  A dry run
//! never calls any write method.

mod digest;
mod parse;
mod repair;
mod report;

pub use self::digest::AuditDigest;
pub use self::report::{
    AuditReport, DamageKind, Evidence, RepairPlan, RepairStep, Structure,
};

use std::io::{self, Read, Seek};
use std::path::Path;

use crate::internal::Validation;
use crate::OpenOptions;

impl OpenOptions {
    /// Audits the structural integrity of a compound file without opening it
    /// for mutation.
    ///
    /// The audit walks the FAT, DIFAT, MiniFAT, and directory chains of the
    /// file behind `reader`, reporting every allocation-chain defect it finds
    /// together with a read-only repair plan.  The reader is only read and
    /// seeked; it is never written to.  The strict/permissive setting of the
    /// options does not apply here: an audit is deliberately permissive so
    /// that every defect is reported instead of aborting at the first one.
    pub fn audit_reader<F: Read + Seek>(
        self,
        reader: F,
    ) -> io::Result<AuditReport> {
        report::audit_reader(reader, Validation::Permissive)
    }

    /// Audits the structural integrity of the compound file at `path`.
    ///
    /// The file is opened read-only; this method never writes to it.  See
    /// [`OpenOptions::audit_reader`] for details.
    pub fn audit<P: AsRef<Path>>(self, path: P) -> io::Result<AuditReport> {
        self.audit_reader(std::fs::File::open(path)?)
    }
}
