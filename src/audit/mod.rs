//! Opt-in, read-only structural auditing of compound files.
//!
//! The normal opening entry points (`cfb::open`, [`crate::OpenOptions::open`],
//! and friends) keep their historical behavior: under permissive validation
//! they quietly repair certain table entries in memory, and under strict
//! validation they reject a file at the first violation.  The audit feature
//! in this module is an additional, explicitly requested view.
//!
//! An audit never writes to the input.  It reads a file and reports the
//! evidence it found in the four CFB allocation structures:
//!
//! - the DIFAT (the chain listing the FAT sectors),
//! - the FAT (regular-sector chains, including the directory chain),
//! - the MiniFAT (mini-sector chains inside the root stream), and
//! - the directory chain itself.
//!
//! Each corruption category is reported separately at its first offending
//! byte: cycles, out-of-bounds references, double occupancy (crossing
//! chains), orphan sectors, declared-length mismatches, and truncated
//! chains.  A [`RepairPlan`] records a *precondition digest* of the input;
//! the plan is only applied when the bytes still hash to that digest.
//!
//! ```no_run
//! use cfb::audit;
//!
//! let report = audit::audit_file("foo.cfb").unwrap();
//! if !report.is_clean() {
//!     for finding in report.findings() {
//!         println!("{finding}");
//!     }
//!     let plan = report.repair_plan().unwrap();
//!     // Dry-run changes nothing on disk:
//!     let preview = plan.dry_run().unwrap();
//!     println!("would change {} bytes", preview.staged_len());
//!     // Explicitly apply, only if the file still matches the digest:
//!     plan.apply_to_file("foo.cfb", "foo.repaired.cfb").unwrap();
//! }
//! ```

mod analyze;
mod diagnose;
mod model;
mod sha256;

use std::collections::BTreeMap;
use std::fs;
use std::io::{self, Read, Seek, Write};
use std::path::Path;

use crate::internal::consts;

pub use model::{CorruptionKind, Finding, FindingLocation, Table};

/// 32-bit sentinel bytes used by repair patches, exposed for tests and
/// callers building their own byte-level reasoning.
pub(crate) const EOC: Vec<u8> = vec![0xfe, 0xff, 0xff, 0xff];
pub(crate) const FREE: Vec<u8> = vec![0xff, 0xff, 0xff, 0xff];

//===========================================================================//
// Digest
//===========================================================================//

/// A cryptographic summary of the exact input bytes a plan was made for.
///
/// Repair plans carry this precondition.  Applying a plan recomputes the
/// digest of the current input and refuses to write anything if it no longer
/// matches.  This turns "the file changed after the plan was made" into an
/// explicit, repeatable error instead of silently patching the wrong bytes.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct AuditDigest {
    sha256: [u8; 32],
    len: u64,
}

impl AuditDigest {
    fn of(data: &[u8]) -> AuditDigest {
        AuditDigest {
            sha256: sha256::sha256(data),
            len: data.len() as u64,
        }
    }

    /// The 32-byte SHA-256 hash of the summarized input.
    pub fn sha256(&self) -> [u8; 32] {
        self.sha256
    }

    /// The length in bytes of the summarized input.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns true only when the length is zero.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the lowercase hexadecimal SHA-256 digest.
    pub fn to_hex(&self) -> String {
        let mut out = String::with_capacity(64);
        for byte in self.sha256 {
            use std::fmt::Write as _;
            write!(out, "{byte:02x}").unwrap();
        }
        out
    }
}

impl std::fmt::Debug for AuditDigest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AuditDigest")
            .field("len", &self.len)
            .field("sha256", &self.to_hex())
            .finish()
    }
}
