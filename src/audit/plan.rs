//! Read-only repair plans and their content-digest gate.

use std::io::{self, Read, Seek, SeekFrom, Write};

use fnv::FnvHasher;
use std::hash::Hasher;


//===========================================================================//

/// Content identity of audited bytes: length plus a 64-bit FNV-1a hash.
///
/// A [`RepairPlan`] only applies while the current file still has this
/// digest, so a file changed after planning is never silently "repaired"
/// against stale assumptions.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Digest {
    len: u64,
    hash: u64,
}

impl Digest {
    pub(crate) fn of_bytes(data: &[u8]) -> Digest {
        let mut hasher = FnvHasher::default();
        hasher.write(data);
        Digest { len: data.len() as u64, hash: hasher.finish() }
    }

    /// Streams a digest over any reader without retaining the file contents.
    pub(crate) fn of_reader<F: Read + Seek>(
        reader: &mut F,
    ) -> io::Result<Digest> {
        let len = reader.seek(SeekFrom::End(0))?;
        reader.seek(SeekFrom::Start(0))?;
        let mut hasher = FnvHasher::default();
        let mut buf = [0u8; 8192];
        loop {
            let n = reader.read(&mut buf)?;
            if n == 0 {
                break;
            }
            hasher.write(&buf[..n]);
        }
        Ok(Digest { len, hash: hasher.finish() })
    }

    /// Audited file length in bytes.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Returns whether the audited input was empty (never the case for a CFB
    /// file, but provided for completeness).
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Opaque fingerprint bytes (length + FNV-1a hash), stable across runs.
    pub fn fingerprint(&self) -> [u8; 16] {
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&self.len.to_le_bytes());
        out[8..].copy_from_slice(&self.hash.to_le_bytes());
        out
    }
}

//===========================================================================//

/// A single byte-level repair: overwrite the (FAT/MiniFAT/directory) cell at
/// `offset` with `new_bytes`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStep {
    pub(crate) offset: u64,
    pub(crate) old_bytes: Vec<u8>,
    pub(crate) new_bytes: Vec<u8>,
    pub(crate) description: String,
}

impl RepairStep {
    /// File offset of the patched cell.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Bytes that the cell will contain after applying.
    pub fn new_bytes(&self) -> &[u8] {
        &self.new_bytes
    }

    /// Human-readable description of what this step repairs.
    pub fn description(&self) -> &str {
        &self.description
    }
}

/// Read-only view of a repair step, used by [`RepairPlan::preview`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepairStepView<'a> {
    pub(crate) step: &'a RepairStep,
}

impl<'a> RepairStepView<'a> {
    /// File offset of the patched cell.
    pub fn offset(&self) -> u64 {
        self.step.offset
    }

    /// Bytes that the cell will contain after applying.
    pub fn new_bytes(&self) -> &[u8] {
        &self.step.new_bytes
    }

    /// Human-readable description.
    pub fn description(&self) -> &str {
        &self.step.description
    }
}

//===========================================================================//

/// Outcome of attempting to apply a plan.
#[derive(Debug)]
pub enum ApplyOutcome {
    /// All steps applied and the post-write digest changed exactly as planned.
    Applied {
        /// Digest of the bytes now on disk.
        new_digest: Digest,
    },
    /// The file changed after the plan was made; nothing was written.
    Stale,
}

//===========================================================================//

/// A read-only, content-bound plan for repairing the evidence in one
/// [`AuditReport`].
///
/// The plan is a value type with no I/O handles and no shared/global state:
/// building it and previewing it never touches the file.  Writes happen only
/// in [`RepairPlan::apply`], which verifies the prerequisite digest first.
#[derive(Clone, Debug)]
pub struct RepairPlan {
    pub(crate) prerequisite: Digest,
    pub(crate) steps: Vec<RepairStep>,
}

impl RepairPlan {
    pub(crate) fn from_parts(
        prerequisite: Digest,
        steps: Vec<RepairStep>,
    ) -> RepairPlan {
        RepairPlan { prerequisite, steps }
    }

    /// Digest the file must still have for this plan to apply.
    pub fn prerequisite_digest(&self) -> &Digest {
        &self.prerequisite
    }

    /// Number of byte-level patches.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Returns true if the plan contains no patches.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// Read-only preview of every patch.  This method never writes.
    pub fn preview(&self) -> Vec<RepairStepView<'_>> {
        self.steps.iter().map(|step| RepairStepView { step }).collect()
    }

    /// Applies the plan, but only if the current file still matches the
    /// prerequisite digest.
    ///
    /// Every patched cell is journaled (offset plus original bytes) before
    /// any write; if a write fails, already-written cells are restored in
    /// reverse order and the error propagates, so a failed call leaves the
    /// input byte-for-byte unchanged.  No temp files or background work are
    /// used.  After a failure the unchanged bytes still match the
    /// prerequisite digest, so the exact same plan can be retried.
    pub fn apply<F: Read + Write + Seek>(
        &self,
        mut file: F,
    ) -> io::Result<ApplyOutcome> {
        let current = Digest::of_reader(&mut file)?;
        if current != self.prerequisite {
            return Ok(ApplyOutcome::Stale);
        }
        if self.steps.is_empty() {
            return Ok(ApplyOutcome::Applied { new_digest: current });
        }

        // Journal and verify each target cell before mutating anything.
        let mut journal: Vec<(u64, Vec<u8>)> = Vec::with_capacity(self.steps.len());
        for step in self.steps.iter() {
            file.seek(SeekFrom::Start(step.offset))?;
            let mut original = vec![0u8; step.new_bytes.len()];
            file.read_exact(&mut original)?;
            // The digest gate already proves identity; this guards against
            // two steps targeting overlapping cells in one plan.
            if original != step.old_bytes {
                invalid_data!(
                    "Repair step at {} does not match the audited bytes",
                    step.offset
                );
            }
            journal.push((step.offset, original));
        }

        // Apply all patches; on the first write error roll back in reverse.
        let applied = match Self::write_all(&mut file, &self.steps) {
            Ok(()) => journal.len(),
            Err(err) => {
                let mut rolled_back = 0;
                for (offset, original) in journal.iter().rev() {
                    file.seek(SeekFrom::Start(*offset))?;
                    if let Err(rollback_err) = file.write_all(original) {
                        return Err(io::Error::other(format!(
                            "repair failed ({err}) and rollback also failed \
                             ({rollback_err})"
                        )));
                    }
                    rolled_back += 1;
                }
                debug_assert_eq!(rolled_back, journal.len());
                file.flush()?;
                return Err(err);
            }
        };
        debug_assert_eq!(applied, self.steps.len());
        file.flush()?;

        // Confirm the bytes now on disk are exactly the intended patches.
        let new_digest = Digest::of_reader(&mut file)?;
        for step in self.steps.iter() {
            file.seek(SeekFrom::Start(step.offset))?;
            let mut actual = vec![0u8; step.new_bytes.len()];
            file.read_exact(&mut actual)?;
            if actual != step.new_bytes {
                // Post-write inconsistency: roll back and surface an error
                // rather than claiming success on a half-patched file.
                for (offset, original) in journal.iter().rev() {
                    file.seek(SeekFrom::Start(*offset))?;
                    file.write_all(original)?;
                }
                file.flush()?;
                invalid_data!(
                    "Post-repair verification failed at offset {}",
                    step.offset
                );
            }
        }
        Ok(ApplyOutcome::Applied { new_digest })
    }

    fn write_all<F: Write + Seek>(
        file: &mut F,
        steps: &[RepairStep],
    ) -> io::Result<()> {
        for step in steps {
            file.seek(SeekFrom::Start(step.offset))?;
            file.write_all(&step.new_bytes)?;
        }
        Ok(())
    }
}

