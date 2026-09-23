//! A small deterministic identity for the exact bytes of an audited file.
//!
//! The digest is not cryptographic; it exists so that a [`super::RepairPlan`]
//! can prove the input it is about to be applied to is still the input the
//! plan was computed from.  FNV-1a (64-bit) is dependency-free and stable
//! across platforms and runs.

use std::fmt;
use std::io::{self, Read, Seek};

/// Identity of one exact sequence of input bytes.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub struct AuditDigest(u64);

impl AuditDigest {
    /// Computes the digest of a byte slice.
    pub fn of_bytes(bytes: &[u8]) -> AuditDigest {
        let mut hasher = Fnv1a64(0xcbf29ce484222325);
        hasher.update(bytes);
        AuditDigest(hasher.0)
    }

    /// Reads `reader` from its current position to the end and digests it.
    pub fn of_reader<F: Read + Seek>(mut reader: F) -> io::Result<AuditDigest> {
        reader.seek(io::SeekFrom::Start(0))?;
        let mut hasher = Fnv1a64(0xcbf29ce484222325);
        let mut buffer = [0u8; 4096];
        loop {
            let count = reader.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
        }
        Ok(AuditDigest(hasher.0))
    }
}

impl fmt::Debug for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AuditDigest({:016x})", self.0)
    }
}

impl fmt::Display for AuditDigest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

struct Fnv1a64(u64);

impl Fnv1a64 {
    fn update(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.0 ^= byte as u64;
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
}
