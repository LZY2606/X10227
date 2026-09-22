// A small, dependency-free implementation of SHA-256 (FIPS 180-4).  The audit
// module uses it to fingerprint the exact bytes a repair plan was computed
// from, so that a plan can only be applied while the input is unchanged.

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Incremental SHA-256 hasher.
#[derive(Clone)]
pub struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffer_len: usize,
    total_len: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Sha256 {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f,
                0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
            ],
            buffer: [0u8; 64],
            buffer_len: 0,
            total_len: 0,
        }
    }
}

impl Sha256 {
    /// Feeds a chunk of input into the hasher.
    pub fn update(&mut self, data: &[u8]) {
        self.total_len = self.total_len.wrapping_add(data.len() as u64);
        let mut data = data;
        if self.buffer_len > 0 {
            let needed = 64 - self.buffer_len;
            let take = needed.min(data.len());
            self.buffer[self.buffer_len..self.buffer_len + take]
                .copy_from_slice(&data[..take]);
            self.buffer_len += take;
            data = &data[take..];
            if self.buffer_len == 64 {
                let block = self.buffer;
                self.process_block(&block);
                self.buffer_len = 0;
            }
        }
        while data.len() >= 64 {
            let mut block = [0u8; 64];
            block.copy_from_slice(&data[..64]);
            self.process_block(&block);
            data = &data[64..];
        }
        if !data.is_empty() {
            self.buffer[..data.len()].copy_from_slice(data);
            self.buffer_len = data.len();
        }
    }

    /// Returns the SHA-256 digest of everything fed in so far.  The hasher is
    /// not consumed: the padding applied here is computed on a clone, so the
    /// same hasher can keep being updated afterwards.
    pub fn finish(&self) -> [u8; 32] {
        let mut finalized = self.clone();
        let bit_len = finalized.total_len.wrapping_mul(8);
        finalized.buffer[finalized.buffer_len] = 0x80;
        for byte in finalized.buffer[finalized.buffer_len + 1..].iter_mut() {
            *byte = 0;
        }
        let mut block = finalized.buffer;
        if finalized.buffer_len >= 56 {
            finalized.process_block(&block);
            block = [0u8; 64];
        }
        block[56..64].copy_from_slice(&bit_len.to_be_bytes());
        finalized.process_block(&block);
        let mut digest = [0u8; 32];
        for (word, bytes) in finalized
            .state
            .iter()
            .zip(digest.chunks_exact_mut(4))
        {
            bytes.copy_from_slice(&word.to_be_bytes());
        }
        digest
    }

    /// Returns the lowercase hexadecimal encoding of the digest.
    pub fn hex_digest(&self) -> String {
        let digest = self.finish();
        let mut out = String::with_capacity(64);
        for byte in digest.iter() {
            out.push(std::char::from_digit((byte >> 4) as u32, 16).unwrap());
            out.push(std::char::from_digit((byte & 0xf) as u32, 16).unwrap());
        }
        out
    }

    fn process_block(&mut self, block: &[u8; 64]) {
        let mut words = [0u32; 64];
        for (index, bytes) in block.chunks_exact(4).enumerate() {
            words[index] = u32::from_be_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3],
            ]);
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }
        let mut working = self.state;
        for index in 0..64 {
            let s1 = working[4].rotate_right(6)
                ^ working[4].rotate_right(11)
                ^ working[4].rotate_right(25);
            let ch = (working[4] & working[5])
                ^ ((!working[4]) & working[6]);
            let temp1 = working[7]
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[index])
                .wrapping_add(words[index]);
            let s0 = working[0].rotate_right(2)
                ^ working[0].rotate_right(13)
                ^ working[0].rotate_right(22);
            let maj = (working[0] & working[1])
                ^ (working[0] & working[2])
                ^ (working[1] & working[2]);
            let temp2 = s0.wrapping_add(maj);
            working[7] = working[6];
            working[6] = working[5];
            working[5] = working[4];
            working[4] = working[3].wrapping_add(temp1);
            working[3] = working[2];
            working[2] = working[1];
            working[1] = working[0];
            working[0] = temp1.wrapping_add(temp2);
        }
        for (state, word) in self.state.iter_mut().zip(working.iter()) {
            *state = state.wrapping_add(*word);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Sha256;

    // Known-answer tests from FIPS 180-4 and NIST examples.
    #[test]
    fn known_answer_vectors() {
        let hash_of = |input: &[u8]| {
            let mut hasher = Sha256::default();
            // Feed at odd boundaries to exercise the buffering path.
            for chunk in input.chunks(7) {
                hasher.update(chunk);
            }
            hasher.hex_digest()
        };
        assert_eq!(
            hash_of(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hash_of(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            hash_of(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
    }

    #[test]
    fn update_is_order_dependent_and_incremental() {
        let mut all_at_once = Sha256::default();
        all_at_once.update(b"the quick brown fox");
        let mut piecemeal = Sha256::default();
        piecemeal.update(b"the quick ");
        piecemeal.update(b"brown fox");
        assert_eq!(all_at_once.finish(), piecemeal.finish());
    }
}
