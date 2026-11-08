// SPDX-License-Identifier: Apache-2.0
//! An **RRR compressed bitvector** (Raman, Raman and Rao 2002): `rank`, `access` and `select` over
//! a bitvector stored in about `n H0(B) + 0.13 n` bits. Navarro, *Compact Data Structures*, §4.1.1
//! and §4.2.3. Blocks of 63 bits store a 6-bit class and a `⌈log2 C(63, c)⌉`-bit offset;
//! every 32 blocks a sample holds the rank so far and the offset position.
//! No Lean model. Positions are at most `u32::MAX`.

use crate::strings::bits::{partition_point, read_bits, select_in_word, write_bits};

/// Bits per block. `63`, so that a class fits six bits exactly and every offset fits a `u64`.
pub const BLOCK_BITS: usize = 63;

/// Blocks per superblock: one rank sample and one offset pointer per this many blocks.
pub const SUPERBLOCK_BLOCKS: usize = 32;

/// Bits per class cell: `⌈log2(BLOCK_BITS + 1)⌉`.
const CLASS_BITS: u32 = 6;

/// Bits per superblock.
const SUPERBLOCK_BITS: usize = BLOCK_BITS * SUPERBLOCK_BLOCKS;

#[cfg(test)]
thread_local! {
    /// Calls to `Rrr::rank` on this thread, for `fm_index`'s `locate` cost tests.
    pub(crate) static RANKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Block seeks on this thread, each followed by one block decode.
    pub(crate) static SEEKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `BINOMIAL[i][j] = C(i, j)` for `i, j ≤ 63`, zero when `j > i`; every entry fits a `u64`.
// A `static`, not a `const`: 32 KiB is too large to inline at every use.
static BINOMIAL: [[u64; BLOCK_BITS + 1]; BLOCK_BITS + 1] = binomials();

/// `OFFSET_BITS[c] = ⌈log2 C(63, c)⌉`: the width of a class-`c` offset (Navarro's array `L`).
const OFFSET_BITS: [u32; BLOCK_BITS + 1] = offset_widths();

const fn binomials() -> [[u64; BLOCK_BITS + 1]; BLOCK_BITS + 1] {
    let mut table = [[0u64; BLOCK_BITS + 1]; BLOCK_BITS + 1];
    let mut i = 0;
    while i <= BLOCK_BITS {
        table[i][0] = 1;
        let mut j = 1;
        while j <= i {
            table[i][j] = table[i - 1][j - 1] + if j < i { table[i - 1][j] } else { 0 };
            j += 1;
        }
        i += 1;
    }
    table
}

const fn offset_widths() -> [u32; BLOCK_BITS + 1] {
    // Not `BINOMIAL`: a `const` may not read a `static` before Rust 1.83 (the MSRV is 1.82).
    let table = binomials();
    let mut widths = [0u32; BLOCK_BITS + 1];
    let mut c = 0;
    while c <= BLOCK_BITS {
        let count = table[BLOCK_BITS][c];
        // Offsets run 0..count, so they need ⌈log2 count⌉ bits: none when count is 1.
        widths[c] = if count <= 1 {
            0
        } else {
            64 - (count - 1).leading_zeros()
        };
        c += 1;
    }
    widths
}

/// The offset of a block of class `class`: its rank among the class's blocks, ordered as
/// integers read from the block's first bit (the most significant) to its last. Navarro's
/// Algorithm 4.1, `encode`. Bit `k` of `block` is the block's `k`-th bit.
fn encode(block: u64, class: u32) -> u64 {
    let mut offset = 0u64;
    let mut left = class as usize;
    let mut pos = 0;
    // Once `left` equals the positions remaining, they are all ones and add nothing.
    while left > 0 && left < BLOCK_BITS - pos {
        if (block >> pos) & 1 == 1 {
            offset += BINOMIAL[BLOCK_BITS - pos - 1][left];
            left -= 1;
        }
        pos += 1;
    }
    offset
}

/// The first `upto` bits of the block with class `class` and offset `offset` -- Navarro's
/// Algorithm 4.1, `decode`, stopped early. Bit `k` of the result is the block's `k`-th bit; bits
/// at or past `upto` are zero.
#[inline]
fn decode(class: u32, mut offset: u64, upto: usize) -> u64 {
    let mut block = 0u64;
    let mut left = class as usize;
    let mut pos = 0;
    while pos < upto && left > 0 {
        let remaining = BLOCK_BITS - pos;
        if left == remaining {
            // Every remaining position is a one.
            block |= prefix_mask(upto) & !prefix_mask(pos);
            break;
        }
        let skip = BINOMIAL[remaining - 1][left];
        if offset >= skip {
            block |= 1u64 << pos;
            offset -= skip;
            left -= 1;
        }
        pos += 1;
    }
    block
}

/// The low `k` bits set, for `k ≤ 64`.
#[inline]
fn prefix_mask(k: usize) -> u64 {
    if k >= 64 {
        u64::MAX
    } else {
        (1u64 << k) - 1
    }
}

/// One superblock's sample: the rank before it and where its first offset begins.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Sample {
    /// Set bits strictly before the superblock.
    rank: u32,
    /// Bit position of the superblock's first offset in the offset stream.
    pointer: u32,
}

/// An RRR compressed bitvector with `rank`, `access` and `select`.
#[derive(Clone, PartialEq, Eq)]
pub struct Rrr {
    /// Bits indexed.
    len: usize,
    /// Set bits in all.
    ones: usize,
    /// Class of each block, [`CLASS_BITS`] bits per cell.
    classes: Vec<u64>,
    /// Every block's offset, concatenated, each in `OFFSET_BITS[class]` bits.
    offsets: Vec<u64>,
    /// One sample per superblock, plus a final one for the end.
    samples: Vec<Sample>,
}

impl Rrr {
    /// Compress the first `len` bits of `bits`, bit `i` being bit `i % 64` of word `i / 64`.
    ///
    /// Bits at or above `len` in the last word are ignored. `O(len)`.
    ///
    /// # Panics
    ///
    /// If `len` exceeds the bits `bits` holds, or `u32::MAX`.
    #[must_use]
    pub fn new(bits: &[u64], len: usize) -> Rrr {
        assert!(
            len <= bits.len() * 64,
            "rrr: len {len} exceeds the {} bits supplied",
            bits.len() * 64
        );
        assert!(
            u32::try_from(len).is_ok(),
            "rrr: one bitvector covers at most u32::MAX positions; shard"
        );
        let blocks = len.div_ceil(BLOCK_BITS);
        let mut classes = vec![0u64; (blocks * CLASS_BITS as usize).div_ceil(64)];
        let mut offsets: Vec<u64> = Vec::new();
        let mut samples = Vec::with_capacity(blocks / SUPERBLOCK_BLOCKS + 2);
        // No offset exceeds 60 bits per 63-bit block, so the stream stays below 2^32 bits.
        let (mut ones, mut pointer) = (0usize, 0usize);
        for t in 0..blocks {
            if t % SUPERBLOCK_BLOCKS == 0 {
                samples.push(Sample {
                    rank: u32::try_from(ones).expect("ones <= len <= u32::MAX"),
                    pointer: u32::try_from(pointer).expect("offset stream fits u32"),
                });
            }
            let start = t * BLOCK_BITS;
            let width = u32::try_from(BLOCK_BITS.min(len - start)).expect("at most BLOCK_BITS");
            let block = read_bits(bits, start, width);
            let class = block.count_ones();
            write_bits(
                &mut classes,
                t * CLASS_BITS as usize,
                CLASS_BITS,
                u64::from(class),
            );
            let offset_width = OFFSET_BITS[class as usize];
            write_bits(&mut offsets, pointer, offset_width, encode(block, class));
            pointer += offset_width as usize;
            ones += class as usize;
        }
        // The end sample lets `select` binary-search the samples without a special case.
        samples.push(Sample {
            rank: u32::try_from(ones).expect("ones <= len <= u32::MAX"),
            pointer: u32::try_from(pointer).expect("offset stream fits u32"),
        });
        // One spare word, so `read_bits` may always look one word past a field's start.
        offsets.push(0);
        Rrr {
            len,
            ones,
            classes,
            offsets,
            samples,
        }
    }

    /// Compress a bitvector given as booleans.
    #[must_use]
    pub fn from_bools(bits: &[bool]) -> Rrr {
        let mut words = vec![0u64; bits.len().div_ceil(64)];
        for (i, &b) in bits.iter().enumerate() {
            words[i / 64] |= u64::from(b) << (i % 64);
        }
        Rrr::new(&words, bits.len())
    }

    /// Bits indexed.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the bitvector is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Set bits in the whole bitvector.
    #[must_use]
    pub fn count_ones(&self) -> usize {
        self.ones
    }

    #[inline]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "a class is `CLASS_BITS` bits wide"
    )]
    fn class(&self, block: usize) -> u32 {
        read_bits(&self.classes, block * CLASS_BITS as usize, CLASS_BITS) as u32
    }

    /// The rank before `block`, its class and its offset, walked from its superblock's sample
    /// (Navarro's Algorithm 4.5).
    #[inline]
    fn seek(&self, block: usize) -> (usize, u32, u64) {
        #[cfg(test)]
        SEEKS.with(|s| s.set(s.get() + 1));
        let sample = self.samples[block / SUPERBLOCK_BLOCKS];
        let (mut rank, mut pointer) = (sample.rank as usize, sample.pointer as usize);
        for t in (block / SUPERBLOCK_BLOCKS) * SUPERBLOCK_BLOCKS..block {
            let class = self.class(t);
            rank += class as usize;
            pointer += OFFSET_BITS[class as usize] as usize;
        }
        let class = self.class(block);
        let offset = read_bits(&self.offsets, pointer, OFFSET_BITS[class as usize]);
        (rank, class, offset)
    }

    /// Set bits strictly before position `i`, saturating at `len`. At most 31 class reads, then
    /// one partial decode.
    #[must_use]
    pub fn rank(&self, i: usize) -> usize {
        #[cfg(test)]
        RANKS.with(|r| r.set(r.get() + 1));
        if i >= self.len {
            return self.ones;
        }
        let (block, within) = (i / BLOCK_BITS, i % BLOCK_BITS);
        if within == 0 && block % SUPERBLOCK_BLOCKS == 0 {
            return self.samples[block / SUPERBLOCK_BLOCKS].rank as usize;
        }
        let (rank, class, offset) = self.seek(block);
        rank + decode(class, offset, within).count_ones() as usize
    }

    /// Whether bit `i` is set; `false` at or past `len`.
    #[must_use]
    pub fn get(&self, i: usize) -> bool {
        if i >= self.len {
            return false;
        }
        let (block, within) = (i / BLOCK_BITS, i % BLOCK_BITS);
        let (_, class, offset) = self.seek(block);
        (decode(class, offset, within + 1) >> within) & 1 == 1
    }

    /// Bit `i` and the number of positions before `i` that hold the same bit, in one decode.
    ///
    /// # Panics
    ///
    /// If `i >= len`.
    #[must_use]
    pub fn access_rank(&self, i: usize) -> (bool, usize) {
        assert!(i < self.len, "rrr::access_rank: {i} is past the end");
        let (block, within) = (i / BLOCK_BITS, i % BLOCK_BITS);
        let (rank, class, offset) = self.seek(block);
        let bits = decode(class, offset, within + 1);
        let ones = rank + (bits & prefix_mask(within)).count_ones() as usize;
        if (bits >> within) & 1 == 1 {
            (true, ones)
        } else {
            (false, i - ones)
        }
    }

    /// Position of the `j`-th (zero-based) set bit, or `None` when there are not `j + 1`.
    ///
    /// Binary search over the samples, a class scan, one decode.
    #[must_use]
    pub fn select1(&self, j: usize) -> Option<usize> {
        self.select(j, true)
    }

    /// Position of the `j`-th (zero-based) clear bit, or `None` when there are not `j + 1`.
    #[must_use]
    pub fn select0(&self, j: usize) -> Option<usize> {
        self.select(j, false)
    }

    fn select(&self, j: usize, bit: bool) -> Option<usize> {
        let total = if bit { self.ones } else { self.len - self.ones };
        if j >= total {
            return None;
        }
        // Bits of the sought value before superblock `s`.
        let before = |s: usize| -> usize {
            let rank = self.samples[s].rank as usize;
            if bit {
                rank
            } else {
                (s * SUPERBLOCK_BITS).min(self.len) - rank
            }
        };
        // The last superblock whose count-before is at most `j`. Sample 0 counts 0, and the end
        // sample counts `total > j`, so the answer lies strictly before the end sample.
        let supers = self.samples.len() - 1;
        let s = partition_point(supers, |s| before(s) <= j) - 1;
        let mut seen = before(s);
        let mut pointer = self.samples[s].pointer as usize;
        let first = s * SUPERBLOCK_BLOCKS;
        let last = (first + SUPERBLOCK_BLOCKS).min(self.len.div_ceil(BLOCK_BITS));
        for t in first..last {
            let class = self.class(t);
            let width = BLOCK_BITS.min(self.len - t * BLOCK_BITS);
            let here = if bit {
                class as usize
            } else {
                width - class as usize
            };
            if seen + here > j {
                let offset = read_bits(&self.offsets, pointer, OFFSET_BITS[class as usize]);
                let mut block = decode(class, offset, width);
                if !bit {
                    block = !block & prefix_mask(width);
                }
                #[allow(
                    clippy::cast_possible_truncation,
                    reason = "j - seen < here <= BLOCK_BITS"
                )]
                let within = (j - seen) as u32;
                return Some(t * BLOCK_BITS + select_in_word(block, within) as usize);
            }
            seen += here;
            pointer += OFFSET_BITS[class as usize] as usize;
        }
        None
    }

    /// Bytes allocated: the class cells, the offset stream and the samples.
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        (self.classes.len() + self.offsets.len()) * size_of::<u64>()
            + self.samples.len() * size_of::<Sample>()
    }
}

impl std::fmt::Debug for Rrr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Rrr")
            .field("len", &self.len)
            .field("ones", &self.ones)
            .field("size_bytes", &self.size_bytes())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "unit_tests/rrr.rs"]
mod tests;
