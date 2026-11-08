// SPDX-License-Identifier: Apache-2.0
//! Rank/select/occ: one two-level counting directory over bits ([`BitIndex`]) and over bytes
//! ([`ByteIndex`], per symbol of an [`Alphabet`]). A `u32` count per superblock of 4096, a `u16`
//! per block of 512, one select sample per 8192 set bits. `rank` and `occ` are O(1), `select`
//! O(log n); out-of-range positions saturate.
//!
//! Lean: `RankSelect/` (`occ_eq_rank`, `rank_select`) and `RankSelect/Directory.lean`
//! (`rankTwoLevel_eq`, `occTwoLevel_eq`).

use crate::strings::bits::select_in_word;

/// Positions per superblock.
const SUPERBLOCK: usize = 4096;
/// Positions per block, [`ByteIndex`]'s default.
pub const DEFAULT_BLOCK: usize = 512;
const WORD: usize = 64;
const WORDS_PER_BLOCK: usize = DEFAULT_BLOCK / WORD;
/// One `select` sample per this many set positions.
const SELECT_SAMPLE: usize = 8192;

const SUPERBLOCK_FITS_U16: () = assert!(SUPERBLOCK <= u16::MAX as usize);

/// The directory over set positions. `BLOCK` must divide [`SUPERBLOCK`].
#[derive(Clone)]
struct TwoLevel<const BLOCK: usize> {
    /// Set positions strictly before each superblock.
    superblocks: Vec<u32>,
    /// Set positions strictly before each block, relative to its superblock.
    blocks: Vec<u16>,
    /// `samples[k]` is the block holding set position number `k * SELECT_SAMPLE`.
    samples: Vec<u32>,
    total: usize,
}

impl<const BLOCK: usize> TwoLevel<BLOCK> {
    const BLOCKS_PER_SUPERBLOCK: usize = SUPERBLOCK / BLOCK;

    const BLOCK_DIVIDES_SUPERBLOCK: () = assert!(BLOCK > 0 && SUPERBLOCK % BLOCK == 0);

    /// Build the directory from one count per block.
    fn from_block_counts(block_counts: &[u32]) -> TwoLevel<BLOCK> {
        let () = SUPERBLOCK_FITS_U16;
        let () = Self::BLOCK_DIVIDES_SUPERBLOCK;
        let nsuper = block_counts.len().div_ceil(Self::BLOCKS_PER_SUPERBLOCK);
        let mut superblocks: Vec<u32> = Vec::with_capacity(nsuper);
        let mut blocks: Vec<u16> = Vec::with_capacity(block_counts.len());
        let mut samples: Vec<u32> = Vec::new();
        let mut total: usize = 0;
        let mut next_sample: usize = 0;
        for (b, &count) in block_counts.iter().enumerate() {
            if b % Self::BLOCKS_PER_SUPERBLOCK == 0 {
                superblocks.push(
                    u32::try_from(total).expect("one index holds at most u32::MAX set positions"),
                );
            }
            let relative = total - superblocks[b / Self::BLOCKS_PER_SUPERBLOCK] as usize;
            blocks.push(u16::try_from(relative).expect("relative count <= SUPERBLOCK <= u16::MAX"));
            while next_sample < total + count as usize {
                samples.push(u32::try_from(b).expect("fewer than 2^32 blocks"));
                next_sample += SELECT_SAMPLE;
            }
            total += count as usize;
        }
        TwoLevel {
            superblocks,
            blocks,
            samples,
            total,
        }
    }

    /// Set positions strictly before the start of `block`: the two-level sum.
    fn count_before_block(&self, block: usize) -> usize {
        self.superblocks[block / Self::BLOCKS_PER_SUPERBLOCK] as usize + self.blocks[block] as usize
    }

    fn count_before_block_or_total(&self, block: usize) -> usize {
        if block == self.blocks.len() {
            self.total
        } else {
            self.count_before_block(block)
        }
    }

    /// The block holding set position number `j`: samples narrow, then two binary searches.
    fn locate(&self, j: usize) -> Option<usize> {
        if j >= self.total {
            return None;
        }
        let k = j / SELECT_SAMPLE;
        let lo_block = self.samples[k] as usize;
        let hi_block = self
            .samples
            .get(k + 1)
            .map_or(self.blocks.len() - 1, |&b| b as usize);
        let (lo_super, hi_super) = (
            lo_block / Self::BLOCKS_PER_SUPERBLOCK,
            hi_block / Self::BLOCKS_PER_SUPERBLOCK,
        );
        // The last superblock whose count is <= j; the sampled one qualifies.
        let s = lo_super
            + self.superblocks[lo_super..=hi_super].partition_point(|&c| c as usize <= j)
            - 1;
        let base = self.superblocks[s] as usize;
        let first = s * Self::BLOCKS_PER_SUPERBLOCK;
        let last = (first + Self::BLOCKS_PER_SUPERBLOCK).min(self.blocks.len());
        // The last block in it whose count is <= j; the first block qualifies.
        Some(first + self.blocks[first..last].partition_point(|&c| base + c as usize <= j) - 1)
    }

    fn overhead_bytes(&self) -> usize {
        self.superblocks.len() * size_of::<u32>()
            + self.blocks.len() * size_of::<u16>()
            + self.samples.len() * size_of::<u32>()
    }
}

/// The effective alphabet of a text: the byte values present, mapped to dense indices in
/// ascending byte order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alphabet {
    to_dense: [Option<u8>; 256],
    symbols: Vec<u8>,
}

impl Alphabet {
    /// The effective alphabet of `text`: every byte value occurring in it, ascending. `O(n)`.
    #[must_use]
    pub fn of(text: &[u8]) -> Alphabet {
        let mut present = [false; 256];
        for &b in text {
            present[b as usize] = true;
        }
        let symbols: Vec<u8> = (0..=u8::MAX).filter(|&b| present[b as usize]).collect();
        let mut to_dense = [None; 256];
        for (dense, &b) in (0..=u8::MAX).zip(&symbols) {
            to_dense[b as usize] = Some(dense);
        }
        Alphabet { to_dense, symbols }
    }

    /// Number of distinct symbols, `σ`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Whether the text was empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Dense index of `byte`, or `None` when it does not occur in the text.
    #[must_use]
    pub fn index_of(&self, byte: u8) -> Option<usize> {
        self.to_dense[byte as usize].map(usize::from)
    }

    /// The byte value at dense index `dense`, or `None` when `dense >= len()`.
    #[must_use]
    pub fn symbol(&self, dense: usize) -> Option<u8> {
        self.symbols.get(dense).copied()
    }

    /// Every symbol, ascending.
    #[must_use]
    pub fn symbols(&self) -> &[u8] {
        &self.symbols
    }

    /// Whether `byte` occurs in the text this alphabet was built from.
    #[must_use]
    pub fn contains(&self, byte: u8) -> bool {
        self.to_dense[byte as usize].is_some()
    }
}

/// `rank` and `select` over a bitvector.
#[derive(Clone)]
pub struct BitIndex {
    words: Vec<u64>,
    len: usize,
    index: TwoLevel<DEFAULT_BLOCK>,
}

impl BitIndex {
    /// Index the first `len` bits of `bits`, bit `i` being bit `i % 64` of word `i / 64`.
    ///
    /// # Panics
    ///
    /// If `len` exceeds the bits `bits` holds, or is more than `u32::MAX`.
    #[must_use]
    pub fn new(bits: &[u64], len: usize) -> BitIndex {
        assert!(
            len <= bits.len() * WORD,
            "len {len} exceeds the {} bits supplied",
            bits.len() * WORD
        );
        assert!(
            u32::try_from(len).is_ok(),
            "one index covers at most u32::MAX positions; shard"
        );
        let mut words = bits[..len.div_ceil(WORD)].to_vec();
        if len % WORD != 0 {
            let last = words.len() - 1;
            words[last] &= (1u64 << (len % WORD)) - 1;
        }
        let block_counts: Vec<u32> = words
            .chunks(WORDS_PER_BLOCK)
            .map(|block| block.iter().map(|w| w.count_ones()).sum())
            .collect();
        let index = TwoLevel::from_block_counts(&block_counts);
        BitIndex { words, len, index }
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

    /// Whether bit `i` is set; `false` at or past `len`.
    #[must_use]
    pub fn get(&self, i: usize) -> bool {
        i < self.len && (self.words[i / WORD] >> (i % WORD)) & 1 == 1
    }

    /// Set bits strictly before position `i`, in `O(1)`. Saturates at `len`.
    #[must_use]
    pub fn rank(&self, i: usize) -> usize {
        let i = i.min(self.len);
        if i == self.len {
            return self.index.total;
        }
        let block = i / DEFAULT_BLOCK;
        let (first_word, last_word) = (block * WORDS_PER_BLOCK, i / WORD);
        let whole: u32 = self.words[first_word..last_word]
            .iter()
            .map(|w| w.count_ones())
            .sum();
        let partial = (self.words[last_word] & ((1u64 << (i % WORD)) - 1)).count_ones();
        self.index.count_before_block(block) + whole as usize + partial as usize
    }

    /// Position of the `j`-th set bit, zero-based, if any. `O(log n)`.
    #[must_use]
    pub fn select(&self, j: usize) -> Option<usize> {
        let block = self.index.locate(j)?;
        let mut rest = j - self.index.count_before_block(block);
        let first_word = block * WORDS_PER_BLOCK;
        let last_word = (first_word + WORDS_PER_BLOCK).min(self.words.len());
        for (offset, &w) in self.words[first_word..last_word].iter().enumerate() {
            let count = w.count_ones() as usize;
            if rest < count {
                #[allow(clippy::cast_possible_truncation, reason = "rest < count <= 64")]
                let rest = rest as u32;
                return Some((first_word + offset) * WORD + select_in_word(w, rest) as usize);
            }
            rest -= count;
        }
        None
    }

    /// Bytes the directory costs, the bitvector itself excluded.
    #[must_use]
    pub fn overhead_bytes(&self) -> usize {
        self.index.overhead_bytes()
    }
}

/// `occ` over a text: one directory per symbol, and a scan of at most `BLOCK / 2` bytes from
/// the nearer checkpoint. Lean: `occ_eq_rank`.
#[derive(Clone)]
pub struct ByteIndex<const BLOCK: usize = DEFAULT_BLOCK> {
    bytes: Vec<u8>,
    alphabet: Alphabet,
    index: Vec<TwoLevel<BLOCK>>,
}

impl ByteIndex {
    /// Index `bytes` over `alphabet` at the shipped block width, [`DEFAULT_BLOCK`].
    #[must_use]
    pub fn new(bytes: &[u8], alphabet: &Alphabet) -> ByteIndex {
        ByteIndex::new_over_blocks(bytes, alphabet)
    }
}

/// Occurrences of `c` in `bytes`, tallied in a `u8` per 255-byte chunk so it vectorises.
fn count_byte(bytes: &[u8], c: u8) -> usize {
    #[cfg(test)]
    SCANNED.with(|s| s.set(s.get() + bytes.len()));
    bytes
        .chunks(TALLY_CHUNK)
        .map(|chunk| usize::from(tally(chunk, c)))
        .sum()
}

const TALLY_CHUNK: usize = u8::MAX as usize;

fn tally(chunk: &[u8], c: u8) -> u8 {
    chunk.iter().fold(0u8, |acc, &b| acc + u8::from(b == c))
}

#[cfg(test)]
thread_local! {
    /// Bytes `count_byte` has scanned on this thread.
    static SCANNED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl<const BLOCK: usize> ByteIndex<BLOCK> {
    /// Index `bytes` over `alphabet` at a chosen block width. `O(n + σ · n / BLOCK)`.
    ///
    /// # Panics
    ///
    /// If `bytes` is longer than `u32::MAX`.
    #[must_use]
    pub fn new_over_blocks(bytes: &[u8], alphabet: &Alphabet) -> ByteIndex<BLOCK> {
        assert!(
            u32::try_from(bytes.len()).is_ok(),
            "one index covers at most u32::MAX positions; shard"
        );
        let (sigma, nblocks) = (alphabet.len(), bytes.len().div_ceil(BLOCK));
        let mut counts = vec![0u32; sigma * nblocks];
        for (i, &byte) in bytes.iter().enumerate() {
            if let Some(dense) = alphabet.index_of(byte) {
                counts[dense * nblocks + i / BLOCK] += 1;
            }
        }
        let index = (0..sigma)
            .map(|dense| {
                TwoLevel::from_block_counts(&counts[dense * nblocks..(dense + 1) * nblocks])
            })
            .collect();
        ByteIndex {
            bytes: bytes.to_vec(),
            alphabet: alphabet.clone(),
            index,
        }
    }

    /// Occurrences of `c` strictly before position `i`, in `O(1)`. Saturates at the text length.
    #[must_use]
    pub fn occ(&self, c: u8, i: usize) -> usize {
        let i = i.min(self.bytes.len());
        let Some(dense) = self.alphabet.index_of(c) else {
            return 0;
        };
        let index = &self.index[dense];
        if i == self.bytes.len() {
            return index.total;
        }
        let block = i / BLOCK;
        let start = block * BLOCK;
        let end = (start + BLOCK).min(self.bytes.len());
        let before = index.count_before_block(block);
        let after = index.count_before_block_or_total(block + 1);
        if before == after {
            return before;
        }
        if i - start <= (end - start) / 2 {
            before + count_byte(&self.bytes[start..i], c)
        } else {
            after - count_byte(&self.bytes[i..end], c)
        }
    }

    /// The indexed text.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// The effective alphabet this index was built over.
    #[must_use]
    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    /// Positions indexed.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Whether the text is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Positions per block, `BLOCK`.
    #[must_use]
    pub fn block_size(&self) -> usize {
        BLOCK
    }

    /// Bytes the directories cost, the text itself excluded.
    #[must_use]
    pub fn overhead_bytes(&self) -> usize {
        self.index
            .iter()
            .map(TwoLevel::<BLOCK>::overhead_bytes)
            .sum()
    }
}

impl std::fmt::Debug for BitIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitIndex")
            .field("len", &self.len)
            .field("overhead_bytes", &self.overhead_bytes())
            .finish_non_exhaustive()
    }
}

impl<const BLOCK: usize> std::fmt::Debug for ByteIndex<BLOCK> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ByteIndex")
            .field("len", &self.len())
            .field("block", &BLOCK)
            .field("alphabet", &self.alphabet)
            .field("overhead_bytes", &self.overhead_bytes())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "unit_tests/count_index.rs"]
mod tests;
