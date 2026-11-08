// SPDX-License-Identifier: Apache-2.0
//! The compressed FM-index's `occ` structure: the last column cut into **chunks of fixed
//! length**, each its own Huffman-shaped wavelet tree over plain bitvectors, plus a table `R` of
//! the ranks at every chunk's start (a final row holds the totals). Space `n H_k(T) + b σ^k` bits
//! for every `k` at once. Navarro, *Compact Data Structures* §11.3.3; Kärkkäinen and Puglisi
//! (SPIRE 2011). No Lean model.

use crate::strings::count_index::{Alphabet, BitIndex};
use crate::strings::wavelet_tree::{RankBits, WaveletTree};

#[cfg(test)]
thread_local! {
    /// Calls to `rank` and `access_rank` on this thread, for tests.
    pub(crate) static OCC_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The last column in fixed-length chunks, a Huffman-shaped wavelet tree per chunk over
/// bitvector `B`.
#[derive(Clone)]
pub struct ChunkedWavelet<B: RankBits = BitIndex> {
    /// Length of the sequence.
    len: usize,
    /// Symbols per chunk (the last chunk may be shorter).
    chunk: usize,
    /// The distinct symbols of the whole sequence.
    alphabet: Alphabet,
    /// One tree per chunk.
    trees: Vec<WaveletTree<B>>,
    /// `ranks[r * σ + d] = rank_d(L, r * chunk)`, for `r` in `0..=chunks`.
    ranks: Vec<u32>,
}

impl<B: RankBits> ChunkedWavelet<B> {
    /// Chunk `seq` at Kärkkäinen--Puglisi's length, `σ ⌈log2(n + 1)⌉²` (at least 1).
    ///
    /// # Panics
    ///
    /// As [`ChunkedWavelet::with_chunk`].
    #[must_use]
    pub fn new(seq: &[u8]) -> ChunkedWavelet<B> {
        ChunkedWavelet::with_chunk(seq, default_chunk(seq.len(), Alphabet::of(seq).len()))
    }

    /// Chunk `seq` into pieces of `chunk` symbols.
    ///
    /// # Panics
    ///
    /// If `chunk` is zero, or `seq` is longer than `u32::MAX`.
    #[must_use]
    pub fn with_chunk(seq: &[u8], chunk: usize) -> ChunkedWavelet<B> {
        assert!(
            chunk > 0,
            "chunked_wavelet: the chunk length must be positive"
        );
        assert!(
            u32::try_from(seq.len()).is_ok(),
            "chunked_wavelet: one index covers at most u32::MAX positions; shard"
        );
        let alphabet = Alphabet::of(seq);
        let sigma = alphabet.len();
        let mut ranks = Vec::with_capacity((seq.len() / chunk + 2) * sigma);
        let mut running = vec![0u32; sigma];
        let mut trees = Vec::with_capacity(seq.len().div_ceil(chunk));
        for piece in seq.chunks(chunk) {
            ranks.extend_from_slice(&running);
            for &s in piece {
                let d = alphabet
                    .index_of(s)
                    .expect("every symbol is in its own alphabet");
                running[d] += 1;
            }
            trees.push(WaveletTree::new(piece));
        }
        ranks.extend_from_slice(&running);
        ChunkedWavelet {
            len: seq.len(),
            chunk,
            alphabet,
            trees,
            ranks,
        }
    }

    /// Length of the sequence.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the sequence is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Symbols per chunk.
    #[must_use]
    pub fn chunk_len(&self) -> usize {
        self.chunk
    }

    /// Number of chunks.
    #[must_use]
    pub fn chunks(&self) -> usize {
        self.trees.len()
    }

    /// The distinct symbols of the whole sequence, ascending.
    #[must_use]
    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    /// Occurrences of `c` strictly before `i`: `R[i / b][c] + rank_c(L_{i/b}, i mod b)`.
    /// Saturates at `len`; `0` for a byte outside the alphabet.
    #[must_use]
    pub fn rank(&self, c: u8, i: usize) -> usize {
        #[cfg(test)]
        OCC_CALLS.with(|n| n.set(n.get() + 1));
        let Some(d) = self.alphabet.index_of(c) else {
            return 0;
        };
        let i = i.min(self.len);
        let (r, within) = (i / self.chunk, i % self.chunk);
        let base = self.ranks[r * self.alphabet.len() + d] as usize;
        if within == 0 {
            base
        } else {
            base + self.trees[r].rank(c, within)
        }
    }

    /// The symbol at `i` and `rank(L[i], i)`, from one descent of `i`'s chunk's tree.
    ///
    /// # Panics
    ///
    /// If `i >= len`.
    #[must_use]
    pub fn access_rank(&self, i: usize) -> (u8, usize) {
        let (s, _, rank) = self.access_dense_rank(i);
        (s, rank)
    }

    /// [`Self::access_rank`] with the symbol's dense number between the two.
    pub(crate) fn access_dense_rank(&self, i: usize) -> (u8, usize, usize) {
        #[cfg(test)]
        OCC_CALLS.with(|n| n.set(n.get() + 1));
        assert!(
            i < self.len,
            "chunked_wavelet: position {i} is past the end ({})",
            self.len
        );
        let r = i / self.chunk;
        let (s, within) = self.trees[r].access_rank(i % self.chunk);
        let d = self
            .alphabet
            .index_of(s)
            .expect("a chunk's symbol is in the whole sequence's alphabet");
        (
            s,
            d,
            self.ranks[r * self.alphabet.len() + d] as usize + within,
        )
    }

    /// Bits the chunk trees store: the sum of the chunks' Huffman encodings.
    #[must_use]
    pub fn stored_bits(&self) -> usize {
        self.trees.iter().map(WaveletTree::stored_bits).sum()
    }

    /// Bytes allocated: every chunk's tree and the rank table.
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        self.trees
            .iter()
            .map(WaveletTree::size_bytes)
            .sum::<usize>()
            + self.ranks.len() * size_of::<u32>()
    }
}

/// Kärkkäinen--Puglisi's block length `σ ⌈log2(n + 1)⌉²`, at least 1.
#[must_use]
pub fn default_chunk(n: usize, sigma: usize) -> usize {
    let log = (usize::BITS - n.leading_zeros()) as usize;
    (sigma * log * log).max(1)
}

impl<B: RankBits> std::fmt::Debug for ChunkedWavelet<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChunkedWavelet")
            .field("len", &self.len)
            .field("chunk", &self.chunk)
            .field("chunks", &self.trees.len())
            .field("size_bytes", &self.size_bytes())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "unit_tests/chunked_wavelet.rs"]
mod tests;
