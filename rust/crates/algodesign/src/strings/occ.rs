// SPDX-License-Identifier: Apache-2.0
//! The **`occ` backend**: the reads an FM-index makes of its last column `L`, `occ(c, i)` and an
//! LF step's `(L[i], occ(L[i], i))` (Navarro, *Compact Data Structures*, §11.2). Implemented by
//! [`ChunkedWavelet`], [`WaveletTree`] and [`ByteIndex`]. No Lean model.

use crate::strings::chunked_wavelet::ChunkedWavelet;
use crate::strings::count_index::{Alphabet, ByteIndex};
use crate::strings::wavelet_tree::{RankBits, WaveletTree};

// `Occ` is sealed: only the three representations below implement it.
mod sealed {
    pub trait Sealed {}
    impl<const BLOCK: usize> Sealed for super::ByteIndex<BLOCK> {}
    impl<B: super::RankBits> Sealed for super::WaveletTree<B> {}
    impl<B: super::RankBits> Sealed for super::ChunkedWavelet<B> {}
}

/// A sequence representation an FM-index can search: `occ`, and one LF step's reads.
pub trait Occ: sealed::Sealed + Sized {
    /// Index the last column `last`.
    fn from_last_column(last: &[u8]) -> Self;
    /// Positions indexed.
    fn len(&self) -> usize;
    /// Whether nothing is indexed.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// The distinct symbols, ascending.
    fn alphabet(&self) -> &Alphabet;
    /// Occurrences of `c` strictly before `i`; saturates at `len`, `0` for a symbol outside the
    /// alphabet.
    fn occ(&self, c: u8, i: usize) -> usize;
    /// `L[i]` and `occ(L[i], i)`: the two reads one LF step makes. `i < len`.
    fn symbol_and_occ(&self, i: usize) -> (u8, usize);
    /// [`Occ::symbol_and_occ`] with `L[i]`'s dense number in [`Occ::alphabet`] between the two.
    /// `i < len`.
    #[allow(
        clippy::missing_panics_doc,
        reason = "every symbol of the column is in its alphabet"
    )]
    fn symbol_dense_and_occ(&self, i: usize) -> (u8, usize, usize) {
        let (c, occ) = self.symbol_and_occ(i);
        let dense = self
            .alphabet()
            .index_of(c)
            .expect("every symbol of the column is in its alphabet");
        (c, dense, occ)
    }
    /// Bytes the representation occupies, the sequence itself included.
    fn size_bytes(&self) -> usize;
}

impl<const BLOCK: usize> Occ for ByteIndex<BLOCK> {
    fn from_last_column(last: &[u8]) -> Self {
        ByteIndex::new_over_blocks(last, &Alphabet::of(last))
    }
    fn len(&self) -> usize {
        ByteIndex::len(self)
    }
    fn alphabet(&self) -> &Alphabet {
        ByteIndex::alphabet(self)
    }
    fn occ(&self, c: u8, i: usize) -> usize {
        ByteIndex::occ(self, c, i)
    }
    fn symbol_and_occ(&self, i: usize) -> (u8, usize) {
        let c = self.bytes()[i];
        (c, ByteIndex::occ(self, c, i))
    }
    fn size_bytes(&self) -> usize {
        ByteIndex::len(self) + self.overhead_bytes()
    }
}

impl<B: RankBits> Occ for WaveletTree<B> {
    fn from_last_column(last: &[u8]) -> Self {
        WaveletTree::new(last)
    }
    fn len(&self) -> usize {
        WaveletTree::len(self)
    }
    fn alphabet(&self) -> &Alphabet {
        WaveletTree::alphabet(self)
    }
    fn occ(&self, c: u8, i: usize) -> usize {
        self.rank(c, i)
    }
    fn symbol_and_occ(&self, i: usize) -> (u8, usize) {
        self.access_rank(i)
    }
    fn size_bytes(&self) -> usize {
        WaveletTree::size_bytes(self)
    }
}

impl<B: RankBits> Occ for ChunkedWavelet<B> {
    fn from_last_column(last: &[u8]) -> Self {
        ChunkedWavelet::new(last)
    }
    fn len(&self) -> usize {
        ChunkedWavelet::len(self)
    }
    fn alphabet(&self) -> &Alphabet {
        ChunkedWavelet::alphabet(self)
    }
    fn occ(&self, c: u8, i: usize) -> usize {
        self.rank(c, i)
    }
    fn symbol_and_occ(&self, i: usize) -> (u8, usize) {
        self.access_rank(i)
    }
    fn symbol_dense_and_occ(&self, i: usize) -> (u8, usize, usize) {
        self.access_dense_rank(i)
    }
    fn size_bytes(&self) -> usize {
        ChunkedWavelet::size_bytes(self)
    }
}

#[cfg(test)]
#[path = "unit_tests/occ.rs"]
mod tests;
