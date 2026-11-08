// SPDX-License-Identifier: Apache-2.0
//! The seeded random source every randomized structure in the crate draws from: SplitMix64
//! (Steele, Lea and Flood 2014; Vigna's `splitmix64.c`), from the treap's priorities to the
//! projections, hash tables and graph levels of the high-dimensional search. It is in the
//! crate, not taken from `rand`, because `rand`'s `StdRng` stream may change between versions,
//! and a seed here must reproduce the same structure forever. The Python's
//! `algodesign._rng.SplitMix64` gives the same stream, so a seed builds the same structures in
//! both languages. The uniform and normal draws, which only the high-dimensional search uses,
//! are defined beside it.

/// SplitMix64. Equality and `Debug` are for the structures that carry one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SplitMix64(u64);

impl SplitMix64 {
    pub(crate) fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}
