// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::count_index::BitIndex;
use crate::strings::rrr::Rrr;
use proptest::prelude::*;

proptest! {
    /// Every backend answers every `occ` and LF read as the checkpoint table does.
    #[test]
    fn wavelet_tree_occ_is_byte_index_occ(seq in prop::collection::vec(0u8..8, 0..700)) {
        let plain = <ByteIndex as Occ>::from_last_column(&seq);
        let chunked = <ChunkedWavelet as Occ>::from_last_column(&seq);
        let short = ChunkedWavelet::<BitIndex>::with_chunk(&seq, 13);
        let rrr = <WaveletTree<Rrr> as Occ>::from_last_column(&seq);
        let bits = <WaveletTree<BitIndex> as Occ>::from_last_column(&seq);
        prop_assert_eq!(plain.alphabet(), chunked.alphabet());
        prop_assert_eq!(plain.alphabet(), rrr.alphabet());
        for c in 0u8..10 {
            for i in 0..=seq.len() + 2 {
                let want = plain.occ(c, i);
                prop_assert_eq!(chunked.occ(c, i), want);
                prop_assert_eq!(short.occ(c, i), want);
                prop_assert_eq!(rrr.occ(c, i), want);
                prop_assert_eq!(bits.occ(c, i), want);
            }
        }
        for i in 0..seq.len() {
            let want = plain.symbol_and_occ(i);
            prop_assert_eq!(chunked.symbol_and_occ(i), want);
            prop_assert_eq!(short.symbol_and_occ(i), want);
            prop_assert_eq!(rrr.symbol_and_occ(i), want);
            prop_assert_eq!(bits.symbol_and_occ(i), want);
            // The dense number the chunked form hands over is the one the default looks up.
            let dense = plain.alphabet().index_of(want.0).unwrap();
            prop_assert_eq!(chunked.symbol_dense_and_occ(i), (want.0, dense, want.1));
            prop_assert_eq!(short.symbol_dense_and_occ(i), (want.0, dense, want.1));
            prop_assert_eq!(plain.symbol_dense_and_occ(i), (want.0, dense, want.1));
        }
    }
}
