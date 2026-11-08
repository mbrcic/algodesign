// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::rrr::Rrr;
use proptest::prelude::*;

fn check<B: RankBits>(seq: &[u8], chunk: usize) -> Result<(), TestCaseError> {
    let cw = ChunkedWavelet::<B>::with_chunk(seq, chunk);
    prop_assert_eq!(cw.chunks(), seq.len().div_ceil(chunk));
    let mut seen = [0usize; 256];
    for i in 0..=seq.len() + 1 {
        for c in [0u8, 1, 2, 3, 4, 9] {
            prop_assert_eq!(cw.rank(c, i), seen[c as usize], "rank({}, {})", c, i);
        }
        if let Some(&s) = seq.get(i) {
            prop_assert_eq!(cw.access_rank(i), (s, seen[s as usize]));
            seen[s as usize] += 1;
        }
    }
    Ok(())
}

proptest! {
    /// Every chunk length that matters at the boundaries: one symbol, two, an odd length,
    /// and either side of 64 -- so `i` lands on exact multiples of `b`, `n` is sometimes a
    /// multiple of `b` (the totals row), and a symbol is often absent from a chunk while
    /// present in the whole.
    #[test]
    fn rank_and_access_match_counting(seq in prop::collection::vec(0u8..5, 0..300)) {
        for chunk in [1, 2, 7, 63, 64, 1000] {
            check::<BitIndex>(&seq, chunk)?;
        }
        check::<Rrr>(&seq, 7)?;
    }
}

#[test]
fn a_length_that_is_a_multiple_of_the_chunk_reads_the_totals_row() {
    let seq = b"abcabcabca";
    let cw = ChunkedWavelet::<BitIndex>::with_chunk(seq, 5);
    assert_eq!(cw.chunks(), 2);
    assert_eq!(cw.rank(b'a', 10), 4);
    assert_eq!(cw.rank(b'a', 99), 4);
    assert_eq!(cw.rank(b'c', 5), 1);
    assert_eq!(cw.rank(b'c', 6), 2);
    // 'z' is absent from everything.
    assert_eq!(cw.rank(b'z', 7), 0);
}

#[test]
fn the_default_chunk_is_sigma_log_squared() {
    let seq: Vec<u8> = b"banana".repeat(200);
    // n = 1200, ⌈log2(n + 1)⌉ = 11 bits, σ = 3: 3 · 121 = 363.
    let cw = ChunkedWavelet::<BitIndex>::new(&seq);
    assert_eq!(cw.chunk_len(), 363);
    assert_eq!(cw.chunks(), 4);
    assert_eq!(ChunkedWavelet::<BitIndex>::new(&[]).chunk_len(), 1);
}

#[test]
#[should_panic(expected = "chunk length must be positive")]
fn a_zero_chunk_is_rejected() {
    let _ = ChunkedWavelet::<BitIndex>::with_chunk(b"ab", 0);
}

#[test]
fn debug_is_a_summary() {
    let shown = format!("{:?}", ChunkedWavelet::<BitIndex>::with_chunk(b"banana", 4));
    assert!(
        shown.starts_with("ChunkedWavelet {") && shown.contains("chunks: 2"),
        "{shown}"
    );
}
