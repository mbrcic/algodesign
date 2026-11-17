// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;

/// Every query, against counting, on one backend. Prefix counts are built once, so the
/// oracle is linear rather than quadratic.
fn check<B: RankBits>(seq: &[u8], probes: &[u8]) -> Result<(), TestCaseError> {
    let wt = WaveletTree::<B>::new(seq);
    prop_assert_eq!(wt.len(), seq.len());
    let mut seen = [0usize; 256];
    for (i, &s) in seq.iter().enumerate() {
        prop_assert_eq!(wt.access_rank(i), (s, seen[s as usize]));
        seen[s as usize] += 1;
    }
    for &c in probes {
        let mut before = 0;
        let mut positions = Vec::new();
        for i in 0..=seq.len() + 1 {
            prop_assert_eq!(wt.rank(c, i), before, "rank({}, {})", c, i);
            if seq.get(i) == Some(&c) {
                before += 1;
                positions.push(i);
            }
        }
        for (j, &p) in positions.iter().enumerate() {
            prop_assert_eq!(wt.select(c, j), Some(p), "select({}, {})", c, j);
        }
        prop_assert_eq!(wt.select(c, positions.len()), None);
    }
    Ok(())
}

/// A skewed draw over the whole byte range: a few frequent symbols and a long tail, which
/// gives deep, unbalanced codes that a uniform five-symbol draw never builds.
fn skewed(len: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            // Halves, quarters, eighths: e, t, a, then the tail.
            match state % 8 {
                0..=3 => b'e',
                4..=5 => b't',
                6 => b'a',
                _ => (state >> 20) as u8,
            }
        })
        .collect()
}

proptest! {
    #[test]
    fn small_alphabet_matches_counting(seq in prop::collection::vec(0u8..5, 0..300)) {
        check::<Rrr>(&seq, &[0, 1, 2, 3, 4, 9])?;
        check::<BitIndex>(&seq, &[0, 1, 2, 3, 4, 9])?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]
    /// Longer than one RRR superblock (2016 bits) and one `BitIndex` superblock (4096 bits)
    /// in the concatenated bitvector, with codes of every depth.
    #[test]
    fn skewed_bytes_match_counting(len in 0usize..5000, seed in any::<u64>()) {
        let seq = skewed(len, seed);
        let probes = [b'e', b't', b'a', 0, 7, 200, 255];
        check::<Rrr>(&seq, &probes)?;
        check::<BitIndex>(&seq, &probes)?;
    }
}

/// The Huffman shape, and the pinned tie-break: on "abracadabra" the counts are a:5, b:2,
/// r:2, c:1, d:1, and the ids a0 b1 c2 d3 r4. Merging by (weight, id): c+d -> 5 (w2), then
/// b+r -> 6 (w4) -- b and r at weight 2 have lower ids than node 5 -- then 5+6 -> 7 (w6),
/// then a+7 -> 8 (w11). So a is `0`; c `100`, d `101`, b `110`, r `111`. Breaking the tie
/// the other way would give b and r codes of different lengths; this pins that it does not.
#[test]
fn huffman_shape_on_abracadabra() {
    let wt = WaveletTree::<Rrr>::new(b"abracadabra");
    let lens: Vec<_> = b"abcdr".iter().map(|&c| wt.code_len(c)).collect();
    assert_eq!(lens, [Some(1), Some(3), Some(3), Some(3), Some(3)]);
    assert_eq!(wt.code_len(b'z'), None);
    // Σ n_c |code(c)| = 5·1 + (2 + 1 + 1 + 2)·3 = 23 bits, the Huffman encoding's length.
    assert_eq!(wt.stored_bits(), 23);
    // Bit d of `bits` is the code's d-th bit, first bit first; dense ids a0 b1 c2 d3 r4.
    let bits = wt.code_bits.clone();
    assert_eq!(bits, [0b0, 0b011, 0b001, 0b101, 0b111]);
    // Preorder: the root, then node 7 (the `1` branch's c,d,b,r), then 5 (c,d), then 6.
    assert_eq!(wt.nodes.len(), 4);
    assert_eq!(wt.node_len(0), 11);
    assert_eq!(wt.nodes[1].start, 11);
    assert_eq!(wt.node_len(1), 6);
    assert_eq!(size_of::<Node>(), 16);
}

/// One distinct symbol: no internal node, empty code, `rank` is the position itself.
#[test]
fn one_symbol_has_no_internal_node() {
    let wt = WaveletTree::<Rrr>::new(&[0; 10]);
    assert_eq!(wt.nodes.len(), 0);
    assert_eq!(wt.code_len(0), Some(0));
    assert_eq!(wt.rank(0, 4), 4);
    assert_eq!(wt.rank(0, 99), 10);
    assert_eq!(wt.rank(1, 4), 0);
    assert_eq!(wt.access_rank(7), (0, 7));
    assert_eq!(wt.select(0, 9), Some(9));
    assert_eq!(wt.select(0, 10), None);
}

#[test]
fn the_empty_sequence() {
    let wt = WaveletTree::<BitIndex>::new(&[]);
    assert!(wt.is_empty());
    assert_eq!(wt.rank(0, 5), 0);
    assert_eq!(wt.select(0, 0), None);
}

/// Every byte value, once each, then a heavy symbol: 256 leaves, codes up to the maximum
/// depth the weights allow.
#[test]
fn the_full_byte_alphabet() {
    let mut seq: Vec<u8> = (0..=255u8).collect();
    seq.extend(std::iter::repeat_n(b'x', 3000));
    check::<BitIndex>(&seq, &[0, 1, 127, b'x', 255]).unwrap();
    let wt = WaveletTree::<BitIndex>::new(&seq);
    assert_eq!(wt.alphabet().len(), 256);
    assert_eq!(wt.code_len(b'x'), Some(1));
}

#[test]
#[should_panic(expected = "past the end")]
fn access_past_the_end_panics() {
    let _ = WaveletTree::<BitIndex>::new(b"ab").access(2);
}

#[test]
fn debug_is_a_summary() {
    let shown = format!("{:?}", WaveletTree::<Rrr>::new(b"banana"));
    assert!(
        shown.starts_with("WaveletTree {") && shown.contains("sigma: 3"),
        "{shown}"
    );
}
