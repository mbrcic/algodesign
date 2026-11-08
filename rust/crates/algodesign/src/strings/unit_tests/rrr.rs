// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;

/// Every query at every position, against one counting pass over the bits.
fn check_all(bits: &[bool]) {
    let rrr = Rrr::from_bools(bits);
    assert_eq!(rrr.len(), bits.len());
    let (mut ones, mut zeros) = (0, 0);
    let (mut set, mut clear) = (Vec::new(), Vec::new());
    for i in 0..=bits.len() + 1 {
        assert_eq!(rrr.rank(i), ones, "rank({i}) of {}", bits.len());
        assert_eq!(
            rrr.get(i),
            bits.get(i).copied().unwrap_or(false),
            "get({i})"
        );
        match bits.get(i) {
            Some(&true) => {
                assert_eq!(rrr.access_rank(i), (true, ones), "access_rank({i})");
                set.push(i);
                ones += 1;
            }
            Some(&false) => {
                assert_eq!(rrr.access_rank(i), (false, zeros), "access_rank({i})");
                clear.push(i);
                zeros += 1;
            }
            None => {}
        }
    }
    assert_eq!(rrr.count_ones(), ones);
    for (j, &p) in set.iter().enumerate() {
        assert_eq!(rrr.select1(j), Some(p), "select1({j})");
    }
    for (j, &p) in clear.iter().enumerate() {
        assert_eq!(rrr.select0(j), Some(p), "select0({j})");
    }
    assert_eq!(rrr.select1(ones), None);
    assert_eq!(rrr.select0(zeros), None);
}

#[test]
fn the_binomial_table_and_the_offset_widths() {
    assert_eq!(BINOMIAL[4][2], 6);
    assert_eq!(BINOMIAL[63][1], 63);
    assert_eq!(BINOMIAL[63][31], 916_312_070_471_295_267);
    assert!(BINOMIAL[63][31] < 1 << 60);
    assert_eq!(OFFSET_BITS[0], 0);
    assert_eq!(OFFSET_BITS[63], 0);
    assert_eq!(OFFSET_BITS[1], 6);
    assert_eq!(OFFSET_BITS[31], 60);
}

/// Navarro's Examples 4.2-4.4, at his `b = 4`, re-read at `b = 63` by padding: a block's
/// offset counts the blocks of its class that precede it, so leading zeros change nothing
/// and the order is "first bit most significant".
#[test]
fn encode_decode_round_trip_and_order() {
    // Among class-1 blocks, the one whose set bit is last comes first.
    assert_eq!(encode(1u64 << 62, 1), 0);
    assert_eq!(encode(1u64 << 61, 1), 1);
    assert_eq!(encode(1, 1), 62);
    for class in 0..=63u32 {
        let block = prefix_mask(class as usize) << (63 - class as usize);
        // All ones packed at the end is offset 0; at the start it is the last.
        assert_eq!(encode(block, class), 0);
        let front = prefix_mask(class as usize);
        let count = BINOMIAL[63][class as usize];
        assert_eq!(encode(front, class), count - 1);
        assert_eq!(decode(class, count - 1, 63), front);
        assert_eq!(decode(class, 0, 63), block);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]
    #[test]
    fn decode_inverts_encode(block in any::<u64>(), upto in 0usize..=63) {
        let block = block & prefix_mask(63);
        let class = block.count_ones();
        let offset = encode(block, class);
        prop_assert!(offset < BINOMIAL[63][class as usize]);
        prop_assert_eq!(decode(class, offset, upto), block & prefix_mask(upto));
    }

}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// Up to three superblocks (6048 bits), so the sample path is reached, at three
    /// densities -- sparse, balanced, dense -- so classes near 0, 31 and 63 all occur.
    /// Oracles from one prefix pass, so a case is linear, not quadratic.
    #[test]
    fn rank_get_select_match_counting(len in 0usize..6100, density in 0u32..3, seed in any::<u64>()) {
        let mut state = seed | 1;
        let bits: Vec<bool> = (0..len).map(|_| {
            state ^= state << 13; state ^= state >> 7; state ^= state << 17;
            match density { 0 => state % 29 == 0, 1 => state % 2 == 0, _ => state % 29 != 0 }
        }).collect();
        let rrr = Rrr::from_bools(&bits);
        let mut ones = 0;
        let (mut set, mut clear) = (Vec::new(), Vec::new());
        for i in 0..=len + 1 {
            prop_assert_eq!(rrr.rank(i), ones);
            prop_assert_eq!(rrr.get(i), bits.get(i).copied().unwrap_or(false));
            match bits.get(i) {
                Some(true) => { set.push(i); ones += 1; }
                Some(false) => clear.push(i),
                None => {}
            }
        }
        for (j, &p) in set.iter().enumerate() {
            prop_assert_eq!(rrr.select1(j), Some(p));
        }
        for (j, &p) in clear.iter().enumerate() {
            prop_assert_eq!(rrr.select0(j), Some(p));
        }
        prop_assert_eq!(rrr.select1(set.len()), None);
        prop_assert_eq!(rrr.select0(clear.len()), None);
    }
}

/// The block and superblock boundaries, exhaustively at every position: lengths either side
/// of one block (63), and of one superblock (2016), and a length that ends mid-block in the
/// third superblock.
#[test]
fn block_and_superblock_boundaries() {
    for len in [
        0, 1, 62, 63, 64, 125, 126, 127, 2015, 2016, 2017, 4032, 4033, 4100,
    ] {
        for pattern in 0..4 {
            let bits: Vec<bool> = (0..len)
                .map(|i| match pattern {
                    0 => false,
                    1 => true,
                    2 => i % 63 == 62 || i % 2016 == 0,
                    _ => (i * 7 + i / 63) % 5 < 2,
                })
                .collect();
            check_all(&bits);
        }
    }
}

/// Runs of all-zero and all-one blocks cost only their class: the offset stream is empty.
#[test]
fn uniform_blocks_store_no_offsets() {
    let zeros = Rrr::new(&vec![0u64; 100], 6400);
    let ones = Rrr::new(&vec![u64::MAX; 100], 6300);
    for rrr in [&zeros, &ones] {
        assert_eq!(rrr.samples.last().map(|s| s.pointer), Some(0));
    }
    assert_eq!(ones.rank(6300), 6300);
    assert_eq!(ones.select0(0), None);
    assert_eq!(zeros.select1(0), None);
}

/// A sparse bitvector costs far less than one bit per bit; a balanced random one a little more.
#[test]
fn space_follows_the_entropy() {
    let n = 1 << 16;
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let sparse: Vec<bool> = (0..n).map(|_| next() % 32 == 0).collect();
    let balanced: Vec<bool> = (0..n).map(|_| next() % 2 == 0).collect();
    let sparse_bits = Rrr::from_bools(&sparse).size_bytes() as f64 * 8.0 / n as f64;
    let balanced_bits = Rrr::from_bools(&balanced).size_bytes() as f64 * 8.0 / n as f64;
    // H0(1/32) = 0.201 bits; overhead ~0.13.
    assert!(sparse_bits < 0.40, "sparse: {sparse_bits:.3} bits/bit");
    assert!(
        balanced_bits > 1.0 && balanced_bits < 1.2,
        "balanced: {balanced_bits:.3}"
    );
}

#[test]
#[should_panic(expected = "exceeds the 64 bits supplied")]
fn a_len_past_the_words_is_rejected() {
    let _ = Rrr::new(&[0], 65);
}

#[test]
fn debug_is_a_summary() {
    let shown = format!("{:?}", Rrr::from_bools(&[true, false, true]));
    assert!(
        shown.starts_with("Rrr {") && shown.contains("ones: 2"),
        "{shown}"
    );
}
