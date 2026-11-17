// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::naive;
use proptest::prelude::*;

/// The `j`-th set bit by scanning: the reference for `select`.
fn naive_select(words: &[u64], len: usize, j: usize) -> Option<usize> {
    (0..len)
        .filter(|&b| words[b / WORD] >> (b % WORD) & 1 == 1)
        .nth(j)
}

proptest! {
    #[test]
    fn rank_matches_the_naive_count(bits in prop::collection::vec(any::<u64>(), 1..40),
                                    i in 0usize..2000) {
        let len = bits.len() * 64;
        let i = i.min(len);
        let idx = BitIndex::new(&bits, len);
        prop_assert_eq!(idx.rank(i), naive::rank(&bits, i));
    }

    /// `get` is the one-bit difference of two ranks.
    #[test]
    fn get_is_the_rank_difference(bits in prop::collection::vec(any::<u64>(), 1..40),
                                  len_cut in 0usize..64) {
        let len = bits.len() * 64 - len_cut;
        let idx = BitIndex::new(&bits, len);
        for i in 0..len + 2 {
            prop_assert_eq!(idx.get(i), idx.rank(i + 1) > idx.rank(i));
        }
    }

    /// `count_byte` counts exactly across its 255-byte chunk boundaries.
    #[test]
    fn count_byte_matches_the_naive_count(bytes in prop::collection::vec(0u8..4, 0..1100),
                                          c in 0u8..4) {
        prop_assert_eq!(count_byte(&bytes, c), bytes.iter().filter(|&&b| b == c).count());
    }

    #[test]
    fn select_inverts_rank(bits in prop::collection::vec(any::<u64>(), 1..40)) {
        let len = bits.len() * 64;
        let idx = BitIndex::new(&bits, len);
        for j in 0..idx.rank(len) {
            let p = idx.select(j).unwrap();
            prop_assert_eq!(idx.rank(p), j);                 // Lean: rank_select
        }
    }

    #[test]
    fn occ_is_rank_over_two_symbols(bits in prop::collection::vec(any::<u64>(), 1..20),
                                    i in 0usize..1000) {
        let len = bits.len() * 64;
        let i = i.min(len);
        let bytes: Vec<u8> = (0..len).map(|b| ((bits[b / 64] >> (b % 64)) & 1) as u8).collect();
        let bi = BitIndex::new(&bits, len);
        let by = ByteIndex::new(&bytes, &Alphabet::of(&bytes));
        prop_assert_eq!(by.occ(1, i), bi.rank(i));           // Lean: occ_eq_rank
    }

    /// The position `select` returns holds a set bit (the first half of Lean `rank_select`).
    #[test]
    fn select_lands_on_the_set_bit_the_scan_finds(bits in prop::collection::vec(any::<u64>(), 1..40)) {
        let len = bits.len() * 64;
        let idx = BitIndex::new(&bits, len);
        for j in 0..idx.rank(len) {
            let p = idx.select(j).unwrap();
            prop_assert!(bits[p / 64] >> (p % 64) & 1 == 1); // Lean: rank_select, first half
            prop_assert_eq!(Some(p), naive_select(&bits, len, j));
        }
        prop_assert_eq!(idx.select(idx.rank(len)), None);
    }

    /// At a set bit `i`, `select(rank(i)) == i`. Lean: `select_rank`.
    #[test]
    fn select_of_rank_returns_the_set_bit_it_was_asked_about(
        bits in prop::collection::vec(any::<u64>(), 1..40),
    ) {
        let len = bits.len() * 64;
        let idx = BitIndex::new(&bits, len);
        for i in (0..len).filter(|&b| bits[b / 64] >> (b % 64) & 1 == 1) {
            prop_assert_eq!(idx.select(idx.rank(i)), Some(i));
        }
    }

    /// The in-word step on its own, against a bit-by-bit scan.
    #[test]
    fn select_in_word_matches_a_bit_scan(x in any::<u64>()) {
        for j in 0..x.count_ones() {
            let expected = (0..64u32).filter(|&b| x >> b & 1 == 1).nth(j as usize).unwrap();
            prop_assert_eq!(select_in_word(x, j), expected);
        }
    }

    /// `rank` over a partial last word: bits above `len` are not counted.
    #[test]
    fn a_partial_last_word_is_masked(bits in prop::collection::vec(any::<u64>(), 1..10),
                                     len in 0usize..640, i in 0usize..640) {
        let len = len.min(bits.len() * 64);
        let idx = BitIndex::new(&bits, len);
        prop_assert_eq!(idx.rank(i), naive::rank(&bits, i.min(len)));
        prop_assert_eq!(idx.rank(len), naive::rank(&bits, len));
    }

    /// `occ` over a real alphabet, against the definition.
    #[test]
    fn occ_matches_the_definition(text in prop::collection::vec(any::<u8>(), 0..900),
                                  i in 0usize..900) {
        let alphabet = Alphabet::of(&text);
        let index = ByteIndex::new(&text, &alphabet);
        let i = i.min(text.len());
        for &c in alphabet.symbols() {
            prop_assert_eq!(index.occ(c, i), text[..i].iter().filter(|&&b| b == c).count());
        }
    }

    /// The dense map and its inverse agree, and the order is ascending.
    #[test]
    fn alphabet_is_a_dense_ascending_bijection(text in prop::collection::vec(any::<u8>(), 0..300)) {
        let alphabet = Alphabet::of(&text);
        prop_assert!(alphabet.symbols().windows(2).all(|w| w[0] < w[1]));
        for (dense, &c) in alphabet.symbols().iter().enumerate() {
            prop_assert_eq!(alphabet.index_of(c), Some(dense));
            prop_assert_eq!(alphabet.symbol(dense), Some(c));
        }
        for b in 0..=u8::MAX {
            prop_assert_eq!(alphabet.contains(b), text.contains(&b));
        }
    }
}

#[test]
fn the_empty_bitvector_answers_both_questions() {
    let idx = BitIndex::new(&[], 0);
    assert!(idx.is_empty());
    assert_eq!(idx.rank(0), 0);
    assert_eq!(idx.rank(99), 0); // saturating, as the Lean's `take` is
    assert_eq!(idx.select(0), None);
    assert_eq!(idx.overhead_bytes(), 0);
}

#[test]
fn all_zeros_has_no_set_bit_to_select() {
    let idx = BitIndex::new(&[0u64; 200], 200 * 64);
    assert_eq!(idx.rank(200 * 64), 0);
    assert_eq!(idx.select(0), None);
    assert_eq!(idx.select(1_000_000), None);
}

#[test]
fn select_past_the_last_set_bit_is_none() {
    let words = [0b1011u64, 0, 1 << 40];
    let idx = BitIndex::new(&words, 192);
    assert_eq!(idx.rank(192), 4);
    assert_eq!(idx.select(0), Some(0));
    assert_eq!(idx.select(1), Some(1));
    assert_eq!(idx.select(2), Some(3));
    assert_eq!(idx.select(3), Some(128 + 40));
    assert_eq!(idx.select(4), None);
    assert_eq!(idx.select(usize::MAX), None);
}

#[test]
fn a_symbol_outside_the_alphabet_never_occurs() {
    let index = ByteIndex::new(b"banana", &Alphabet::of(b"banana"));
    assert_eq!(index.occ(b'z', 6), 0);
    assert_eq!(index.occ(b'a', 6), 3);
    assert_eq!(index.occ(b'a', 99), 3); // saturating
    let empty = ByteIndex::new(b"", &Alphabet::of(b""));
    assert!(empty.is_empty());
    assert_eq!(empty.occ(b'a', 0), 0);
    assert_eq!(empty.overhead_bytes(), 0);
    // An empty text over another text's alphabet: every symbol answers 0.
    let empty_shard = ByteIndex::new(b"", &Alphabet::of(b"banana"));
    assert_eq!(empty_shard.alphabet().len(), 3);
    for &c in empty_shard.alphabet().symbols() {
        assert_eq!(empty_shard.occ(c, 0), 0);
        assert_eq!(empty_shard.occ(c, 7), 0);
    }
}

/// The tail scan reads at most half a block, from the nearer checkpoint, and nothing when the
/// block's two checkpoints agree.
#[test]
fn occ_scans_at_most_half_a_block_and_nothing_when_the_checkpoints_agree() {
    let mut state = 0x9e37_79b9_u32;
    let mut text: Vec<u8> = (0..3000)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            (state % 4) as u8
        })
        .collect();
    // A symbol confined to block 0: every later block's checkpoints agree on it.
    text[7] = 9;
    let index = ByteIndex::new(&text, &Alphabet::of(&text));
    let scanned = |c: u8, i: usize| {
        SCANNED.with(|s| s.set(0));
        let answer = index.occ(c, i);
        assert_eq!(answer, text[..i].iter().filter(|&&b| b == c).count());
        SCANNED.with(std::cell::Cell::get)
    };
    let mut widest = 0;
    for i in 0..=text.len() {
        for c in [0u8, 1, 2, 3, 9] {
            let bytes = scanned(c, i);
            assert!(
                bytes <= DEFAULT_BLOCK / 2,
                "occ({c}, {i}) scanned {bytes} bytes, more than half a block"
            );
            widest = widest.max(bytes);
            if c == 9 && i >= DEFAULT_BLOCK {
                assert_eq!(
                    bytes, 0,
                    "occ(9, {i}) scanned a block its checkpoints rule out"
                );
            }
        }
    }
    // The counter is live: the far end of the bound is reached, from both checkpoints.
    assert_eq!(widest, DEFAULT_BLOCK / 2);
    assert_eq!(scanned(1, DEFAULT_BLOCK + 100), 100);
    assert_eq!(scanned(1, 2 * DEFAULT_BLOCK - 100), 100);
}

/// A chunk of 255 equal bytes, the largest count a `u8` tally holds.
#[test]
fn the_tail_tally_is_a_u8_over_chunks_it_cannot_overflow() {
    let narrow: fn(&[u8], u8) -> u8 = tally;
    assert_eq!(TALLY_CHUNK, 255);
    assert_eq!(narrow(&[7u8; TALLY_CHUNK], 7), 255);
    assert_eq!(
        count_byte(&[7u8; 3 * TALLY_CHUNK + 1], 7),
        3 * TALLY_CHUNK + 1
    );
}

/// `select` is total: a directory claiming more set bits than its words hold gets `None`.
#[test]
fn select_is_total_over_a_directory_that_overstates_its_bits() {
    let words = [0b1011u64, 0, 1 << 40];
    let mut idx = BitIndex::new(&words, 192);
    assert_eq!(idx.select(3), Some(128 + 40));
    idx.index.total += 5;
    for j in 4..9 {
        assert_eq!(idx.select(j), None);
    }
    assert_eq!(idx.select(9), None);
}

/// Past 8192 set bits `select` uses the sample array: every set bit of three such vectors.
#[test]
fn select_reads_the_sample_array_past_8192_set_bits() {
    let mut state = 0x2545_f491_4f6c_dd1d_u64;
    let mut random = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let dense: Vec<u64> = (0..3000).map(|_| random()).collect();
    let full = vec![u64::MAX; 800];
    let sparse: Vec<u64> = (0..15_000)
        .map(|w| 1u64 << (w % 64) | 1u64 << ((w * 7) % 64))
        .collect();
    for words in [dense, full, sparse] {
        let len = words.len() * WORD - 3;
        let idx = BitIndex::new(&words, len);
        let set: Vec<usize> = (0..len)
            .filter(|&b| words[b / WORD] >> (b % WORD) & 1 == 1)
            .collect();
        assert!(set.len() > 3 * SELECT_SAMPLE, "only {} set bits", set.len());
        for (j, &p) in set.iter().enumerate() {
            assert_eq!(idx.select(j), Some(p), "select({j})");
        }
        assert_eq!(idx.select(set.len()), None);
    }
}

/// Bit overhead: `32 / 4096 + 16 / 512` is 3.91 %, plus at most 0.39 % for samples.
#[test]
fn bit_index_overhead_is_under_five_percent() {
    let words = vec![u64::MAX; 1 << 14]; // 2^20 bits, all set: the worst case for samples
    let idx = BitIndex::new(&words, 1 << 20);
    let data = words.len() * size_of::<u64>();
    assert_eq!(idx.overhead_bytes(), 256 * 4 + 2048 * 2 + 128 * 4);
    assert_eq!(idx.overhead_bytes(), 5632);
    assert!(
        idx.overhead_bytes() * 100 < data * 5,
        "{} of {data} bytes",
        idx.overhead_bytes()
    );
}

/// Byte overhead at `σ = 256`: `(4 / 4096 + 2 / 512) * 256` is 1.25 bytes per position.
#[test]
fn byte_index_overhead_is_1_25_n() {
    let text: Vec<u8> = (0..1u32 << 16).map(|i| (i % 256) as u8).collect();
    let alphabet = Alphabet::of(&text);
    assert_eq!(alphabet.len(), 256);
    let index = ByteIndex::new(&text, &alphabet);
    let per_position = index.overhead_bytes() as f64 / text.len() as f64;
    assert!(
        (1.25..1.27).contains(&per_position),
        "{per_position} bytes per position, expected 1.25 n"
    );
}

/// Bit vectors of 10 000 to 70 000 bits at a drawn density: several superblocks and samples.
fn long_bits() -> impl Strategy<Value = (Vec<u64>, usize)> {
    (10_000usize..70_000, 0u8..5).prop_flat_map(|(len, density)| {
        prop::collection::vec(any::<[u64; 3]>(), len.div_ceil(WORD)).prop_map(move |words| {
            let words = words
                .iter()
                .map(|&[a, b, c]| match density {
                    0 => 0,
                    1 => a & b & c, // about one bit in eight
                    2 => a,         // one in two
                    3 => a | b | c, // seven in eight
                    _ => u64::MAX,
                })
                .collect();
            (words, len)
        })
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    /// `rank` at every position and `select` of every set bit, against one scan, on vectors
    /// that reach the directory's second level.
    #[test]
    fn rank_and_select_past_one_superblock((bits, len) in long_bits()) {
        let idx = BitIndex::new(&bits, len);
        let mut ones = Vec::new();
        for i in 0..len {
            prop_assert_eq!(idx.rank(i), ones.len());
            if bits[i / WORD] >> (i % WORD) & 1 == 1 {
                ones.push(i);
            }
        }
        prop_assert_eq!(idx.rank(len), ones.len());
        for (j, &p) in ones.iter().enumerate() {
            prop_assert_eq!(idx.select(j), Some(p));
            prop_assert_eq!(idx.rank(p), j);                 // Lean: rank_select
        }
        prop_assert_eq!(idx.select(ones.len()), None);
    }
}
