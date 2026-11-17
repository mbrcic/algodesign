// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::count_index::{Alphabet, BitIndex, ByteIndex};
use crate::strings::wavelet_tree::WaveletTree;
use crate::strings::{naive, suffix_array};
use proptest::prelude::*;
use std::collections::HashMap;

proptest! {
    #[test]
    fn count_and_locate_match_naive(mut text in prop::collection::vec(1u8..5, 1..300),
                                    pat in prop::collection::vec(1u8..5, 1..6)) {
        text.push(bwt::SENTINEL);
        let idx = FmIndex::build(&text, 32);
        let expected = naive::search(&text, &pat);
        prop_assert_eq!(idx.count(&pat), expected.len());     // Lean: fmCount_eq
        let mut got = idx.locate(&pat); got.sort_unstable();
        prop_assert_eq!(got, expected);                       // Lean: fmLocate_perm
    }

    #[test]
    fn extract_reproduces_the_text(mut text in prop::collection::vec(1u8..5, 1..300),
                                   from in 0usize..300, len in 0usize..50) {
        text.push(bwt::SENTINEL);
        let (from, len) = (from.min(text.len()), len);
        let end = (from + len).min(text.len());
        let idx = FmIndex::build(&text, 32);
        prop_assert_eq!(idx.extract(from as u32, (end - from) as u32), text[from..end].to_vec());
    }
}

proptest! {
    /// The samples recover every row's text position, which must be the suffix array.
    #[test]
    fn sample_walk_agrees_with_the_suffix_array(mut text in prop::collection::vec(1u8..5, 1..200),
                                                sample in 2u32..40) {
        text.push(bwt::SENTINEL);
        let idx = FmIndex::build(&text, sample);
        let walked: Vec<u32> = (0..idx.text_len()).map(|row| idx.position_of(row)).collect();
        prop_assert_eq!(walked, suffix_array::suffix_array(&text));
    }

    /// Sampling rates below the text length, every range extracted.
    #[test]
    fn every_sampling_rate_answers_the_same(mut text in prop::collection::vec(1u8..5, 1..200),
                                            pat in prop::collection::vec(1u8..5, 1..5),
                                            sample in 2u32..64) {
        text.push(bwt::SENTINEL);
        let idx = FmIndex::build(&text, sample);
        let mut got = idx.locate(&pat);
        got.sort_unstable();
        prop_assert_eq!(got, naive::search(&text, &pat));
        let n = text.len();
        for from in 0..n {
            for end in [from + 1, (from + sample as usize).min(n), n] {
                prop_assert_eq!(idx.extract(from as u32, (end - from) as u32), text[from..end].to_vec());
            }
        }
    }

    /// A rate past the text length leaves one sample, position 0.
    #[test]
    fn one_sample_only(mut text in prop::collection::vec(1u8..5, 1..120),
                       pat in prop::collection::vec(1u8..5, 1..4)) {
        text.push(bwt::SENTINEL);
        let idx = FmIndex::build(&text, 4096);
        let mut got = idx.locate(&pat);
        got.sort_unstable();
        prop_assert_eq!(got, naive::search(&text, &pat));
        prop_assert_eq!(idx.extract(0, text.len() as u32), text.clone());
    }
}

// -- The oracle: the same index over the checkpoint table. ---------------------------------

/// Identical `count`, identical `locate` *vectors* (same row order), identical `extract`,
/// for every pattern and range asked, between this index over `make`'s structure and over
/// [`ByteIndex`].
fn agrees<O: Occ>(
    text: &[u8],
    sample: u32,
    make: impl FnOnce(&[u8]) -> O,
    pats: &[Vec<u8>],
    ranges: &[(usize, usize)],
) -> Result<(), TestCaseError> {
    let oracle = FmIndex::build_over(text, sample, <ByteIndex as Occ>::from_last_column);
    let idx = FmIndex::build_over(text, sample, make);
    prop_assert_eq!(idx.text_len(), oracle.text_len());
    for pat in pats {
        prop_assert_eq!(idx.count(pat), oracle.count(pat), "count {:?}", pat);
        prop_assert_eq!(idx.locate(pat), oracle.locate(pat), "locate {:?}", pat);
    }
    for &(from, len) in ranges {
        let from = from.min(text.len());
        let len = len.min(text.len() - from);
        prop_assert_eq!(
            idx.extract(from as u32, len as u32),
            oracle.extract(from as u32, len as u32)
        );
    }
    Ok(())
}

/// Patterns drawn from the text itself (so most occur) and a few given ones.
fn patterns_of(text: &[u8], seed: u64, given: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut state = seed | 1;
    let mut out: Vec<Vec<u8>> = given.to_vec();
    for _ in 0..12 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let at = (state % text.len() as u64) as usize;
        let len = 1 + (state >> 32) as usize % 6;
        out.push(text[at..(at + len).min(text.len())].to_vec());
    }
    out
}

/// Prose-like skew over a wide byte range, sentinel appended.
fn skewed_text(len: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    let mut text: Vec<u8> = (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            match state % 16 {
                0..=5 => b'e',
                6..=8 => b' ',
                9..=10 => b't',
                11 => b'h',
                _ => 1 + ((state >> 24) % 255) as u8,
            }
        })
        .collect();
    text.push(bwt::SENTINEL);
    text
}

proptest! {
    /// Against the checkpoint oracle, at the default chunk length and a short one.
    #[test]
    fn matches_the_checkpoint_oracle(mut text in prop::collection::vec(1u8..5, 1..300),
                                     pats in prop::collection::vec(prop::collection::vec(1u8..5, 0..6), 1..8),
                                     from in 0usize..300, len in 0usize..60,
                                     sample in 2u32..40, chunk in 1usize..40) {
        text.push(bwt::SENTINEL);
        let ranges = [(from, len), (0, usize::MAX)];
        agrees(&text, sample, ChunkedWavelet::<BitIndex>::new, &pats, &ranges)?;
        agrees(&text, sample, |l: &[u8]| ChunkedWavelet::<BitIndex>::with_chunk(l, chunk), &pats, &ranges)?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(16))]
    /// Long texts over a wide skewed alphabet: deep Huffman codes, many chunks.
    #[test]
    fn matches_the_checkpoint_oracle_on_long_skewed_texts(len in 2000usize..6000, seed in any::<u64>(),
                                                           sample in 2u32..64) {
        let text = skewed_text(len, seed);
        let pats = patterns_of(&text, seed, &[vec![b'e', b'e'], vec![bwt::SENTINEL], vec![b'h', bwt::SENTINEL]]);
        let ranges = [(seed as usize % len, 100), (len - 10, 11), (0, usize::MAX)];
        agrees(&text, sample, ChunkedWavelet::<BitIndex>::new, &pats, &ranges)?;
        agrees(&text, sample, |l: &[u8]| ChunkedWavelet::<BitIndex>::with_chunk(l, 64), &pats, &ranges)?;
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    /// The alternative `occ` structures answer as the oracle does.
    #[test]
    fn the_measured_alternatives_answer_alike(mut text in prop::collection::vec(1u8..5, 1..300),
                                              pats in prop::collection::vec(prop::collection::vec(1u8..5, 1..5), 1..6),
                                              sample in 2u32..16) {
        text.push(bwt::SENTINEL);
        let all = [(0, usize::MAX)];
        agrees(&text, sample, WaveletTree::<BitIndex>::new, &pats, &all)?;
        agrees(&text, sample, WaveletTree::<Rrr>::new, &pats, &all)?;
        agrees(&text, sample, |l: &[u8]| ChunkedWavelet::<Rrr>::with_chunk(l, 7), &pats, &all)?;
    }
}

/// A clone answers as the original does, and `Debug` is a few fields, not the arrays.
#[test]
fn clone_answers_alike_and_debug_is_a_summary() {
    let mut text = b"banana".repeat(500);
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 4);
    let copy = idx.clone();
    assert_eq!(copy.locate(b"nan"), idx.locate(b"nan"));
    assert_eq!(copy.extract(0, 12), idx.extract(0, 12));
    let shown = format!("{idx:?}");
    assert!(shown.starts_with("FmIndex {") && shown.contains("text_len: 3001"));
    assert!(shown.len() < 300, "Debug printed {} bytes", shown.len());
}

/// The textbook example, end to end, with the text deleted in between.
#[test]
fn banana() {
    let mut text = b"banana".to_vec();
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 2);
    assert_eq!(idx.count(b"ana"), 2);
    let mut hits = idx.locate(b"ana");
    hits.sort_unstable();
    assert_eq!(hits, vec![1, 3]);
    assert_eq!(idx.count(b"na"), 2);
    assert_eq!(idx.count(b"banana"), 1);
    assert_eq!(idx.extract(0, 6), b"banana".to_vec());
    assert_eq!(idx.extract(1, 3), b"ana".to_vec());
    assert_eq!(idx.extract(3, 3), b"ana".to_vec());
    assert_eq!(idx.extract(0, 7), text);
}

/// Extract's start on `banana$` at `l = 3`, including a range reaching the sentinel.
#[test]
fn extract_starts_at_the_first_sample_past_the_range() {
    let text = b"banana\0";
    let idx = FmIndex::build(text, 3);
    LF_STEPS.with(|n| n.set(0));
    assert_eq!(idx.extract(4, 1), b"n".to_vec());
    // From position 6: emit text[5], text[4]; one discarded.
    assert_eq!(LF_STEPS.with(std::cell::Cell::get), 2);
    LF_STEPS.with(|n| n.set(0));
    assert_eq!(idx.extract(5, 2), b"a\0".to_vec());
    // From position 7, i.e. row of position 0: emit text[6] (the sentinel), then text[5].
    assert_eq!(LF_STEPS.with(std::cell::Cell::get), 2);
    assert_eq!(idx.extract(6, 1), vec![bwt::SENTINEL]);
}

#[test]
fn a_pattern_absent_from_the_text() {
    let mut text = b"banana".to_vec();
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 32);
    assert_eq!(idx.count(b"xyz"), 0);
    assert_eq!(idx.locate(b"xyz"), Vec::<u32>::new());
    // Absent outside the alphabet, and absent as a string.
    assert_eq!(idx.count(b"nab"), 0);
    assert_eq!(idx.locate(b"nab"), Vec::<u32>::new());
    assert_eq!(naive::search(&text, b"nab"), Vec::<u32>::new());
}

#[test]
fn a_pattern_longer_than_the_text() {
    let mut text = b"ab".to_vec();
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 32);
    assert_eq!(idx.count(b"abababab"), 0);
    assert_eq!(idx.locate(b"abababab"), Vec::<u32>::new());
    assert_eq!(naive::search(&text, b"abababab"), Vec::<u32>::new());
}

/// The empty pattern occurs at every position of the text without its sentinel, its end included:
/// `n` of them for a stored text of `n` bytes.
#[test]
fn the_empty_pattern_occurs_at_every_position() {
    for text in [&b"banana\0"[..], b"\0", b"abracadabra\0"] {
        for sample in [2, 3, 32] {
            let idx = FmIndex::build(text, sample);
            assert_eq!(idx.count(b""), text.len()); // Lean: FMIndex.count_of_valid, occurs_nil
            let mut all = idx.locate(b"");
            all.sort_unstable();
            // Lean: FMIndex.locate_perm_of_valid
            assert_eq!(all, (0..text.len() as u32).collect::<Vec<_>>());
        }
    }
}

#[test]
fn an_empty_range_extracts_nothing() {
    let mut text = b"banana".to_vec();
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 32);
    assert_eq!(idx.extract(0, 0), Vec::<u8>::new());
    assert_eq!(idx.extract(3, 0), Vec::<u8>::new());
    // Including at the very end, where there is no sample at or past the range.
    assert_eq!(idx.extract(7, 0), Vec::<u8>::new());
}

#[test]
#[should_panic(expected = "runs past the text's 7 bytes")]
fn extracting_past_the_end_panics() {
    let mut text = b"banana".to_vec();
    text.push(bwt::SENTINEL);
    let _ = FmIndex::build(&text, 32).extract(5, 5);
}

#[test]
fn a_pattern_holding_the_sentinel_occurs_nowhere() {
    // The index answers about `banana`, without its sentinel: "na$" occurs nowhere there, though
    // the stored text ends with it. Lean: `FMIndex.count_of_valid`, `FMIndex.locate_perm_of_valid`.
    let mut text = b"banana".to_vec();
    text.push(bwt::SENTINEL);
    let idx = FmIndex::build(&text, 32);
    for pat in [
        &[b'n', b'a', bwt::SENTINEL][..],
        &[bwt::SENTINEL],
        &[b'a', bwt::SENTINEL, b'b'],
    ] {
        assert_eq!(idx.count(pat), 0);
        assert_eq!(idx.locate(pat), Vec::<u32>::new());
        assert_eq!(naive::search(b"banana", pat), Vec::<u32>::new());
    }
}

#[test]
fn pinned_wraparound_match_without_the_guard() {
    // `"\0a"` is a rotation of `"ab\0"` but not a substring; the sentinel guard refuses it.
    let text = [b'a', b'b', bwt::SENTINEL];
    let idx = FmIndex::build(&text, 32);
    let wrapping = [bwt::SENTINEL, b'a'];
    assert_eq!(naive::search(&text, &wrapping), Vec::<u32>::new());
    assert_eq!(idx.count(&wrapping), 0);
    assert_eq!(idx.locate(&wrapping), Vec::<u32>::new());

    assert_eq!(idx.count(&[b'b', bwt::SENTINEL]), 0);
}

/// A lone sentinel: a one-symbol BWT, so a chunk tree with no internal node.
#[test]
fn a_lone_sentinel_is_a_legal_text() {
    let text = [bwt::SENTINEL];
    let idx = FmIndex::build(&text, 32);
    assert_eq!(idx.text_len(), 1);
    assert_eq!(idx.count(&[bwt::SENTINEL]), 0);
    assert_eq!(idx.locate(&[bwt::SENTINEL]), Vec::<u32>::new());
    assert_eq!(idx.count(b""), 1);
    assert_eq!(idx.extract(0, 1), vec![bwt::SENTINEL]);
}

/// `new` builds at `SAMPLE`: the same samples as `build(text, 32)`, not those of a nearby rate.
#[test]
fn new_samples_at_the_default_rate() {
    assert_eq!(SAMPLE, 32);
    let mut text = b"mississippi banana ".repeat(20);
    text.push(bwt::SENTINEL);
    let default = FmIndex::new(&text);
    let explicit = FmIndex::build(&text, SAMPLE);
    assert_eq!(default.sample, SAMPLE);
    assert!(default.sa_samples == explicit.sa_samples);
    assert!(default.isa_samples == explicit.isa_samples);
    assert_eq!(default.size_bytes(), explicit.size_bytes());
    assert_ne!(default.size_bytes(), FmIndex::build(&text, 16).size_bytes());
    assert_eq!(FmIndex::new(b"banana\0").count(b"ana"), 2);
}

#[test]
#[should_panic(expected = "sampling rate must be at least 2")]
fn a_zero_sampling_rate_is_rejected() {
    let _ = FmIndex::build(&[b'a', bwt::SENTINEL], 0);
}
#[test]
#[should_panic(expected = "sampling rate must be at least 2")]
fn a_sampling_rate_of_one_is_rejected() {
    let _ = FmIndex::build(b"banana\0", 1);
}

#[test]
#[should_panic(expected = "text must end with SENTINEL")]
fn unterminated_text_is_rejected() {
    let _ = FmIndex::build(b"banana", 32);
}

#[test]
fn the_chunk_length_is_the_backend_s() {
    let mut text = b"banana".repeat(200);
    text.push(bwt::SENTINEL);
    assert_eq!(FmIndex::build_with_chunk(&text, 32, 50).chunk_len(), 50);
    // n = 1201, 11 bits, σ = 4: 4 · 121.
    assert_eq!(FmIndex::build(&text, 32).chunk_len(), 484);
    assert_eq!(
        FmIndex::build_with_chunk(&text, 3, 7).locate(b"nan"),
        FmIndex::build(&text, 3).locate(b"nan")
    );
}

#[test]
fn packed_ints_round_trip_at_every_width() {
    for bound in [1usize, 2, 3, 64, 65, 1 << 20, u32::MAX as usize] {
        let values: Vec<u32> = (0..200u64)
            .map(|k| ((k * 2_654_435_761) % bound as u64) as u32)
            .collect();
        let packed = Packed::new(&values, bound);
        for (k, &v) in values.iter().enumerate() {
            assert_eq!(packed.get(k), v as usize);
        }
    }
}

/// This crate's own source, the nearest real text to hand.
fn crate_sources() -> Vec<u8> {
    let mut text: Vec<u8> = concat!(
        include_str!("count_index.rs"),
        include_str!("suffix_array.rs"),
        include_str!("bwt.rs"),
        include_str!("rabin_karp.rs"),
        include_str!("patricia.rs"),
    )
    .bytes()
    .filter(|&b| b != bwt::SENTINEL)
    .collect();
    text.push(bwt::SENTINEL);
    text
}

/// The index, samples and all, is smaller than the text it replaces.
#[test]
fn index_is_smaller_than_the_text() {
    let text = crate_sources();
    let n = text.len();
    let idx = FmIndex::build(&text, 32);
    let index = idx.size_bytes();
    println!(
        "n = {n} bytes, sigma_eff = {}; index = {index} bytes ({:.2} n)",
        Alphabet::of(&text).len(),
        index as f64 / n as f64,
    );
    assert!(index < n, "index is {index} bytes for a {n}-byte text");
    // The claim is only worth anything if the text really is recoverable from the index.
    assert_eq!(idx.extract(0, n as u32), text);
}

/// A text where one pattern occurs often, at every residue of the sampling rate.
fn repetitive() -> Vec<u8> {
    let mut text: Vec<u8> = b"abracadabra".repeat(40);
    text.push(bwt::SENTINEL);
    text
}

/// `build` reads both sample arrays off the suffix array rather than walking LF.
#[test]
fn build_reads_its_samples_off_the_one_suffix_array() {
    let text = repetitive();
    let sigma = Alphabet::of(&text).len();
    LF_STEPS.with(|n| n.set(0));
    suffix_array::SA_BUILDS.with(|n| n.set(0));
    crate::strings::chunked_wavelet::OCC_CALLS.with(|n| n.set(0));
    let idx = FmIndex::build(&text, 4);
    assert_eq!(LF_STEPS.with(std::cell::Cell::get), 0, "build walked LF");
    assert_eq!(suffix_array::SA_BUILDS.with(std::cell::Cell::get), 1);
    // The only `occ` calls `build` makes are the `σ` totals for `C`.
    let calls = crate::strings::chunked_wavelet::OCC_CALLS.with(std::cell::Cell::get);
    assert!(
        calls <= sigma,
        "build made {calls} occ calls, sigma = {sigma}"
    );
    // The counter is live: the walks `locate` makes are LF steps.
    let _ = idx.locate(b"abra");
    assert!(LF_STEPS.with(std::cell::Cell::get) > 0);
    assert!(crate::strings::chunked_wavelet::OCC_CALLS.with(std::cell::Cell::get) > calls);
}

/// A `locate` walk reads each row's mark and rank in one RRR decode per row visited.
#[test]
fn locate_reads_each_mark_and_its_rank_in_one_decode() {
    let text = repetitive();
    let idx = FmIndex::build(&text, 8);
    crate::strings::rrr::RANKS.with(|n| n.set(0));
    crate::strings::rrr::SEEKS.with(|n| n.set(0));
    LF_STEPS.with(|n| n.set(0));
    let hits = idx.locate(b"abra");
    assert_eq!(hits.len(), 80);
    let steps = LF_STEPS.with(std::cell::Cell::get);
    assert!(steps > hits.len(), "the walks took steps");
    assert_eq!(
        crate::strings::rrr::SEEKS.with(std::cell::Cell::get),
        steps + hits.len(),
        "one decode of the marks per row visited"
    );
    assert_eq!(crate::strings::rrr::RANKS.with(std::cell::Cell::get), 0);
}

/// `locate_iter` is `locate` drawn lazily: same order, and taking three resolves three.
#[test]
fn locate_iter_resolves_only_the_hits_drawn() {
    let idx = FmIndex::build(&repetitive(), 8);
    let all = idx.locate(b"abra");
    assert_eq!(idx.locate_iter(b"abra").collect::<Vec<_>>(), all);
    LOCATED.with(|n| n.set(0));
    let first: Vec<u32> = idx.locate_iter(b"abra").take(3).collect();
    assert_eq!(first, all[..3]);
    assert_eq!(LOCATED.with(std::cell::Cell::get), 3);
}

/// A corrupt index (no row marked) panics within `min(sample, n)` steps, not loops.
#[test]
fn a_walk_that_meets_no_sample_panics_instead_of_looping() {
    let mut idx = FmIndex::build(&repetitive(), 4);
    let n = idx.text_len();
    idx.marks = Rrr::new(&vec![0u64; n.div_ceil(64)], n);
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let walked = std::panic::catch_unwind(|| idx.position_of(0));
        let _ = tx.send(walked.is_err());
    });
    let panicked = rx
        .recv_timeout(std::time::Duration::from_secs(30))
        .expect("the LF walk is still running: it has no bound");
    assert!(panicked, "a walk with no sampled row returned a position");
}

// -- Space and time, measured against the empirical entropies of the text. -----------------

/// `H_k` of `text` in bits per symbol, the context being the `k` following symbols
/// (Navarro §11.3.2). `k = 0` is `H0`.
fn entropy(text: &[u8], k: usize) -> f64 {
    assert!(k <= 7);
    let mut pairs: HashMap<u64, u64> = HashMap::new();
    let mut contexts: HashMap<u64, u64> = HashMap::new();
    for i in 0..text.len() {
        let ctx = &text[(i + 1).min(text.len())..(i + 1 + k).min(text.len())];
        let mut key = ctx.len() as u64;
        for &b in ctx {
            key = (key << 8) | u64::from(b);
        }
        *contexts.entry(key).or_default() += 1;
        *pairs.entry((key << 8) | u64::from(text[i])).or_default() += 1;
    }
    let bits: f64 = pairs
        .iter()
        .map(|(&pair, &count)| {
            let total = contexts[&(pair >> 8)] as f64;
            count as f64 * (total / count as f64).log2()
        })
        .sum();
    bits / text.len() as f64
}

/// What one text measured, in bits per symbol.
struct Measured {
    /// `H_0 ..= H_4`.
    entropies: Vec<f64>,
    /// The shipped `occ` structure: fixed chunks at the default length, plain bitvectors.
    fixed_block: f64,
    /// The bits its chunk trees store: the chunks' Huffman encodings.
    fixed_block_huffman: f64,
    /// The shipped index in total, at rates 32 and 64.
    shipped: [f64; 2],
    /// The same index over the checkpoint table, at rates 32 and 64.
    checkpoints: [f64; 2],
}

fn measure(label: &str, text: &[u8]) -> Measured {
    let n = text.len() as f64;
    let per = |bytes: usize| bytes as f64 * 8.0 / n;
    let last = bwt::encode(text);
    let fixed = ChunkedWavelet::<BitIndex>::new(&last);
    let b = fixed.chunk_len();
    let over_checkpoints =
        |l| FmIndex::build_over(text, l, <ByteIndex as Occ>::from_last_column).size_bytes();
    let shipped32 = FmIndex::build(text, 32);
    let m = Measured {
        entropies: (0..=4).map(|k| entropy(text, k)).collect(),
        fixed_block: per(fixed.size_bytes()),
        fixed_block_huffman: fixed.stored_bits() as f64 / n,
        shipped: [
            per(shipped32.size_bytes()),
            per(FmIndex::build(text, 64).size_bytes()),
        ],
        checkpoints: [per(over_checkpoints(32)), per(over_checkpoints(64))],
    };
    let e = &m.entropies;
    println!(
        "{label}: n = {}, sigma = {}; H0..H4 = {:.3} {:.3} {:.3} {:.3} {:.3} bits/symbol",
        text.len(),
        fixed.alphabet().len(),
        e[0],
        e[1],
        e[2],
        e[3],
        e[4]
    );
    println!(
        "{label}: occ structure, bits/symbol: fixed block (b = {b}, {} chunks, shipped) {:.3} \
             [Huffman-coded bits {:.3}]; fixed block + RRR {:.3}; SSA {:.3}; SSA + RRR {:.3}; \
             raw BWT + checkpoints {:.3}",
        fixed.chunks(),
        m.fixed_block,
        m.fixed_block_huffman,
        per(ChunkedWavelet::<Rrr>::with_chunk(&last, b).size_bytes()),
        per(WaveletTree::<BitIndex>::new(&last).size_bytes()),
        per(WaveletTree::<Rrr>::new(&last).size_bytes()),
        per(<ByteIndex as Occ>::from_last_column(&last).size_bytes()),
    );
    let sweep: Vec<String> = [b / 8, b / 4, b / 2, 2 * b, 4 * b]
        .iter()
        .map(|&len| {
            let cw = ChunkedWavelet::<BitIndex>::with_chunk(&last, len.max(1));
            format!("b = {}: {:.3}", len.max(1), per(cw.size_bytes()))
        })
        .collect();
    println!(
        "{label}: fixed-block chunk sweep, bits/symbol: {}",
        sweep.join("; ")
    );
    println!(
        "{label}: whole index, bits/symbol: shipped {:.3} (rate 32) / {:.3} (rate 64); \
             over checkpoints {:.3} / {:.3}",
        m.shipped[0], m.shipped[1], m.checkpoints[0], m.checkpoints[1]
    );
    // Whatever the numbers, the text must come back.
    assert_eq!(shipped32.extract(0, text.len() as u32), text);
    m
}

/// The loose pins every measured text must clear, set after measuring.
fn pin(m: &Measured) {
    let e = &m.entropies;
    // The chunks' Huffman encodings sum below the text's H0 and above H4.
    assert!(
        m.fixed_block_huffman < e[0],
        "{:.3} >= H0 {:.3}",
        m.fixed_block_huffman,
        e[0]
    );
    assert!(
        m.fixed_block_huffman > e[4],
        "{:.3} <= H4 {:.3}",
        m.fixed_block_huffman,
        e[4]
    );
    // The structure, tables and directories included, is below the raw byte.
    assert!(
        m.fixed_block < 8.0,
        "fixed block {:.3} bits/symbol",
        m.fixed_block
    );
    // The whole index is below the text, and well under the index over checkpoints.
    for (shipped, checkpoints) in m.shipped.iter().zip(&m.checkpoints) {
        assert!(*shipped < 8.0, "index {shipped:.3} bits/symbol");
        assert!(
            *shipped < 0.6 * checkpoints,
            "{shipped:.3} vs {checkpoints:.3}"
        );
    }
}

/// This crate's own sources: real text, always present. Measured, then pinned loosely.
#[test]
fn space_on_this_crate_s_sources() {
    let m = measure("crate sources", &crate_sources());
    pin(&m);
}

/// The corpus named by `STRINGS_CORPUS`, else `corpus/corpus.txt` (`scripts/fetch_corpus.sh`
/// fetches it). Ignored by default; run with `--release --ignored --nocapture`.
#[test]
#[ignore = "reads the corpus and takes minutes in a debug build"]
fn space_and_time_on_the_corpus() {
    let path = std::env::var("STRINGS_CORPUS").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../../corpus/corpus.txt").to_string()
    });
    let Ok(mut text) = std::fs::read(&path) else {
        println!("no corpus at {path}; nothing measured");
        return;
    };
    text.retain(|&b| b != bwt::SENTINEL);
    text.push(bwt::SENTINEL);
    let m = measure(&path, &text);
    pin(&m);

    let time = |f: &dyn Fn() -> usize| {
        let start = std::time::Instant::now();
        let sink = f();
        (start.elapsed(), sink)
    };
    // Per structure: the LF read and `occ`, at 200 000 pseudo-random positions.
    let last = bwt::encode(&text);
    let n = last.len();
    let at: Vec<usize> = (0..200_000u64)
        .map(|k| ((k * 2_654_435_761) % n as u64) as usize)
        .collect();
    fn bench<O: Occ>(o: &O, at: &[usize]) -> (std::time::Duration, usize) {
        let start = std::time::Instant::now();
        let sink: usize = at
            .iter()
            .map(|&i| {
                let (c, r) = o.symbol_and_occ(i);
                r + o.occ(c, i / 2)
            })
            .sum();
        (start.elapsed(), sink)
    }
    let checkpoints = <ByteIndex as Occ>::from_last_column(&last);
    let want = bench(&checkpoints, &at).1;
    let fixed = ChunkedWavelet::<BitIndex>::new(&last);
    let b = fixed.chunk_len();
    for (name, (t, sink)) in [
        ("raw BWT + checkpoints", bench(&checkpoints, &at)),
        ("fixed block (shipped)", bench(&fixed, &at)),
        (
            "fixed block + RRR",
            bench(&ChunkedWavelet::<Rrr>::with_chunk(&last, b), &at),
        ),
        ("SSA", bench(&WaveletTree::<BitIndex>::new(&last), &at)),
        ("SSA + RRR", bench(&WaveletTree::<Rrr>::new(&last), &at)),
    ] {
        assert_eq!(sink, want);
        println!("LF read + occ x {}: {name} {t:?}", at.len());
    }

    // Whole-index queries, the shipped index against the same index over checkpoints.
    let old = FmIndex::build_over(&text, 32, <ByteIndex as Occ>::from_last_column);
    let new = FmIndex::build(&text, 32);
    let pats: Vec<Vec<u8>> = (0..2000u64)
        .map(|k| {
            let at = ((k * 2_654_435_761) % (text.len() as u64 - 20)) as usize;
            text[at..at + 8].to_vec()
        })
        .collect();
    let (to, so) = time(&|| pats.iter().map(|p| old.count(p)).sum());
    let (tn, sn) = time(&|| pats.iter().map(|p| new.count(p)).sum());
    assert_eq!(so, sn);
    println!(
        "count x{} (length 8): over checkpoints {to:?}, shipped {tn:?}",
        pats.len()
    );
    let few = &pats[..100];
    let (to, so) = time(&|| few.iter().map(|p| old.locate(p).len()).sum());
    let (tn, sn) = time(&|| few.iter().map(|p| new.locate(p).len()).sum());
    assert_eq!(so, sn);
    println!(
        "locate x{} ({sn} hits): over checkpoints {to:?}, shipped {tn:?}",
        few.len()
    );
    let step = (text.len() as u32 - 200) / 200;
    let (to, _) = time(&|| (0..200u32).map(|k| old.extract(k * step, 100).len()).sum());
    let (tn, _) = time(&|| (0..200u32).map(|k| new.extract(k * step, 100).len()).sum());
    println!("extract 200 x 100 bytes: over checkpoints {to:?}, shipped {tn:?}");
}

// -- `is_valid`: the stored pieces agree with each other and with the column. ---------------

#[test]
fn banana_is_valid_at_every_rate() {
    for k in 2..=8 {
        let idx = FmIndex::build(b"banana\0", k);
        assert_eq!(idx.check_valid(), Ok(()), "k = {k}");
        assert!(idx.is_valid());
    }
}

proptest! {
    /// Lean: `FMIndex.valid_build`, all seven pieces.
    #[test]
    fn build_is_valid(mut text in prop::collection::vec(1u8..5, 0..200), sample in 2u32..20) {
        text.push(bwt::SENTINEL);
        let idx = FmIndex::build(&text, sample);
        prop_assert_eq!(idx.check_valid(), Ok(()));
        let oracle = FmIndex::build_over(&text, sample, <ByteIndex as Occ>::from_last_column);
        prop_assert_eq!(oracle.check_valid(), Ok(()));
    }
}

/// Column, `C`, marks, and both sample arrays.
type Pieces = (Vec<u8>, Vec<u32>, Vec<bool>, Vec<u32>, Vec<u32>);

/// The pieces of a built index, as plain data.
fn pieces(idx: &FmIndex) -> Pieces {
    let packed = |p: &Packed| (0..p.len).map(|k| p.get(k) as u32).collect();
    (
        idx.column(),
        idx.c.clone(),
        (0..idx.marks.len()).map(|i| idx.marks.get(i)).collect(),
        packed(&idx.sa_samples),
        packed(&idx.isa_samples),
    )
}

/// Which of the seven pieces hold, in `check_valid`'s order.
fn conjuncts(idx: &FmIndex) -> [bool; 7] {
    [
        idx.is_positions_kept(),
        idx.is_sentinel_once(),
        idx.is_smaller_letters_counted(),
        idx.is_walk_visits_every_row(),
        idx.is_kept_rows_listed(),
        idx.is_letters_are_bytes(),
        idx.is_rate_at_least_two(),
    ]
}

/// Which of invariant 2's three parts hold, in `is_positions_kept`'s order.
fn kept_parts(idx: &FmIndex) -> [bool; 3] {
    [
        idx.kept_evenly(),
        idx.kept_rows_flagged(),
        idx.kept_positions_correct(),
    ]
}

/// `conjuncts` with only the `i`-th false.
fn all_but(i: usize) -> [bool; 7] {
    let mut want = [true; 7];
    want[i] = false;
    want
}

/// `kept_parts` with only the `i`-th false.
fn all_parts_but(i: usize) -> [bool; 3] {
    let mut want = [true; 3];
    want[i] = false;
    want
}

#[test]
fn the_pieces_reassemble_into_a_valid_index() {
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, marks, sa, isa) = pieces(&idx);
    let again = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(again.check_valid(), Ok(()));
    assert_eq!(again.locate(b"ana"), idx.locate(b"ana"));
}

#[test]
fn a_zero_rate_breaks_rate_at_least_two_and_the_kept_positions() {
    // At k = n only position 0 is kept; at rate 0 no position may be kept (`(n + 0 - 1) / 0` is
    // 0), yet position 0 must be marked (`p % 0 = p`): with the sentinel in the column, rate 0
    // always breaks invariant 2 as well, so `check_valid` names that first.
    let idx = FmIndex::build(b"banana\0", 7);
    let (last, c, marks, sa, _) = pieces(&idx);
    let idx = FmIndex::assemble(&last, c, &marks, &sa, &[], 0);
    let mut want = all_but(0);
    want[6] = false;
    assert_eq!(conjuncts(&idx), want);
    assert_eq!(kept_parts(&idx), all_parts_but(0));
    assert_eq!(idx.check_valid(), Err("invariant 2 (positions_kept)"));
}

#[test]
fn a_mark_past_the_rows_breaks_positions_kept_alone() {
    // One mark more than rows: no row's mark changes, no rank the samples read moves.
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, mut marks, sa, isa) = pieces(&idx);
    marks.push(false);
    let idx = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(conjuncts(&idx), all_but(0));
    assert_eq!(kept_parts(&idx), all_parts_but(1));
    assert_eq!(idx.check_valid(), Err("invariant 2 (positions_kept)"));
}

#[test]
fn values_swapped_with_their_listed_rows_break_positions_kept_alone() {
    // Swap positions 2 and 4's rows and samples: the pieces agree, but not with the walk.
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, marks, mut sa, mut isa) = pieces(&idx);
    let rank = |row: u32| marks[..row as usize].iter().filter(|&&b| b).count();
    sa.swap(rank(isa[1]), rank(isa[2]));
    isa.swap(1, 2);
    let idx = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(conjuncts(&idx), all_but(0));
    assert_eq!(kept_parts(&idx), all_parts_but(2));
    assert_eq!(idx.check_valid(), Err("invariant 2 (positions_kept)"));
}

#[test]
fn a_wrong_c_breaks_smaller_letters_counted_alone() {
    let mut idx = FmIndex::build(b"banana\0", 2);
    idx.c[1] += 1;
    assert_eq!(conjuncts(&idx), all_but(2));
    assert_eq!(
        idx.check_valid(),
        Err("not in the box (smaller_letters_counted)")
    );
}

#[test]
fn a_column_with_two_sentinels_breaks_sentinel_once_alone() {
    // `ba$$`, the transform of `a$b$`: one LF cycle, two sentinels.
    let idx = FmIndex::assemble(
        &[b'b', b'a', 0, 0],
        vec![0, 2, 3],
        &[false, false, true, true],
        &[0, 2],
        &[2, 3],
        2,
    );
    assert_eq!(conjuncts(&idx), all_but(1));
}

#[test]
fn a_column_of_two_cycles_breaks_walk_visits_every_row_with_the_kept_positions() {
    // `a$a`: LF is 0 -> 1 -> 0 and 2 -> 2, so the walk from the sentinel's row fails.
    let idx = FmIndex::assemble(
        &[b'a', 0, b'a'],
        vec![0, 1],
        &[false, true, false],
        &[0],
        &[1],
        3,
    );
    assert_eq!(
        conjuncts(&idx),
        [false, true, true, false, true, true, true]
    );
    assert_eq!(kept_parts(&idx), all_parts_but(2));
}

#[test]
fn listed_rows_swapped_break_kept_rows_listed_alone() {
    // The rows of positions 2 and 4 listed the wrong way round; the samples are untouched.
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, marks, sa, mut isa) = pieces(&idx);
    isa.swap(1, 2);
    let idx = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(conjuncts(&idx), all_but(4));
    assert_eq!(idx.check_valid(), Err("not in the box (kept_rows_listed)"));
}

#[test]
fn samples_in_the_wrong_order_break_the_walk_and_the_listed_rows() {
    // A permuted grid is still the grid; the walk and the listed rows catch it.
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, marks, mut sa, isa) = pieces(&idx);
    sa.swap(0, 1);
    let idx = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(
        conjuncts(&idx),
        [false, true, true, true, false, true, true]
    );
    assert_eq!(kept_parts(&idx), all_parts_but(2));
}

#[test]
fn is_valid_does_not_panic_on_out_of_range_pieces() {
    let idx = FmIndex::build(b"banana\0", 2);
    let (last, c, marks, _, _) = pieces(&idx);
    // Samples and rows past `n`, a short `C`, short marks, and a zero rate.
    let bad = [
        FmIndex::assemble(&last, c.clone(), &marks, &[0, 100, 2, 4], &[0, 9, 99, 4], 2),
        FmIndex::assemble(&last, vec![0], &marks[..3], &[1000], &[1000], 2),
        FmIndex::assemble(&last, c, &marks, &[0, 2, 4, 6], &[3, 4, 5, 6], 0),
        FmIndex::assemble(&[], Vec::new(), &[], &[5], &[5], 1),
    ];
    for idx in &bad {
        let _ = (conjuncts(idx), kept_parts(idx));
        assert!(!idx.is_valid());
    }
}

#[test]
fn the_empty_column_fails_only_on_its_sentinel() {
    let idx = FmIndex::assemble(&[], Vec::new(), &[], &[], &[], 2);
    assert_eq!(conjuncts(&idx), all_but(1));
}

#[cfg(feature = "unchecked")]
#[test]
fn parts_round_trip() {
    let idx = FmIndex::build(b"mississippi\0", 3);
    let parts = idx.to_parts();
    let again = FmIndex::from_parts_unchecked(parts.clone());
    assert_eq!(again.to_parts(), parts);
    assert!(again.is_valid());
}

#[test]
fn a_rotated_sample_frame_breaks_positions_kept_alone() {
    // `aba$` at k = 2 with every sample moved on by 2, mod 4: still the grid, still the marked rows,
    // so only the walk sees it.
    let idx = FmIndex::build(b"aba\0", 2);
    let (last, c, marks, sa, _) = pieces(&idx);
    let sa: Vec<u32> = sa.iter().map(|&p| (p + 2) % 4).collect();
    let rows: Vec<u32> = (0..4u32).filter(|&r| marks[r as usize]).collect();
    let mut isa = vec![0u32; 2];
    for (i, &p) in sa.iter().enumerate() {
        isa[p as usize / 2] = rows[i];
    }
    let rotated = FmIndex::assemble(&last, c, &marks, &sa, &isa, 2);
    assert_eq!(conjuncts(&rotated), all_but(0));
    assert_eq!(kept_parts(&rotated), all_parts_but(2));
    assert_eq!(rotated.check_valid(), Err("invariant 2 (positions_kept)"));
    assert_ne!(rotated.locate(b"b"), idx.locate(b"b")); // what the frame is for
}
