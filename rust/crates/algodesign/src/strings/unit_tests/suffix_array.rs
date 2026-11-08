// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::naive;
use proptest::prelude::*;

#[test]
fn banana() {
    assert_eq!(suffix_array(b"banana"), vec![5, 3, 1, 0, 4, 2]);
}

proptest! {
    /// Lean: `valid_suffixArray`, `suffixArrayEarly_eq`.
    #[test]
    fn matches_the_naive_sort(text in prop::collection::vec(0u8..5, 0..300)) {
        prop_assert_eq!(suffix_array(&text), naive::suffix_array(&text));
    }

    #[test]
    fn search_finds_every_occurrence(text in prop::collection::vec(0u8..4, 1..200),
                                     pat in prop::collection::vec(0u8..4, 0..6)) {
        let sa = suffix_array(&text);
        let mut got = search(&text, &sa, &pat);
        got.sort_unstable();
        prop_assert_eq!(got, naive::search(&text, &pat));
    }
}

#[test]
fn empty_and_single_byte_texts() {
    assert_eq!(suffix_array(b""), Vec::<u32>::new());
    assert_eq!(suffix_array(b"a"), vec![0]);
    assert_eq!(suffix_array(&[0u8]), vec![0]);
    assert_eq!(search(b"", &[], b"a"), Vec::<u32>::new());
    assert_eq!(search(b"", &[], b""), vec![0]);
    assert_eq!(search(b"a", &[0], b"a"), vec![0]);
}

#[test]
fn a_proper_prefix_sorts_before_its_extension() {
    // No sentinel: "a" < "aa" < "abaa".
    assert_eq!(suffix_array(b"abaa"), vec![3, 2, 0, 1]);
    assert_eq!(suffix_array(b"abaa"), naive::suffix_array(b"abaa"));
}

#[test]
fn distinct_bytes_need_no_doubling_round() {
    // Round 0 hands out distinct tags, so the loop is never entered. Lean: suffixArrayEarly_eq.
    assert_eq!(suffix_array(b"abcdef"), vec![0, 1, 2, 3, 4, 5]);
    assert_eq!(suffix_array(b"fedcba"), vec![5, 4, 3, 2, 1, 0]);
}

/// `retag`'s group count, which the early exit reads, and its group-start tags.
#[test]
fn retag_counts_groups_and_tags_by_group_start() {
    // "banana" by first byte: a a a b n n.
    let text = b"banana";
    let sa = [5u32, 3, 1, 0, 4, 2];
    let mut tag = [0u32; 6];
    let groups = retag(&sa, &mut tag, |a, b| text[a as usize] == text[b as usize]);
    assert_eq!(groups, 3);
    // Positions 1, 3, 5 ('a') start at index 0, 0 ('b') at 3, 2 and 4 ('n') at 4.
    assert_eq!(tag, [4, 1, 5, 1, 5, 1]);
    // All distinct: the count reaches the length, which is the exit.
    let groups = retag(&sa, &mut tag, |a, b| a == b);
    assert_eq!(groups, 6);
}

#[test]
fn counting_sort_is_stable() {
    // The counting sort must be stable: sorting [1, 0, 1, 0] by the low bit gives 1, 3, 0, 2.
    let input = [10u32, 21, 12, 23];
    let mut out = [0u32; 4];
    let mut starts = [0u32; 2];
    counting_sort_by(&input, &mut out, &mut starts, |p| (p % 2) as usize);
    assert_eq!(out, [10, 12, 21, 23]);
}

#[test]
fn all_equal_bytes_force_every_round() {
    // Nothing separates until the window covers the text, so the loop runs to `h >= n`.
    let text = vec![7u8; 64];
    assert_eq!(suffix_array(&text), naive::suffix_array(&text));
}

/// One counting sort per suffix array, in round 0, however many doubling rounds follow.
#[test]
fn one_counting_sort_per_suffix_array_whatever_the_rounds() {
    let count = |text: &[u8]| {
        SORTS.with(|c| c.set(0));
        let (sa, rounds) = doubling(text);
        assert_eq!(sa, naive::suffix_array(text));
        (SORTS.with(std::cell::Cell::get), rounds)
    };
    // All-equal bytes run every round the window allows: h = 1, 2, 4, ..., 512 below 1000.
    assert_eq!(count(&[7u8; 1000]), (1, 10));
    assert_eq!(count(b"abcdef"), (1, 0));
    let mixed: Vec<u8> = (0..700u32).map(|i| (i * i % 7 % 3) as u8).collect();
    let (sorts, rounds) = count(&mixed);
    assert_eq!(sorts, 1);
    assert!(rounds >= 3, "{rounds} rounds");
}

#[test]
fn the_empty_pattern_occurs_at_every_shift_the_empty_suffix_first() {
    // n + 1 shifts: the empty suffix at n, which sorts first, is added by hand.
    let sa = suffix_array(b"banana");
    let got = search(b"banana", &sa, b"");
    assert_eq!(got, [6, 5, 3, 1, 0, 4, 2]);
    let mut sorted = got.clone();
    sorted.sort_unstable();
    assert_eq!(sorted, naive::search(b"banana", b""));
}

#[test]
fn search_returns_a_contiguous_run_in_suffix_order() {
    let sa = suffix_array(b"banana");
    assert_eq!(search(b"banana", &sa, b"ana"), [3, 1]); // suffix order, not text order
    assert_eq!(search(b"banana", &sa, b"banana"), [0]);
    assert_eq!(search(b"banana", &sa, b"bananas"), Vec::<u32>::new());
    assert_eq!(search(b"banana", &sa, b"x"), Vec::<u32>::new());
}

// `is_valid` and its two pieces: the Lean `SuffixArray.Valid`.

#[test]
fn the_suffix_array_of_abaa_is_one() {
    let sa = [3, 2, 0, 1];
    assert!(is_each_position_once(b"abaa", &sa));
    assert!(is_suffixes_sorted(b"abaa", &sa));
    assert!(is_valid(b"abaa", &sa));
}

#[test]
fn rotation_order_fails_on_order_alone() {
    // "aa" before "a": the cyclic rotation order, which no sentinel breaks.
    let sa = [2, 3, 0, 1];
    assert!(is_each_position_once(b"abaa", &sa));
    assert!(!is_suffixes_sorted(b"abaa", &sa));
    assert!(!is_valid(b"abaa", &sa));
    assert_eq!(
        check_valid(b"abaa", &sa),
        Err("invariant 2 (suffixes_sorted)")
    );
}

#[test]
fn a_repeated_position_fails_on_permutation_alone() {
    let sa = [3, 3, 0, 1];
    assert!(!is_each_position_once(b"abaa", &sa));
    assert!(is_suffixes_sorted(b"abaa", &sa));
    assert!(!is_valid(b"abaa", &sa));
    assert_eq!(
        check_valid(b"abaa", &sa),
        Err("invariant 1 (each_position_once)")
    );
}

#[test]
fn a_position_past_the_end_fails_both_and_does_not_panic() {
    // 9 names the empty suffix, as Lean's `List.drop` reads it, and "baa" <= "" is false.
    let sa = [3, 2, 0, 1, 9];
    assert!(!is_each_position_once(b"abaa", &sa));
    assert!(!is_suffixes_sorted(b"abaa", &sa));
    assert!(!is_valid(b"abaa", &sa));
    assert!(is_suffixes_sorted(b"abaa", &[9, 3]));
}

proptest! {
    /// Lean: `valid_suffixArray`, checked by the library's own predicate.
    #[test]
    fn suffix_array_passes_is_valid(text in prop::collection::vec(0u8..4, 0..200)) {
        prop_assert!(is_valid(&text, &suffix_array(&text)));
        prop_assert_eq!(check_valid(&text, &suffix_array(&text)), Ok(()));
    }
}
