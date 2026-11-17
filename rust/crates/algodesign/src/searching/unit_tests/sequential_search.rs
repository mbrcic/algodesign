// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;
use std::collections::HashSet;

#[test]
fn contains_empty_is_false() {
    let xs: Vec<i32> = vec![];
    assert!(!contains(&xs, &0));
}

#[test]
fn contains_single_found() {
    let xs = vec![42];
    assert!(contains(&xs, &42));
}

#[test]
fn contains_single_not_found() {
    let xs = vec![42];
    assert!(!contains(&xs, &7));
}

#[test]
fn contains_found_at_start() {
    let xs = vec![1, 2, 3, 4];
    assert!(contains(&xs, &1));
}

#[test]
fn contains_found_at_middle() {
    let xs = vec![1, 2, 3, 4];
    assert!(contains(&xs, &3));
}

#[test]
fn contains_found_at_end() {
    let xs = vec![1, 2, 3, 4];
    assert!(contains(&xs, &4));
}

#[test]
fn contains_not_found() {
    let xs = vec![1, 2, 3, 4];
    assert!(!contains(&xs, &99));
}

#[test]
fn build_empty() {
    let built: Vec<i32> = build(&[]);
    assert!(built.is_empty());
}

#[test]
fn build_skips_duplicates() {
    let keys = vec![1, 2, 1, 3, 2, 2, 4];
    let built = build(&keys);
    assert_eq!(built, vec![1, 2, 3, 4]);
}

#[test]
fn build_all_distinct_preserves_first_seen_order() {
    let keys = vec![5, 3, 1, 4];
    let built = build(&keys);
    assert_eq!(built, vec![5, 3, 1, 4]);
}

proptest! {
    /// `contains` agrees with the naive "any element equals target" check — the statement
    /// the cost theorems are *about*, checked here independently of cost.
    #[test]
    fn contains_matches_naive_any(
        xs in prop::collection::vec(any::<i32>(), 0..200),
        target in any::<i32>(),
    ) {
        let expected = xs.contains(&target);
        prop_assert_eq!(contains(&xs, &target), expected);
    }

    /// `build`'s output never contains duplicates — the Lean file's "a `Set`, not a `Map`"
    /// semantics, checked directly.
    #[test]
    fn build_has_no_duplicates(keys in prop::collection::vec(any::<i32>(), 0..200)) {
        let built = build(&keys);
        let mut seen = HashSet::new();
        for k in &built {
            prop_assert!(seen.insert(*k), "build produced a duplicate: {k}");
        }
    }

    /// `build`'s output, as a set, is exactly the set of distinct elements of `keys` —
    /// duplicate-free *and* nothing lost or invented.
    #[test]
    fn build_matches_dedup_set(keys in prop::collection::vec(any::<i32>(), 0..200)) {
        let built = build(&keys);
        let expected: HashSet<i32> = keys.iter().copied().collect();
        let actual: HashSet<i32> = built.iter().copied().collect();
        prop_assert_eq!(actual, expected.clone());
        prop_assert_eq!(built.len(), expected.len());
    }
}

proptest! {
    /// The counted scan answers as `contains` does and checks every key on a miss, one more than
    /// the first match's position on a hit.
    #[test]
    fn contains_with_checks_counts_what_the_chapter_counts(
        xs in prop::collection::vec(0..20i32, 0..60),
        target in 0..20i32,
    ) {
        let (found, checks) = contains_with_checks(&xs, &target);
        prop_assert_eq!(found, contains(&xs, &target));
        let want = xs.iter().position(|x| *x == target).map_or(xs.len(), |i| i + 1);
        prop_assert_eq!(checks, want);
    }
}
