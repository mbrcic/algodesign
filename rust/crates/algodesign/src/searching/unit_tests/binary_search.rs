// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;

#[test]
fn search_empty_slice() {
    let xs: Vec<i32> = vec![];
    assert_eq!(search(&xs, &0), None);
}

#[test]
fn search_single_found() {
    let xs = vec![5];
    assert_eq!(search(&xs, &5), Some(0));
}

#[test]
fn search_single_not_found() {
    let xs = vec![5];
    assert_eq!(search(&xs, &1), None);
}

#[test]
fn search_found_at_start() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &1), Some(0));
}

#[test]
fn search_found_at_middle() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &5), Some(2));
}

#[test]
fn search_found_at_end() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &9), Some(4));
}

#[test]
fn search_not_found_between_elements() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &4), None);
}

#[test]
fn search_not_found_below_range() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &0), None);
}

#[test]
fn search_not_found_above_range() {
    let xs = vec![1, 3, 5, 7, 9];
    assert_eq!(search(&xs, &100), None);
}

#[test]
fn search_duplicate_adjacent_elements_finds_a_valid_index() {
    let xs = vec![1, 2, 2, 2, 3];
    let result = search(&xs, &2);
    assert!(result.is_some());
    assert_eq!(xs[result.unwrap()], 2);
}

/// The stretch is Sedgewick's closed `[0, N - 1]`, so the first probe of four equal keys is
/// index 1 (`0 + 3 / 2`); a half-open `[0, N)` stretch would probe index 2, so which of several
/// equal keys comes back tells the two stretches apart.
#[test]
fn search_uses_the_closed_stretch_midpoint() {
    assert_eq!(search(&[2, 2, 2, 2], &2), Some(1));
    assert_eq!(search(&[1, 2, 3, 4], &2), Some(1));
}

proptest! {
    /// The standard binary-search correctness property: `search` returns `Some(i)` with
    /// `sorted[i] == target` iff `target` is actually present in `sorted`, and `None` iff
    /// absent. Checked against the naive `contains` definition of "present," independent of
    /// `search`'s own logic.
    #[test]
    fn search_agrees_with_presence(
        mut xs in prop::collection::vec(any::<i32>(), 0..200),
        target in any::<i32>(),
    ) {
        xs.sort();
        let present = xs.contains(&target);
        match search(&xs, &target) {
            Some(i) => {
                prop_assert!(i < xs.len());
                prop_assert_eq!(xs[i], target);
                prop_assert!(present);
            }
            None => prop_assert!(!present),
        }
    }

    /// A target drawn from the (sorted, possibly duplicate-containing) slice itself is
    /// always found — biases the property generator towards the "present" branch, which
    /// `search_agrees_with_presence` alone rarely hits by chance.
    #[test]
    fn search_finds_present_target(xs in prop::collection::vec(any::<i32>(), 1..200)) {
        let mut sorted = xs;
        sorted.sort();
        let idx = sorted.len() / 2;
        let target = sorted[idx];
        let result = search(&sorted, &target);
        prop_assert!(result.is_some());
        prop_assert_eq!(sorted[result.unwrap()], target);
    }
}

proptest! {
    /// The counted search answers as `search` does, in at most `⌈log₂(N+1)⌉` glances, and a miss
    /// on `N = 2^k - 1` keys takes exactly `k`.
    #[test]
    fn search_with_glances_stays_within_the_chapter_bound(
        mut xs in prop::collection::vec(any::<i32>(), 0..300),
        target in any::<i32>(),
    ) {
        xs.sort_unstable();
        let (found, glances) = search_with_glances(&xs, &target);
        prop_assert_eq!(found, search(&xs, &target));
        let bound = (usize::BITS - xs.len().leading_zeros()) as usize; // ⌈log₂(N+1)⌉
        prop_assert!(glances <= bound, "{} glances on {} keys", glances, xs.len());
    }
}

#[test]
fn a_miss_on_a_full_row_takes_every_level() {
    for k in 1..12u32 {
        let row: Vec<u32> = (0..(1u32 << k) - 1).map(|i| 2 * i + 1).collect();
        for miss in [0, 2 * (row.len() as u32) + 1, 4] {
            assert_eq!(search_with_glances(&row, &miss), (None, k as usize));
        }
    }
}
