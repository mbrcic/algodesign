// SPDX-License-Identifier: Apache-2.0
//! Sequential search: a linear scan, and a duplicate-free builder on top of it (Sedgewick
//! §3.1, Algorithm 3.1).
//!
//! Lean counterpart: `containsM`/`buildM` in `lean/AlgoDesign/Searching/SequentialSearch.lean`,
//! with the cost theorems `time_containsM_tickEq_eq_length_of_not_mem` (a miss checks every key)
//! and `time_buildM_eq`.
//!
//! [`contains_with_checks`] also returns how many keys the scan checked, the count the chapter
//! states: `N` on a miss. It runs the same scan as [`contains`], which is handed nothing to count
//! into and so pays nothing for the count.

use crate::searching::Count;

/// Does `target` occur in `items`? One `PartialEq` comparison per element, stopping at a match.
///
/// At most `items.len()` comparisons, exactly that on a miss (`time_containsM_tickEq_le`,
/// `time_containsM_tickEq_eq_length_of_not_mem`).
#[must_use]
pub fn contains<T: PartialEq>(items: &[T], target: &T) -> bool {
    scan(items, target, &mut ())
}

/// [`contains`], and how many keys it checked: `items.len()` on a miss, the position of the
/// first match plus one on a hit.
///
/// ```
/// use algodesign::searching::sequential_search::contains_with_checks;
///
/// assert_eq!(contains_with_checks(&[4, 8, 15, 16], &15), (true, 3));
/// assert_eq!(contains_with_checks(&[4, 8, 15, 16], &23), (false, 4));
/// ```
#[must_use]
pub fn contains_with_checks<T: PartialEq>(items: &[T], target: &T) -> (bool, usize) {
    let mut checks = 0;
    let found = scan(items, target, &mut checks);
    (found, checks)
}

/// The scan behind both entry points: one check per element, front to back, until a match.
fn scan<T: PartialEq, C: Count>(items: &[T], target: &T, checks: &mut C) -> bool {
    items.iter().any(|item| {
        checks.add_one();
        item == target
    })
}

/// Build a duplicate-free collection from `keys`, skipping any key already present.
///
/// `n * (n - 1) / 2` comparisons for `n` distinct keys (`time_buildM_eq`). Appends, so the
/// output is in first-seen order.
#[must_use]
pub fn build<T: PartialEq + Clone>(keys: &[T]) -> Vec<T> {
    let mut acc: Vec<T> = Vec::new();
    for k in keys {
        if !contains(&acc, k) {
            acc.push(k.clone());
        }
    }
    acc
}

#[cfg(test)]
#[path = "unit_tests/sequential_search.rs"]
mod tests;
