// SPDX-License-Identifier: Apache-2.0
//! Binary search on a sorted slice: Sedgewick's closed stretch `[lo, hi]` (Sedgewick §3.1,
//! Algorithm 3.2).
//!
//! Lean counterpart: `searchM`/`searchTimed` in `lean/AlgoDesign/Searching/BinarySearch.lean`,
//! with the same stretch and midpoint, and the bound `searchProbes_le`.
//!
//! [`search_with_glances`] also returns how many middle keys the search looked at, the chapter's
//! glances: at most `floor(lg N) + 1`, which is `⌈log₂(N+1)⌉`. It runs the same loop as
//! [`search`], which is handed nothing to count into and so pays nothing for the count.

use crate::searching::Count;
use std::cmp::Ordering;

/// Binary search for `target` in `sorted`; `Some(i)` with `sorted[i] == *target`, or `None`.
///
/// `sorted` must be non-decreasing, otherwise the result is unspecified (still memory-safe and
/// terminating). On duplicates any matching index may be returned. At most `floor(lg N) + 1`
/// probes (`searchProbes_le`); sound and complete (`searchM_sound`, `search_complete`).
///
/// A `usize` `hi` cannot reach Sedgewick's `-1`, so a search sent left of index 0 stops there.
#[must_use]
pub fn search<T: Ord>(sorted: &[T], target: &T) -> Option<usize> {
    halve(sorted, target, &mut ())
}

/// [`search`], and how many glances it took: one per middle key compared.
///
/// ```
/// use algodesign::searching::binary_search::search_with_glances;
///
/// let row: Vec<i32> = (1..=15).map(|i| 3 * i - 1).collect(); // 2, 5, ..., 44
/// assert_eq!(search_with_glances(&row, &38), (Some(12), 4));
/// assert_eq!(search_with_glances(&row, &39), (None, 4));
/// ```
#[must_use]
pub fn search_with_glances<T: Ord>(sorted: &[T], target: &T) -> (Option<usize>, usize) {
    let mut glances = 0;
    let found = halve(sorted, target, &mut glances);
    (found, glances)
}

/// The loop behind both entry points: one glance at the middle of `[lo, hi]` per round.
fn halve<T: Ord, C: Count>(sorted: &[T], target: &T, glances: &mut C) -> Option<usize> {
    let mut lo = 0usize;
    let mut hi = sorted.len().checked_sub(1)?;
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        glances.add_one();
        match sorted[mid].cmp(target) {
            Ordering::Equal => return Some(mid),
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid.checked_sub(1)?,
        }
    }
    None
}

#[cfg(test)]
#[path = "unit_tests/binary_search.rs"]
mod tests;
