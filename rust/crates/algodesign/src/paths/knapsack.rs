// SPDX-License-Identifier: Apache-2.0
//! Knapsack as a longest path: the most value a box of capacity `C` can hold, and the items that
//! give it.
//!
//! A state `(i, w)` says the first `i` items are decided and they use weight `w`. From it there
//! are two arrows: skip item `i`, to `(i + 1, w)`, gaining nothing; or take it, to
//! `(i + 1, w + weight)`, gaining its value, when that weight is at most `C`. Every arrow decides
//! one more item, so the graph has no cycle, and each path from `(0, 0)` to the last layer is one
//! packing that fits, worth what the path gains. The states are never built as a graph: a table
//! `best[i][w]` holds the largest gain known into each, `None` while no arrow has reached it, and
//! is filled layer by layer, which is a topological order. From each reached state of a layer,
//! by increasing weight, the walk tries the skip, then the take when it fits; an arrow raises its
//! end's gain when it gains more, or reaches it first. This is Ahuja, Magnanti and Orlin, *Network
//! Flows*, Fig. 4.3, pp. 101–102.
//!
//! The answer is the best gain in the last layer, the least weight on a tie. The items come from
//! walking back from there through the table: item `i − 1` is taken when taking it fits and gains
//! at least as much as skipping it, a tie taking it (Roughgarden, *Algorithms Illuminated*, Part 3,
//! §16.5, p. 131). That test reads only the layer before, so the walk makes it while it fills each
//! layer and keeps the answer as one bit per cell, set where the walk back takes the item; of the
//! table it keeps only the layer it reads and the layer it fills (Sanders, Mehlhorn, Dietzfelbinger
//! and Dementiev, *Sequential and Parallel Algorithms and Data Structures*, Ex. 12.11, p. 369;
//! Korte and Vygen, *Combinatorial Optimization*, p. 475): `n (C + 1)` bits and `2 (C + 1)` cells
//! of `Option<i64>` for `n` items.
//!
//! The sums are not saturated: the input range is values whose total over every packing fits an
//! `i64`.
//!
//! **Against the Python, and how fast.** The Python keeps the whole table, `(n + 1)(C + 1)`
//! cells, and walks back through it by one call per item. Here the walk keeps two layers and one
//! bit per state, and walks back by a loop over the bits. The Python also keeps `State`, the
//! walk's state with its `start` and `step`, as the Lean's. The arrows, their order, the answer
//! and the items are the same. The two layers are allocated once and refilled for every item, and
//! the bits are packed 64 to a word.
//! `cargo bench -p algodesign --bench paths -- knapsack` times it on 1000 items in a box of 10^4.
//!
//! Lean counterpart: `AlgoDesign.Paths.Knapsack`.

use super::network::PathsError;

/// The answer: the best value and the items that give it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Packing {
    /// The best value over every set of items that fits.
    pub value: i64,
    /// The items chosen, by index in increasing order.
    pub items: Vec<usize>,
}

/// The most value that fits in a box of `capacity`, item `i` weighing `weights[i]` and worth
/// `values[i]`, and the items that give it. A value may be below zero; such an item is never
/// worth taking. `O(n (C + 1))` time for `n` items and capacity `C`: at most two arrows out of each
/// state before the last layer. `n (C + 1)` bits and `2 (C + 1)` cells of table.
///
/// The values of every packing must sum within `i64`.
///
/// Lean: `Knapsack.knapsack_spec`, `chosen_spec` and `knapsack_cost`.
///
/// # Errors
///
/// [`PathsError::ValueCountMismatch`] when `values` does not have one entry per weight.
///
/// # Panics
///
/// If the record (two layers of `capacity + 1` cells and `n (capacity + 1)` bits) does not fit in
/// memory: "a capacity that fits in memory" when the `capacity + 1` cells of a layer overflow a
/// `usize`, "a table that fits in memory" when the words that hold the bits do.
///
/// # Examples
///
/// ```
/// use algodesign::paths::{knapsack, Packing, PathsError};
///
/// // A box of 10 kg: one order of 6 kg for 30, two of 5 kg for 20 each. Greedy by value per kilo
/// // takes the 6 kg order and then nothing fits; the two 5 kg orders together give 40.
/// let p = knapsack(&[6, 5, 5], &[30, 20, 20], 10).unwrap();
/// assert_eq!(p, Packing { value: 40, items: vec![1, 2] });
/// assert_eq!(
///     knapsack(&[6, 5], &[30], 10),
///     Err(PathsError::ValueCountMismatch { values: 1, weights: 2 })
/// );
/// ```
pub fn knapsack(weights: &[u64], values: &[i64], capacity: u64) -> Result<Packing, PathsError> {
    if values.len() != weights.len() {
        return Err(PathsError::ValueCountMismatch {
            values: values.len(),
            weights: weights.len(),
        });
    }
    Ok(walk(weights, values, capacity))
}

/// Relax the cell `x` of the next layer with the gain `b`: keep `b` if `x` has no known gain or
/// `b` is more.
fn relax(layer: &mut [Option<i64>], x: usize, b: i64) {
    if layer[x].is_none_or(|old| old < b) {
        layer[x] = Some(b);
    }
}

/// The walk: the layers filled one after another in two rows, the answer read off the last, and
/// the items read back through the bits. The caller checks that there is one value per weight.
fn walk(weights: &[u64], values: &[i64], capacity: u64) -> Packing {
    debug_assert_eq!(weights.len(), values.len());
    let n = weights.len();
    let width = usize::try_from(capacity)
        .ok()
        .and_then(|c| c.checked_add(1))
        .expect("a capacity that fits in memory");
    // One bit per cell of every layer after the first, 64 to a word: layer `i + 1` has the words
    // `taken[i * words..(i + 1) * words]`, and its bit at `w` says the walk back takes item `i`
    // from `(i + 1, w)`. The count of words must fit a `usize`.
    let words = width.div_ceil(64);
    let mut taken: Vec<u64> = vec![0; n.checked_mul(words).expect("a table that fits in memory")];
    let mut row: Vec<Option<i64>> = vec![None; width];
    let mut next: Vec<Option<i64>> = vec![None; width];
    row[0] = Some(0);
    for i in 0..n {
        next.fill(None);
        let bits = &mut taken[i * words..(i + 1) * words];
        let (weight, value) = (weights[i], values[i]);
        for (w, &cell) in row.iter().enumerate() {
            let Some(b) = cell else {
                continue;
            };
            // Skip the item.
            relax(&mut next, w, b);
            // Take it, if it fits: w ≤ C, so C − w does not wrap.
            if weight <= capacity - w as u64 {
                let x = w + weight as usize;
                relax(&mut next, x, b + value);
                // The walk back's test at `x`, which reads only the layer before, `row`.
                if take_wins(cell, value, row[x]) {
                    bits[x / 64] |= 1 << (x % 64);
                }
            }
        }
        std::mem::swap(&mut row, &mut next);
    }
    // The best gain in the last layer, the least weight on a tie.
    let mut end: Option<(i64, usize)> = None;
    for (w, &cell) in row.iter().enumerate() {
        if let Some(b) = cell {
            if end.is_none_or(|(b0, _)| b0 < b) {
                end = Some((b, w));
            }
        }
    }
    let Some((value, mut w)) = end else {
        return Packing {
            value: 0,
            items: Vec::new(),
        };
    };
    // Walk back: item i is taken where its bit is set, which is where taking it fits and gains at
    // least as much as skipping it.
    let mut items = Vec::new();
    for i in (0..n).rev() {
        if (taken[i * words + w / 64] >> (w % 64)) & 1 == 1 {
            items.push(i);
            w -= weights[i] as usize;
        }
    }
    items.reverse();
    Packing { value, items }
}

/// Taking the item wins: the gain from taking it, `b + value`, is known and at least the gain `c`
/// from skipping it.
fn take_wins(b: Option<i64>, value: i64, c: Option<i64>) -> bool {
    b.is_some_and(|b| c.is_none_or(|c| c <= b + value))
}

#[cfg(test)]
#[path = "unit_tests/knapsack.rs"]
mod tests;
