// SPDX-License-Identifier: Apache-2.0
//! The cheapest path from one start to one goal, by A*: Dijkstra's walk with each queue entry's
//! key the known cost plus an estimate of the cost still to go.
//!
//! The estimate is one number per vertex, given by the caller. The walk is Dijkstra's, entry for
//! entry: the smallest (key, vertex id) comes off the queue, a settled vertex is skipped and never
//! tried again (no reopening), and the vertex taken off is settled at its key less its estimate.
//! It stops when the goal comes off the queue, settled and its row untried (Hart, Nilsson and
//! Raphael, "A Formal Basis for the Heuristic Determination of Minimum Cost Paths", IEEE Trans.
//! SSC 4 (1968), p. 102). Read with the changed costs, arrow `a → b` costing its cost plus the
//! estimate at `b` minus the estimate at `a`, the search is Dijkstra's walk to the goal (Sanders,
//! Mehlhorn, Dietzfelbinger and Dementiev, *Sequential and Parallel Algorithms and Data
//! Structures*, §10.8.1, pp. 323–324); Cormen, Leiserson, Rivest and Stein, *Introduction to
//! Algorithms*, 4th ed., §23.3, eq. (23.10), p. 663, reweight by
//! `w + h(u) − h(v)`, the same change with `h` the negated estimate.
//!
//! **The estimate must be consistent** (box invariant 1): at least zero, zero at the goal, and
//! along any arrow it drops by no more than the arrow costs. Then every changed cost is at least
//! zero, and the goal gets its cheapest cost. Release builds do not check it: an estimate that
//! never overstates the cost to go but breaks it can give a dearer path (petgraph issue #378).
//! Debug builds assert it. No arrow needs to cost at least zero; the changed costs do, by the
//! invariant. The sums are not saturated: the input range is costs and estimates whose total over
//! every path fits an `i64`.
//!
//! The search's states are [`State`]s of Dijkstra's walk, their keys moved by the estimate; the
//! functions [`is_estimate_is_consistent`], [`is_walk_is_cheapest_paths_on_changed_costs`],
//! [`is_valid`] and [`check_valid`] are the pieces of the Lean `Valid` and `WellFormed` on them.
//!
//! **Against the Python, and how fast.** Debug builds assert the invariant, where the Python
//! checks nothing, and an estimate list of the wrong length is an `Err` here, a `ValueError`
//! there. The search is Dijkstra's keyed walk, the one `dijkstra_to` runs, with the estimate added
//! to each key as it is pushed, where the Python writes its own loop. [`a_star_with_settled`] runs
//! that heap walk too, where the Python's runs `start_state` and `step` on `State`. The walk reads
//! each row straight from the graph's packed arrays and queues plain (key, vertex) pairs in the
//! standard library's binary heap.
//! `cargo bench -p algodesign --bench paths -- a_star` times it on a 300 × 300 grid with the grid
//! distance to the goal as the estimate, beside the zero estimate, which makes it Dijkstra's walk
//! to the goal.
//!
//! Lean counterpart: `AlgoDesign.Paths.AStar`. The Lean reads a missing estimate as 0, so it
//! takes an estimate list of any length, where [`a_star`] refuses one of the wrong length.

use super::dijkstra::{walk_keyed, State};
use super::distances::Distances;
use super::network::{Network, PathsError};

/// The cost of the cheapest path from `start` to `goal`, and the previous vertex of each vertex
/// the search reached; the goal's cost is `None` when no path leads there. Other vertices may be
/// left with a known cost that is not their cheapest, or none. `O(m log m)` for `m` arrows, as
/// Dijkstra's walk; how many vertices are settled depends on the estimate.
///
/// `estimate[v]` is the estimate at vertex `v`; it must be consistent (debug builds assert it).
///
/// Lean: `AStar.contract`.
///
/// # Errors
///
/// [`PathsError::EstimateCountMismatch`] when `estimate` does not have one entry per vertex.
///
/// # Panics
///
/// If `start` or `goal` is not a vertex of `net`; in debug builds, if the estimate is not
/// consistent.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{a_star, Network};
///
/// // 0 → 1 → 2 costs 2, 0 → 2 costs 3; the estimate is the cost still to go.
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![1, 1, 3]).unwrap();
/// let d = a_star(&net, 0, 2, &[2, 1, 0]).unwrap();
/// assert_eq!(d.cost[2], Some(2));
/// assert_eq!(d.path_to(2), Some(vec![0, 1, 2]));
/// ```
pub fn a_star(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
) -> Result<Distances, PathsError> {
    check_input(net, goal, estimate)?;
    Ok(search(net, start, goal, estimate, None))
}

/// [`a_star`], with the vertices in the order the search settles them, the goal last if it is
/// reached. `O(m log m)`, as [`a_star`].
///
/// Lean: `AStar.contract`.
///
/// # Errors
///
/// As [`a_star`].
///
/// # Panics
///
/// As [`a_star`].
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{a_star_with_settled, Network};
///
/// // 0 → 1 and 0 → 2 cost 1, 2 → 3 costs 1; the estimate steers the search away from 1.
/// let g = Digraph::new(4, &[(0, 1), (0, 2), (2, 3)]).unwrap();
/// let net = Network::new(g, vec![1, 1, 1]).unwrap();
/// let (d, settled) = a_star_with_settled(&net, 0, 3, &[2, 5, 1, 0]).unwrap();
/// assert_eq!(settled, [0, 2, 3]);
/// assert_eq!(d.cost[3], Some(2));
/// ```
pub fn a_star_with_settled(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
) -> Result<(Distances, Vec<u32>), PathsError> {
    check_input(net, goal, estimate)?;
    let mut settled = Vec::new();
    let d = search(net, start, goal, estimate, Some(&mut settled));
    Ok((d, settled))
}

/// One estimate per vertex, the goal a vertex; the invariant asserted in debug builds only.
fn check_input(net: &Network, goal: u32, estimate: &[i64]) -> Result<(), PathsError> {
    let n = net.n();
    if estimate.len() != n {
        return Err(PathsError::EstimateCountMismatch {
            estimates: estimate.len(),
            vertices: n,
        });
    }
    assert!((goal as usize) < n, "goal {goal} out of range 0..{n}");
    debug_assert!(
        is_estimate_is_consistent(net, goal, estimate),
        "the estimate is not consistent: A* assumes it is at least zero, zero at the goal, and \
         dropping by no more than each arrow costs"
    );
    Ok(())
}

/// The search as release builds run it: the invariant unchecked, the estimate one per vertex.
fn search(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
    order: Option<&mut Vec<u32>>,
) -> Distances {
    walk_keyed(
        net,
        start,
        Some(goal),
        |v| estimate[v],
        order,
        |_, _, _, _, _| {},
    )
}

/// The labels [`check_valid`] names, in the order of the Lean `Valid` and `WellFormed`.
const LABELS: [&str; 2] = [
    "invariant 1 (estimate_is_consistent)",
    "not in the box (walk_is_cheapest_paths_on_changed_costs)",
];

/// The estimate at `v`; 0 past the list, as the Lean reads it.
fn at(estimate: &[i64], v: usize) -> i64 {
    estimate.get(v).copied().unwrap_or(0)
}

/// The changed costs: arrow `i` from `a` to `b` costs its cost plus the estimate at `b` minus the
/// estimate at `a`, on the same graph. An estimate past the list counts as 0. `None` when a changed
/// cost leaves `i64`.
///
/// Lean: `AStar.changed`.
#[must_use]
pub fn changed(net: &Network, estimate: &[i64]) -> Option<Network> {
    let g = net.graph();
    let cost = (0..g.arrow_count())
        .map(|i| {
            let (a, b) = g.arrow(i);
            net.arrow_cost(i)
                .checked_add(at(estimate, b as usize))?
                .checked_sub(at(estimate, a as usize))
        })
        .collect::<Option<Vec<i64>>>()?;
    Network::new(g.clone(), cost).ok()
}

/// A state of the search read on the changed costs: each known cost plus the estimate at its
/// vertex, and each queue key, less `h0`, the estimate at the start. `None` when a moved number
/// leaves `i64`.
///
/// Lean: `AStar.shifted`.
#[must_use]
pub fn shifted(st: &State, estimate: &[i64], h0: i64) -> Option<State> {
    let known = st
        .known
        .iter()
        .enumerate()
        .map(|(v, k)| match k {
            None => Some(None),
            Some(d) => d
                .checked_add(at(estimate, v))
                .and_then(|x| x.checked_sub(h0))
                .map(Some),
        })
        .collect::<Option<Vec<_>>>()?;
    let queue = st
        .queue
        .iter()
        .map(|&(key, v)| key.checked_sub(h0).map(|k| (k, v)))
        .collect::<Option<Vec<_>>>()?;
    Some(State {
        settled: st.settled.clone(),
        known,
        previous: st.previous.clone(),
        queue,
        pushed: st.pushed,
    })
}

/// Box invariant 1: the estimate is at least zero, is zero at the goal, and along any arrow
/// drops by no more than the arrow costs. An estimate past the list counts as 0.
///
/// Lean: `EstimateIsConsistent`.
#[must_use]
pub fn is_estimate_is_consistent(net: &Network, goal: u32, estimate: &[i64]) -> bool {
    let g = net.graph();
    (0..g.n()).all(|v| at(estimate, v) >= 0)
        && at(estimate, goal as usize) == 0
        && (0..g.arrow_count()).all(|i| {
            let (a, b) = g.arrow(i);
            i128::from(at(estimate, a as usize))
                <= i128::from(net.arrow_cost(i)) + i128::from(at(estimate, b as usize))
        })
}

/// Not in the box: read on the changed costs, the search's state is a legal state of Dijkstra's
/// walk from `start`. `cheapest` and `through` are the answers Dijkstra's checks take, on the
/// changed costs: each vertex's cheapest cost from the start, and the cheapest over paths whose
/// every vertex but the last is settled in `st`.
///
/// Lean: `WalkIsCheapestPathsOnChangedCosts`.
#[must_use]
pub fn is_walk_is_cheapest_paths_on_changed_costs(
    net: &Network,
    start: u32,
    estimate: &[i64],
    st: &State,
    cheapest: &[Option<i64>],
    through: &[Option<i64>],
) -> bool {
    let Some(changed) = changed(net, estimate) else {
        return false;
    };
    shifted(st, estimate, at(estimate, start as usize))
        .is_some_and(|sh| sh.is_valid(&changed, start, cheapest, through))
}

/// Lean `Valid` and `WellFormed`: [`is_estimate_is_consistent`], then
/// [`is_walk_is_cheapest_paths_on_changed_costs`].
#[must_use]
pub fn is_valid(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
    st: &State,
    cheapest: &[Option<i64>],
    through: &[Option<i64>],
) -> bool {
    check_valid(net, start, goal, estimate, st, cheapest, through).is_ok()
}

/// [`is_valid`], naming the first piece that fails.
///
/// # Errors
///
/// `"invariant 1 (estimate_is_consistent)"` or
/// `"not in the box (walk_is_cheapest_paths_on_changed_costs)"`.
pub fn check_valid(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
    st: &State,
    cheapest: &[Option<i64>],
    through: &[Option<i64>],
) -> Result<(), &'static str> {
    let pieces = [
        is_estimate_is_consistent(net, goal, estimate),
        is_walk_is_cheapest_paths_on_changed_costs(net, start, estimate, st, cheapest, through),
    ];
    match pieces.iter().position(|&ok| !ok) {
        Some(i) => Err(LABELS[i]),
        None => Ok(()),
    }
}

/// Every state of the search from `start` to `goal`, from the start to the step before the goal
/// comes off the queue (or to the empty queue), one per entry taken off; the state the stop leaves,
/// its goal row untried, is not one of them. The keys are the search's, known cost plus estimate.
/// The invariant is not checked, so an estimate that breaks it gives the states of the wrong
/// answer. For tests; not part of the API.
///
/// # Panics
///
/// If `start` is not a vertex of `net`, or `estimate` has fewer entries than `net` has vertices.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn trace(net: &Network, start: u32, goal: u32, estimate: &[i64]) -> Vec<State> {
    State::trace_keyed(net, start, Some(goal), |v| estimate[v])
}

#[cfg(test)]
#[path = "unit_tests/a_star.rs"]
mod tests;
