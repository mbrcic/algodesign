// SPDX-License-Identifier: Apache-2.0
//! The cheapest path from one start to every vertex, by Dijkstra's walk: a settled vertex is never
//! changed again.
//!
//! A binary heap holds lazy entries (key, vertex) and gives the smallest by key, then by vertex
//! id. The walk takes the smallest entry; if its vertex is settled, the entry is dropped; otherwise
//! the vertex is settled and its row walked in the Graphs chapter's order, by neighbor, then id.
//! For each arrow to a vertex not settled, a cost lower than the known one (or the first) is
//! recorded with the vertex it came from, and a new entry is pushed; the old entry stays in the
//! heap and is dropped when it comes off. The previous vertex changes only when a cost drops. This
//! is Weiss, *Data Structures and Algorithm Analysis in C++*, 4th ed., Fig. 9.31, p. 399, and
//! Kleinberg and Tardos, *Algorithm Design*, §4.4, p. 180; ties by vertex id as Goldberg and
//! Harrelson (SODA 2005).
//!
//! **Assumes no arrow is negative.** Release builds do not check it: with such an
//! arrow a settled cost can be wrong (0 → 1 costing 1, 0 → 2 costing 2, 2 → 1 costing −2 settles
//! vertex 1 at 1, though 0 → 2 → 1 costs 0). Debug builds assert it. The sums are not saturated:
//! the input range is costs whose total over every path fits an `i64`.
//!
//! [`State`] is a state of the walk, with one check per piece of the Lean `Valid` and `WellFormed`
//! on it.
//!
//! **Against the Python, and how fast.** Debug builds assert that no arrow is
//! negative, where the Python checks nothing. One keyed walk serves [`dijkstra`], [`dijkstra_to`],
//! [`dijkstra_with_settled`] and A*, where the Python writes the loop in each, and
//! [`dijkstra_with_settled`] runs that heap walk, where the Python's runs `State`. The walk reads
//! each row straight from the graph's packed arrays, keeps the known costs, the previous vertices
//! and the settled marks in flat vectors, and queues plain (cost, vertex) pairs in the standard
//! library's binary heap. The hooks that record its states are compiled only into test builds and
//! under the `unchecked` feature.
//! `cargo bench -p algodesign --bench paths -- dijkstra` times it on 10^5 vertices and 4 · 10^5
//! arrows.
//!
//! Lean counterpart: `AlgoDesign.Paths.Dijkstra`.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use super::distances::Distances;
use super::network::Network;

/// The queue: the smallest (key, vertex) on top.
pub(super) type Queue = BinaryHeap<Reverse<(i64, u32)>>;

/// The cheapest cost from `start` to every vertex, and each vertex's previous vertex on a
/// cheapest path. `O(m log m)` for `m` arrows: each arrow is tried at most once and pushes at
/// most one entry.
///
/// No arrow may be negative; with one, a cost can be wrong (debug builds assert it).
/// The costs along every path must sum within `i64`.
///
/// Lean: `Dijkstra.contract`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`; in debug builds, if an arrow is negative.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dijkstra, Network};
///
/// // Two arrows from 0 to 1 that cost differently; 2 is out of reach.
/// let g = Digraph::new(3, &[(0, 1), (0, 1)]).unwrap();
/// let d = dijkstra(&Network::new(g, vec![5, 3]).unwrap(), 0);
/// assert_eq!(d.cost, [Some(0), Some(3), None]);
/// assert_eq!(d.previous, [None, Some(0), None]);
/// ```
#[must_use]
pub fn dijkstra(net: &Network, start: u32) -> Distances {
    debug_assert_no_arrow_below_zero(net);
    walk(net, start, None, None, |_, _, _, _, _| {})
}

/// [`dijkstra`], stopping when `goal` comes off the queue: the goal is settled and its row is not
/// tried. The goal's cost and the path to it are as [`dijkstra`] gives them; other vertices may be
/// left with a known cost that is not their cheapest, or none. `O(m log m)`, as [`dijkstra`].
///
/// Lean: `Dijkstra.dijkstraTo_goal`, `Dijkstra.dijkstraTo_previous`,
/// `Dijkstra.dijkstraTo_unreached`.
///
/// # Panics
///
/// If `start` or `goal` is not a vertex of `net`; in debug builds, if an arrow is
/// negative.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dijkstra_to, Network};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2)]).unwrap();
/// let d = dijkstra_to(&Network::new(g, vec![1, 1]).unwrap(), 0, 1);
/// assert_eq!(d.cost, [Some(0), Some(1), None]);
/// ```
#[must_use]
pub fn dijkstra_to(net: &Network, start: u32, goal: u32) -> Distances {
    let n = net.n();
    assert!((goal as usize) < n, "goal {goal} out of range 0..{n}");
    debug_assert_no_arrow_below_zero(net);
    walk(net, start, Some(goal), None, |_, _, _, _, _| {})
}

/// [`dijkstra`], with the vertices in the order the walk settles them. `O(m log m)`, as
/// [`dijkstra`].
///
/// Lean: `Dijkstra.contract`.
///
/// # Panics
///
/// As [`dijkstra`].
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dijkstra_with_settled, Network};
///
/// // 0 → 2 costs 1 and 0 → 1 costs 1: the tie goes to the lower vertex id.
/// let g = Digraph::new(3, &[(0, 2), (0, 1)]).unwrap();
/// let (d, settled) = dijkstra_with_settled(&Network::new(g, vec![1, 1]).unwrap(), 0);
/// assert_eq!(settled, [0, 1, 2]);
/// assert_eq!(d.cost, [Some(0), Some(1), Some(1)]);
/// ```
#[must_use]
pub fn dijkstra_with_settled(net: &Network, start: u32) -> (Distances, Vec<u32>) {
    debug_assert_no_arrow_below_zero(net);
    let mut settled = Vec::new();
    let d = walk(net, start, None, Some(&mut settled), |_, _, _, _, _| {});
    (d, settled)
}

/// The box's Assumes, checked in debug builds only.
fn debug_assert_no_arrow_below_zero(net: &Network) {
    debug_assert!(
        net.cost().iter().all(|&c| c >= 0),
        "an arrow costs less than nothing: Dijkstra assumes none does"
    );
}

/// Dijkstra's walk from `start`, stopping when `goal` comes off the queue if there is one, and
/// recording the settled vertices in `order` if it is given. It hands `watch` its state at the
/// start and after every entry taken off the queue: the settled vertices in order, the known costs,
/// the previous vertices, the queue and the entries pushed. Only test builds and the `unchecked`
/// feature make the calls, and only the traces of `State`, which give an `order`, read them.
/// The Assumes is not checked here.
fn walk(
    net: &Network,
    start: u32,
    goal: Option<u32>,
    order: Option<&mut Vec<u32>>,
    watch: impl FnMut(&[u32], &[Option<i64>], &[Option<u32>], &Queue, usize),
) -> Distances {
    walk_keyed(net, start, goal, |_| 0, order, watch)
}

/// The walk of `walk` with each queue entry's key the known cost plus `estimate` at its vertex:
/// the start is queued with its estimate, and a vertex taken off the queue is settled at its key
/// less its estimate. With the estimate zero everywhere it is Dijkstra's walk; A* runs it with
/// the caller's estimate.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
pub(super) fn walk_keyed(
    net: &Network,
    start: u32,
    goal: Option<u32>,
    estimate: impl Fn(usize) -> i64,
    mut order: Option<&mut Vec<u32>>,
    mut watch: impl FnMut(&[u32], &[Option<i64>], &[Option<u32>], &Queue, usize),
) -> Distances {
    let g = net.graph();
    let cost = net.cost();
    let n = g.n();
    let s = start as usize;
    assert!(s < n, "start {start} out of range 0..{n}");
    let (offsets, neighbors, ids) = (&g.out.offsets, &g.out.neighbors, &g.out.ids);
    let mut known: Vec<Option<i64>> = vec![None; n];
    let mut previous: Vec<Option<u32>> = vec![None; n];
    let mut settled = vec![false; n];
    let mut queue: Queue = BinaryHeap::new();
    known[s] = Some(0);
    queue.push(Reverse((estimate(s), start)));
    let mut pushed = 1usize;
    watched!(watch(
        order.as_deref().map_or(&[], |o| o),
        &known,
        &previous,
        &queue,
        pushed
    ));
    while let Some(Reverse((key, u))) = queue.pop() {
        let u_at = u as usize;
        if !settled[u_at] {
            let du = key - estimate(u_at);
            settled[u_at] = true;
            if let Some(o) = order.as_deref_mut() {
                o.push(u);
            }
            if goal == Some(u) {
                break;
            }
            for k in offsets[u_at]..offsets[u_at + 1] {
                let w = neighbors[k];
                let w_at = w as usize;
                if settled[w_at] {
                    continue;
                }
                let dw = du + cost[ids[k] as usize];
                if known[w_at].is_none_or(|old| dw < old) {
                    known[w_at] = Some(dw);
                    previous[w_at] = Some(u);
                    queue.push(Reverse((dw + estimate(w_at), w)));
                    watched!(pushed += 1);
                }
            }
        }
        watched!(watch(
            order.as_deref().map_or(&[], |o| o),
            &known,
            &previous,
            &queue,
            pushed
        ));
    }
    Distances {
        cost: known,
        previous,
    }
}

/// The labels [`State::check_valid`] names, in the order of the Lean `Valid` and `WellFormed`.
const LABELS: [&str; 6] = [
    "invariant 1 (settled_are_cheapest)",
    "invariant 2 (known_is_cheapest_through_settled)",
    "not in the box (start_settled_first)",
    "not in the box (settled_rows_tried)",
    "not in the box (queue_holds_known)",
    "not in the box (previous_leads_back)",
];

/// A state of Dijkstra's walk: the settled vertices in the order settled, each vertex's known cost
/// and previous vertex, the queue's entries smallest first, and the number of entries pushed. The
/// states come only from the walk itself, under the `unchecked` feature, for tests that watch it:
/// `cargo test --features unchecked`.
///
/// The two box pieces need answers the state cannot give: the cheapest cost of each vertex, and
/// the cheapest over paths whose every vertex but the last is settled in this state. The checks
/// take them as arguments; the tests compute them by trying every path.
///
/// Lean: `Dijkstra.State`; the checks below are the pieces of its `Valid` and `WellFormed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// The settled vertices, in the order settled.
    pub(super) settled: Vec<u32>,
    /// Each vertex's known cost; `None` while no arrow has reached it.
    pub(super) known: Vec<Option<i64>>,
    /// Each vertex's recorded previous vertex.
    pub(super) previous: Vec<Option<u32>>,
    /// The queue's entries (key, vertex), smallest first.
    pub(super) queue: Vec<(i64, u32)>,
    /// How many entries the queue has received.
    pub(super) pushed: usize,
}

impl State {
    /// The known cost of `v`; `None` past the costs.
    fn known_at(&self, v: usize) -> Option<i64> {
        self.known.get(v).copied().flatten()
    }

    /// The previous vertex of `v`; `None` past the records.
    fn previous_at(&self, v: usize) -> Option<u32> {
        self.previous.get(v).copied().flatten()
    }

    /// Which vertices of a graph on `n` vertices are settled.
    fn settled_among(&self, n: usize) -> Vec<bool> {
        let mut is = vec![false; n];
        for &v in &self.settled {
            if let Some(slot) = is.get_mut(v as usize) {
                *slot = true;
            }
        }
        is
    }

    /// Box invariant 1: every settled vertex's cost is its cheapest, and a settled vertex is never
    /// settled again. `cheapest` holds each vertex's cheapest cost from the start, `None` where no
    /// path leads.
    ///
    /// Lean: `SettledAreCheapest`.
    #[must_use]
    pub fn is_settled_are_cheapest(&self, net: &Network, cheapest: &[Option<i64>]) -> bool {
        let mut seen = vec![false; net.n()];
        self.settled.iter().all(|&v| {
            let v = v as usize;
            let fresh = v < seen.len() && !seen[v];
            if fresh {
                seen[v] = true;
            }
            fresh && self.known_at(v).is_some() && cheapest.get(v) == Some(&self.known_at(v))
        })
    }

    /// Box invariant 2: every unsettled vertex's known cost is the cheapest over paths on which
    /// every earlier vertex is settled. `through` holds, for each vertex, the cheapest cost from
    /// the start over the paths whose every vertex but the last is settled in this state, `None`
    /// where there is none.
    ///
    /// Lean: `KnownIsCheapestThroughSettled`.
    #[must_use]
    pub fn is_known_is_cheapest_through_settled(
        &self,
        net: &Network,
        through: &[Option<i64>],
    ) -> bool {
        let settled = self.settled_among(net.n());
        (0..net.n()).all(|v| settled[v] || self.known_at(v) == through.get(v).copied().flatten())
    }

    /// Not in the box: once a vertex is settled, the start is the first.
    ///
    /// Lean: `StartSettledFirst`.
    #[must_use]
    pub fn is_start_settled_first(&self, start: u32) -> bool {
        self.settled.first().is_none_or(|&v| v == start)
    }

    /// Not in the box: every arrow from a settled vertex to an unsettled one has been tried; the
    /// unsettled vertex's known cost is at most the settled one's plus the arrow's.
    ///
    /// Lean: `SettledRowsTried`.
    #[must_use]
    pub fn is_settled_rows_tried(&self, net: &Network) -> bool {
        let g = net.graph();
        let settled = self.settled_among(g.n());
        self.settled.iter().all(|&x| {
            let x = x as usize;
            if x >= g.n() {
                return true;
            }
            let Some(dx) = self.known_at(x) else {
                return true;
            };
            g.out(x).iter().all(|(w, id)| {
                let w = w as usize;
                settled[w]
                    || self.known_at(w).is_some_and(|dw| {
                        i128::from(dw) <= i128::from(dx) + i128::from(net.arrow_cost(id as usize))
                    })
            })
        })
    }

    /// Not in the box: the queue is in order, holds each unsettled vertex's known cost, and each
    /// entry is a vertex of the graph, not below its known cost.
    ///
    /// Lean: `QueueHoldsKnown`.
    #[must_use]
    pub fn is_queue_holds_known(&self, net: &Network) -> bool {
        let settled = self.settled_among(net.n());
        let in_order = self.queue.windows(2).all(|p| p[0] <= p[1]);
        let holds = (0..net.n()).all(|v| {
            settled[v]
                || self
                    .known_at(v)
                    .is_none_or(|d| self.queue.contains(&(d, v as u32)))
        });
        let none_below = self.queue.iter().all(|&(key, v)| {
            (v as usize) < net.n() && self.known_at(v as usize).is_some_and(|d| d <= key)
        });
        in_order && holds && none_below
    }

    /// Not in the box: following the previous vertices back from a vertex with a known cost gives
    /// a path from the start of exactly that cost, every earlier vertex of it settled.
    ///
    /// Lean: `PreviousLeadsBack`.
    #[must_use]
    pub fn is_previous_leads_back(&self, net: &Network, start: u32) -> bool {
        let g = net.graph();
        let n = g.n();
        let settled = self.settled_among(n);
        self.previous_at(start as usize).is_none()
            && (0..n).all(|v| {
                let Some(d) = self.known_at(v) else {
                    return true;
                };
                // The vertices back from v to the start, each recording the one before it.
                let mut back = vec![v];
                let mut on = vec![false; n];
                on[v] = true;
                while back.last() != Some(&(start as usize)) {
                    let Some(p) = self.previous_at(back[back.len() - 1]) else {
                        return false;
                    };
                    let p = p as usize;
                    if p >= n || on[p] {
                        return false;
                    }
                    on[p] = true;
                    back.push(p);
                }
                back.reverse();
                if !back[..back.len() - 1].iter().all(|&x| settled[x]) {
                    return false;
                }
                // Every cost an arrow choice along those vertices gives; some choice must give d.
                let mut sums: Vec<i128> = vec![0];
                for hop in back.windows(2) {
                    let row = g.out(hop[0]);
                    let mut next: Vec<i128> = Vec::new();
                    for (w, id) in row.iter() {
                        if w as usize == hop[1] {
                            let c = i128::from(net.arrow_cost(id as usize));
                            next.extend(sums.iter().map(|&x| x + c));
                        }
                    }
                    next.sort_unstable();
                    next.dedup();
                    sums = next;
                }
                sums.contains(&i128::from(d))
            })
    }

    /// Lean `Valid` and `WellFormed`: [`State::is_settled_are_cheapest`],
    /// [`State::is_known_is_cheapest_through_settled`],
    /// [`State::is_start_settled_first`], [`State::is_settled_rows_tried`],
    /// [`State::is_queue_holds_known`] and [`State::is_previous_leads_back`].
    #[must_use]
    pub fn is_valid(
        &self,
        net: &Network,
        start: u32,
        cheapest: &[Option<i64>],
        through: &[Option<i64>],
    ) -> bool {
        self.check_valid(net, start, cheapest, through).is_ok()
    }

    /// [`State::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (settled_are_cheapest)"`, `"invariant 2 (known_is_cheapest_through_settled)"`,
    /// `"not in the box (start_settled_first)"`, `"not in the box (settled_rows_tried)"`,
    /// `"not in the box (queue_holds_known)"` or `"not in the box (previous_leads_back)"`.
    pub fn check_valid(
        &self,
        net: &Network,
        start: u32,
        cheapest: &[Option<i64>],
        through: &[Option<i64>],
    ) -> Result<(), &'static str> {
        let pieces = [
            self.is_settled_are_cheapest(net, cheapest),
            self.is_known_is_cheapest_through_settled(net, through),
            self.is_start_settled_first(start),
            self.is_settled_rows_tried(net),
            self.is_queue_holds_known(net),
            self.is_previous_leads_back(net, start),
        ];
        match pieces.iter().position(|&ok| !ok) {
            Some(i) => Err(LABELS[i]),
            None => Ok(()),
        }
    }

    /// Every state of the walk from `start`, from the start to the empty queue, one per entry
    /// taken off. The Assumes is not checked, so a network with a negative arrow gives the
    /// states of the wrong answer. For tests; not part of the API.
    ///
    /// # Panics
    ///
    /// If `start` is not a vertex of `net`.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(net: &Network, start: u32) -> Vec<Self> {
        Self::trace_keyed(net, start, None, |_| 0)
    }

    /// Every state of `walk_keyed` from `start` with `estimate`, stopped at `goal` if there is
    /// one: the start and one state per entry taken off, but not the state the stop leaves, whose
    /// goal row is untried.
    #[cfg(any(test, feature = "unchecked"))]
    pub(super) fn trace_keyed(
        net: &Network,
        start: u32,
        goal: Option<u32>,
        estimate: impl Fn(usize) -> i64,
    ) -> Vec<Self> {
        let mut states = Vec::new();
        let mut order = Vec::new();
        let _ = walk_keyed(
            net,
            start,
            goal,
            estimate,
            Some(&mut order),
            |settled, known, previous, queue, pushed| {
                let mut entries: Vec<(i64, u32)> = queue.iter().map(|e| e.0).collect();
                entries.sort_unstable();
                states.push(Self {
                    settled: settled.to_vec(),
                    known: known.to_vec(),
                    previous: previous.to_vec(),
                    queue: entries,
                    pushed,
                });
            },
        );
        states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no walk reaches. Not
    /// part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(
        settled: Vec<u32>,
        known: Vec<Option<i64>>,
        previous: Vec<Option<u32>>,
        queue: Vec<(i64, u32)>,
        pushed: usize,
    ) -> Self {
        Self {
            settled,
            known,
            previous,
            queue,
            pushed,
        }
    }

    /// The stored parts: the settled vertices, the known costs, the previous vertices, the queue
    /// and the entries pushed. For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    #[allow(clippy::type_complexity)]
    pub fn parts(&self) -> (&[u32], &[Option<i64>], &[Option<u32>], &[(i64, u32)], usize) {
        (
            &self.settled,
            &self.known,
            &self.previous,
            &self.queue,
            self.pushed,
        )
    }
}

#[cfg(test)]
#[path = "unit_tests/dijkstra.rs"]
mod tests;
