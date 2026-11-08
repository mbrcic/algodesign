// SPDX-License-Identifier: Apache-2.0
//! The cheapest path from one start to every vertex when some arrows are negative, or a
//! negative cycle that the start reaches, by Bellman–Ford's rounds.
//!
//! In place: one list of costs, which every round reads and writes. The vertices go by increasing
//! id, each row in the Graphs chapter's order (by neighbor, then id); every arrow out of a vertex
//! with a cost is tried against that cost as it is now, so a cost lowered earlier in the round is
//! used later in the same round, and a cost lower than its end's (or the first) is written at
//! once, with the vertex it came from. The previous vertex changes only when a cost drops. This is
//! Kleinberg and Tardos, *Algorithm Design*, §6.8, pp. 292–297, whose (6.26), pp. 295–296, holds in
//! place: "after i rounds of updates the value M\[v\] is no larger than the length of the shortest
//! path from v to t using at most i edges". So after `k` rounds each cost is the cost of some path,
//! and no more than the cheapest over paths of at most `k` arrows. The rounds stop after the first
//! that lowers nothing (KT p. 297); that round is the check, and its costs are the answer. At most
//! one round per vertex runs: if the last still lowers a cost, a negative cycle is reached,
//! and the answer is one. The previous vertices, written in any order, close only negative
//! cycles (Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, 4th ed., Lemma 22.16
//! and its proof, pp. 636–637). From the last vertex that round lowered, the previous vertices are
//! followed back `n` steps to a vertex on the cycle, and then on until it comes back
//! (cp-algorithms, "Bellman–Ford algorithm", `bellman_ford.md` l. 154). Only cycles the start
//! reaches are reported.
//!
//! **The input range.** The sums are not saturated. Within one round a path grows only along
//! increasing ids and around loops, by at most `n` arrows and one more per loop. So after at most
//! `n` rounds every cost the rounds hold or try is the cost of a path of at most `n (n + ℓ)`
//! arrows, for `ℓ` loops, and `n (n + ℓ)` times the largest arrow cost, in absolute value, must
//! fit an `i64`. While a negative cycle is relaxed the costs drift down by up to that much.
//!
//! [`State`] is the state after some rounds, with one check per piece of the Lean `Valid` and
//! `WellFormed` on it.
//!
//! **Against the Python, and how fast.** The rounds keep one list of costs and write it in place,
//! where the Python's `State.round` builds the next state's lists, and the arrows tried are
//! counted only when asked: [`bellman_ford_with_rounds`] counts them, and [`bellman_ford`] is
//! compiled without the count. Each round reads the rows straight from the graph's packed arrays.
//! `cargo bench -p algodesign --bench paths -- bellman_ford` times it on 10^5 vertices and
//! 4 · 10^5 arrows whose costs, shifted by a potential, make about three arrows in ten
//! negative and no cycle negative.
//!
//! Lean counterpart: `AlgoDesign.Paths.BellmanFord`.

use std::fmt;

use super::distances::Distances;
use super::network::Network;

/// A negative cycle that the start reaches: its vertices `v₀, v₁, …, v₀`, the first again
/// last, each with an arrow to the next, the arrows with a negative total.
///
/// Lean: `BellmanFord.CycleBelowZero`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NegativeCycle {
    /// The cycle's vertices, the first repeated at the end.
    pub vertices: Vec<u32>,
}

impl fmt::Display for NegativeCycle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "a cycle below zero: {:?}", self.vertices)
    }
}

impl std::error::Error for NegativeCycle {}

/// The cheapest cost from `start` to every vertex, and each vertex's previous vertex on a
/// cheapest path; or, when the start reaches a cycle whose arrows have a negative total, one such
/// cycle. `O(n m)` for `n` vertices and `m` arrows: at most `n` rounds, each trying every arrow.
///
/// The arrow costs must be in the module's input range: `n (n + ℓ)` times the largest, for `ℓ`
/// loops, fits an `i64`.
///
/// Lean: `BellmanFord.contract`.
///
/// # Errors
///
/// [`NegativeCycle`] when the start reaches a negative cycle.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{bellman_ford, Network, NegativeCycle};
///
/// // 0 → 1 costs 1, 0 → 2 costs 2, 2 → 1 costs −2: through 2, vertex 1 costs 0.
/// let g = Digraph::new(3, &[(0, 1), (0, 2), (2, 1)]).unwrap();
/// let d = bellman_ford(&Network::new(g, vec![1, 2, -2]).unwrap(), 0).unwrap();
/// assert_eq!(d.cost, [Some(0), Some(0), Some(2)]);
/// assert_eq!(d.path_to(1), Some(vec![0, 2, 1]));
///
/// // 1 → 2 and 2 → 1 total −1.
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (2, 1)]).unwrap();
/// let c = bellman_ford(&Network::new(g, vec![1, -3, 2]).unwrap(), 0).unwrap_err();
/// assert_eq!(c, NegativeCycle { vertices: vec![2, 1, 2] });
/// ```
pub fn bellman_ford(net: &Network, start: u32) -> Result<Distances, NegativeCycle> {
    run::<false>(net, start, |_, _, _, _, _| {}).0
}

/// [`bellman_ford`], with the number of rounds run and the number of arrows tried, every arrow
/// once per round: at most `n` rounds, and the rounds times the arrows tried.
///
/// Lean: `BellmanFord.Contract.cost`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{bellman_ford_with_rounds, Network};
///
/// // Round 1 reaches 1, round 2 lowers nothing: the check round, and the answer.
/// let g = Digraph::new(4, &[(0, 1)]).unwrap();
/// let (d, rounds, tried) = bellman_ford_with_rounds(&Network::new(g, vec![5]).unwrap(), 0);
/// assert_eq!(d.unwrap().cost, [Some(0), Some(5), None, None]);
/// assert_eq!((rounds, tried), (2, 2));
/// ```
pub fn bellman_ford_with_rounds(
    net: &Network,
    start: u32,
) -> (Result<Distances, NegativeCycle>, usize, usize) {
    run::<true>(net, start, |_, _, _, _, _| {})
}

/// The rounds from `start`, at most `n` of them, stopping after the first that lowers nothing,
/// and the answer they give, with the rounds run and the arrows tried (counted only when `COUNT`,
/// otherwise 0). It hands `watch` the state at the start and after every round: the costs, the
/// previous vertices, the rounds run, the last vertex lowered and the arrows tried. Only test
/// builds and the `unchecked` feature make the calls, and only `State::trace` reads them.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn run<const COUNT: bool>(
    net: &Network,
    start: u32,
    mut watch: impl FnMut(&[Option<i64>], &[Option<u32>], usize, Option<u32>, usize),
) -> (Result<Distances, NegativeCycle>, usize, usize) {
    let g = net.graph();
    let arrow_cost = net.cost();
    let n = g.n();
    let s = start as usize;
    assert!(s < n, "start {start} out of range 0..{n}");
    let (offsets, neighbors, ids) = (&g.out.offsets, &g.out.neighbors, &g.out.ids);
    let mut cost: Vec<Option<i64>> = vec![None; n];
    let mut previous: Vec<Option<u32>> = vec![None; n];
    cost[s] = Some(0);
    let mut lowered: Option<u32> = None;
    let mut rounds = 0;
    let mut tried = 0;
    watched!(watch(&cost, &previous, rounds, lowered, tried));
    while rounds < n {
        lowered = None;
        rounds += 1;
        for u in 0..n {
            let row = offsets[u]..offsets[u + 1];
            // A vertex with no cost gets none from its own row: only its loops lead back to it.
            let Some(mut du) = cost[u] else {
                if COUNT {
                    tried += row.len();
                }
                continue;
            };
            for k in row {
                if COUNT {
                    tried += 1;
                }
                let w = neighbors[k] as usize;
                let dw = du + arrow_cost[ids[k] as usize];
                if cost[w].is_none_or(|known| dw < known) {
                    cost[w] = Some(dw);
                    previous[w] = Some(u as u32);
                    lowered = Some(w as u32);
                    // A loop lowered `u` itself: the rest of its row reads the new cost.
                    if w == u {
                        du = dw;
                    }
                }
            }
        }
        watched!(watch(&cost, &previous, rounds, lowered, tried));
        if lowered.is_none() {
            break;
        }
    }
    let answer = match lowered {
        None => Ok(Distances { cost, previous }),
        Some(x) => Err(NegativeCycle {
            vertices: cycle_from(&previous, n, x),
        }),
    };
    (answer, rounds, tried)
}

/// The cycle a round that still lowers a cost shows: from `x`, the last vertex it lowered, follow
/// the previous vertices back `n` steps to a vertex `y`, staying put at a vertex that records
/// none; follow them on from `y` until `y` comes back, at most `n` steps; and turn the list
/// around, so each vertex is followed by the one its arrow points to.
///
/// Lean: `BellmanFord.cycleFrom`.
fn cycle_from(previous: &[Option<u32>], n: usize, x: u32) -> Vec<u32> {
    let back = |v: u32| previous[v as usize].unwrap_or(v);
    let mut y = x;
    for _ in 0..n {
        y = back(y);
    }
    let mut cycle = vec![y];
    let mut v = y;
    for _ in 0..n {
        v = back(v);
        cycle.push(v);
        if v == y {
            break;
        }
    }
    cycle.reverse();
    cycle
}

/// The labels [`State::check_valid`] names, in the order of the Lean `Valid` and `WellFormed`.
const LABELS: [&str; 5] = [
    "invariant 1 (cost_is_walk_at_most_cheapest)",
    "not in the box (path_within_tries)",
    "not in the box (previous_arrow_fits)",
    "not in the box (recorded_cycles_below_zero)",
    "not in the box (no_previous_keeps_start)",
];

/// The state after some rounds: each vertex's cost and previous vertex, the rounds run, the last
/// vertex the last round lowered, and the arrows tried. The states come only from the rounds
/// themselves, under the `unchecked` feature, for tests that watch them: `cargo test --features
/// unchecked`.
///
/// The box's piece and the paths within the tries speak of paths, which the state cannot see: their
/// checks take the answers about those paths as arguments, and the tests compute them by a plain
/// count over the number of arrows.
///
/// Lean: `BellmanFord.State`; the checks below are the pieces of its `Valid` and `WellFormed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// Each vertex's cost; `None` while no path has reached it.
    cost: Vec<Option<i64>>,
    /// Each vertex's recorded previous vertex.
    previous: Vec<Option<u32>>,
    /// How many rounds have run.
    rounds: usize,
    /// The last vertex the last round lowered; `None` when it lowered nothing.
    lowered: Option<u32>,
    /// How many arrows the rounds have tried.
    tried: usize,
}

impl State {
    /// The cost of `v`; `None` past the costs.
    fn cost_at(&self, v: usize) -> Option<i64> {
        self.cost.get(v).copied().flatten()
    }

    /// The previous vertex of `v`; `None` past the records.
    fn previous_at(&self, v: usize) -> Option<u32> {
        self.previous.get(v).copied().flatten()
    }

    /// Whether `d` is among the costs `costs` lists for `v`, sorted.
    fn listed(costs: &[Vec<i64>], v: usize, d: i64) -> bool {
        costs.get(v).is_some_and(|c| c.binary_search(&d).is_ok())
    }

    /// Box invariant 1: after any number of rounds, every vertex's cost is the cost of some path
    /// to it (a path may pass a vertex more than once), and no more than the cheapest over paths
    /// with at most that many arrows. `walks[v]` lists, sorted, the costs of paths from the start
    /// to `v` the check accepts as that path (the tests take every path of at most
    /// `naive::walk_arrows_after` arrows, which the tries cannot outgrow); `cheapest[v]` is the
    /// cheapest over paths to `v` of at most the rounds arrows, `None` where there is none.
    ///
    /// Lean: `CostIsWalkAtMostCheapest`.
    #[must_use]
    pub fn is_cost_is_walk_at_most_cheapest(
        &self,
        net: &Network,
        walks: &[Vec<i64>],
        cheapest: &[Option<i64>],
    ) -> bool {
        (0..net.n()).all(|v| {
            let is_walk = self.cost_at(v).is_none_or(|d| Self::listed(walks, v, d));
            let at_most = match cheapest.get(v) {
                None => false,
                Some(None) => true,
                Some(Some(c)) => self.cost_at(v).is_some_and(|d| d <= *c),
            };
            is_walk && at_most
        })
    }

    /// Not in the box: the path a cost is the cost of has at most as many arrows as arrows have
    /// been tried. `within[v]` lists, sorted, the costs of every path from the start to `v` of at
    /// most the tried arrows.
    ///
    /// Lean: `PathWithinTries`.
    #[must_use]
    pub fn is_path_within_tries(&self, net: &Network, within: &[Vec<i64>]) -> bool {
        (0..net.n()).all(|v| self.cost_at(v).is_none_or(|d| Self::listed(within, v, d)))
    }

    /// Not in the box: an arrow leads from each vertex's previous vertex to it, and the previous
    /// vertex's cost plus the arrow's is at most the vertex's cost.
    ///
    /// Lean: `PreviousArrowFits`.
    #[must_use]
    pub fn is_previous_arrow_fits(&self, net: &Network) -> bool {
        let g = net.graph();
        let n = g.n();
        (0..n).all(|v| {
            let Some(u) = self.previous_at(v) else {
                return true;
            };
            let u = u as usize;
            let (Some(du), Some(dv)) = (self.cost_at(u), self.cost_at(v)) else {
                return false;
            };
            u < n
                && g.out(u).iter().any(|(w, id)| {
                    let sum = i128::from(du) + i128::from(net.arrow_cost(id as usize));
                    w as usize == v && sum <= i128::from(dv)
                })
        })
    }

    /// The cheapest arrow from `x` to `y`; `None` where there is none.
    fn cheapest_arrow(net: &Network, x: usize, y: usize) -> Option<i64> {
        if x >= net.n() {
            return None;
        }
        net.graph()
            .out(x)
            .iter()
            .filter(|&(w, _)| w as usize == y)
            .map(|(_, id)| net.arrow_cost(id as usize))
            .min()
    }

    /// Not in the box: every cycle the previous vertices close has arrows with a negative total.
    /// From each vertex the records are followed back `n` steps; when they never stop, the vertex
    /// reached is on a cycle, and once round it the cheapest arrow of each recorded step, from a
    /// vertex's previous vertex to it, must have a negative total. A step with no arrow fails.
    ///
    /// Lean: `RecordedCyclesBelowZero`.
    #[must_use]
    pub fn is_recorded_cycles_below_zero(&self, net: &Network) -> bool {
        let n = net.n();
        (0..n).all(|v| {
            let mut y = v;
            for _ in 0..n {
                match self.previous_at(y) {
                    Some(u) => y = u as usize,
                    None => return true,
                }
            }
            let mut total = 0i128;
            let mut x = y;
            for _ in 0..n {
                let Some(u) = self.previous_at(x) else {
                    return true;
                };
                let Some(c) = Self::cheapest_arrow(net, u as usize, x) else {
                    return false;
                };
                total += i128::from(c);
                x = u as usize;
                if x == y {
                    return total < 0;
                }
            }
            true
        })
    }

    /// Not in the box: a vertex that records no previous vertex keeps its first cost, 0 for the
    /// start and none for every other vertex.
    ///
    /// Lean: `NoPreviousKeepsStart`.
    #[must_use]
    pub fn is_no_previous_keeps_start(&self, net: &Network, start: u32) -> bool {
        (0..net.n()).all(|v| {
            self.previous_at(v).is_some()
                || self.cost_at(v) == if v == start as usize { Some(0) } else { None }
        })
    }

    /// Lean `Valid` and `WellFormed`: [`State::is_cost_is_walk_at_most_cheapest`],
    /// [`State::is_path_within_tries`], [`State::is_previous_arrow_fits`],
    /// [`State::is_recorded_cycles_below_zero`] and [`State::is_no_previous_keeps_start`].
    /// `walks` and `cheapest` are as the first check takes them, `within` as the second.
    #[must_use]
    pub fn is_valid(
        &self,
        net: &Network,
        start: u32,
        walks: &[Vec<i64>],
        within: &[Vec<i64>],
        cheapest: &[Option<i64>],
    ) -> bool {
        self.check_valid(net, start, walks, within, cheapest)
            .is_ok()
    }

    /// [`State::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (cost_is_walk_at_most_cheapest)"`, `"not in the box (path_within_tries)"`,
    /// `"not in the box (previous_arrow_fits)"`, `"not in the box (recorded_cycles_below_zero)"`
    /// or `"not in the box (no_previous_keeps_start)"`.
    pub fn check_valid(
        &self,
        net: &Network,
        start: u32,
        walks: &[Vec<i64>],
        within: &[Vec<i64>],
        cheapest: &[Option<i64>],
    ) -> Result<(), &'static str> {
        let pieces = [
            self.is_cost_is_walk_at_most_cheapest(net, walks, cheapest),
            self.is_path_within_tries(net, within),
            self.is_previous_arrow_fits(net),
            self.is_recorded_cycles_below_zero(net),
            self.is_no_previous_keeps_start(net, start),
        ];
        match pieces.iter().position(|&ok| !ok) {
            Some(i) => Err(LABELS[i]),
            None => Ok(()),
        }
    }

    /// Every state of the rounds from `start`: the start, then one per round run. For tests; not
    /// part of the API.
    ///
    /// # Panics
    ///
    /// If `start` is not a vertex of `net`.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(net: &Network, start: u32) -> Vec<Self> {
        let mut states = Vec::new();
        let _ = run::<true>(net, start, |cost, previous, rounds, lowered, tried| {
            states.push(Self {
                cost: cost.to_vec(),
                previous: previous.to_vec(),
                rounds,
                lowered,
                tried,
            });
        });
        states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no round reaches. Not
    /// part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(
        cost: Vec<Option<i64>>,
        previous: Vec<Option<u32>>,
        rounds: usize,
        lowered: Option<u32>,
        tried: usize,
    ) -> Self {
        Self {
            cost,
            previous,
            rounds,
            lowered,
            tried,
        }
    }

    /// The stored parts: the costs, the previous vertices, the rounds run, the last vertex
    /// lowered and the arrows tried. For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    #[allow(clippy::type_complexity)]
    pub fn parts(&self) -> (&[Option<i64>], &[Option<u32>], usize, Option<u32>, usize) {
        (
            &self.cost,
            &self.previous,
            self.rounds,
            self.lowered,
            self.tried,
        )
    }
}

#[cfg(test)]
#[path = "unit_tests/bellman_ford.rs"]
mod tests;
