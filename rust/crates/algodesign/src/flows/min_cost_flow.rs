// SPDX-License-Identifier: Apache-2.0
//! The cheapest flow of a given amount: max flow's loop with the path rule "cheapest", stopped at
//! the requested amount.
//!
//! Each arrow has a cost per unit; `along i` costs what arrow `i` costs and `back i` refunds it.
//! Every vertex carries a height, all zero at the start. A round is one Dijkstra search from the
//! source over the arrows with residual capacity, each vertex's row in input order, on changed
//! costs: an arrow's cost plus the height at its start minus the height at its end. The queue gives
//! the smallest entry by (distance, vertex id), with lazy deletion, as chapter 6's Dijkstra; a
//! vertex's distance and the arrow that reached it change only when the distance strictly drops, so
//! on a tie the first vertex labeled wins. The search stops as soon as the sink is settled. The
//! path back from the sink is sent its bottleneck, or the amount still requested if that is less.
//! Then every settled vertex adds its distance to its height and every other vertex adds the
//! sink's. The rounds stop when the requested amount is sent, or when a search never settles the
//! sink; then the answer carries the source's side of a cut that proves the smaller amount, the
//! vertices the residual graph still reaches from the source.
//!
//! This is successive shortest paths with heights: Edmonds and Karp, "Theoretical improvements in
//! algorithmic efficiency for network flow problems" (1972), for the first heights all zero;
//! Ahuja, Magnanti and Orlin, *Network Flows*, §9.7, p. 320, and the height update of a search
//! stopped at the sink, p. 323, there with the opposite sign.
//!
//! Under the heights every arrow with residual capacity has a changed cost of zero or more, so
//! Dijkstra's search finds a cheapest path, and the heights are the certificate that the flow is
//! the cheapest for its amount. The box assumes no arrow costs less than nothing; [`min_cost_flow`]
//! checks it on its input and refuses a negative cost, since the zero heights fit only then.
//!
//! Cost: one search, `O(m log m)` for `m` arrows, per round; each round sends at least one unit,
//! so at most as many rounds as the requested amount.
//!
//! The rounds (the path, the amount, the heights after it, the number of vertices settled), and the
//! number of vertices every search settled, a last one that missed the sink included, are recorded
//! only in test builds and under the `unchecked` feature (`min_cost_flow_with_rounds`).
//!
//! **Against the Python, and how fast.** The same search, ties and heights. The search's arrays and
//! queue are kept from round to round, and the path is sent along the arrows that reached each
//! vertex without building a list outside the trace, where the Python builds the path.
//!
//! Lean counterpart: `AlgoDesign.Flows.MinCostFlow`, the contract in
//! `Flows/MinCostFlow/Spec.lean`.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use super::edmonds_karp::{NONE, ROOT};
use super::max_flow::{net_out, MaxFlow};
use super::network::{Capacity, FlowsError, Network};
use super::residual::{Augmentation, Residual};

/// The answer: the amount sent, its total cost, the flow, the heights, and the source's side of a
/// cut.
///
/// Lean: `MinCostFlow.Answer`, with the amount and the total cost beside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinCostFlow<C = u64> {
    /// The amount sent from the source to the sink: the requested amount, or less when the network
    /// cannot carry it.
    pub value: u64,
    /// The flow's cost: each arrow's cost times the amount on it, summed.
    pub cost: i64,
    /// The amount on each arrow, by id.
    pub flow: Vec<C>,
    /// The height of each vertex: under them every residual arrow with residual capacity has a
    /// changed cost of at least zero.
    pub heights: Vec<i64>,
    /// For each vertex, whether the residual graph reaches it from the source; when less than the
    /// requested amount was sent, the source's side of a cut whose capacity is that amount.
    pub side: Vec<bool>,
}

/// Judging an answer on its problem, anyone's, piece by piece: the box's three invariants on the
/// flow and the heights, one amount per arrow and one height per vertex, and the promise's amount
/// and cut. Invariant 2, the flow cheapest for its amount, is judged against `cheapest`, the
/// smallest cost of any flow of the amount the flow sends, found elsewhere (for a small network,
/// by trying every flow); heights that fit a flow also prove it (Lean `cheapest_of_heightsFit`).
/// The reported `value` and `cost` have no piece of their own; the amount and the cost are
/// measured on the flow itself. Each piece is linear in vertices plus arrows, never panics, and
/// reads a missing amount, cost or height as 0.
impl<C: Capacity> MinCostFlow<C> {
    /// The flow and the side as a max flow's answer, to read max flow's pieces on.
    fn as_max_flow(&self) -> MaxFlow<C> {
        MaxFlow {
            value: self.value,
            flow: self.flow.clone(),
            side: self.side.clone(),
        }
    }

    /// The amount on arrow `i`, read as 0 past the end of the list.
    fn on(&self, i: usize) -> u64 {
        self.flow.get(i).map_or(0, |x| x.to_u64())
    }

    /// Box invariant 1: max flow's invariants 1–3, no arrow over its capacity and nothing lost at
    /// any vertex but the source and the sink; no amount is negative, by its unsigned type.
    ///
    /// Lean: `FlowRespected`.
    #[must_use]
    pub fn is_flow_respected(&self, net: &Network<C>) -> bool {
        let f = self.as_max_flow();
        f.is_within_capacity(net) && f.is_conserved(net)
    }

    /// Box invariant 2: the current flow is the cheapest for its current amount. `cheapest` is the
    /// smallest cost of any flow of the amount this flow sends, `None` when no flow sends it, and
    /// then no flow is cheaper.
    ///
    /// Lean: `CheapestForAmount`.
    #[must_use]
    pub fn is_cheapest_for_amount(
        &self,
        net: &Network<C>,
        cost: &[i64],
        cheapest: Option<i64>,
    ) -> bool {
        // A 64-bit cost times a 64-bit amount fits an `i128`; the sum over the arrows saturates
        // rather than wraps.
        let own = (0..net.arrow_count()).fold(0i128, |sum, i| {
            let c = i128::from(cost.get(i).copied().unwrap_or(0));
            sum.saturating_add(c.saturating_mul(i128::from(self.on(i))))
        });
        cheapest.is_none_or(|best| own <= i128::from(best))
    }

    /// Box invariant 3: under the heights, every unsaturated arrow has a changed cost of at least
    /// zero. Arrow `i` from `a` to `b` has the changed cost `cost[i] + h(a) - h(b)` if it has
    /// residual capacity left, and its reverse arrow the negative of that if it carries something.
    /// On a flow within capacity this is the rule per arrow: at least zero on an empty arrow, zero
    /// on a partly loaded one, at most zero on a full one, and nothing on an arrow of capacity
    /// zero.
    ///
    /// Lean: `HeightsFitEverywhere`.
    #[must_use]
    pub fn is_heights_fit_everywhere(&self, net: &Network<C>, cost: &[i64]) -> bool {
        let g = net.graph();
        let height = |v: u32| i128::from(self.heights.get(v as usize).copied().unwrap_or(0));
        (0..g.arrow_count()).all(|i| {
            let (a, b) = g.arrow(i);
            let x = self.on(i);
            let changed = i128::from(cost.get(i).copied().unwrap_or(0)) + height(a) - height(b);
            (x >= net.arrow_capacity(i).to_u64() || changed >= 0) && (x == 0 || changed <= 0)
        })
    }

    /// Not in the box: one amount per arrow and one height per vertex.
    ///
    /// Lean: `WellFormed`.
    #[must_use]
    pub fn is_well_formed(&self, net: &Network<C>) -> bool {
        self.flow.len() == net.arrow_count() && self.heights.len() == net.n()
    }

    /// The promise's flow: a flow, carrying at most the requested amount. That it is a flow is
    /// invariant 1 with one amount per arrow, checked before it; this piece checks the amount.
    ///
    /// Lean: `Ops.SendsAFlow`.
    #[must_use]
    pub fn is_sends_a_flow(&self, net: &Network<C>, amount: u64) -> bool {
        net_out(net, |i| self.on(i))[net.source() as usize] <= i128::from(amount)
    }

    /// The promise's cut: when less than the requested amount is sent, the source is on the side,
    /// the sink is not, and the capacities of the arrows leaving the side add up to the amount
    /// sent.
    ///
    /// Lean: `Ops.ShortOnlyAtACut`.
    #[must_use]
    pub fn is_short_only_at_a_cut(&self, net: &Network<C>, amount: u64) -> bool {
        net_out(net, |i| self.on(i))[net.source() as usize] >= i128::from(amount)
            || self.as_max_flow().is_cut_matches_flow(net)
    }

    /// Lean `Valid` and `WellFormed` on the flow and the heights, and `Ops.SendsAFlow` and
    /// `Ops.ShortOnlyAtACut`: [`MinCostFlow::is_flow_respected`],
    /// [`MinCostFlow::is_cheapest_for_amount`], [`MinCostFlow::is_heights_fit_everywhere`],
    /// [`MinCostFlow::is_well_formed`], [`MinCostFlow::is_sends_a_flow`] and
    /// [`MinCostFlow::is_short_only_at_a_cut`]; `cheapest` as for
    /// [`MinCostFlow::is_cheapest_for_amount`].
    #[must_use]
    pub fn is_valid(
        &self,
        net: &Network<C>,
        cost: &[i64],
        amount: u64,
        cheapest: Option<i64>,
    ) -> bool {
        self.check_valid(net, cost, amount, cheapest).is_ok()
    }

    /// [`MinCostFlow::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (flow_respected)"`, `"invariant 2 (cheapest_for_amount)"`,
    /// `"invariant 3 (heights_fit_everywhere)"`, `"not in the box (well_formed)"`,
    /// `"promise (sends_a_flow)"` or `"promise (short_only_at_a_cut)"`.
    pub fn check_valid(
        &self,
        net: &Network<C>,
        cost: &[i64],
        amount: u64,
        cheapest: Option<i64>,
    ) -> Result<(), &'static str> {
        if !self.is_flow_respected(net) {
            return Err("invariant 1 (flow_respected)");
        }
        if !self.is_cheapest_for_amount(net, cost, cheapest) {
            return Err("invariant 2 (cheapest_for_amount)");
        }
        if !self.is_heights_fit_everywhere(net, cost) {
            return Err("invariant 3 (heights_fit_everywhere)");
        }
        if !self.is_well_formed(net) {
            return Err("not in the box (well_formed)");
        }
        if !self.is_sends_a_flow(net, amount) {
            return Err("promise (sends_a_flow)");
        }
        if !self.is_short_only_at_a_cut(net, amount) {
            return Err("promise (short_only_at_a_cut)");
        }
        Ok(())
    }
}

/// One round: the path it added, the heights after it, and how many vertices its search settled.
/// Only test builds and the `unchecked` feature record rounds (`min_cost_flow_with_rounds`).
///
/// Lean: `Ops.steps` and `Ops.heightsAfter`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinCostRound<C = u64> {
    /// The residual arrows, from the source, and the amount sent.
    pub sent: Augmentation<C>,
    /// The height of each vertex after the round.
    pub heights: Vec<i64>,
    /// The number of vertices the round's search settled, the source and the sink included.
    pub settled: usize,
}

/// The cheapest flow of `amount` from the source to the sink of `net`, arrow `i` costing
/// `cost[i]` per unit; if the network cannot carry `amount`, the largest amount it can, cheapest
/// for it, with a cut that proves it. `O(a · m log m)` for the requested amount `a` and `m`
/// arrows: at most `a` rounds, one search each.
///
/// The box's Assumes, no arrow costing less than nothing, is checked here, on the caller's input.
/// So that the heights and the search's sums fit an `i64`, the costs of all arrows may add up to
/// at most `i64::MAX / 4`; the search itself runs unchecked within that range (argued). The total
/// cost, each arrow's cost times its amount, is summed in `i128` and refused when it does not fit
/// an `i64`.
///
/// Lean: `MinCostFlow.contract`.
///
/// # Errors
///
/// [`FlowsError::CostCountMismatch`] when `cost` does not have one entry per arrow,
/// [`FlowsError::NegativeCost`] for the first arrow that costs less than nothing,
/// [`FlowsError::CostSumTooLarge`] when the costs add up to more than `i64::MAX / 4`, and
/// [`FlowsError::TotalCostTooLarge`] when the flow's total cost does not fit an `i64`.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{min_cost_flow, Network};
/// use algodesign::graphs::Digraph;
///
/// // 0 → 1 → 2 costs 1 + 1, and 0 → 2 costs 5; each arrow carries 1.
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![1u64, 1, 1], 0, 2).unwrap();
/// let answer = min_cost_flow(&net, &[1, 1, 5], 2).unwrap();
/// assert_eq!((answer.value, answer.cost), (2, 7));
/// assert_eq!(answer.flow, [1, 1, 1]);
/// // Three units: the network carries only two, and the cut around the source proves it.
/// let short = min_cost_flow(&net, &[1, 1, 5], 3).unwrap();
/// assert_eq!(short.value, 2);
/// assert_eq!(short.side, [true, false, false]);
/// ```
pub fn min_cost_flow<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
    cost: &[i64],
    amount: u64,
) -> Result<MinCostFlow<C>, FlowsError> {
    refuse(net, cost)?;
    run(net, cost, amount, None)
}

/// [`min_cost_flow`], with every round: the path from the source as residual arrow ids and the
/// amount, the heights after it, and the number of vertices its search settled; and the number of
/// vertices every search settled, in order, a last search that missed the sink included. Only in
/// test builds and under the `unchecked` feature.
///
/// Lean: `Ops.steps`, `Ops.heightsAfter`, `Ops.walks`; the searches, `settledEach`.
///
/// # Errors
///
/// As [`min_cost_flow`].
#[cfg(any(test, feature = "unchecked"))]
#[allow(clippy::type_complexity)]
pub fn min_cost_flow_with_rounds<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
    cost: &[i64],
    amount: u64,
) -> Result<(MinCostFlow<C>, Vec<MinCostRound<C>>, Vec<usize>), FlowsError> {
    refuse(net, cost)?;
    let mut trace = Trace {
        rounds: Vec::new(),
        searches: Vec::new(),
    };
    let answer = run(net, cost, amount, Some(&mut trace))?;
    Ok((answer, trace.rounds, trace.searches))
}

/// What a run records: its rounds, and the number of vertices each search settled.
#[cfg_attr(not(any(test, feature = "unchecked")), allow(dead_code))]
struct Trace<C> {
    /// The rounds, in order.
    rounds: Vec<MinCostRound<C>>,
    /// The number of vertices each search settled, in order.
    searches: Vec<usize>,
}

/// The input [`min_cost_flow`] refuses: a cost count that is not the arrow count, the first
/// negative cost, and costs that add up to more than `i64::MAX / 4`.
fn refuse<C: Capacity>(net: &Network<C>, cost: &[i64]) -> Result<(), FlowsError> {
    let arrows = net.arrow_count();
    if cost.len() != arrows {
        return Err(FlowsError::CostCountMismatch {
            costs: cost.len(),
            arrows,
        });
    }
    if let Some(arrow) = cost.iter().position(|&c| c < 0) {
        return Err(FlowsError::NegativeCost {
            arrow,
            cost: cost[arrow],
        });
    }
    let sum: i128 = cost.iter().map(|&c| i128::from(c)).sum();
    if sum > i128::from(COST_SUM_LIMIT) {
        return Err(FlowsError::CostSumTooLarge);
    }
    Ok(())
}

/// The most the costs of all arrows may add up to. A path's cost, refunds included, is at most
/// that sum `S` in magnitude; so are the heights, which start at zero, never drop, and stay at most
/// a cheapest path's cost (argued). A distance on changed costs is a path's cost less a height, at
/// most `2S`, and the search's sum `distance + cost + height - height` stays within `4S`, which
/// this limit keeps inside an `i64`.
const COST_SUM_LIMIT: i64 = i64::MAX / 4;

/// The search's arrays, kept from round to round.
struct Search {
    /// Each vertex's known distance on changed costs; meaningful only where `reached_by` is set.
    distance: Vec<i64>,
    /// The arrow that last lowered each vertex's distance; `ROOT` at the source, `NONE` if none.
    reached_by: Vec<u32>,
    /// Whether each vertex is settled.
    settled: Vec<bool>,
    /// The queue: the smallest (distance, vertex) on top, with entries left behind by a drop.
    queue: BinaryHeap<Reverse<(i64, u32)>>,
    /// The number of vertices the last search settled; counted only for the trace.
    #[cfg(any(test, feature = "unchecked"))]
    count: usize,
}

/// The rounds from the zero flow with all heights zero, until `amount` is sent or a search misses
/// the sink, recording the rounds and the searches into `trace` when it is given (test builds and
/// the `unchecked` feature only).
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn run<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
    cost: &[i64],
    amount: u64,
    mut trace: Option<&mut Trace<C>>,
) -> Result<MinCostFlow<C>, FlowsError> {
    let n = net.n();
    let mut r = Residual::new(net);
    let mut heights = vec![0i64; n];
    let mut search = Search {
        distance: vec![0; n],
        reached_by: vec![NONE; n],
        settled: vec![false; n],
        queue: BinaryHeap::new(),
        #[cfg(any(test, feature = "unchecked"))]
        count: 0,
    };
    let mut sent: u64 = 0;
    while sent < amount {
        let found = cheapest_path(&r, cost, &heights, &mut search);
        watched!(if let Some(trace) = trace.as_deref_mut() {
            trace.searches.push(search.count);
        });
        if !found {
            break;
        }
        let added = send(&mut r, &search.reached_by, amount - sent);
        sent += added.to_u64();
        let t = r.sink as usize;
        let to_sink = search.distance[t];
        for (v, h) in heights.iter_mut().enumerate() {
            *h += if search.settled[v] {
                search.distance[v]
            } else {
                to_sink
            };
        }
        watched!(if let Some(trace) = trace.as_deref_mut() {
            trace.rounds.push(MinCostRound {
                sent: Augmentation {
                    path: path_back(&r, &search.reached_by),
                    amount: added,
                },
                heights: heights.clone(),
                settled: search.count,
            });
        });
    }
    let flow = r.flow();
    let total = total_cost(&flow, cost).ok_or(FlowsError::TotalCostTooLarge)?;
    Ok(MinCostFlow {
        value: sent,
        cost: total,
        flow,
        heights,
        side: r.reached(),
    })
}

/// Each arrow's cost times the amount on it, summed in `i128`; `None` when the sum does not fit an
/// `i64`. One product of an `i64` and a `u64` always fits an `i128`.
fn total_cost<C: Capacity>(flow: &[C], cost: &[i64]) -> Option<i64> {
    let mut total: i128 = 0;
    for (&x, &c) in flow.iter().zip(cost) {
        total = total.checked_add(i128::from(c) * i128::from(x.to_u64()))?;
    }
    i64::try_from(total).ok()
}

/// Dijkstra's search from the source on changed costs over the arrows with residual capacity, each
/// row in input order, stopped when the sink is settled. Whether the sink was settled.
fn cheapest_path<C: Capacity>(
    r: &Residual<C>,
    cost: &[i64],
    heights: &[i64],
    search: &mut Search,
) -> bool {
    let (s, t) = (r.source, r.sink);
    search.reached_by.fill(NONE);
    search.settled.fill(false);
    search.queue.clear();
    search.distance[s as usize] = 0;
    search.reached_by[s as usize] = ROOT;
    search.queue.push(Reverse((0, s)));
    watched!(search.count = 0);
    while let Some(Reverse((du, u))) = search.queue.pop() {
        let u_at = u as usize;
        // an entry left behind: u was settled at a smaller distance
        if search.settled[u_at] {
            continue;
        }
        search.settled[u_at] = true;
        watched!(search.count += 1);
        if u == t {
            return true;
        }
        for k in r.offsets[u_at] as usize..r.offsets[u_at + 1] as usize {
            let e = r.rows[k] as usize;
            if r.residual_capacity[e] == C::ZERO {
                continue;
            }
            let w = r.heads[e];
            let w_at = w as usize;
            if search.settled[w_at] {
                continue;
            }
            let along = cost[e >> 1];
            let arrow_cost = if e & 1 == 0 { along } else { -along };
            let dw = du + arrow_cost + heights[u_at] - heights[w_at];
            if search.reached_by[w_at] == NONE || dw < search.distance[w_at] {
                search.distance[w_at] = dw;
                search.reached_by[w_at] = e as u32;
                search.queue.push(Reverse((dw, w)));
            }
        }
    }
    false
}

/// Send along the path the arrows in `reached_by` lead back along from the sink: its bottleneck,
/// or `rest` if that is less. The amount sent.
fn send<C: Capacity + TryFrom<u64>>(r: &mut Residual<C>, reached_by: &[u32], rest: u64) -> C {
    let (s, t) = (r.source as usize, r.sink as usize);
    let mut bottleneck = C::MAX;
    let mut v = t;
    while v != s {
        let e = reached_by[v] as usize;
        bottleneck = bottleneck.min(r.residual_capacity[e]);
        v = r.heads[e ^ 1] as usize;
    }
    // A rest that does not fit `C` is above every residual capacity.
    let amount = C::try_from(rest).map_or(bottleneck, |rest| rest.min(bottleneck));
    let mut v = t;
    while v != s {
        let e = reached_by[v] as usize;
        r.push(e, amount);
        v = r.heads[e ^ 1] as usize;
    }
    amount
}

/// The path the arrows in `reached_by` lead back along from the sink, from the source.
#[cfg(any(test, feature = "unchecked"))]
fn path_back<C: Capacity>(r: &Residual<C>, reached_by: &[u32]) -> Vec<u32> {
    let (s, t) = (r.source as usize, r.sink as usize);
    let mut path = Vec::new();
    let mut v = t;
    while v != s {
        path.push(reached_by[v]);
        v = r.heads[reached_by[v] as usize ^ 1] as usize;
    }
    path.reverse();
    path
}

#[cfg(test)]
#[path = "unit_tests/min_cost_flow.rs"]
mod tests;
