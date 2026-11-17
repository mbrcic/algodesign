// SPDX-License-Identifier: Apache-2.0
//! Slow references that are correct by inspection, for the tests to compare the real rules
//! against. Built only for the tests and behind the `unchecked` feature, so they are not part of
//! the library's interface.

use super::max_flow::{self, MaxFlow};
use super::network::{Capacity, Network};

/// The capacity of the cut whose source side is `side`: the capacities of the arrows leaving it.
///
/// Lean: `Flows.cutCapacity`.
///
/// # Panics
///
/// If `side` does not have one entry per vertex.
#[must_use]
pub fn cut_capacity<C: Capacity>(net: &Network<C>, side: &[bool]) -> u128 {
    assert_eq!(side.len(), net.n(), "one entry per vertex");
    max_flow::cut_capacity(net, side)
}

/// The smallest capacity of a cut, by trying every set of vertices with the source and without
/// the sink. Exponential; for networks of a handful of vertices.
///
/// # Panics
///
/// If `net` has more than 20 vertices.
#[must_use]
pub fn min_cut<C: Capacity>(net: &Network<C>) -> u128 {
    let n = net.n();
    assert!(n <= 20, "a small network");
    let (s, t) = (net.source() as usize, net.sink() as usize);
    let others: Vec<usize> = (0..n).filter(|&v| v != s && v != t).collect();
    let mut best = u128::MAX;
    let mut side = vec![false; n];
    for mask in 0u32..(1 << others.len()) {
        side.fill(false);
        side[s] = true;
        for (k, &v) in others.iter().enumerate() {
            side[v] = mask >> k & 1 == 1;
        }
        best = best.min(cut_capacity(net, &side));
    }
    best
}

/// Whether `answer` is what the contract asks of a max flow on `net`: the label
/// [`MaxFlow::check_valid`] gives, then `"value"` when the reported amount is not what the flow
/// sends.
///
/// Lean: `Ops.ReturnsAFlow` (`WithinCapacity`, `Conserved`, `WellFormed`), `Ops.CutMatchesFlow`,
/// `value`.
///
/// # Errors
///
/// The label of the first part that does not hold.
pub fn check<C: Capacity>(net: &Network<C>, answer: &MaxFlow<C>) -> Result<(), &'static str> {
    answer.check_valid(net)?;
    let sent = max_flow::net_out(net, |i| answer.flow[i].to_u64())[net.source() as usize];
    if sent != i128::from(answer.value) {
        return Err("value");
    }
    Ok(())
}

/// The smallest cost of a flow of amount `value` on `net`, arrow `i` costing `cost[i]` per unit, by
/// trying every integer amount on every arrow; `None` if no flow has that amount. Exponential; for
/// networks of a handful of small arrows.
///
/// Lean: `MinCostFlow.CheapestForAmount`.
///
/// # Panics
///
/// If `cost` does not have one entry per arrow, or there are more than 65536 ways to fill the
/// arrows.
#[must_use]
pub fn cheapest_cost<C: Capacity>(net: &Network<C>, cost: &[i64], value: u64) -> Option<i64> {
    let g = net.graph();
    let m = g.arrow_count();
    assert_eq!(cost.len(), m, "one cost per arrow");
    let room: Vec<u64> = net.capacity().iter().map(|c| c.to_u64() + 1).collect();
    let ways = room.iter().try_fold(1u64, |w, &k| w.checked_mul(k));
    assert!(ways.is_some_and(|w| w <= 1 << 16), "a small network");
    let (s, t) = (net.source() as usize, net.sink() as usize);
    let mut best = None;
    let mut flow = vec![0u64; m];
    loop {
        let mut net_out = vec![0i128; net.n()];
        for (i, &x) in flow.iter().enumerate() {
            let (tail, head) = g.arrow(i);
            net_out[tail as usize] += i128::from(x);
            net_out[head as usize] -= i128::from(x);
        }
        let conserved = (0..net.n()).all(|v| v == s || v == t || net_out[v] == 0);
        if conserved && net_out[s] == i128::from(value) {
            let total: i64 = flow.iter().zip(cost).map(|(&x, &c)| c * x as i64).sum();
            best = Some(best.map_or(total, |b: i64| b.min(total)));
        }
        // The next filling, counting in the mixed base whose digit `i` runs from 0 to arrow `i`'s
        // capacity.
        let Some(i) = (0..m).find(|&i| flow[i] + 1 < room[i]) else {
            return best;
        };
        flow[i] += 1;
        flow[..i].fill(0);
    }
}

/// The smallest total cost of an assignment of the square table `cost`, by trying every order of
/// the objects, in lexicographic order. Exponential; for tables of a handful of people.
///
/// Lean: `Ops.LeastCost`.
///
/// # Panics
///
/// If the table is not square, or has more than 9 people.
#[must_use]
pub fn cheapest_assignment(cost: &[Vec<i64>]) -> i64 {
    let n = cost.len();
    assert!(n <= 9, "a small table");
    assert!(cost.iter().all(|row| row.len() == n), "a square table");
    let mut obj: Vec<usize> = (0..n).collect();
    let mut best = i64::MAX;
    loop {
        best = best.min((0..n).map(|p| cost[p][obj[p]]).sum());
        // The next order: the last rise, swapped with the last larger object after it, the rest
        // reversed.
        let Some(k) = (1..n).rev().find(|&k| obj[k - 1] < obj[k]).map(|k| k - 1) else {
            return best;
        };
        let l = (k + 1..n).rev().find(|&l| obj[l] > obj[k]).unwrap_or(k);
        obj.swap(k, l);
        obj[k + 1..].reverse();
    }
}
