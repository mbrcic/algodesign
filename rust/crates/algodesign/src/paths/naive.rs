// SPDX-License-Identifier: Apache-2.0
//! Slow references that are correct by inspection, for the tests to compare the real walks
//! against. Built only for the tests and behind the `unchecked` feature, so they are not part of
//! the library's interface.

use super::network::Network;

/// The cheapest cost from `start` to each vertex over the paths `extend` admits, by trying every
/// path: a list of distinct arrows, leaving each vertex the one before arrived at, that passes no
/// vertex twice. A path is only extended past a vertex `extend` accepts. `None` where no admitted
/// path leads. Exponential; for networks of a handful of vertices.
///
/// # Panics
///
/// If `start` is not a vertex of `net`, or `net` has more than 64 vertices.
fn cheapest_among(net: &Network, start: u32, extend: impl Fn(u32) -> bool) -> Vec<Option<i64>> {
    let g = net.graph();
    let n = g.n();
    assert!(
        (start as usize) < n && n <= 64,
        "a start of a small network"
    );
    let mut best: Vec<Option<i64>> = vec![None; n];
    // Each path: where it ends, what it costs, the vertices it passes.
    let mut paths: Vec<(u32, i64, u64)> = vec![(start, 0, 1 << start)];
    while let Some((v, c, passed)) = paths.pop() {
        let slot = &mut best[v as usize];
        if slot.is_none_or(|b| c < b) {
            *slot = Some(c);
        }
        if !extend(v) {
            continue;
        }
        for (w, id) in g.out(v as usize).iter() {
            if passed & (1 << w) == 0 {
                paths.push((w, c + net.arrow_cost(id as usize), passed | (1 << w)));
            }
        }
    }
    best
}

/// The cheapest cost from `start` to each vertex, by trying every path; `None` where no path
/// leads. Any arrow cost is allowed. Exponential; for networks of a handful of vertices.
///
/// Lean: `Network.Cheapest`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`, or `net` has more than 64 vertices.
#[must_use]
pub fn cheapest(net: &Network, start: u32) -> Vec<Option<i64>> {
    cheapest_among(net, start, |_| true)
}

/// The cheapest cost from `start` to each vertex over the paths whose every vertex but the last
/// is in `settled`, by trying every such path; `None` where there is none. The start itself is
/// reached by the path of no arrows, settled or not.
///
/// Lean: `Network.CheapestAmong (Dijkstra.Through N settled s)`.
///
/// # Panics
///
/// As [`cheapest`].
#[must_use]
pub fn cheapest_through(net: &Network, start: u32, settled: &[u32]) -> Vec<Option<i64>> {
    let mut is = vec![false; net.n()];
    for &v in settled {
        is[v as usize] = true;
    }
    cheapest_among(net, start, |v| is[v as usize])
}

/// The cheapest cost from each vertex to `goal`, by trying every path from each; `None` where no
/// path leads to the goal. Any arrow cost is allowed. Exponential; for networks of a handful of
/// vertices.
///
/// # Panics
///
/// If `goal` is not a vertex of `net`, or `net` has more than 64 vertices.
#[must_use]
pub fn cheapest_to(net: &Network, goal: u32) -> Vec<Option<i64>> {
    assert!((goal as usize) < net.n(), "a goal of the network");
    (0..net.n() as u32)
        .map(|v| cheapest(net, v)[goal as usize])
        .collect()
}

/// For each number of arrows `j` from 0 to `k`, the cheapest cost from `start` to each vertex
/// over the paths of at most `j` arrows; `None` where no such path leads. A path may pass a vertex
/// more than once. Row `j + 1` is row `j`, lowered by every arrow out of a vertex row `j` reaches:
/// a path of at most `j + 1` arrows is one of at most `j`, or one of at most `j` and one arrow
/// more. Any arrow cost is allowed.
///
/// Lean: the paths of `BellmanFord.CostIsWalkAtMostCheapest`, at most so many arrows.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
#[must_use]
pub fn cheapest_walks(net: &Network, start: u32, k: usize) -> Vec<Vec<Option<i64>>> {
    let g = net.graph();
    let mut first = vec![None; g.n()];
    first[start as usize] = Some(0);
    let mut rows = vec![first];
    for _ in 0..k {
        let last = &rows[rows.len() - 1];
        let mut next = last.clone();
        for id in 0..g.arrow_count() {
            let (u, w) = g.arrow(id);
            if let Some(du) = last[u as usize] {
                let dw = du + net.arrow_cost(id);
                if next[w as usize].is_none_or(|b| dw < b) {
                    next[w as usize] = Some(dw);
                }
            }
        }
        rows.push(next);
    }
    rows
}

/// For each vertex, every cost of a path from `start` to it of at most `k` arrows, sorted, each
/// once. Two arrows between the same vertices are two different paths. The number of costs grows
/// with `k`; for networks of a handful of vertices and small costs.
///
/// Lean: the paths of `BellmanFord.CostIsWalkAtMostCheapest`, some path, and of
/// `BellmanFord.PathWithinTries`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
#[must_use]
pub fn walk_costs(net: &Network, start: u32, k: usize) -> Vec<Vec<i64>> {
    use std::collections::BTreeSet;
    let g = net.graph();
    // The costs of the paths of exactly j arrows, for j = 0, 1, ..., k.
    let mut exactly: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); g.n()];
    exactly[start as usize].insert(0);
    let mut all = exactly.clone();
    for _ in 0..k {
        let mut next: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); g.n()];
        for id in 0..g.arrow_count() {
            let (u, w) = g.arrow(id);
            for &c in &exactly[u as usize] {
                next[w as usize].insert(c + net.arrow_cost(id));
            }
        }
        for (v, costs) in next.iter().enumerate() {
            all[v].extend(costs);
        }
        exactly = next;
    }
    all.into_iter().map(|c| c.into_iter().collect()).collect()
}

/// How many arrows the paths [`walk_costs`] takes must have room for, for a state that has tried
/// `tried` arrows: each try grows a path by at most one arrow, so `tried`; and `n` more, so that
/// every path counts too. The Lean link judges with the same bound.
#[must_use]
pub fn walk_arrows_after(net: &Network, tried: usize) -> usize {
    tried + net.n()
}

/// Whether `start` reaches a negative cycle, by trying every cycle: from
/// each vertex the start reaches, every path that passes no vertex twice and an arrow back to that
/// vertex. A loop is a cycle of one arrow. Exponential; for networks of a handful of vertices.
///
/// Lean: `∃ c, BellmanFord.CycleBelowZero N s c`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`, or `net` has more than 64 vertices.
#[must_use]
pub fn reaches_cycle_below_zero(net: &Network, start: u32) -> bool {
    assert!(net.n() <= 64, "a small network");
    let reached = reached_from(net, start);
    (0..net.n() as u32)
        .filter(|&v| reached[v as usize])
        .any(|v| {
            let g = net.graph();
            // Each path from v: where it ends, what it costs, the vertices it passes.
            let mut paths: Vec<(u32, i64, u64)> = vec![(v, 0, 1 << v)];
            while let Some((x, c, passed)) = paths.pop() {
                for (w, id) in g.out(x as usize).iter() {
                    let cw = c + net.arrow_cost(id as usize);
                    if w == v && cw < 0 {
                        return true;
                    }
                    if passed & (1 << w) == 0 {
                        paths.push((w, cw, passed | (1 << w)));
                    }
                }
            }
            false
        })
}

/// Whether `vertices` is a negative cycle that `start` reaches: at least one arrow, the first
/// vertex again last and no other vertex twice, an arrow from each vertex to the next, the
/// cheapest such arrows with a negative total, and the first vertex reached from `start`.
///
/// Lean: `BellmanFord.CycleBelowZero`.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
#[must_use]
pub fn is_cycle_below_zero(net: &Network, start: u32, vertices: &[u32]) -> bool {
    let n = net.n();
    let g = net.graph();
    let [first, .., last] = vertices else {
        return false;
    };
    let body = &vertices[..vertices.len() - 1];
    let distinct = body.iter().enumerate().all(|(i, v)| !body[..i].contains(v));
    if first != last || !distinct || vertices.iter().any(|&v| v as usize >= n) {
        return false;
    }
    let mut total = 0;
    for hop in vertices.windows(2) {
        let cheapest = g
            .out(hop[0] as usize)
            .iter()
            .filter(|&(w, _)| w == hop[1])
            .map(|(_, id)| net.arrow_cost(id as usize))
            .min();
        let Some(c) = cheapest else {
            return false;
        };
        total += c;
    }
    total < 0 && reached_from(net, start)[*first as usize]
}

/// Which vertices `start` reaches, the start included.
fn reached_from(net: &Network, start: u32) -> Vec<bool> {
    let g = net.graph();
    let mut reached = vec![false; g.n()];
    reached[start as usize] = true;
    let mut todo = vec![start];
    while let Some(v) = todo.pop() {
        for (w, _) in g.out(v as usize).iter() {
            if !reached[w as usize] {
                reached[w as usize] = true;
                todo.push(w);
            }
        }
    }
    reached
}

/// Every cheapest spanning forest of `net`, by trying every set of links: each a list of link
/// ids in increasing order. A spanning forest always exists, so the list is never empty.
/// Exponential in the links; for a dozen at most.
///
/// Lean: `LinkNetwork.CheapestForest`.
///
/// # Panics
///
/// If `net` has more than 16 links.
#[must_use]
pub fn cheapest_forests(net: &super::link_network::LinkNetwork) -> Vec<Vec<u32>> {
    let m = net.graph().link_count();
    assert!(m <= 16, "a network of a dozen links or so");
    let forests: Vec<Vec<u32>> = (0u32..1 << m)
        .map(|set| {
            (0..m as u32)
                .filter(|&i| set & (1 << i) != 0)
                .collect::<Vec<u32>>()
        })
        .filter(|links| net.is_spanning_forest(links))
        .collect();
    let least = forests.iter().map(|f| net.total(f)).min();
    forests
        .into_iter()
        .filter(|f| Some(net.total(f)) == least)
        .collect()
}

/// The largest value of a set of items that fits in a box of `capacity`, by trying every set; the
/// empty set fits and is worth 0. Exponential; for a handful of items.
///
/// Lean: `Knapsack.IsBest`.
///
/// # Panics
///
/// If `weights` and `values` differ in length, or there are more than 20 items.
#[must_use]
pub fn best_value(weights: &[u64], values: &[i64], capacity: u64) -> i64 {
    let n = weights.len();
    assert!(n == values.len() && n <= 20, "a handful of items");
    (0u32..1 << n)
        .filter_map(|set| {
            let picked = (0..n).filter(|&k| set & (1 << k) != 0);
            let weight: u128 = picked.clone().map(|k| u128::from(weights[k])).sum();
            (weight <= u128::from(capacity)).then(|| picked.map(|k| values[k]).sum())
        })
        .max()
        .unwrap_or(0)
}

/// For each vertex `(i, w)` of the knapsack's graph, `i ≤ n` and `w ≤ capacity`, the largest
/// gain of a path into it from `(0, 0)`: the most value of a set of the first `i` items weighing
/// exactly `w`, by trying every set; `None` where no set weighs `w`. Exponential; for a handful
/// of items.
///
/// Lean: `Knapsack.LongestTo`.
///
/// # Panics
///
/// If `weights` and `values` differ in length, there are more than 20 items, or `capacity` is
/// past 10 000.
#[must_use]
pub fn longest_gains(weights: &[u64], values: &[i64], capacity: u64) -> Vec<Vec<Option<i64>>> {
    let n = weights.len();
    assert!(
        n == values.len() && n <= 20 && capacity <= 10_000,
        "a handful of items and a small box"
    );
    let width = capacity as usize + 1;
    (0..=n)
        .map(|i| {
            let mut layer: Vec<Option<i64>> = vec![None; width];
            for set in 0u32..1 << i {
                let picked = (0..i).filter(|&k| set & (1 << k) != 0);
                let weight: u128 = picked.clone().map(|k| u128::from(weights[k])).sum();
                if weight <= u128::from(capacity) {
                    let value: i64 = picked.map(|k| values[k]).sum();
                    let slot = &mut layer[weight as usize];
                    if slot.is_none_or(|b| b < value) {
                        *slot = Some(value);
                    }
                }
            }
            layer
        })
        .collect()
}
