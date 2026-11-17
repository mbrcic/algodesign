// SPDX-License-Identifier: Apache-2.0
//! The cheapest path from one start to every vertex of a graph with no cycle: each vertex's row
//! tried once, in a topological order.
//!
//! The order is the Graphs chapter's Kahn order ([`topological_order`]); on a graph with a cycle
//! there is none, and the answer is Kahn's [`Stuck`] set. The walk takes the vertices in that
//! order. A vertex with no known cost is passed without trying its row; for one with a known cost,
//! every arrow out of it is tried in its row's order, by neighbor, then id: when the arrow's end
//! has no known cost, or the arrow gives less, the end gets the new cost and this vertex as its
//! previous one. The previous vertex changes only when a cost drops. Every arrow into a vertex
//! comes from one taken before it, so its cost is final when it is taken. This is Cormen,
//! Leiserson, Rivest and Stein, *Introduction to Algorithms*, 4th ed., §22.2, DAG-SHORTEST-PATHS,
//! p. 617.
//!
//! Arrows may be negative. The sums are not saturated: the input range is costs whose
//! total over every path fits an `i64`.
//!
//! **Against the Python, and how fast.** The walk is [`dag_paths`] alone, where the Python also
//! keeps `State`, the walk's state with its `start` and `step`, as the Lean's. Kahn's order comes
//! from the Graphs chapter's packed rows, and the walk then reads each row straight from the same
//! arrays, keeping the known costs and the previous vertices in two flat vectors.
//! `cargo bench -p algodesign --bench paths -- dag` times it on 10^5 vertices and 4 · 10^5 arrows
//! with no cycle.
//!
//! Lean counterpart: `AlgoDesign.Paths.DagOrder`.

use crate::graphs::{topological_order, Stuck};

use super::distances::Distances;
use super::network::Network;

/// The cheapest cost from `start` to every vertex of a graph with no cycle, and each vertex's
/// previous vertex on a cheapest path; arrows may be negative. Linear in vertices plus
/// arrows: Kahn's order, then one look at every vertex and every arrow.
///
/// The costs along every path must sum within `i64`.
///
/// Lean: `DagOrder.dagPaths_reached`, `dagPaths_previous`, `dagPaths_unreached`,
/// `dagPaths_stuck` and `dagPaths_cost`.
///
/// # Errors
///
/// [`Stuck`], Kahn's set of the vertices that could not be placed, when the graph has a cycle.
///
/// # Panics
///
/// If `start` is not a vertex of `net`.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dag_paths, Network};
///
/// // The way round through 2 costs less than the direct arrow to 1.
/// let g = Digraph::new(4, &[(0, 1), (0, 2), (2, 1), (1, 3)]).unwrap();
/// let d = dag_paths(&Network::new(g, vec![5, 2, -4, 1]).unwrap(), 0).unwrap();
/// assert_eq!(d.cost, [Some(0), Some(-2), Some(2), Some(-1)]);
/// assert_eq!(d.path_to(3), Some(vec![0, 2, 1, 3]));
///
/// // A cycle of two: every vertex waits forever.
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// let stuck = dag_paths(&Network::new(g, vec![1, 1, 1]).unwrap(), 0).unwrap_err();
/// assert_eq!(stuck.vertices, [0, 1, 2]);
/// ```
pub fn dag_paths(net: &Network, start: u32) -> Result<Distances, Stuck> {
    let g = net.graph();
    let cost = net.cost();
    let n = g.n();
    let s = start as usize;
    assert!(s < n, "start {start} out of range 0..{n}");
    let order = topological_order(g)?;
    let (offsets, neighbors, ids) = (&g.out.offsets, &g.out.neighbors, &g.out.ids);
    let mut known: Vec<Option<i64>> = vec![None; n];
    let mut previous: Vec<Option<u32>> = vec![None; n];
    known[s] = Some(0);
    for &u in &order {
        let u_at = u as usize;
        // A vertex never reached: its row is not tried.
        if let Some(du) = known[u_at] {
            for k in offsets[u_at]..offsets[u_at + 1] {
                let w_at = neighbors[k] as usize;
                let dw = du + cost[ids[k] as usize];
                if known[w_at].is_none_or(|old| dw < old) {
                    known[w_at] = Some(dw);
                    previous[w_at] = Some(u);
                }
            }
        }
    }
    Ok(Distances {
        cost: known,
        previous,
    })
}

#[cfg(test)]
#[path = "unit_tests/dag.rs"]
mod tests;
