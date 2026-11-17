// SPDX-License-Identifier: Apache-2.0
//! Breadth-first search: the fewest arrows from one start to every vertex, and the previous vertex
//! on such a path.
//!
//! A first-in-first-out queue holds the vertices found and not yet looked out from; a vertex is
//! marked when it is first found, given its distance and the vertex it was found from, and queued
//! (Weiss, *Data Structures and Algorithm Analysis in C++*, 4th ed., Fig. 9.18, p. 392; CLRS 4th
//! ed., §20.2, p. 556). Rows are walked in the Graphs chapter's order, by neighbor, then id. Every
//! arrow costs one, so the answer is Dijkstra's on a network of unit costs.
//!
//! **Against the Python, and how fast.** The Python's queue is a `deque` of (vertex, cost) pairs;
//! here the queue is the vector of vertices in the order found, read from a front index, and each
//! vertex's cost is one more than the cost of the vertex it leaves from. Rows are read straight
//! from the graph's packed arrays. `cargo bench -p algodesign --bench paths -- bfs` times it beside
//! Dijkstra's algorithm on the same graph.
//!
//! Lean counterpart: `AlgoDesign.Paths.Bfs`.

use crate::graphs::Digraph;

use super::distances::Distances;

/// The fewest arrows from `start` to every vertex, and each vertex's previous vertex. Linear in
/// vertices plus arrows.
///
/// Lean: `Bfs.bfs_reached`, `Bfs.bfs_previous`, `Bfs.bfs_unreached`.
///
/// # Panics
///
/// If `start` is not a vertex of `g`.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::bfs;
///
/// let g = Digraph::new(4, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let d = bfs(&g, 0);
/// assert_eq!(d.cost, [Some(0), Some(1), Some(1), None]);
/// assert_eq!(d.path_to(2), Some(vec![0, 2]));
/// ```
#[must_use]
pub fn bfs(g: &Digraph, start: u32) -> Distances {
    let n = g.n();
    let s = start as usize;
    assert!(s < n, "start {start} out of range 0..{n}");
    let mut cost: Vec<Option<i64>> = vec![None; n];
    let mut previous: Vec<Option<u32>> = vec![None; n];
    // The queue is the found vertices in the order found; `front` is the next one to leave.
    let mut found: Vec<u32> = Vec::with_capacity(n);
    cost[s] = Some(0);
    found.push(start);
    let (offsets, neighbors) = (&g.out.offsets, &g.out.neighbors);
    let mut front = 0;
    while front < found.len() {
        let u = found[front] as usize;
        front += 1;
        let next = cost[u].map(|d| d + 1);
        for &w in &neighbors[offsets[u]..offsets[u + 1]] {
            let w_at = w as usize;
            if cost[w_at].is_none() {
                cost[w_at] = next;
                previous[w_at] = Some(u as u32);
                found.push(w);
            }
        }
    }
    Distances { cost, previous }
}

#[cfg(test)]
#[path = "unit_tests/bfs.rs"]
mod tests;
