// SPDX-License-Identifier: Apache-2.0
//! The cheapest spanning forest, grown one tree at a time by Prim's walk: Dijkstra's walk with the
//! key the link alone.
//!
//! The skeleton is Dijkstra's: a binary heap of lazy entries, the smallest taken first, a vertex
//! already in a tree skipped when it comes off, a link pushed only when it is cheaper, by (cost,
//! id), than every link pushed so far towards its vertex, as Dijkstra pushes only a lower cost,
//! and the row of each vertex added walked in the Graphs chapter's order, by neighbor, then id.
//! Only the key changes: Dijkstra's is the cost so far plus the arrow, Prim's is the link's cost
//! alone. An entry is (link cost, link id, vertex), so equal costs go by link id, the order Kruskal
//! takes the links in. The walk starts at vertex 0; when the heap is empty it starts again from the
//! lowest-numbered vertex not yet in a tree, so a graph in several pieces gets one tree per piece.
//! Any costs are allowed. Jarník (1930) and Prim (1957); the method as Cormen, Leiserson, Rivest
//! and Stein, *Introduction to Algorithms*, 4th ed., §21.2, `MST-PRIM`, p. 596, which lowers a key
//! in place where this walk pushes a new entry.
//!
//! `O(m log m)` for `m` links: each link pushes at most one entry.
//!
//! **Against the Python, and how fast.** The walk counts the entries it pushes in test builds, for
//! the tests that hold the push rule, where the Python's tests count them by wrapping
//! `heapq.heappush`. The links tried, their order and the links added are the same. The walk reads
//! each row straight from the graph's packed arrays, keeps the cheapest (cost, id) pushed towards
//! each vertex in one flat vector, and queues plain (cost, id, vertex) triples in the standard
//! library's binary heap.
//! `cargo bench -p algodesign --bench paths -- prim` times it on the links `kruskal` is timed on.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use super::link_network::LinkNetwork;

/// The queue: the smallest (link cost, link id, vertex) on top.
type Queue = BinaryHeap<Reverse<(i64, u32, u32)>>;

/// The link ids of a cheapest spanning forest, in the order added: each tree started at its
/// lowest-numbered vertex and grown by the cheapest link that leaves the tree, equal costs by link
/// id. The
/// same set as [`kruskal`](super::kruskal()) gives, since both take the cheapest link by (cost,
/// id). `O(m log m)` for `m` links.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Graph;
/// use algodesign::paths::{prim, LinkNetwork};
///
/// // A square 0 – 1 – 2 – 3 – 0 whose link 3 – 0 is dear, and an island 4.
/// let g = Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 0)]).unwrap();
/// assert_eq!(prim(&LinkNetwork::new(g, vec![2, 1, 3, 9]).unwrap()), [0, 1, 2]);
/// ```
#[must_use]
pub fn prim(net: &LinkNetwork) -> Vec<u32> {
    walk(net, |_| {})
}

/// Prim's walk, handing `watch` the number of entries pushed once the forest is grown. Only test
/// builds and the `unchecked` feature make the call.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn walk(net: &LinkNetwork, mut watch: impl FnMut(usize)) -> Vec<u32> {
    let g = net.graph();
    let cost = net.cost();
    let n = g.n();
    let (offsets, neighbors, ids) = (&g.adj.offsets, &g.adj.neighbors, &g.adj.ids);
    let mut in_tree = vec![false; n];
    // The cheapest (link cost, link id) pushed so far towards each vertex.
    let mut best: Vec<Option<(i64, u32)>> = vec![None; n];
    let mut added = Vec::with_capacity(n.saturating_sub(1));
    let mut queue: Queue = BinaryHeap::new();
    let mut pushed = 0usize;
    let push_row = |v: usize,
                    in_tree: &[bool],
                    best: &mut [Option<(i64, u32)>],
                    queue: &mut Queue,
                    pushed: &mut usize| {
        for k in offsets[v]..offsets[v + 1] {
            let w = neighbors[k] as usize;
            let key = (cost[ids[k] as usize], ids[k]);
            if !in_tree[w] && best[w].is_none_or(|old| key < old) {
                best[w] = Some(key);
                queue.push(Reverse((key.0, key.1, neighbors[k])));
                watched!(*pushed += 1);
            }
        }
    };
    for root in 0..n {
        if in_tree[root] {
            continue;
        }
        in_tree[root] = true;
        push_row(root, &in_tree, &mut best, &mut queue, &mut pushed);
        while let Some(Reverse((_, id, v))) = queue.pop() {
            let v = v as usize;
            if in_tree[v] {
                continue;
            }
            in_tree[v] = true;
            added.push(id);
            push_row(v, &in_tree, &mut best, &mut queue, &mut pushed);
        }
    }
    watched!(watch(pushed));
    added
}

#[cfg(test)]
#[path = "unit_tests/prim.rs"]
mod tests;
