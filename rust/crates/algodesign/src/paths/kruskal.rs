// SPDX-License-Identifier: Apache-2.0
//! The cheapest spanning forest, by Kruskal's walk: take the links cheapest first, and keep a link
//! unless it closes a cycle.
//!
//! The link ids are sorted by cost with a stable sort, so equal costs go by id. The walk takes the
//! next link and gives its two ends to the Graphs chapter's [`UnionFind::union`]: the merge answers
//! yes when the ends were in two groups, and the link is kept; it answers no when they were already
//! in one, and the link would close a cycle. A loop is never kept, and of two links between the
//! same vertices the first in the order is. The walk stops once one group is left, since every
//! later link has both ends in it; on a graph in several pieces it never stops early and gives one
//! tree per piece. Any costs are allowed, zero and negative included. This is Cormen,
//! Leiserson, Rivest and Stein, *Introduction to Algorithms*, 4th ed., §21.2, `MST-KRUSKAL`,
//! p. 594, with the union's answer as the test; that the kept links stay part of some cheapest
//! forest is the cut property with ties allowed, Theorem 21.1, p. 587.
//!
//! `O(m log m)` for `m` links: the sort, then two lookups per link given to the union-find, each
//! nearly constant over the run.
//!
//! [`State`] is a state of the walk, with one check per piece of the Lean `Valid` and `WellFormed`
//! on it.
//!
//! **Against the Python, and how fast.** One walk serves [`kruskal`] and [`kruskal_with_tried`],
//! keeping a position in the sorted ids instead of a list of the rest, and records the links tried
//! only when asked, where the Python's `kruskal_with_tried` runs `State`. The sort is the standard
//! library's stable sort of `u32` link ids by cost, and the walk reads each link's two ends from
//! the graph's list of links by id.
//! `cargo bench -p algodesign --bench paths -- kruskal` times it on 10^5 vertices and 4 · 10^5
//! links.
//!
//! Lean counterpart: `AlgoDesign.Paths.Kruskal`.

use super::link_network::LinkNetwork;
use crate::graphs::UnionFind;

/// The kept link ids of a cheapest spanning forest, in the order kept: by cost, equal costs by id.
/// They join every two vertices the graph joins, close no cycle, and no other such set of links
/// has a smaller total. `O(m log m)` for `m` links.
///
/// Lean: `Kruskal.contract` (`kruskal_cheapestForest`).
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Graph;
/// use algodesign::paths::{kruskal, LinkNetwork};
///
/// // A triangle whose links all cost 1: links 0 and 1 are kept, and one group is left.
/// let g = Graph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// assert_eq!(kruskal(&LinkNetwork::new(g, vec![1, 1, 1]).unwrap()), [0, 1]);
/// ```
#[must_use]
pub fn kruskal(net: &LinkNetwork) -> Vec<u32> {
    walk(net, None, |_, _, _, _| {})
}

/// [`kruskal`], with the link ids given to the union-find, in order: each link at most once, and
/// none after one group is left.
///
/// Lean: `Kruskal.kruskal_cost`.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::Graph;
/// use algodesign::paths::{kruskal_with_tried, LinkNetwork};
///
/// // Link 2 is never tried: after links 0 and 1 one group is left.
/// let g = Graph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let (kept, tried) = kruskal_with_tried(&LinkNetwork::new(g, vec![1, 1, 1]).unwrap());
/// assert_eq!(kept, [0, 1]);
/// assert_eq!(tried, [0, 1]);
/// ```
#[must_use]
pub fn kruskal_with_tried(net: &LinkNetwork) -> (Vec<u32>, Vec<u32>) {
    let mut tried = Vec::new();
    let kept = walk(net, Some(&mut tried), |_, _, _, _| {});
    (kept, tried)
}

/// The link ids sorted by cost, equal costs by id: a stable sort of the ids in order (Lean
/// `order`).
fn order(net: &LinkNetwork) -> Vec<u32> {
    let cost = net.cost();
    let m = u32::try_from(cost.len()).expect("a graph has at most u32::MAX links");
    let mut ids: Vec<u32> = (0..m).collect();
    ids.sort_by(|&i, &j| cost[i as usize].cmp(&cost[j as usize]));
    ids
}

/// Kruskal's walk over the library's order, recording the links tried in `tried` if it is given.
/// It hands `watch` its state at the start and after every step: the links still to take, the
/// kept links, the links tried and the union-find. Only test builds and the `unchecked` feature
/// make the calls, and only `State::trace`, which gives a `tried`, reads them.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn walk(
    net: &LinkNetwork,
    mut tried: Option<&mut Vec<u32>>,
    mut watch: impl FnMut(&[u32], &[u32], &[u32], &UnionFind),
) -> Vec<u32> {
    let g = net.graph();
    let order = order(net);
    let mut uf = UnionFind::new(g.n());
    let mut kept = Vec::with_capacity(g.n().saturating_sub(1));
    watched!(watch(
        &order,
        &kept,
        tried.as_deref().map_or(&[], |t| t),
        &uf
    ));
    for (k, &i) in order.iter().enumerate() {
        if uf.count() == 1 {
            break;
        }
        let (a, b) = g.link(i as usize);
        if uf.union(a as usize, b as usize) {
            kept.push(i);
        }
        if let Some(t) = tried.as_deref_mut() {
            t.push(i);
        }
        watched!(watch(
            &order[k + 1..],
            &kept,
            tried.as_deref().map_or(&[], |t| t),
            &uf
        ));
    }
    kept
}

/// The labels [`State::check_valid`] names, in the order of the Lean `Valid` and `WellFormed`.
const LABELS: [&str; 6] = [
    "invariant 1 (part_of_cheapest)",
    "invariant 2 (groups_are_kept_joins)",
    "not in the box (union_find_ready)",
    "not in the box (kept_closes_no_cycle)",
    "not in the box (rest_cheapest_first)",
    "not in the box (passed_are_joined)",
];

/// A state of Kruskal's walk: the link ids still to take, in order; the kept link ids, in the
/// order kept; the link ids given to the union-find, in order; and the union-find. The states come
/// only from the walk itself, under the `unchecked` feature, for tests that watch it: `cargo test
/// --features unchecked`.
///
/// Box invariant 1 needs an answer the state cannot give: the cheapest spanning forests of the
/// network. Its check takes them as an argument; the tests find them by trying every set of links.
///
/// Lean: `Kruskal.State`; the checks below are the pieces of its `Valid` and `WellFormed`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// The link ids still to take, in order.
    rest: Vec<u32>,
    /// The kept link ids, in the order kept.
    kept: Vec<u32>,
    /// The link ids given to the union-find, in order.
    tried: Vec<u32>,
    /// The union-find over the vertices, its groups joined by the kept links.
    uf: UnionFind,
}

impl State {
    /// Box invariant 1: the links kept so far are part of some minimum such set. `cheapest`
    /// holds the network's cheapest spanning forests, each a list of link ids.
    ///
    /// Lean: `PartOfCheapest`.
    #[must_use]
    pub fn is_part_of_cheapest(&self, cheapest: &[Vec<u32>]) -> bool {
        cheapest
            .iter()
            .any(|t| self.kept.iter().all(|i| t.contains(i)))
    }

    /// Box invariant 2: two vertices are in one union-find group exactly when the kept links join
    /// them. The groups are read without compressing, so a broken union-find gets an answer.
    ///
    /// Lean: `GroupsAreKeptJoins`.
    #[must_use]
    pub fn is_groups_are_kept_joins(&self, net: &LinkNetwork) -> bool {
        let n = net.n();
        let joined = net.groups(&self.kept);
        (0..n).all(|u| (0..n).all(|v| self.uf.same(u, v) == joined.same(u, v)))
    }

    /// Not in the box: the union-find is legal and well formed, over the graph's vertices.
    ///
    /// Lean: `UnionFindReady`.
    #[must_use]
    pub fn is_union_find_ready(&self, net: &LinkNetwork) -> bool {
        self.uf.is_valid() && self.uf.items() == net.n()
    }

    /// Not in the box: the kept links are links of the graph and close no cycle.
    ///
    /// Lean: `KeptClosesNoCycle`.
    #[must_use]
    pub fn is_kept_closes_no_cycle(&self, net: &LinkNetwork) -> bool {
        let m = net.graph().link_count();
        self.kept.iter().all(|&i| (i as usize) < m) && net.closes_no_cycle(&self.kept)
    }

    /// Not in the box: the links still to take are links of the graph, cheapest first.
    ///
    /// Lean: `RestCheapestFirst`.
    #[must_use]
    pub fn is_rest_cheapest_first(&self, net: &LinkNetwork) -> bool {
        let m = net.graph().link_count();
        self.rest.iter().all(|&i| (i as usize) < m)
            && self
                .rest
                .windows(2)
                .all(|p| net.cost_at(p[0]) <= net.cost_at(p[1]))
    }

    /// Not in the box: the kept links join the two ends of every link already taken, every link of
    /// the graph not among those still to take.
    ///
    /// Lean: `PassedAreJoined`.
    #[must_use]
    pub fn is_passed_are_joined(&self, net: &LinkNetwork) -> bool {
        let mut joined = net.groups(&self.kept);
        (0..net.graph().link_count()).all(|i| {
            let (a, b) = net.graph().link(i);
            self.rest.contains(&(i as u32)) || joined.joined(a as usize, b as usize)
        })
    }

    /// Lean `Valid` and `WellFormed`: [`State::is_part_of_cheapest`],
    /// [`State::is_groups_are_kept_joins`], [`State::is_union_find_ready`],
    /// [`State::is_kept_closes_no_cycle`], [`State::is_rest_cheapest_first`] and
    /// [`State::is_passed_are_joined`].
    #[must_use]
    pub fn is_valid(&self, net: &LinkNetwork, cheapest: &[Vec<u32>]) -> bool {
        self.check_valid(net, cheapest).is_ok()
    }

    /// [`State::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (part_of_cheapest)"`, `"invariant 2 (groups_are_kept_joins)"`,
    /// `"not in the box (union_find_ready)"`, `"not in the box (kept_closes_no_cycle)"`,
    /// `"not in the box (rest_cheapest_first)"` or `"not in the box (passed_are_joined)"`.
    pub fn check_valid(
        &self,
        net: &LinkNetwork,
        cheapest: &[Vec<u32>],
    ) -> Result<(), &'static str> {
        let pieces = [
            self.is_part_of_cheapest(cheapest),
            self.is_groups_are_kept_joins(net),
            self.is_union_find_ready(net),
            self.is_kept_closes_no_cycle(net),
            self.is_rest_cheapest_first(net),
            self.is_passed_are_joined(net),
        ];
        match pieces.iter().position(|&ok| !ok) {
            Some(i) => Err(LABELS[i]),
            None => Ok(()),
        }
    }

    /// Every state of the walk, from the start to the last step, one per link taken. For tests;
    /// not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(net: &LinkNetwork) -> Vec<Self> {
        let mut states = Vec::new();
        let mut tried = Vec::new();
        let _ = walk(net, Some(&mut tried), |rest, kept, tried, uf| {
            states.push(Self {
                rest: rest.to_vec(),
                kept: kept.to_vec(),
                tried: tried.to_vec(),
                uf: uf.clone(),
            });
        });
        states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no walk reaches. Not
    /// part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(rest: Vec<u32>, kept: Vec<u32>, tried: Vec<u32>, uf: UnionFind) -> Self {
        Self {
            rest,
            kept,
            tried,
            uf,
        }
    }

    /// The stored parts: the links still to take, the kept links, the links tried and the
    /// union-find. For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn parts(&self) -> (&[u32], &[u32], &[u32], &UnionFind) {
        (&self.rest, &self.kept, &self.tried, &self.uf)
    }
}

#[cfg(test)]
#[path = "unit_tests/kruskal.rs"]
mod tests;
