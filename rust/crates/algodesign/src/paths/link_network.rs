// SPDX-License-Identifier: Apache-2.0
//! A link network: an undirected graph of the Graphs chapter and one integer cost per link, listed
//! by link id, the undirected sibling of [`Network`](super::Network).
//!
//! Two links between the same two vertices may cost differently, so a set of links is a list of
//! link ids, not of vertex pairs. A set of links **joins** two vertices when a chain of its links
//! leads from one to the other; it **closes no cycle** when none of its links joins two vertices
//! the others already join, so a loop, or a link twice, closes a cycle. A **spanning forest** is a
//! set of the graph's links that joins every two vertices the graph joins and closes no cycle.
//!
//! The checks below read any list of ids, as the Lean does: an id past the links has the ends
//! (0, 0) and costs 0.
//!
//! Lean counterpart: `AlgoDesign.Paths.LinkNetwork` (`LinkNetwork.lean`).

use super::network::PathsError;
use crate::graphs::{Graph, UnionFind};

/// An undirected graph and the cost of each of its links, by link id.
///
/// Lean: `Paths.LinkNetwork`, with `WellFormed` holding by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinkNetwork {
    graph: Graph,
    cost: Vec<i64>,
}

impl LinkNetwork {
    /// The link network of `graph` whose link `id` costs `cost[id]`.
    ///
    /// # Errors
    ///
    /// [`PathsError::LinkCostCountMismatch`] when `cost` does not have one entry per link.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::Graph;
    /// use algodesign::paths::{LinkNetwork, PathsError};
    ///
    /// let g = Graph::new(2, &[(0, 1), (0, 1)]).unwrap();
    /// let net = LinkNetwork::new(g.clone(), vec![5, 3]).unwrap();
    /// assert_eq!(net.link_cost(1), 3);
    /// assert_eq!(
    ///     LinkNetwork::new(g, vec![5]),
    ///     Err(PathsError::LinkCostCountMismatch { costs: 1, links: 2 })
    /// );
    /// ```
    pub fn new(graph: Graph, cost: Vec<i64>) -> Result<Self, PathsError> {
        if cost.len() != graph.link_count() {
            return Err(PathsError::LinkCostCountMismatch {
                costs: cost.len(),
                links: graph.link_count(),
            });
        }
        Ok(Self { graph, cost })
    }

    /// The graph.
    #[must_use]
    pub fn graph(&self) -> &Graph {
        &self.graph
    }

    /// The cost of every link, by id.
    #[must_use]
    pub fn cost(&self) -> &[i64] {
        &self.cost
    }

    /// The cost of link `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not below the number of links.
    #[must_use]
    pub fn link_cost(&self, id: usize) -> i64 {
        self.cost[id]
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.graph.n()
    }

    /// The graph and the costs, given back.
    #[must_use]
    pub fn into_parts(self) -> (Graph, Vec<i64>) {
        (self.graph, self.cost)
    }

    /// The cost of link `id`; 0 past the links (Lean `linkCost`).
    pub(crate) fn cost_at(&self, id: u32) -> i64 {
        self.cost.get(id as usize).copied().unwrap_or(0)
    }

    /// The two ends of link `id`; (0, 0) past the links (Lean `ends`).
    pub(crate) fn ends(&self, id: u32) -> (u32, u32) {
        if (id as usize) < self.graph.link_count() {
            self.graph.link(id as usize)
        } else {
            (0, 0)
        }
    }

    /// The groups the links `links` make: a union-find over the vertices with every link merged.
    /// An id past the links is a loop at 0 and merges nothing.
    pub(crate) fn groups(&self, links: &[u32]) -> UnionFind {
        let mut uf = UnionFind::new(self.n());
        for &i in links {
            if (i as usize) < self.graph.link_count() {
                let (a, b) = self.graph.link(i as usize);
                uf.union(a as usize, b as usize);
            }
        }
        uf
    }

    /// Whether the links `links` join `u` and `v`: a chain of them, each read either way, leads
    /// from one to the other. Every vertex is joined to itself, a vertex of the graph or not.
    /// Linear in the vertices and the links given.
    ///
    /// Lean: `LinkNetwork.Joins`.
    #[must_use]
    pub fn joins(&self, links: &[u32], u: u32, v: u32) -> bool {
        let n = self.n();
        u == v
            || ((u as usize) < n
                && (v as usize) < n
                && self.groups(links).joined(u as usize, v as usize))
    }

    /// The total cost of the links `links`, a link listed twice counted twice. In `i128`, so no
    /// sum of `i64` costs overflows.
    ///
    /// Lean: `LinkNetwork.total`.
    #[must_use]
    pub fn total(&self, links: &[u32]) -> i128 {
        links.iter().map(|&i| i128::from(self.cost_at(i))).sum()
    }

    /// Whether the links `links` join every two vertices the graph joins: the two ends of every
    /// link of the graph.
    ///
    /// Lean: `LinkNetwork.JoinsWhatGraphJoins` (by `joinsWhatGraphJoins_iff`).
    #[must_use]
    pub fn joins_what_graph_joins(&self, links: &[u32]) -> bool {
        let mut uf = self.groups(links);
        (0..self.graph.link_count()).all(|i| {
            let (a, b) = self.graph.link(i);
            uf.joined(a as usize, b as usize)
        })
    }

    /// Whether the links `links` close no cycle: no link among them joins two vertices that the
    /// others already join, the list with that one occurrence taken out. A loop, a link listed
    /// twice and an id past the links each close a cycle. Quadratic in the links given.
    ///
    /// Lean: `LinkNetwork.ClosesNoCycle`.
    #[must_use]
    pub fn closes_no_cycle(&self, links: &[u32]) -> bool {
        (0..links.len()).all(|k| {
            let mut others = links.to_vec();
            let i = others.remove(k);
            let (a, b) = self.ends(i);
            !self.joins(&others, a, b)
        })
    }

    /// Whether the links `links` are a spanning forest: links of the graph that join every two
    /// vertices the graph joins and close no cycle.
    ///
    /// Lean: `LinkNetwork.IsSpanningForest`.
    #[must_use]
    pub fn is_spanning_forest(&self, links: &[u32]) -> bool {
        links
            .iter()
            .all(|&i| (i as usize) < self.graph.link_count())
            && self.joins_what_graph_joins(links)
            && self.closes_no_cycle(links)
    }
}

#[cfg(test)]
#[path = "unit_tests/link_network.rs"]
mod tests;
