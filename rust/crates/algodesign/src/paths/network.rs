// SPDX-License-Identifier: Apache-2.0
//! A network: a directed graph of the Graphs chapter and one integer cost per arrow, listed by
//! arrow id.
//!
//! Two arrows between the same two vertices may cost differently, so a path is told by the ids of
//! the arrows it takes. Costs are signed 64-bit integers; a negative arrow is allowed here,
//! and each algorithm says whether it accepts one.
//!
//! Lean counterpart: `AlgoDesign.Paths.Network` (`Network.lean`).

use std::fmt;

use crate::graphs::Digraph;

/// Why a network, an estimate for it, or a knapsack's items were refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathsError {
    /// The number of costs is not the number of arrows.
    CostCountMismatch {
        /// The number of costs given.
        costs: usize,
        /// The number of arrows of the graph.
        arrows: usize,
    },
    /// The number of costs is not the number of links.
    LinkCostCountMismatch {
        /// The number of costs given.
        costs: usize,
        /// The number of links of the graph.
        links: usize,
    },
    /// The number of estimates given to A* is not the number of vertices.
    EstimateCountMismatch {
        /// The number of estimates given.
        estimates: usize,
        /// The number of vertices of the graph.
        vertices: usize,
    },
    /// The number of values given to knapsack is not the number of weights.
    ValueCountMismatch {
        /// The number of values given.
        values: usize,
        /// The number of weights given.
        weights: usize,
    },
}

impl fmt::Display for PathsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CostCountMismatch { costs, arrows } => {
                write!(f, "{costs} costs for {arrows} arrows: one cost per arrow")
            }
            Self::LinkCostCountMismatch { costs, links } => {
                write!(f, "{costs} costs for {links} links: one cost per link")
            }
            Self::EstimateCountMismatch {
                estimates,
                vertices,
            } => {
                write!(
                    f,
                    "{estimates} estimates for {vertices} vertices: one estimate per vertex"
                )
            }
            Self::ValueCountMismatch { values, weights } => {
                write!(
                    f,
                    "{weights} weights for {values} values: one of each per item"
                )
            }
        }
    }
}

impl std::error::Error for PathsError {}

/// A directed graph and the cost of each of its arrows, by arrow id.
///
/// Lean: `Paths.Network`, with `WellFormed` holding by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Network {
    graph: Digraph,
    cost: Vec<i64>,
}

impl Network {
    /// The network of `graph` whose arrow `id` costs `cost[id]`.
    ///
    /// # Errors
    ///
    /// [`PathsError::CostCountMismatch`] when `cost` does not have one entry per arrow.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::Digraph;
    /// use algodesign::paths::{Network, PathsError};
    ///
    /// let g = Digraph::new(2, &[(0, 1), (0, 1)]).unwrap();
    /// let net = Network::new(g.clone(), vec![5, 3]).unwrap();
    /// assert_eq!(net.arrow_cost(1), 3);
    /// assert_eq!(
    ///     Network::new(g, vec![5]),
    ///     Err(PathsError::CostCountMismatch { costs: 1, arrows: 2 })
    /// );
    /// ```
    pub fn new(graph: Digraph, cost: Vec<i64>) -> Result<Self, PathsError> {
        if cost.len() != graph.arrow_count() {
            return Err(PathsError::CostCountMismatch {
                costs: cost.len(),
                arrows: graph.arrow_count(),
            });
        }
        Ok(Self { graph, cost })
    }

    /// The graph.
    #[must_use]
    pub fn graph(&self) -> &Digraph {
        &self.graph
    }

    /// The cost of every arrow, by id.
    #[must_use]
    pub fn cost(&self) -> &[i64] {
        &self.cost
    }

    /// The cost of arrow `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not below the number of arrows.
    #[must_use]
    pub fn arrow_cost(&self, id: usize) -> i64 {
        self.cost[id]
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.graph.n()
    }

    /// The graph and the costs, given back.
    #[must_use]
    pub fn into_parts(self) -> (Digraph, Vec<i64>) {
        (self.graph, self.cost)
    }
}

#[cfg(test)]
#[path = "unit_tests/network.rs"]
mod tests;
