// SPDX-License-Identifier: Apache-2.0
//! A network: a directed graph of the Graphs chapter, one capacity per arrow, listed by arrow id,
//! a source and a sink.
//!
//! Two arrows between the same two vertices, in the same or opposite directions, stay two arrows,
//! each with its own capacity, so a flow is told by arrow id. A loop is allowed and never carries
//! anything: no augmenting path passes a vertex twice. Capacities are unsigned integers of a type
//! the caller picks, [`u64`] by default or [`u32`]; amounts are summed in [`u64`].
//!
//! **Against the Python, and how fast.** The Python's network is its own; here it wraps the Graphs
//! chapter's [`Digraph`], its capacities are `u64` or `u32`, and it also refuses more than
//! [`ARROW_LIMIT`] arrows and capacities leaving the source that add up past `u64::MAX`, so no flow
//! amount overflows. It is built once, checked once, and read by every method.
//!
//! Lean counterpart: `AlgoDesign.Flows.Network` (`Flows/MaxFlow/Spec.lean`), with `WellFormed`
//! holding by construction.

use std::fmt;

use crate::graphs::Digraph;

mod sealed {
    pub trait Sealed {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
}

/// A capacity: an unsigned integer, [`u32`] or [`u64`]. Sealed: the library's procedures rely on
/// exactly these two types.
pub trait Capacity:
    sealed::Sealed
    + Copy
    + Ord
    + Default
    + fmt::Debug
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + 'static
{
    /// Nothing.
    const ZERO: Self;
    /// One unit.
    const ONE: Self;
    /// The largest value of the type.
    const MAX: Self;
    /// The same amount as a [`u64`].
    fn to_u64(self) -> u64;
    /// The largest power of two not above this amount; zero for zero.
    #[must_use]
    fn power_of_two_below(self) -> Self;
    /// Half this amount, rounded down.
    #[must_use]
    fn half(self) -> Self;
}

impl Capacity for u32 {
    const ZERO: Self = 0;
    const ONE: Self = 1;
    const MAX: Self = u32::MAX;
    fn to_u64(self) -> u64 {
        u64::from(self)
    }
    fn power_of_two_below(self) -> Self {
        if self == 0 {
            0
        } else {
            1 << (u32::BITS - 1 - self.leading_zeros())
        }
    }
    fn half(self) -> Self {
        self >> 1
    }
}

impl Capacity for u64 {
    const ZERO: Self = 0;
    const ONE: Self = 1;
    const MAX: Self = u64::MAX;
    fn to_u64(self) -> u64 {
        self
    }
    fn power_of_two_below(self) -> Self {
        if self == 0 {
            0
        } else {
            1 << (u64::BITS - 1 - self.leading_zeros())
        }
    }
    fn half(self) -> Self {
        self >> 1
    }
}

/// The most arrows a network may have: each arrow gives two residual arrows, and their ids, `2i`
/// and `2i + 1`, are `u32`s with two values kept apart.
pub const ARROW_LIMIT: usize = (1 << 31) - 1;

/// Why a network, or an assignment's table, was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowsError {
    /// The number of capacities is not the number of arrows.
    CapacityCountMismatch {
        /// The number of capacities given.
        capacities: usize,
        /// The number of arrows of the graph.
        arrows: usize,
    },
    /// More than [`ARROW_LIMIT`] arrows.
    TooManyArrows {
        /// The number of arrows of the graph.
        count: usize,
    },
    /// The source or the sink is not a vertex of the graph.
    EndOutOfRange {
        /// The vertex given.
        vertex: u32,
        /// The number of vertices.
        n: usize,
    },
    /// The source is the sink.
    SourceIsSink {
        /// The vertex given as both.
        vertex: u32,
    },
    /// The capacities of the arrows leaving the source add up to more than [`u64::MAX`], so a
    /// flow amount might not fit a `u64`.
    SourceCapacityTooLarge,
    /// The number of costs is not the number of arrows.
    CostCountMismatch {
        /// The number of costs given.
        costs: usize,
        /// The number of arrows of the network.
        arrows: usize,
    },
    /// An arrow costs less than nothing.
    NegativeCost {
        /// The arrow's id.
        arrow: usize,
        /// Its cost.
        cost: i64,
    },
    /// The costs of a cheapest flow's arrows add up to more than `i64::MAX / 4`, so the heights
    /// and the search's sums might not fit an [`i64`].
    CostSumTooLarge,
    /// A cheapest flow's total cost does not fit an [`i64`].
    TotalCostTooLarge,
    /// An assignment's table has a row whose length is not the number of rows: not as many
    /// objects as people.
    NotSquare {
        /// The first such row.
        row: usize,
        /// Its length.
        length: usize,
        /// The number of rows, one per person.
        people: usize,
    },
    /// An assignment's decimal cost is infinite or not a number.
    CostNotFinite {
        /// The person, the row.
        person: usize,
        /// The object, the column.
        object: usize,
    },
    /// An assignment's decimal cost is larger in magnitude than `f64::MAX / (16 n)` for `n`
    /// people, so the labels might overflow.
    CostTooLarge {
        /// The person, the row.
        person: usize,
        /// The object, the column.
        object: usize,
    },
}

impl fmt::Display for FlowsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityCountMismatch { capacities, arrows } => write!(
                f,
                "{capacities} capacities for {arrows} arrows: one capacity per arrow"
            ),
            Self::TooManyArrows { count } => {
                write!(f, "{count} arrows: at most 2^31 - 1 allowed")
            }
            Self::EndOutOfRange { vertex, n } => {
                write!(f, "source or sink {vertex} out of range 0..{n}")
            }
            Self::SourceIsSink { vertex } => {
                write!(f, "vertex {vertex} is both the source and the sink")
            }
            Self::SourceCapacityTooLarge => write!(
                f,
                "the capacities leaving the source add up to more than u64::MAX"
            ),
            Self::CostCountMismatch { costs, arrows } => {
                write!(f, "{costs} costs for {arrows} arrows: one cost per arrow")
            }
            Self::NegativeCost { arrow, cost } => {
                write!(f, "arrow {arrow} costs {cost}, less than nothing")
            }
            Self::CostSumTooLarge => {
                write!(f, "the costs add up to more than i64::MAX / 4")
            }
            Self::TotalCostTooLarge => {
                write!(f, "the flow's total cost does not fit an i64")
            }
            Self::NotSquare {
                row,
                length,
                people,
            } => write!(
                f,
                "row {row} has {length} costs for {people} people: one cost per object, as many \
                 objects as people"
            ),
            Self::CostNotFinite { person, object } => {
                write!(
                    f,
                    "the cost of object {object} for person {person} is not finite"
                )
            }
            Self::CostTooLarge { person, object } => write!(
                f,
                "the cost of object {object} for person {person} is above f64::MAX / (16 n) in \
                 magnitude"
            ),
        }
    }
}

impl std::error::Error for FlowsError {}

/// A directed graph, the capacity of each of its arrows by id, a source and a sink.
///
/// Lean: `Flows.Network`, with `WellFormed` holding by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Network<C = u64> {
    graph: Digraph,
    capacity: Vec<C>,
    source: u32,
    sink: u32,
}

impl<C: Capacity> Network<C> {
    /// The network of `graph` whose arrow `id` has capacity `capacity[id]`, from `source` to
    /// `sink`.
    ///
    /// # Errors
    ///
    /// [`FlowsError::CapacityCountMismatch`] when `capacity` does not have one entry per arrow,
    /// [`FlowsError::TooManyArrows`] past [`ARROW_LIMIT`] arrows,
    /// [`FlowsError::EndOutOfRange`] when the source or the sink is not a vertex,
    /// [`FlowsError::SourceIsSink`] when they are the same vertex, and
    /// [`FlowsError::SourceCapacityTooLarge`] when the capacities of the arrows leaving the source
    /// (loops not counted) add up to more than [`u64::MAX`].
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::flows::{FlowsError, Network};
    /// use algodesign::graphs::Digraph;
    ///
    /// let g = Digraph::new(3, &[(0, 1), (1, 2)]).unwrap();
    /// let net: Network = Network::new(g.clone(), vec![4, 3], 0, 2).unwrap();
    /// assert_eq!(net.arrow_capacity(1), 3);
    /// assert_eq!(
    ///     Network::new(g, vec![4u64, 3], 1, 1),
    ///     Err(FlowsError::SourceIsSink { vertex: 1 })
    /// );
    /// ```
    pub fn new(
        graph: Digraph,
        capacity: Vec<C>,
        source: u32,
        sink: u32,
    ) -> Result<Self, FlowsError> {
        let m = graph.arrow_count();
        if capacity.len() != m {
            return Err(FlowsError::CapacityCountMismatch {
                capacities: capacity.len(),
                arrows: m,
            });
        }
        if m > ARROW_LIMIT {
            return Err(FlowsError::TooManyArrows { count: m });
        }
        let n = graph.n();
        for vertex in [source, sink] {
            if vertex as usize >= n {
                return Err(FlowsError::EndOutOfRange { vertex, n });
            }
        }
        if source == sink {
            return Err(FlowsError::SourceIsSink { vertex: source });
        }
        let mut leaving: u64 = 0;
        for (to, id) in graph.out(source as usize).iter() {
            if to != source {
                leaving = leaving
                    .checked_add(capacity[id as usize].to_u64())
                    .ok_or(FlowsError::SourceCapacityTooLarge)?;
            }
        }
        Ok(Self {
            graph,
            capacity,
            source,
            sink,
        })
    }
}

impl<C: Copy> Network<C> {
    /// The graph.
    #[must_use]
    pub fn graph(&self) -> &Digraph {
        &self.graph
    }

    /// The capacity of every arrow, by id.
    #[must_use]
    pub fn capacity(&self) -> &[C] {
        &self.capacity
    }

    /// The capacity of arrow `id`.
    ///
    /// # Panics
    ///
    /// If `id` is not below the number of arrows.
    #[must_use]
    pub fn arrow_capacity(&self, id: usize) -> C {
        self.capacity[id]
    }

    /// Where the flow starts.
    #[must_use]
    pub fn source(&self) -> u32 {
        self.source
    }

    /// Where the flow ends.
    #[must_use]
    pub fn sink(&self) -> u32 {
        self.sink
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.graph.n()
    }

    /// The number of arrows.
    #[must_use]
    pub fn arrow_count(&self) -> usize {
        self.graph.arrow_count()
    }

    /// The graph, the capacities, the source and the sink, given back.
    #[must_use]
    pub fn into_parts(self) -> (Digraph, Vec<C>, u32, u32) {
        (self.graph, self.capacity, self.source, self.sink)
    }
}

#[cfg(test)]
#[path = "unit_tests/network.rs"]
mod tests;
