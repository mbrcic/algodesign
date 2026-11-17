//! Flows. Each taught module mirrors a file of `lean/AlgoDesign/Flows/`.
//!
//! - [`network`]: a directed graph of the Graphs chapter, one capacity per arrow id, a source and a
//!   sink; the [`Capacity`] types, `u64` by default or `u32`.
//! - [`residual`]: the residual graph of a flow, each arrow paired with its reverse arrow, and each
//!   vertex's row in input order.
//! - [`max_flow`](mod@max_flow): the loop around a path rule, the [`PathRule`] a caller may bring,
//!   and the answer, a flow with a cut of the same amount.
//! - [`dinic`]: Dinic's rule in the Even–Itai form, the library's default: one round sends a
//!   blocking flow through the layers of a first-in-first-out search.
//! - [`edmonds_karp`]: Edmonds–Karp's rule: one round sends along one path of the fewest arrows.
//! - [`capacity_scaling`]: capacity scaling: one round sends along one path whose every arrow has
//!   residual capacity at least a threshold, halved when no such path is left.
//! - [`dinic_scaling`]: Dinic with scaling: one round is a round of Dinic's over the arrows with
//!   residual capacity at least capacity scaling's threshold; not taught, with no Lean file.
//! - [`min_cost_flow`](mod@min_cost_flow): the cheapest flow of a given amount, max flow's loop
//!   with the path rule "cheapest", a search on changed costs under heights on the vertices.
//! - [`matching`](mod@matching): a maximum matching of people with objects by max flow on a
//!   network of unit arrows, with a cover as large and, when someone stays unmatched, a blocked
//!   group, both read from the last search.
//! - [`assignment`](mod@assignment): the least-cost assignment of a square table, one person at a
//!   time, with labels on both sides that prove no assignment costs less; also on decimals.
//! - [`push_relabel`](mod@push_relabel): a largest flow and a cut by heights instead of paths,
//!   highest vertex first, with the gap step and global relabels; the same answer as max flow's.

// A rule's call to note what it sent, compiled only in test builds and with the `unchecked`
// feature: the library's rules run without it.
#[cfg(any(test, feature = "unchecked"))]
macro_rules! watched {
    ($($call:tt)*) => {
        $($call)*
    };
}
#[cfg(not(any(test, feature = "unchecked")))]
macro_rules! watched {
    ($($call:tt)*) => {};
}

pub mod assignment;
pub mod capacity_scaling;
pub mod dinic;
pub mod dinic_scaling;
pub mod edmonds_karp;
pub mod matching;
pub mod max_flow;
pub mod min_cost_flow;
pub mod network;
pub mod push_relabel;
pub mod residual;

#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
pub mod naive;

#[cfg(any(test, feature = "unchecked"))]
pub use assignment::assignment_with_steps;
pub use assignment::{assignment, assignment_f64, Assignment, AssignmentStep};
pub use capacity_scaling::CapacityScaling;
pub use dinic::Dinic;
pub use dinic_scaling::DinicScaling;
pub use edmonds_karp::EdmondsKarp;
#[cfg(any(test, feature = "unchecked"))]
pub use matching::max_matching_with_rounds;
pub use matching::{max_matching, BlockedGroup, Matching, MatchingError};
#[cfg(any(test, feature = "unchecked"))]
pub use max_flow::max_flow_with_rounds;
pub use max_flow::{max_flow, max_flow_with, MaxFlow, PathRule};
#[cfg(any(test, feature = "unchecked"))]
pub use min_cost_flow::min_cost_flow_with_rounds;
pub use min_cost_flow::{min_cost_flow, MinCostFlow, MinCostRound};
pub use network::{Capacity, FlowsError, Network, ARROW_LIMIT};
pub use push_relabel::push_relabel;
#[cfg(any(test, feature = "unchecked"))]
pub use push_relabel::{push_relabel_with_counts, Counts};
pub use residual::{Augmentation, Residual};

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "flows/unit_tests/unchecked.rs"]
mod unchecked_doctests;
