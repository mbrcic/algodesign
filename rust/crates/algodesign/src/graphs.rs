// SPDX-License-Identifier: Apache-2.0
//! Graphs. Each module mirrors a folder of `lean/AlgoDesign/Graphs/`.
//!
//! - [`block_cut`]: the bridges, cut vertices and blocks of an undirected graph by one low-link
//!   walk with a link stack ([`blocks`](fn@blocks)), and the block-cut forest that names the
//!   vertices separating two others.
//! - [`digraph`]: directed and undirected graphs, each vertex's row sorted by neighbour, then id.
//! - [`topo`]: a topological order by Kahn's method or the stuck set, and the reverse depth-first
//!   finishing order or a named cycle.
//! - [`scc`]: the strong components by Tarjan and Zwick's Algorithm T and by Kosaraju–Sharir,
//!   the graph of groups, and a checker for a grouping computed elsewhere.
//! - [`satisfiability`]: an assignment that satisfies every two-literal clause, or the variable
//!   that rules one out ([`two_sat`](fn@two_sat)).
//! - [`union_find`]: union by rank with full path compression, the groups of items joined so far.
//! - [`union_find_undo`]: union by rank without compression, with a log that takes merges back,
//!   last first.
// A walk's call to its watch, compiled only in test builds and with the `unchecked` feature: the
// library's walks run without it.
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

pub mod block_cut;
pub mod digraph;
pub mod satisfiability;
pub mod scc;
pub mod topo;
pub mod union_find;
pub mod union_find_undo;

#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
pub mod naive;

pub use block_cut::{blocks, BlockCutForest, Blocks};
pub use digraph::{Digraph, Graph, GraphError, Row};
pub use satisfiability::{two_sat, TwoSatError};
pub use scc::{
    check_components, condensation, kosaraju_sharir, strong_components, Components, ComponentsError,
};
pub use topo::{dfs_order, topological_order, Cycle, Stuck};
pub use union_find::UnionFind;
pub use union_find_undo::UndoUnionFind;

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "graphs/unit_tests/unchecked.rs"]
mod unchecked_doctests;
