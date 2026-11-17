//! Paths. Each module mirrors a file or folder of `lean/AlgoDesign/Paths/`.
//!
//! - [`network`]: a directed graph of the Graphs chapter and one integer cost per arrow id.
//! - [`distances`]: the answer for one start, each vertex's cost and previous vertex, and the path
//!   they lead back along.
//! - [`bfs`](mod@bfs): breadth-first search, every arrow costing one.
//! - [`dijkstra`](mod@dijkstra): Dijkstra's walk, a settled vertex never changed again, to every
//!   vertex or to one goal.
//! - [`a_star`](mod@a_star): A*, Dijkstra's walk to one goal with each key the known cost plus an
//!   estimate of the cost still to go.
//! - [`bellman_ford`](mod@bellman_ford): Bellman–Ford's rounds, some negative arrows allowed,
//!   giving the cheapest costs or a negative cycle that the start reaches.
//! - [`dag`]: the cheapest paths in a graph with no cycle, each vertex's row tried in Kahn's order.
//! - [`knapsack`](mod@knapsack): knapsack as a longest path through the vertices (items decided,
//!   weight used), filled layer by layer.
//! - [`link_network`]: an undirected graph of the Graphs chapter and one integer cost per link id.
//! - [`kruskal`](mod@kruskal): the cheapest spanning forest, by Kruskal's walk over the links
//!   cheapest first.
//! - [`prim`](mod@prim): the cheapest spanning forest, by Prim's walk, Dijkstra's with the key the
//!   link alone.

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

pub mod a_star;
pub mod bellman_ford;
pub mod bfs;
pub mod dag;
pub mod dijkstra;
pub mod distances;
pub mod knapsack;
pub mod network;

pub mod kruskal;
pub mod link_network;
pub mod prim;

#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
pub mod naive;

pub use a_star::{a_star, a_star_with_settled};
pub use bellman_ford::{bellman_ford, bellman_ford_with_rounds, NegativeCycle};
pub use bfs::bfs;
pub use dag::dag_paths;
pub use dijkstra::{dijkstra, dijkstra_to, dijkstra_with_settled};
pub use distances::Distances;
pub use knapsack::{knapsack, Packing};
pub use network::{Network, PathsError};

pub use kruskal::{kruskal, kruskal_with_tried};
pub use link_network::LinkNetwork;
pub use prim::prim;

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "paths/unit_tests/unchecked.rs"]
mod unchecked_doctests;
