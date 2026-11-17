//! Geometry and high-dimensional search, one variant per algorithm. Points are `f64`, row-major
//! in [`Points`]; every comparison is by squared Euclidean distance (high-dimensional data is
//! normalized first, so this ranks as cosine similarity does), and every nearest-neighbor answer
//! breaks ties toward the point stored first, as the [`scan`] does. Each module mirrors a file of
//! `lean/AlgoDesign/Geometry/`, except `rng` and [`rabitq`] (Rust only).
//!
//! - [`scan`]: the specification and every structure's oracle.
//! - [`kdtree`]: de Berg's leaf-stored k-d tree, best-first nearest neighbors, box queries.
//! - [`range_tree`]: the static 1D and 2D range trees.
//! - [`orientation`]: Shewchuk's adaptive `orient2d`, the exact sign of "which side".
//! - [`projection`]: the seeded Gaussian (Johnson–Lindenstrauss) projection.
//! - [`lsh`]: locality-sensitive hashing over any hash family; SimHash and p-stable.
//! - [`hnsw`]: HNSW, with the flat graph as its one-level case; no search guarantee is claimed.
//! - [`rabitq`]: RaBitQ's one-bit codes, a filter with an exact re-rank.
pub mod hnsw;
pub mod kdtree;
pub mod lsh;
pub mod orientation;
pub mod point;
pub mod projection;
pub mod rabitq;
pub mod range_tree;
pub(crate) mod rng;
pub mod scan;

pub use hnsw::{Hnsw, HnswParams};
pub use kdtree::{KdTree, SearchStats};
pub use lsh::{HashFamily, LshIndex, PStable, SimHash};
pub use point::{Points, PointsError};
pub use projection::GaussianProjection;
pub use rabitq::{DistanceEstimator, Rabitq, SignCodes};
pub use range_tree::{RangeTree1D, RangeTree2D};
pub use scan::Neighbor;

#[cfg(feature = "unchecked")]
#[doc(hidden)]
pub use rng::draws as rng_draws;

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "geometry/unit_tests/unchecked.rs"]
mod unchecked_doctests;
