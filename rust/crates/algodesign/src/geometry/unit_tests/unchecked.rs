// SPDX-License-Identifier: Apache-2.0
//! What the geometry module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, or not at all, and checks the error code it fails with; with the feature
//! on, the feature-gated ones run. Compiled only when rustdoc collects doctests, so no page of the
//! documentation shows them.

/// `Hnsw::build_with_pickings`, `search_beam` and `from_links_unchecked` need the
/// `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::hnsw::{Hnsw, HnswParams};
/// use algodesign::geometry::point::Points;
///
/// let pts = Points::from_rows(1, &[[0.0], [1.0], [3.0]]).unwrap();
/// let (h, pickings) = Hnsw::build_with_pickings(pts.clone(), HnswParams::new(2).flat());
/// assert_eq!(pickings.len(), 2);
/// assert_eq!(h.search_beam(&[0.0], 1, 4).len(), 3);
/// let same = Hnsw::from_links_unchecked(pts, h.params().clone(), vec![vec![vec![]]; 3], Some(0));
/// assert!(!same.is_nested_layers() || same.is_valid());
/// ```
pub struct HnswPickings;

/// `Hnsw::search_walk` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::hnsw::{Hnsw, HnswParams};
/// use algodesign::geometry::point::Points;
///
/// let pts = Points::from_rows(1, &[[0.0], [1.0], [3.0]]).unwrap();
/// let h = Hnsw::build(pts, HnswParams::new(2).flat());
/// let (beam, walk) = h.search_walk(&[0.0], 1, 4);
/// assert_eq!(beam.len(), 3);
/// assert!(walk.upper.is_empty() && walk.start == Some(0));
/// ```
pub struct HnswWalk;

/// `hnsw::select_neighbors` and `hnsw::greedy_step` need the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::hnsw;
/// use algodesign::geometry::point::Points;
///
/// let pts = Points::from_rows(1, &[[0.0], [1.0], [3.0]]).unwrap();
/// assert_eq!(hnsw::select_neighbors(&pts, &[0.0], &[(1.0, 1), (9.0, 2)], 2), vec![1]);
/// assert_eq!(hnsw::greedy_step(&pts, &[3.0], 0, &[1, 2]), 2);
/// ```
pub struct HnswSteps;

/// `KdTree::from_shape_unchecked` and `search_states` need the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::kdtree::KdTree;
/// use algodesign::geometry::point::Points;
///
/// let t = KdTree::with_bucket(Points::from_rows(1, &[[0.0], [1.0]]).unwrap(), 1);
/// let same = KdTree::from_shape_unchecked(t.points().clone(), &t.shape());
/// assert!(same.is_valid());
/// assert_eq!(t.search_states(&[0.0], 1).len(), 3);
/// ```
pub struct KdTreeFromShape;

/// `LshIndex::from_buckets_unchecked` and `buckets` need the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::lsh::{LshIndex, SimHash};
/// use algodesign::geometry::point::Points;
///
/// let pts = Points::from_rows(1, &[[0.0], [1.0]]).unwrap();
/// let idx = LshIndex::new(pts, SimHash::new(1, 2, 2, 7));
/// let same = LshIndex::from_buckets_unchecked(idx.points().clone(), idx.family().clone(),
///     idx.buckets().to_vec());
/// assert!(same.is_valid());
/// ```
pub struct LshFromBuckets;

/// `RangeTree1D::from_shape_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::geometry::range_tree::RangeTree1D;
///
/// let t = RangeTree1D::new(vec![3, 1, 2]);
/// let same = RangeTree1D::from_shape_unchecked(&t.shape().unwrap());
/// assert!(same.is_valid());
/// ```
pub struct RangeTreeFromShape;
