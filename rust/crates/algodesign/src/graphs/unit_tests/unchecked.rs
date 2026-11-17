// SPDX-License-Identifier: Apache-2.0
//! What the graphs module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, or not at all, and checks the error code it fails with; with the feature
//! on, the feature-gated ones run. Compiled only when rustdoc collects doctests, so no page of the
//! documentation shows them.

/// `block_cut::Walk::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::{block_cut::Walk, Graph};
///
/// let g = Graph::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
/// let states = Walk::trace(&g);
/// assert!(states.iter().all(|w| w.is_valid(&g)));
/// ```
pub struct BlocksWalk;

/// `scc::Walk::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::{scc::Walk, Digraph};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// let states = Walk::trace(&g);
/// assert!(states.iter().all(|w| w.is_valid(&g)));
/// ```
pub struct SccWalk;

/// `topo::KahnState::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::{topo::KahnState, Digraph};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2)]).unwrap();
/// let states = KahnState::trace(&g);
/// assert_eq!(states.len(), 4);
/// assert!(states.iter().all(|st| st.is_valid(&g)));
/// ```
pub struct KahnStates;

/// `UnionFind::parents` and `ranks` need the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::UnionFind;
///
/// let mut u = UnionFind::new(3);
/// u.union(0, 1);
/// assert_eq!(u.parents(), &[0, 0, 2]);
/// assert_eq!(u.ranks(), &[1, 0, 0]);
/// ```
pub struct UnionFindParts;
