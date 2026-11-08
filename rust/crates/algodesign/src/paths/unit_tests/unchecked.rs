// SPDX-License-Identifier: Apache-2.0
//! What the paths module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, or not at all, and checks the error code it fails with; with the feature
//! on, the feature-gated ones run. Compiled only when rustdoc collects doctests, so no page of the
//! documentation shows them.

/// `dijkstra::State::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dijkstra::State, Network};
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let states = State::trace(&Network::new(g, vec![1]).unwrap(), 0);
/// assert_eq!(states.len(), 3);
/// ```
pub struct DijkstraStates;

/// `dijkstra::State::from_parts` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{dijkstra::State, Network};
///
/// let net = Network::new(Digraph::new(1, &[]).unwrap(), vec![]).unwrap();
/// let st = State::from_parts(vec![0], vec![Some(0)], vec![None], vec![], 1);
/// assert!(st.is_valid(&net, 0, &[Some(0)], &[Some(0)]));
/// ```
pub struct DijkstraParts;

/// `a_star::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{a_star, Network};
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let states = a_star::trace(&Network::new(g, vec![1]).unwrap(), 0, 1, &[1, 0]);
/// assert_eq!(states.len(), 2);
/// ```
pub struct AStarStates;

/// `bellman_ford::State::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{bellman_ford::State, Network};
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let states = State::trace(&Network::new(g, vec![-1]).unwrap(), 0);
/// assert_eq!(states.len(), 3);
/// ```
pub struct BellmanFordStates;

/// `bellman_ford::State::from_parts` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Digraph;
/// use algodesign::paths::{bellman_ford::State, Network};
///
/// let net = Network::new(Digraph::new(1, &[]).unwrap(), vec![]).unwrap();
/// let st = State::from_parts(vec![Some(0)], vec![None], 0, None, 0);
/// assert!(st.is_valid(&net, 0, &[vec![0]], &[vec![0]], &[Some(0)]));
/// ```
pub struct BellmanFordParts;

/// `kruskal::State::trace` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::Graph;
/// use algodesign::paths::{kruskal::State, LinkNetwork};
///
/// let g = Graph::new(2, &[(0, 1)]).unwrap();
/// let states = State::trace(&LinkNetwork::new(g, vec![1]).unwrap());
/// assert_eq!(states.len(), 2);
/// ```
pub struct KruskalStates;

/// `kruskal::State::from_parts` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::graphs::{Graph, UnionFind};
/// use algodesign::paths::{kruskal::State, LinkNetwork};
///
/// let net = LinkNetwork::new(Graph::new(1, &[]).unwrap(), vec![]).unwrap();
/// let st = State::from_parts(vec![], vec![], vec![], UnionFind::new(1));
/// assert!(st.is_valid(&net, &[vec![]]));
/// ```
pub struct KruskalParts;
