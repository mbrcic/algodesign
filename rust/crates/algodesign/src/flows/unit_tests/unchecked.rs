// SPDX-License-Identifier: Apache-2.0
//! What the flows module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, and checks the error code it fails with without it; with the feature on,
//! it runs. Compiled only when rustdoc collects doctests, so no page of the documentation shows
//! them.

/// `max_flow_with_rounds` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::flows::{Dinic, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let net = Network::new(g, vec![3u64], 0, 1).unwrap();
/// let (answer, rounds) = algodesign::flows::max_flow_with_rounds(&net, Dinic::new());
/// assert_eq!((answer.value, rounds.len()), (3, 1));
/// ```
pub struct MaxFlowRounds;

/// `Dinic::sweep_steps` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::flows::{max_flow_with, Dinic, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let net = Network::new(g, vec![3u64], 0, 1).unwrap();
/// let mut rule = Dinic::new();
/// let _ = max_flow_with(&net, &mut rule);
/// // Along 0 → 1, send, past the full 0 → 1, the source a dead end.
/// assert_eq!(rule.sweep_steps(), [4]);
/// ```
pub struct DinicSweepSteps;

/// `min_cost_flow_with_rounds` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::flows::Network;
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let net = Network::new(g, vec![3u64], 0, 1).unwrap();
/// let (answer, rounds, searches) =
///     algodesign::flows::min_cost_flow_with_rounds(&net, &[2], 2).unwrap();
/// assert_eq!((answer.cost, rounds.len(), searches), (4, 1, vec![2]));
/// ```
pub struct MinCostFlowRounds;

/// `assignment_with_steps` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// let (answer, steps) =
///     algodesign::flows::assignment_with_steps(&[vec![0, 0], vec![0, 0]]).unwrap();
/// // Person 1 finds objects 0 (held) and 1 (free) at the same changed cost: the free one.
/// assert_eq!((answer.obj, steps[1].settled.clone()), (vec![0, 1], vec![1]));
/// ```
pub struct AssignmentSteps;

/// `push_relabel_with_counts` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::flows::Network;
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(2, &[(0, 1)]).unwrap();
/// let net = Network::new(g, vec![3u64], 0, 1).unwrap();
/// let (answer, counts) = algodesign::flows::push_relabel_with_counts(&net);
/// assert_eq!((answer.value, counts.pushes, counts.global_relabels), (3, 0, 1));
/// ```
pub struct PushRelabelCounts;

/// `max_matching_with_rounds` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0425")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// let (m, rounds) =
///     algodesign::flows::max_matching_with_rounds(2, 2, &[(0, 0), (0, 1), (1, 0)]).unwrap();
/// // The second round sends person 1 to object 0 and person 0 on to object 1.
/// assert_eq!((m.pairs, rounds.len()), (vec![(0, 1), (1, 0)], 2));
/// ```
pub struct MaxMatchingRounds;
