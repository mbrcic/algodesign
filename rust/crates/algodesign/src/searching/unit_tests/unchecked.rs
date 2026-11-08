// SPDX-License-Identifier: Apache-2.0
//! What the searching module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, or not at all, and checks the error code it fails with; with the feature
//! on, the feature-gated ones run. Compiled only when rustdoc collects doctests, so no page of the
//! documentation shows them.

/// `Bst::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::searching::bst::Bst;
///
/// let leaf = |k| Bst::from_parts_unchecked(Bst::new(), k, Bst::new(), 1);
/// let backwards = Bst::from_parts_unchecked(leaf(3), 2, Bst::new(), 2);
/// assert_eq!(backwards.check_valid(), Err("invariant 1 (sorted)"));
/// let miscounted = Bst::from_parts_unchecked(leaf(1), 2, Bst::new(), 3);
/// assert_eq!(miscounted.check_valid(), Err("layout (sizes_add_up)"));
/// ```
pub struct BstFromParts;

/// A B-tree `Node::Internal` cannot be built outside the crate.
///
/// ```compile_fail,E0603
/// use algodesign::searching::btree::Node;
///
/// let too_few_children: Node<i32> = Node::Internal(vec![1], vec![]);
/// ```
pub struct BTreeInternalPrivate;

/// A B-tree `Node::Leaf` cannot be built outside the crate.
///
/// ```compile_fail,E0603
/// use algodesign::searching::btree::Node;
///
/// let leaf: Node<i32> = Node::Leaf(vec![2, 1]);
/// ```
pub struct BTreeLeafPrivate;

/// `Node::leaf_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::searching::btree::Node;
///
/// let leaf: Node<i32> = Node::leaf_unchecked(vec![2, 1]);
/// assert_eq!(leaf.check_valid(2), Err("invariant 1 (keys_in_order)"));
/// ```
pub struct BTreeUnchecked;

/// `Llrb::node` is private: a tree is built only by its own operations.
///
/// ```compile_fail,E0624
/// use algodesign::searching::llrb::{Color, Llrb};
///
/// let red_root = Llrb::node(Color::Red, Llrb::new(), 1, Llrb::new());
/// ```
pub struct LlrbNodePrivate;

/// `Llrb::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::searching::llrb::{Color, Llrb};
///
/// let red_root = Llrb::from_parts_unchecked(Color::Red, Llrb::new(), 1, Llrb::new());
/// assert!(!red_root.is_valid()); // a red root: the tree `insert` could never build
/// ```
pub struct LlrbFromParts;

/// `Lsm::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::searching::lsm::Lsm;
///
/// let two_on_level_1 = vec![vec![], vec![vec![(1, Some(1))], vec![(2, Some(2))]]];
/// let s: Lsm<i64, i64> = Lsm::from_parts_unchecked(two_on_level_1, 1, 2, 1);
/// assert_eq!(s.check_valid(), Err("invariant 2 (few_batches)"));
/// ```
pub struct LsmFromParts;
