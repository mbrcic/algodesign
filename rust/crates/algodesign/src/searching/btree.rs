// SPDX-License-Identifier: Apache-2.0
//! B-tree of minimum degree `t`: search, insert with CLRS §18.2's proactive split on the way
//! down, and delete by CLRS §18.3's borrow-and-merge (top a child up before descending into it;
//! an emptied root collapses).
//!
//! Lean counterpart: `AlgoDesign.Searching.BTree` (`search_correct`, `insertSpec`,
//! `deleteSpec`, and block-transfer costs for all three operations).
//!
//! **Against the Python, and how fast.** The same splits, borrows and merges. A node is searched by
//! binary search, where the Python scans its keys as CLRS does; a split node is given its full
//! capacity at once; and `len` is `O(1)`, a walk in the Python. The fan-out is what makes it fast.
//! `cargo bench -p algodesign --bench structures -- btree` times it at `t = 8` against
//! `std::collections::BTreeSet`.

use crate::searching::check_bounds;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Bound, RangeBounds};

/// A B-tree node: a leaf holds its keys; an internal node also holds one more child than it has
/// keys. Mirrors the Lean `inductive BTree`; the invariant, the Lean `Valid` that
/// [`Node::is_valid`] checks piece by piece, is a property of a value, not of the type. Keys and
/// children are `Vec`s, since the degree is a runtime argument.
///
/// Readable outside this crate, not constructible: both variants are `#[non_exhaustive]`.
///
/// ```
/// use algodesign::searching::btree::BTree;
///
/// let t: BTree<i32> = (0..100).collect();
/// let root = t.root();
/// assert_eq!(root.children().len(), root.keys().len() + 1);
/// ```
///
/// `leaf_unchecked` and `internal_unchecked`, which check nothing, exist only behind the
/// `unchecked` feature, for tests that build a broken tree on purpose: `cargo test --features
/// unchecked`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node<T> {
    /// A leaf: just its keys, no children.
    #[non_exhaustive]
    Leaf(Vec<T>),
    /// An internal node: its keys, and one more child than it has keys.
    #[non_exhaustive]
    Internal(Vec<T>, Vec<Node<T>>),
}

impl<T> Default for Node<T> {
    /// The empty tree: a leaf with no keys, legal at any degree, since `HalfFullToFull` puts no
    /// lower bound on the root.
    fn default() -> Self {
        Node::Leaf(Vec::new())
    }
}

impl<T> Node<T> {
    /// The Lean `leaf ks`, **checking no invariant**, for tests that must hand the
    /// predicates illegal trees. Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn leaf_unchecked(keys: Vec<T>) -> Self {
        Node::Leaf(keys)
    }

    /// The Lean `node ks cs`, **checking no invariant**, any number of children included.
    /// Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn internal_unchecked(keys: Vec<T>, children: Vec<Node<T>>) -> Self {
        Node::Internal(keys, children)
    }

    /// The empty tree. See [`Default::default`].
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// This node's own keys, in order, regardless of variant.
    #[must_use]
    pub fn keys(&self) -> &[T] {
        match self {
            Node::Leaf(keys) | Node::Internal(keys, _) => keys,
        }
    }

    /// This node's children, in order: empty for a leaf, one more than [`Node::keys`] otherwise.
    #[must_use]
    pub fn children(&self) -> &[Node<T>] {
        match self {
            Node::Leaf(_) => &[],
            Node::Internal(_, children) => children,
        }
    }

    /// Total number of keys in the subtree (walks it). Lean: `size`.
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Node::Leaf(keys) => keys.len(),
            Node::Internal(keys, children) => {
                keys.len() + children.iter().map(Node::len).sum::<usize>()
            }
        }
    }

    /// Is the tree empty? `O(1)`: an empty tree is exactly a root leaf with no keys.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.keys().is_empty() && matches!(self, Node::Leaf(_))
    }

    /// Height: `0` for a leaf, one more than the tallest child otherwise. Lean: `height`.
    #[must_use]
    pub fn height(&self) -> usize {
        match self {
            Node::Leaf(_) => 0,
            Node::Internal(_, children) => 1 + children.iter().map(Node::height).max().unwrap_or(0),
        }
    }

    /// The keys in sorted order (sorted whenever the tree is `Valid`).
    #[must_use]
    pub fn in_order(&self) -> Vec<&T> {
        self.iter().collect()
    }
}

impl<T: Ord> Node<T> {
    /// Is `key` one of the tree's keys? `O(t log_t n)` comparisons. Lean: `search`,
    /// `search_correct`.
    #[must_use]
    pub fn search<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        // Compare the stored key borrowed down to `Q`, so `Node<String>` accepts a `&str`.
        let find = |keys: &[T]| keys.binary_search_by(|probe| probe.borrow().cmp(key));
        match self {
            Node::Leaf(keys) => find(keys).is_ok(),
            Node::Internal(keys, children) => match find(keys) {
                Ok(_) => true,
                Err(idx) => children[idx].search(key),
            },
        }
    }

    /// Is `key` one of the tree's keys? The `std` spelling of [`Node::search`].
    #[must_use]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.search(key)
    }

    /// Inserts `key` at minimum degree `t`, splitting each full child before entering it (one
    /// pass). The duplicate check is the descent's own key scan, so a repeat insert can still
    /// split the full nodes above the key (CLRS assumes distinct keys). Panics if `t < 2`.
    fn insert_at(&mut self, t: usize, key: T) -> bool {
        assert!(t >= 2, "B-tree minimum degree t must be at least 2");
        if is_full(self, t) {
            // Preemptive root split, the one place the height grows.
            let mut keys = Vec::with_capacity(2 * t - 1);
            let mut children = Vec::with_capacity(2 * t);
            children.push(std::mem::take(self));
            split_child_in_place(&mut keys, &mut children, 0, t);
            *self = Node::Internal(keys, children);
        }
        insert_nonfull(self, t, key)
    }

    /// Deletes `key` at minimum degree `t`: never descend into a child with `t - 1` keys without
    /// first topping it up; a key found in an internal node is replaced by its predecessor or
    /// successor, or its two children are merged around it. Panics if `t < 2`.
    fn delete_at<Q>(&mut self, t: usize, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        assert!(t >= 2, "B-tree minimum degree t must be at least 2");
        let found = delete_rec(self, t, key);
        collapse_root(self);
        found
    }
}

/// Does `node` already have the maximum allowed `2t - 1` keys?
fn is_full<T>(node: &Node<T>, t: usize) -> bool {
    node.keys().len() == 2 * t - 1
}

/// Splits a full node (`2t - 1` keys) into its median and two halves of `t - 1` keys each.
fn split_full_child<T>(child: Node<T>, t: usize) -> (T, Node<T>, Node<T>) {
    match child {
        Node::Leaf(mut keys) => {
            debug_assert_eq!(keys.len(), 2 * t - 1, "split_full_child on a non-full leaf");
            let right_keys = split_off_full(&mut keys, t, 2 * t - 1);
            let median = keys.pop().expect("a full node has at least one key");
            (median, Node::Leaf(keys), Node::Leaf(right_keys))
        }
        Node::Internal(mut keys, mut children) => {
            debug_assert_eq!(keys.len(), 2 * t - 1, "split_full_child on a non-full node");
            let right_keys = split_off_full(&mut keys, t, 2 * t - 1);
            let median = keys.pop().expect("a full node has at least one key");
            let right_children = split_off_full(&mut children, t, 2 * t);
            (
                median,
                Node::Internal(keys, children),
                Node::Internal(right_keys, right_children),
            )
        }
    }
}

/// `v.split_off(at)`, but the new half is allocated at a node's full `capacity`, so a node born
/// from a split does not reallocate as it grows back towards full.
fn split_off_full<E>(v: &mut Vec<E>, at: usize, capacity: usize) -> Vec<E> {
    let mut right = Vec::with_capacity(capacity);
    right.extend(v.drain(at..));
    right
}

/// Splits the full child `children[idx]` in place, putting its median into `keys` at `idx`.
/// The left half takes the child's slot and the right half is inserted after it, so the
/// children's tail shifts once (an empty leaf holds the slot while the child is split).
fn split_child_in_place<T>(keys: &mut Vec<T>, children: &mut Vec<Node<T>>, idx: usize, t: usize) {
    let child = std::mem::take(&mut children[idx]);
    let (median, left, right) = split_full_child(child, t);
    keys.insert(idx, median);
    children[idx] = left;
    children.insert(idx + 1, right);
}

/// Inserts `key` into `node`, which the caller guarantees is not full, splitting full children
/// on the way down. Returns whether `key` was new.
fn insert_nonfull<T: Ord>(node: &mut Node<T>, t: usize, key: T) -> bool {
    match node {
        Node::Leaf(keys) => {
            // Already here: the leaf absorbs the repeat.
            match keys.binary_search(&key) {
                Ok(_) => false,
                Err(idx) => {
                    keys.insert(idx, key);
                    true
                }
            }
        }
        Node::Internal(keys, children) => {
            // Already here, at this level? Stop: nothing to insert and nothing to split.
            let Err(idx) = keys.binary_search(&key) else {
                return false;
            };
            let target = if is_full(&children[idx], t) {
                // The median to be promoted is the last key visible without another block
                // read; if it is the key, the key is present and nothing is split.
                if children[idx].keys()[t - 1] == key {
                    return false;
                }
                split_child_in_place(keys, children, idx, t);
                match key.cmp(&keys[idx]) {
                    Ordering::Less => idx,
                    Ordering::Greater => idx + 1,
                    Ordering::Equal => unreachable!("the promoted median was checked just above"),
                }
            } else {
                idx
            };
            insert_nonfull(&mut children[target], t, key)
        }
    }
}

/// Tops up `children[idx]` to at least `t` keys before the descent enters it (CLRS §18.3): borrow
/// from the left sibling, else from the right, else merge, with the left sibling if there is one.
/// Returns the child's index after a merge.
fn top_up<T>(keys: &mut Vec<T>, children: &mut Vec<Node<T>>, idx: usize, t: usize) -> usize {
    if children[idx].keys().len() >= t {
        return idx;
    }
    let has_left = idx > 0;
    let has_right = idx + 1 < children.len();
    if has_left && children[idx - 1].keys().len() >= t {
        borrow_from_left(keys, children, idx);
        idx
    } else if has_right && children[idx + 1].keys().len() >= t {
        borrow_from_right(keys, children, idx);
        idx
    } else if has_left {
        merge_at(keys, children, idx - 1);
        idx - 1
    } else {
        // Every node this is called on has at least two children, so a right sibling exists.
        debug_assert!(
            has_right,
            "a node needing this fix-up must have a right sibling here"
        );
        merge_at(keys, children, idx);
        idx
    }
}

/// Rotates the left sibling's last key up through `keys[idx - 1]` into `children[idx]`, with
/// its last child if internal.
fn borrow_from_left<T>(keys: &mut [T], children: &mut [Node<T>], idx: usize) {
    let (left_part, right_part) = children.split_at_mut(idx);
    let left = &mut *left_part.last_mut().expect("idx > 0");
    let target = &mut *right_part.first_mut().expect("idx < children.len()");
    match (left, target) {
        (Node::Leaf(lk), Node::Leaf(tk)) => {
            let borrowed = lk.pop().expect("left sibling has a spare key");
            let separator = std::mem::replace(&mut keys[idx - 1], borrowed);
            tk.insert(0, separator);
        }
        (Node::Internal(lk, lc), Node::Internal(tk, tc)) => {
            let borrowed_key = lk.pop().expect("left sibling has a spare key");
            let borrowed_child = lc.pop().expect("left sibling has a spare child");
            let separator = std::mem::replace(&mut keys[idx - 1], borrowed_key);
            tk.insert(0, separator);
            tc.insert(0, borrowed_child);
        }
        _ => unreachable!("siblings under a well-formed B-tree are at the same level"),
    }
}

/// Mirror of [`borrow_from_left`], from the right sibling through `keys[idx]`.
fn borrow_from_right<T>(keys: &mut [T], children: &mut [Node<T>], idx: usize) {
    let (left_part, right_part) = children.split_at_mut(idx + 1);
    let target = &mut *left_part.last_mut().expect("idx < children.len()");
    let right = &mut *right_part.first_mut().expect("idx + 1 < children.len()");
    match (target, right) {
        (Node::Leaf(tk), Node::Leaf(rk)) => {
            let borrowed = rk.remove(0);
            let separator = std::mem::replace(&mut keys[idx], borrowed);
            tk.push(separator);
        }
        (Node::Internal(tk, tc), Node::Internal(rk, rc)) => {
            let borrowed_key = rk.remove(0);
            let borrowed_child = rc.remove(0);
            let separator = std::mem::replace(&mut keys[idx], borrowed_key);
            tk.push(separator);
            tc.push(borrowed_child);
        }
        _ => unreachable!("siblings under a well-formed B-tree are at the same level"),
    }
}

/// Merges `children[i + 1]` into `children[i]`, pulling `keys[i]` down between them: at most
/// `(t - 1) + 1 + (t - 1) = 2t - 1` keys, so always legal.
fn merge_at<T>(keys: &mut Vec<T>, children: &mut Vec<Node<T>>, i: usize) {
    let separator = keys.remove(i);
    let right = children.remove(i + 1);
    match (&mut children[i], right) {
        (Node::Leaf(lk), Node::Leaf(mut rk)) => {
            lk.push(separator);
            lk.append(&mut rk);
        }
        (Node::Internal(lk, lc), Node::Internal(mut rk, mut rc)) => {
            lk.push(separator);
            lk.append(&mut rk);
            lc.append(&mut rc);
        }
        _ => unreachable!("siblings under a well-formed B-tree are at the same level"),
    }
}

/// Removes and returns the maximum key of `node`'s subtree (a predecessor), topping up each
/// child before descending into it. `node` must already have `≥ t` keys.
fn take_max<T>(node: &mut Node<T>, t: usize) -> T {
    match node {
        Node::Leaf(keys) => keys.pop().expect("take_max requires a non-empty subtree"),
        Node::Internal(keys, children) => {
            let last = children.len() - 1;
            top_up(keys, children, last, t);
            // A merge here can only be with the left sibling, which moves the last index.
            let last = children.len() - 1;
            take_max(&mut children[last], t)
        }
    }
}

/// Mirror of [`take_max`]: removes and returns the subtree's minimum (a successor).
fn take_min<T>(node: &mut Node<T>, t: usize) -> T {
    match node {
        Node::Leaf(keys) => keys.remove(0),
        Node::Internal(keys, children) => {
            // Child 0 can only merge rightwards and stays at index 0.
            top_up(keys, children, 0, t);
            take_min(&mut children[0], t)
        }
    }
}

/// The recursion behind [`BTree::delete`]. `node` is the root or has already been topped up to
/// `≥ t` keys. Returns whether `key` was found.
fn delete_rec<T, Q>(node: &mut Node<T>, t: usize, key: &Q) -> bool
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    match node {
        Node::Leaf(keys) => match keys.binary_search_by(|p| p.borrow().cmp(key)) {
            Ok(idx) => {
                keys.remove(idx);
                true
            }
            Err(_) => false,
        },
        Node::Internal(keys, children) => match keys.binary_search_by(|p| p.borrow().cmp(key)) {
            Ok(idx) => {
                if children[idx].keys().len() >= t {
                    // Predecessor: the max of the left child's subtree, which can spare a key.
                    keys[idx] = take_max(&mut children[idx], t);
                } else if children[idx + 1].keys().len() >= t {
                    // Successor: the min of the right child's subtree, which can spare a key.
                    keys[idx] = take_min(&mut children[idx + 1], t);
                } else {
                    // Neither child can spare a key: merge them around `key` and recurse.
                    merge_at(keys, children, idx);
                    let found = delete_rec(&mut children[idx], t, key);
                    debug_assert!(
                        found,
                        "key was just merged in as the separator, must be found"
                    );
                }
                true
            }
            Err(idx) => {
                let fixed_idx = top_up(keys, children, idx, t);
                delete_rec(&mut children[fixed_idx], t, key)
            }
        },
    }
}

/// Replaces an internal root with no keys by its only child: the one place the height shrinks.
fn collapse_root<T>(root: &mut Node<T>) {
    let Node::Internal(keys, children) = root else {
        return;
    };
    if !keys.is_empty() {
        return;
    }
    debug_assert_eq!(
        children.len(),
        1,
        "an empty-keyed node must have exactly one child"
    );
    let only = children.remove(0);
    *root = only;
}

// --- The invariant, one piece per box line, as the Lean states it ------------------------------

impl<T> Node<T> {
    /// The Lean `OneMoreChild`: every internal node has one more child than
    /// it has keys.
    #[must_use]
    pub fn is_one_more_child(&self) -> bool {
        match self {
            Node::Leaf(_) => true,
            Node::Internal(keys, children) => {
                children.len() == keys.len() + 1 && children.iter().all(Node::is_one_more_child)
            }
        }
    }

    /// The Lean `HalfFullToFull deg`, with `t` for `deg`: the root holds at
    /// most `2t - 1` keys, and every node below it is half full to full.
    #[must_use]
    pub fn is_half_full_to_full(&self, t: usize) -> bool {
        self.keys().len() <= t.saturating_mul(2).saturating_sub(1)
            && self.children().iter().all(|c| node_half_full(c, t))
    }

    /// The Lean `RootBranches`: the root is a leaf or has at least two
    /// children.
    #[must_use]
    pub fn is_root_branches(&self) -> bool {
        match self {
            Node::Leaf(_) => true,
            Node::Internal(_, children) => children.len() >= 2,
        }
    }

    /// The Lean `SameDepth`: every leaf sits at the same depth.
    #[must_use]
    pub fn is_same_depth(&self) -> bool {
        depth_of(self).is_some()
    }
}

impl<T: Ord> Node<T> {
    /// The Lean `KeysInOrder`: the keys in strictly increasing order,
    /// inside every node and across nodes. Reads the keys in the Lean `toList` order, which is
    /// defined however many children a node has. `O(n)`, no allocation.
    #[must_use]
    pub fn is_keys_in_order(&self) -> bool {
        keys_in_order_from(self, &mut None)
    }

    /// The Lean `Valid` of a tree of minimum degree `t` rooted here: the five box pieces in
    /// Lean order. A degree below 2 is no B-tree at all: [`BTree::new`] refuses it.
    #[must_use]
    pub fn is_valid(&self, t: usize) -> bool {
        self.check_valid(t).is_ok()
    }

    /// [`Node::is_valid`] with the first failed piece named, in the Lean `Valid`'s order.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (keys_in_order)"`, `"invariant 2 (one_more_child)"`,
    /// `"invariant 3 (half_full_to_full)"`, `"invariant 4 (root_branches)"`,
    /// or `"invariant 5 (same_depth)"`.
    pub fn check_valid(&self, t: usize) -> Result<(), &'static str> {
        if !self.is_keys_in_order() {
            return Err("invariant 1 (keys_in_order)");
        }
        if !self.is_one_more_child() {
            return Err("invariant 2 (one_more_child)");
        }
        if !self.is_half_full_to_full(t) {
            return Err("invariant 3 (half_full_to_full)");
        }
        if !self.is_root_branches() {
            return Err("invariant 4 (root_branches)");
        }
        if !self.is_same_depth() {
            return Err("invariant 5 (same_depth)");
        }
        Ok(())
    }
}

/// `true` if `key` comes strictly after the key read before it; `key` becomes the one before.
fn follows<'a, T: Ord>(prev: &mut Option<&'a T>, key: &'a T) -> bool {
    let ok = prev.is_none_or(|p| p < key);
    *prev = Some(key);
    ok
}

/// `KeysInOrder`'s walk: each key of `node`, in the Lean `toList` order, follows the one before.
/// Lean `childrenToList` interleaves child, key, child, key, ..., then whatever is left over.
fn keys_in_order_from<'a, T: Ord>(node: &'a Node<T>, prev: &mut Option<&'a T>) -> bool {
    match node {
        Node::Leaf(keys) => keys.iter().all(|k| follows(prev, k)),
        Node::Internal(keys, children) => {
            let mut keys = keys.iter();
            let mut children = children.iter();
            loop {
                match children.next() {
                    Some(c) if !keys_in_order_from(c, prev) => return false,
                    Some(_) => {}
                    None => return keys.all(|k| follows(prev, k)),
                }
                match keys.next() {
                    Some(k) if !follows(prev, k) => return false,
                    Some(_) => {}
                    None => return children.all(|c| keys_in_order_from(c, prev)),
                }
            }
        }
    }
}

/// Lean `NodeHalfFull deg`: a node below the root holds between `t - 1` and `2t - 1` keys, and so
/// does every node beneath it. The subtractions are the Lean's natural-number ones and the
/// doubling saturates, so `t = 0` and a `t` past `usize::MAX / 2` answer rather than panic.
fn node_half_full<T>(node: &Node<T>, t: usize) -> bool {
    let n = node.keys().len();
    t.saturating_sub(1) <= n
        && n <= t.saturating_mul(2).saturating_sub(1)
        && node.children().iter().all(|c| node_half_full(c, t))
}

/// Lean `depth?`: `Some` depth iff every leaf agrees; `None` for a node with no children.
fn depth_of<T>(node: &Node<T>) -> Option<usize> {
    match node {
        Node::Leaf(_) => Some(0),
        Node::Internal(_, children) => {
            let mut agreed: Option<usize> = None;
            for c in children {
                let d = depth_of(c)?;
                match agreed {
                    None => agreed = Some(d),
                    Some(prev) if prev == d => {}
                    Some(_) => return None,
                }
            }
            agreed.map(|d| d + 1)
        }
    }
}

/// The minimum degree [`BTree::default`] and `FromIterator` use: `std`'s `BTreeMap` fanout.
pub const DEFAULT_DEGREE: usize = 6;

/// A B-tree of minimum degree `t`: every non-root node holds between `t - 1` and `2t - 1` keys.
///
/// `==` compares shape, not only contents: the same keys inserted in a different order can
/// compare unequal. To compare contents, compare `iter()`.
#[derive(Debug, PartialEq, Eq)]
pub struct BTree<T> {
    degree: usize,
    root: Node<T>,
    /// Maintained by `insert`/`delete`, so `len()` is `O(1)`.
    len: usize,
}

impl<T> Default for BTree<T> {
    fn default() -> Self {
        BTree::new(DEFAULT_DEGREE)
    }
}

/// Written by hand to keep every node's full capacity, as a derived clone would not.
impl<T: Clone> Clone for BTree<T> {
    fn clone(&self) -> Self {
        fn clone_node<T: Clone>(node: &Node<T>, t: usize) -> Node<T> {
            let mut keys = Vec::with_capacity(2 * t - 1);
            keys.extend_from_slice(node.keys());
            match node {
                Node::Leaf(_) => Node::Leaf(keys),
                Node::Internal(_, children) => {
                    let mut out = Vec::with_capacity(2 * t);
                    out.extend(children.iter().map(|c| clone_node(c, t)));
                    Node::Internal(keys, out)
                }
            }
        }
        BTree {
            degree: self.degree,
            root: clone_node(&self.root, self.degree),
            len: self.len,
        }
    }
}

impl<T> BTree<T> {
    /// An empty tree of minimum degree `t`.
    ///
    /// # Panics
    /// If `t < 2`, as the Lean's `BTree` requires `2 ≤ deg`, or `t > usize::MAX / 2`, where a
    /// node's `2t` children could not be counted.
    #[must_use]
    pub fn new(t: usize) -> Self {
        assert!(t >= 2, "B-tree minimum degree t must be at least 2");
        assert!(
            t <= usize::MAX / 2,
            "B-tree minimum degree t must be at most usize::MAX / 2, so that 2t fits"
        );
        BTree {
            degree: t,
            root: Node::default(),
            len: 0,
        }
    }

    /// The minimum degree this tree was built with.
    #[must_use]
    pub fn degree(&self) -> usize {
        self.degree
    }

    /// The root node, for callers that walk the structure.
    #[must_use]
    pub fn root(&self) -> &Node<T> {
        &self.root
    }

    /// Total number of keys. `O(1)`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is the tree empty? `O(1)`.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Height: `0` for a tree that is a single leaf.
    #[must_use]
    pub fn height(&self) -> usize {
        self.root.height()
    }

    /// The keys in ascending order.
    #[must_use]
    pub fn in_order(&self) -> Vec<&T> {
        self.root.in_order()
    }

    /// The keys in ascending order, lazily.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: vec![(&self.root, 0)],
            remaining: self.len,
        }
    }
}

impl<T: Ord> BTree<T> {
    /// Is `key` present? `O(t log_t n)` comparisons. Lean: `search`, `search_correct`.
    #[must_use]
    pub fn search<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.root.search(key)
    }

    /// Is `key` present? The `std` spelling of [`BTree::search`].
    #[must_use]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.root.search(key)
    }

    /// Insert `key`, reporting whether it was new. CLRS §18.2's proactive split. Lean:
    /// `insertSpec`; at most `Nat.log deg ((n+1)/2) + 2` block transfers
    /// (`time_insertM_le_log`).
    pub fn insert(&mut self, key: T) -> bool {
        let added = self.root.insert_at(self.degree, key);
        self.len += usize::from(added);
        added
    }

    /// Remove `key`, reporting whether it was there. CLRS §18.3's borrow-and-merge. Lean:
    /// `deleteSpec`; at most `Nat.log deg ((n+1)/2) + 2` block transfers
    /// (`time_deleteM_le_log`).
    pub fn delete<Q>(&mut self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let removed = self.root.delete_at(self.degree, key);
        self.len -= usize::from(removed);
        removed
    }

    /// The Lean `Valid` at this tree's degree: [`Node::is_valid`] on the
    /// root.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.root.is_valid(self.degree)
    }

    /// [`BTree::is_valid`] with the first failed piece named: [`Node::check_valid`] on the root.
    ///
    /// # Errors
    ///
    /// The first failed piece's name, e.g. `"invariant 3 (half_full_to_full)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        self.root.check_valid(self.degree)
    }
}

/// A sub-range of the keys, in order, lazily — what [`BTree::range`] and [`Node::range`] return.
///
/// Two cursors in [`Iter`]'s `(node, position)` encoding, seeded by descents to the two bounds;
/// the range ends when the front key passes the back key.
pub struct Range<'a, T> {
    front: Vec<(&'a Node<T>, usize)>,
    back: Vec<(&'a Node<T>, usize)>,
    /// An upper bound for `size_hint` only: known for [`BTree::range`], `None` for
    /// [`Node::range`].
    upper: Option<usize>,
}

impl<T> Range<'_, T> {
    /// Move the forward cursor to a key position, or empty the stack.
    fn settle_front(&mut self) {
        while let Some(&(node, i)) = self.front.last() {
            if i > 2 * node.keys().len() {
                self.front.pop();
                continue;
            }
            if i % 2 == 1 {
                return;
            }
            self.front.last_mut().expect("just read it").1 += 1;
            if let Node::Internal(_, children) = node {
                self.front.push((&children[i / 2], 0));
            }
        }
    }

    /// The mirror of `settle_front`; at position 0 the node leaves the stack before its child.
    fn settle_back(&mut self) {
        while let Some(&(node, i)) = self.back.last() {
            if i % 2 == 1 {
                return;
            }
            let child = match node {
                Node::Internal(_, children) => Some(&children[i / 2]),
                Node::Leaf(_) => None,
            };
            if i == 0 {
                self.back.pop();
            } else {
                self.back.last_mut().expect("just read it").1 -= 1;
            }
            if let Some(c) = child {
                self.back.push((c, 2 * c.keys().len()));
            }
        }
    }
}

impl<T: Ord> Range<'_, T> {
    /// Have the two ends met? Both cursors must be settled first.
    fn met(&self) -> bool {
        match (self.front.last(), self.back.last()) {
            (Some(&(fnode, i)), Some(&(bnode, j))) => fnode.keys()[i / 2] > bnode.keys()[j / 2],
            _ => true,
        }
    }

    /// Drop both cursors, so every later call is an `O(1)` `None`.
    fn finish(&mut self) {
        self.front.clear();
        self.back.clear();
    }
}

impl<'a, T: Ord> Iterator for Range<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.settle_front();
        self.settle_back();
        if self.met() {
            self.finish();
            return None;
        }
        let (node, i) = *self.front.last().expect("met() excludes an empty front");
        self.front.last_mut().expect("just read it").1 += 1;
        self.upper = self.upper.map(|u| u.saturating_sub(1));
        Some(&node.keys()[i / 2])
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.upper)
    }
}

impl<'a, T: Ord> DoubleEndedIterator for Range<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.settle_front();
        self.settle_back();
        if self.met() {
            self.finish();
            return None;
        }
        let (node, i) = *self.back.last().expect("met() excludes an empty back");
        self.back.last_mut().expect("just read it").1 -= 1;
        self.upper = self.upper.map(|u| u.saturating_sub(1));
        Some(&node.keys()[i / 2])
    }
}

// Hand-written: the derive would demand `T: Clone`, and this holds references.
impl<T> Clone for Range<'_, T> {
    fn clone(&self) -> Self {
        Range {
            front: self.front.clone(),
            back: self.back.clone(),
            upper: self.upper,
        }
    }
}

/// The keys not yet yielded, as `std`'s set iterators show themselves.
impl<T: Ord + fmt::Debug> fmt::Debug for Range<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<T: Ord> std::iter::FusedIterator for Range<'_, T> {}

impl<T: Ord> Node<T> {
    /// Seed the two cursors for `range`: the descent [`Node::search`] makes, with the bound in
    /// place of the key and the whole path recorded.
    fn seed_range<'a, Q>(
        &'a self,
        start: Bound<&Q>,
        end: Bound<&Q>,
        upper: Option<usize>,
    ) -> Range<'a, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut it = Range {
            front: Vec::new(),
            back: Vec::new(),
            upper,
        };

        // Forward: `j` is the first key at or above the lower bound.
        let mut node = self;
        loop {
            let keys = node.keys();
            let j = keys.partition_point(|k| match start {
                Bound::Unbounded => false,
                Bound::Included(s) => k.borrow() < s,
                Bound::Excluded(s) => k.borrow() <= s,
            });
            // Child `j` is entered here, not by `settle_front`: only this descent knows the bound.
            it.front.push((node, 2 * j + 1));
            match node {
                Node::Internal(_, children) => node = &children[j],
                Node::Leaf(_) => break,
            }
        }

        // Backward: key `j - 1` is the last one under the upper bound; a node with `j == 0`
        // owes nothing and stays off the stack.
        let mut node = self;
        loop {
            let keys = node.keys();
            let j = keys.partition_point(|k| match end {
                Bound::Unbounded => true,
                Bound::Included(e) => k.borrow() <= e,
                Bound::Excluded(e) => k.borrow() < e,
            });
            if j > 0 {
                it.back.push((node, 2 * j - 1));
            }
            match node {
                Node::Internal(_, children) => node = &children[j],
                Node::Leaf(_) => break,
            }
        }

        it
    }

    /// The keys of this subtree in a sub-range, in order, lazily.
    ///
    /// Reports no `size_hint` upper bound: a node does not know its own count.
    ///
    /// # Panics
    ///
    /// If the start bound is above the end bound, or if both bounds exclude the same key.
    #[must_use]
    pub fn range<Q, R>(&self, range: R) -> Range<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = check_bounds(&range, "Node::range");
        self.seed_range(start, end, None)
    }
}

impl<T: Ord> BTree<T> {
    /// The keys in a sub-range, in order, lazily.
    ///
    /// ```
    /// # use algodesign::searching::btree::BTree;
    /// let mut t = BTree::new(3);
    /// for k in (1..=9).map(|k| k * 10) {
    ///     t.insert(k);
    /// }
    /// assert_eq!(t.range(35..=60).copied().collect::<Vec<_>>(), vec![40, 50, 60]);
    /// assert_eq!(t.range(..=35).next_back(), Some(&30)); // floor(35)
    /// assert_eq!(t.range(35..).next(), Some(&40)); // ceiling(35)
    /// ```
    ///
    /// Cost: two descents, `O(log_t n)` node visits, then `O(1)` amortised per key.
    ///
    /// # Panics
    ///
    /// If the start bound is above the end bound, or if both bounds exclude the same key.
    #[must_use]
    pub fn range<Q, R>(&self, range: R) -> Range<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = check_bounds(&range, "BTree::range");
        self.root.seed_range(start, end, Some(self.len))
    }
}

impl<'a, T> IntoIterator for &'a BTree<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T: Ord> Extend<T> for BTree<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

/// Collected at [`DEFAULT_DEGREE`]. Use [`BTree::new`] and [`Extend`] to choose the degree.
impl<T: Ord> FromIterator<T> for BTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut t = BTree::default();
        t.extend(iter);
        t
    }
}

/// In-order iteration without building a `Vec` first.
///
/// A node's `k` keys and `k + 1` children alternate; the cursor per stacked node runs `0..=2k`,
/// even positions descending into child `i / 2`, odd positions yielding key `i / 2`.
pub struct Iter<'a, T> {
    stack: Vec<(&'a Node<T>, usize)>,
    /// Keys still owed, exact: [`BTree::iter`] reads the container's count, [`Node::iter`] walks
    /// for it.
    remaining: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (node, i) = *self.stack.last()?;
            match node {
                Node::Leaf(keys) => {
                    if i < keys.len() {
                        self.stack.last_mut().expect("just read it").1 += 1;
                        self.remaining -= 1;
                        return Some(&keys[i]);
                    }
                    self.stack.pop();
                }
                Node::Internal(keys, children) => {
                    if i > 2 * keys.len() {
                        self.stack.pop();
                        continue;
                    }
                    self.stack.last_mut().expect("just read it").1 += 1;
                    if i % 2 == 0 {
                        self.stack.push((&children[i / 2], 0));
                    } else {
                        self.remaining -= 1;
                        return Some(&keys[i / 2]);
                    }
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

// Hand-written: the derive would demand `T: Clone`, and this holds references.
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            stack: self.stack.clone(),
            remaining: self.remaining,
        }
    }
}

/// The keys not yet yielded, as `std`'s set iterators show themselves.
impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}
impl<T> std::iter::FusedIterator for Iter<'_, T> {}

impl<T> Node<T> {
    /// The keys in order, lazily.
    ///
    /// Walks the subtree once up front to report an exact length; [`BTree::iter`] does not.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: vec![(self, 0)],
            remaining: self.len(),
        }
    }
}

impl<'a, T> IntoIterator for &'a Node<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

#[cfg(test)]
#[path = "unit_tests/btree.rs"]
mod tests;
