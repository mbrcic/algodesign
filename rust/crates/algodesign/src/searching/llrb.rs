// SPDX-License-Identifier: Apache-2.0
//! Left-leaning red-black tree (Sedgewick, *Algorithms* 4e §3.3): insert by `rotate_left`,
//! `rotate_right`, `flip_colors` and `fix_up`; delete by `move_red_left`/`move_red_right`.
//!
//! A set, not a map. Each node carries the color of the link into it and Sedgewick's subtree
//! count `N`, so `len` is `O(1)`.
//!
//! Lean counterpart: `lean/AlgoDesign/Searching/LLRB/`, whose `LLRB.Valid` is the five conditions
//! `Sorted ∧ RootBlack ∧ LeftLeaning ∧ NoRedRed ∧ BlackHeightOk` that [`Llrb::is_valid`] checks.
//!
//! [`Llrb::insert_with_rotations`] and [`Llrb::delete_with_rotations`] return the rotations an
//! update made, the counts the chapter reports. They run the same insert and delete, made generic
//! over what receives the count; [`Llrb::insert`] and [`Llrb::delete`] give it nothing to
//! receive, so they pay nothing for it.
//!
//! **Against the Python, and how fast.** The same insert and delete, with three differences: each
//! node keeps Sedgewick's count `N`, so `len` is `O(1)` where the Python walks the tree;
//! `rotate_left`, `rotate_right` and `flip_colors` are total, a no-op on an empty child as in the
//! Lean, where the Python's raise; and `delete` handles, as the Lean's `match r2.min?` does, a key
//! found with an empty right side, which the Python leaves to the invariants. Rotations reuse their
//! boxes, so an insert allocates one node and a delete nothing.
//! `cargo bench -p algodesign --bench structures -- llrb` times it against
//! `std::collections::BTreeSet`.

use crate::searching::{check_bounds, height_bound, Count};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Bound, RangeBounds};

/// The color of the link *into* a node (Sedgewick's convention), stored on the node.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    /// A red link: the node hangs from its parent at the same black depth.
    Red,
    /// A black link: the node is one black level below its parent.
    Black,
}

impl Color {
    /// The other color; the Lean `Color.flip`.
    fn flip(self) -> Color {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red,
        }
    }
}

/// A left-leaning red-black tree of keys (a set, no values); the Lean `inductive Llrb`.
///
/// `==` compares shape, not only contents. To compare contents, compare `iter()`.
///
/// ```
/// use algodesign::searching::llrb::{Color, Llrb};
///
/// let a: Llrb<i32> = [1, 2, 3].into_iter().collect(); // 2 at the root
/// let b: Llrb<i32> = [3, 2, 1].into_iter().collect(); // 2 at the root as well
/// let c: Llrb<i32> = [1, 2, 3, 4, 0].into_iter().collect();
/// let mut d: Llrb<i32> = [0, 1, 2, 3, 4, 5].into_iter().collect();
/// d.delete(&5);
/// assert_eq!(a, b);
/// assert!(c.iter().eq(d.iter())); // the same keys...
/// assert_ne!(c, d); // ...in different shapes
/// assert_eq!(a.as_node().map(|n| n.color), Some(Color::Black)); // the root is black
/// ```
///
/// Built only by its own operations; the node constructor is private:
///
/// `from_parts_unchecked`, which checks nothing, exists only behind the `unchecked` feature, for
/// tests that build a broken tree on purpose: `cargo test --features unchecked`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Llrb<T>(Option<Box<Node<T>>>);

// Hand-written: the derive would add a `T: Default` bound.
impl<T> Default for Llrb<T> {
    fn default() -> Self {
        Llrb(None)
    }
}

/// What a non-empty `Llrb` holds; the arguments of the Lean `node` constructor, plus a count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T> {
    /// The color of the link *into* this node.
    pub color: Color,
    /// Everything ordered before `key`.
    pub left: Llrb<T>,
    /// The key this node holds.
    pub key: T,
    /// Everything ordered after `key`.
    pub right: Llrb<T>,
    /// How many keys hang below this node, counting its own — Sedgewick's `N`.
    pub size: usize,
}

impl<T> Llrb<T> {
    /// The Lean `node c l k r`, with the allocation this representation needs.
    fn node(color: Color, left: Llrb<T>, key: T, right: Llrb<T>) -> Self {
        let size = left.len() + right.len() + 1;
        Llrb(Some(Box::new(Node {
            color,
            left,
            key,
            right,
            size,
        })))
    }

    /// Recompute this node's count from its children's; run after anything moves a subtree.
    fn fix_size(&mut self) {
        if let Some(n) = self.0.as_mut() {
            n.size = n.left.len() + n.right.len() + 1;
        }
    }

    /// The Lean `node c l k r`, **checking no invariant**, for tests that must hand the
    /// predicates illegal trees. Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts_unchecked(color: Color, left: Llrb<T>, key: T, right: Llrb<T>) -> Self {
        Self::node(color, left, key, right)
    }

    /// The node behind a non-empty tree, or `None` for the Lean `leaf`.
    #[must_use]
    pub fn as_node(&self) -> Option<&Node<T>> {
        self.0.as_deref()
    }

    /// The node behind a non-empty tree, mutably.
    fn as_node_mut(&mut self) -> Option<&mut Node<T>> {
        self.0.as_deref_mut()
    }
}

/// Structural helpers and the color repairs, which need no `T: Ord`.
impl<T> Llrb<T> {
    /// The empty tree.
    #[must_use]
    pub fn new() -> Self {
        Llrb(None)
    }

    /// Is this the empty tree? The Lean name; [`Llrb::is_empty`] is the `std` one.
    #[must_use]
    pub fn is_leaf(&self) -> bool {
        self.0.is_none()
    }

    /// How many keys the tree holds. `O(1)`: the root's [`Node::size`].
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.size)
    }

    /// Is the tree empty? The `std` spelling of `is_leaf`.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.is_leaf()
    }

    /// Is the link into this node red? The Lean `isRed`.
    fn is_red(&self) -> bool {
        self.as_node().is_some_and(|n| n.color == Color::Red)
    }

    /// The left subtree, or `None` for a leaf.
    fn left(&self) -> Option<&Self> {
        self.as_node().map(|n| &n.left)
    }

    /// The right subtree, or `None` for a leaf.
    fn right(&self) -> Option<&Self> {
        self.as_node().map(|n| &n.right)
    }

    /// Force the root's link color; a no-op on a leaf.
    fn set_color(&mut self, c: Color) {
        if let Some(n) = self.as_node_mut() {
            n.color = c;
        }
    }

    /// Sedgewick's `rotateLeft`: the right child comes up, this node becomes its red left child.
    /// A no-op if the right child is a leaf, as in the Lean.
    fn rotate_left<C: Count>(&mut self, rotations: &mut C) {
        if self.as_node().is_none_or(|n| n.right.is_leaf()) {
            return;
        }
        rotations.add_one();
        // Both boxes are reused: nothing is allocated.
        let mut here = self.0.take().expect("checked Some just above");
        let mut up = here.right.0.take().expect("checked non-leaf just above");
        here.right = std::mem::take(&mut up.left);
        up.color = here.color;
        here.color = Color::Red;
        up.left = Llrb(Some(here));
        *self = Llrb(Some(up));
        // The demoted node first: the new root reads its count.
        if let Some(n) = self.0.as_mut() {
            n.left.fix_size();
        }
        self.fix_size();
    }

    /// Sedgewick's `rotateRight`, symmetric to `rotate_left`.
    fn rotate_right<C: Count>(&mut self, rotations: &mut C) {
        if self.as_node().is_none_or(|n| n.left.is_leaf()) {
            return;
        }
        rotations.add_one();
        let mut here = self.0.take().expect("checked Some just above");
        let mut up = here.left.0.take().expect("checked non-leaf just above");
        here.left = std::mem::take(&mut up.right);
        up.color = here.color;
        here.color = Color::Red;
        up.right = Llrb(Some(here));
        *self = Llrb(Some(up));
        if let Some(n) = self.0.as_mut() {
            n.right.fix_size();
        }
        self.fix_size();
    }

    /// Sedgewick's `flipColors`: flip this node's color and both children's, splitting a
    /// temporary 4-node. A no-op unless both children are nodes, as in the Lean.
    fn flip_colors(&mut self) {
        let Some(n) = self.as_node_mut() else {
            return;
        };
        if n.left.is_leaf() || n.right.is_leaf() {
            return;
        }
        n.color = n.color.flip();
        if let Some(l) = n.left.as_node_mut() {
            l.color = l.color.flip();
        }
        if let Some(r) = n.right.as_node_mut() {
            r.color = r.color.flip();
        }
    }

    /// Sedgewick's fix-up, run on the way back up from every update; the Lean `fixUp`.
    fn fix_up<C: Count>(&mut self, rotations: &mut C) {
        if self.right().is_some_and(Llrb::is_red) && !self.left().is_some_and(Llrb::is_red) {
            self.rotate_left(rotations);
        }
        if self.left().is_some_and(Llrb::is_red)
            && self.left().and_then(Llrb::left).is_some_and(Llrb::is_red)
        {
            self.rotate_right(rotations);
        }
        if self.left().is_some_and(Llrb::is_red) && self.right().is_some_and(Llrb::is_red) {
            self.flip_colors();
        }
        // The one place that sees every node whose subtree changed size.
        self.fix_size();
    }

    /// Sedgewick's `moveRedLeft` (exercise 3.3.39): before descending into a bare 2-node left
    /// child, borrow from the right sibling. Unchecked precondition: `self` is red-linked.
    fn move_red_left<C: Count>(&mut self, rotations: &mut C) {
        self.flip_colors();
        if !self.right().and_then(Llrb::left).is_some_and(Llrb::is_red) {
            return;
        }
        if let Some(n) = self.as_node_mut() {
            n.right.rotate_right(rotations);
        }
        self.rotate_left(rotations);
        self.flip_colors();
    }

    /// Sedgewick's `moveRedRight`, symmetric to `move_red_left`.
    fn move_red_right<C: Count>(&mut self, rotations: &mut C) {
        self.flip_colors();
        if self.left().and_then(Llrb::left).is_some_and(Llrb::is_red) {
            self.rotate_right(rotations);
            self.flip_colors();
        }
    }

    /// The Lean `blackHeight`: `Some n` if every root-to-leaf path has `n`
    /// black links (a leaf counts as one), `None` otherwise.
    #[must_use]
    pub fn black_height(&self) -> Option<usize> {
        let Some(n) = self.as_node() else {
            return Some(1);
        };
        let bl = n.left.black_height()?;
        let br = n.right.black_height()?;
        if bl == br {
            Some(bl + usize::from(n.color == Color::Black))
        } else {
            None
        }
    }

    /// The Lean `LeftLeaning`: no right link is red.
    #[must_use]
    pub fn is_left_leaning(&self) -> bool {
        self.as_node().is_none_or(|n| {
            !n.right.is_red() && n.left.is_left_leaning() && n.right.is_left_leaning()
        })
    }

    /// The Lean `NoRedRed`: no two red links touch.
    #[must_use]
    pub fn is_no_red_red(&self) -> bool {
        self.as_node().is_none_or(|n| {
            let ok_here = n.color != Color::Red || (!n.left.is_red() && !n.right.is_red());
            ok_here && n.left.is_no_red_red() && n.right.is_no_red_red()
        })
    }

    /// The Lean `RootBlack`.
    #[must_use]
    pub fn is_root_black(&self) -> bool {
        !self.is_red()
    }

    /// The Lean `BlackHeightOk`: every path from the root down to a leaf
    /// crosses the same number of black links, so [`Llrb::black_height`] is `Some`.
    #[must_use]
    pub fn is_black_height_ok(&self) -> bool {
        self.black_height().is_some()
    }
}

impl<T: Ord> Llrb<T> {
    /// The Lean `Sorted`, by carrying bounds down: `O(n)`, no allocation.
    #[must_use]
    pub fn is_sorted(&self) -> bool {
        fn within<T: Ord>(t: &Llrb<T>, lo: Option<&T>, hi: Option<&T>) -> bool {
            t.as_node().is_none_or(|n| {
                lo.is_none_or(|l| l < &n.key)
                    && hi.is_none_or(|h| &n.key < h)
                    && within(&n.left, lo, Some(&n.key))
                    && within(&n.right, Some(&n.key), hi)
            })
        }
        within(self, None, None)
    }

    /// The Lean `Valid`: ordering plus the four color invariants.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Llrb::is_valid`] with the first failed piece named, in the Lean `Valid`'s order.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (sorted)"`, `"invariant 2 (root_black)"`, `"invariant 3 (left_leaning)"`,
    /// `"invariant 4 (no_red_red)"` or `"invariant 5 (black_height_ok)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_sorted() {
            return Err("invariant 1 (sorted)");
        }
        if !self.is_root_black() {
            return Err("invariant 2 (root_black)");
        }
        if !self.is_left_leaning() {
            return Err("invariant 3 (left_leaning)");
        }
        if !self.is_no_red_red() {
            return Err("invariant 4 (no_red_red)");
        }
        if !self.is_black_height_ok() {
            return Err("invariant 5 (black_height_ok)");
        }
        Ok(())
    }

    /// The stored key equal to `a`, if any. `O(log n)`.
    #[must_use]
    pub fn get<Q>(&self, a: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        while let Some(n) = cur.as_node() {
            match a.cmp(n.key.borrow()) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
                Ordering::Equal => return Some(&n.key),
            }
        }
        None
    }

    /// Is `a` a key? The Lean `search`.
    #[must_use]
    pub fn search<Q>(&self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.contains(a)
    }

    /// Is `a` a key? The `std` spelling of [`Llrb::search`].
    #[must_use]
    pub fn contains<Q>(&self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(a).is_some()
    }

    /// The smallest key, if any; the Lean `min?`.
    #[must_use]
    pub fn min(&self) -> Option<&T> {
        let n = self.as_node()?;
        n.left.min().or(Some(&n.key))
    }

    /// Insert below the root, `fix_up` on the way back; a duplicate is a no-op. The Lean
    /// `insertAux`.
    fn insert_aux<C: Count>(&mut self, a: T, rotations: &mut C) -> bool {
        let Some(n) = self.as_node_mut() else {
            *self = Llrb::node(Color::Red, Llrb(None), a, Llrb(None));
            return true;
        };
        let added = match a.cmp(&n.key) {
            Ordering::Less => n.left.insert_aux(a, rotations),
            Ordering::Greater => n.right.insert_aux(a, rotations),
            Ordering::Equal => false,
        };
        self.fix_up(rotations);
        added
    }

    /// Insert `a`; `false` if it was already present. `O(log n)`. Lean: `valid_insert`,
    /// `mem_insert`.
    pub fn insert(&mut self, a: T) -> bool {
        self.insert_counting(a, &mut ())
    }

    /// [`Llrb::insert`], and how many rotations it made. The chapter's figure, on trees of 4 096
    /// random keys: up to 11 for one insert.
    ///
    /// ```
    /// use algodesign::searching::Llrb;
    ///
    /// let mut t: Llrb<i32> = [3, 2].into_iter().collect();
    /// assert_eq!(t.insert_with_rotations(1), (true, 1)); // two reds in a row: one right rotation
    /// assert_eq!(t.insert_with_rotations(1), (false, 0));
    /// ```
    pub fn insert_with_rotations(&mut self, a: T) -> (bool, usize) {
        let mut rotations = 0;
        let added = self.insert_counting(a, &mut rotations);
        (added, rotations)
    }

    fn insert_counting<C: Count>(&mut self, a: T, rotations: &mut C) -> bool {
        let added = self.insert_aux(a, rotations);
        self.set_color(Color::Black);
        added
    }

    /// The Lean `deleteMin`, returning the removed key. Preconditions: `self` is not a bare
    /// 2-node and not empty.
    fn delete_min_pair<C: Count>(&mut self, rotations: &mut C) -> T {
        let n = self
            .as_node()
            .expect("delete_min_pair is only called on a non-empty tree");
        if n.left.is_leaf() {
            let here = self.0.take().expect("checked Some just above");
            let Node { key, right, .. } = *here;
            *self = right;
            return key;
        }
        let borrow = !n.left.is_red() && !n.left.left().is_some_and(Llrb::is_red);
        if borrow {
            self.move_red_left(rotations);
        }
        let n = self
            .as_node_mut()
            .expect("move_red_left keeps a non-empty tree non-empty");
        let m = n.left.delete_min_pair(rotations);
        self.fix_up(rotations);
        m
    }

    /// Remove and return the smallest key. `O(log n)`. Sedgewick's `deleteMin` with its
    /// root-reddening wrapper; the Lean `deleteMinTop` (`valid_deleteMinTop`).
    pub fn delete_min(&mut self) -> Option<T> {
        if self.is_leaf() {
            return None;
        }
        let root_is_2node =
            !self.left().is_some_and(Llrb::is_red) && !self.right().is_some_and(Llrb::is_red);
        if root_is_2node {
            self.set_color(Color::Red);
        }
        // The Lean's `blacken`, unconditionally.
        let removed = self.delete_min_pair(&mut ());
        self.set_color(Color::Black);
        Some(removed)
    }

    /// The Lean `delete`. After the borrowing rotations, `a` is compared with the *current* top
    /// key, which they may have changed. Same precondition as `delete_min_pair`.
    fn delete_inner<Q, C>(&mut self, a: &Q, rotations: &mut C)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        C: Count,
    {
        let Some(n) = self.as_node() else { return };
        if a < n.key.borrow() {
            let borrow = !n.left.is_red() && !n.left.left().is_some_and(Llrb::is_red);
            if borrow {
                self.move_red_left(rotations);
            }
            let Some(n) = self.as_node_mut() else { return };
            n.left.delete_inner(a, rotations);
            self.fix_up(rotations);
            return;
        }
        // `a >= key`: lean a red left link right first.
        if n.left.is_red() {
            self.rotate_right(rotations);
        }
        let Some(n) = self.as_node() else { return };
        if n.right.is_leaf() {
            // If the key here is not `a`, `a` is absent: returning `left` would delete a key.
            let hit = a == n.key.borrow();
            if hit {
                let here = self.0.take().expect("checked Some just above");
                *self = here.left;
            } else {
                self.fix_up(rotations);
            }
            return;
        }
        // `!isRed(h.right) && !isRed(h.right.left)`, as Sedgewick guards.
        let need_borrow = !n.right.is_red() && !n.right.left().is_some_and(Llrb::is_red);
        if need_borrow {
            self.move_red_right(rotations);
        }
        let Some(n) = self.as_node_mut() else { return };
        // The Lean's `match r2.min?`, asked of the shape: `delete_min_pair` needs a non-empty tree.
        let collapse = if a == n.key.borrow() {
            if n.right.is_leaf() {
                true
            } else {
                n.key = n.right.delete_min_pair(rotations);
                false
            }
        } else {
            n.right.delete_inner(a, rotations);
            false
        };
        if collapse {
            let here = self.0.take().expect("checked Some just above");
            *self = here.left;
            return;
        }
        self.fix_up(rotations);
    }

    /// Remove `a`; `false` if it was absent. `O(log n)`. Sedgewick's `delete` with its
    /// root-reddening wrapper and `contains` guard; the Lean `deleteTop` (`valid_deleteTop`,
    /// `mem_deleteTop_iff`).
    pub fn delete<Q>(&mut self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.delete_counting(a, &mut ())
    }

    /// [`Llrb::delete`], and how many rotations it made, the borrowing ones on the way down
    /// included. The chapter's figures, on trees of 4 096 random keys: up to 15 for one delete,
    /// about 5 on average.
    pub fn delete_with_rotations<Q>(&mut self, a: &Q) -> (bool, usize)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut rotations = 0;
        let removed = self.delete_counting(a, &mut rotations);
        (removed, rotations)
    }

    fn delete_counting<Q, C>(&mut self, a: &Q, rotations: &mut C) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        C: Count,
    {
        if !self.contains(a) {
            return false;
        }
        let root_is_2node =
            !self.left().is_some_and(Llrb::is_red) && !self.right().is_some_and(Llrb::is_red);
        if root_is_2node {
            self.set_color(Color::Red);
        }
        self.delete_inner(a, rotations);
        self.set_color(Color::Black);
        true
    }
}

/// In-order iteration on an explicit stack: `next` is `O(1)` amortised.
pub struct Iter<'a, T> {
    stack: Vec<&'a Llrb<T>>,
    /// How many keys are still owed; exact.
    remaining: usize,
}

impl<'a, T> Iter<'a, T> {
    fn push_left_spine(&mut self, mut t: &'a Llrb<T>) {
        while let Some(n) = t.as_node() {
            self.stack.push(t);
            t = &n.left;
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let node = self.stack.pop()?;
        let n = node.as_node().expect("only nodes are pushed");
        self.push_left_spine(&n.right);
        self.remaining -= 1;
        Some(&n.key)
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

impl<T> Llrb<T> {
    /// The keys in order, lazily.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        // Sized once from the proved height bound `2*lg(n+1)`; the empty tree allocates nothing.
        let n = self.len();
        let mut it = Iter {
            stack: Vec::with_capacity(height_bound(n)),
            remaining: n,
        };
        it.push_left_spine(self);
        it
    }
}

impl<T> std::iter::FusedIterator for Iter<'_, T> {}

impl<'a, T> IntoIterator for &'a Llrb<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// A sub-range of the keys, in order, lazily — what [`Llrb::range`] returns.
///
/// Two stacks, one seeded below each bound; the range is exhausted when the front's next key
/// has passed the back's.
pub struct Range<'a, T> {
    front: Vec<&'a Node<T>>,
    back: Vec<&'a Node<T>>,
    /// An upper bound for `size_hint`; like `std`'s ranges, no exact length.
    upper: usize,
}

impl<'a, T> Range<'a, T> {
    /// Push the left spine of `t`, the nodes whose keys `next` now owes in order.
    fn push_left_spine(&mut self, mut t: &'a Llrb<T>) {
        while let Llrb(Some(n)) = t {
            self.front.push(n);
            t = &n.left;
        }
    }

    /// The mirror: the right spine, which `next_back` owes in reverse order.
    fn push_right_spine(&mut self, mut t: &'a Llrb<T>) {
        while let Llrb(Some(n)) = t {
            self.back.push(n);
            t = &n.right;
        }
    }
}

impl<T: Ord> Range<'_, T> {
    /// Have the two ends met? Either stack running dry ends the range: the other may still
    /// hold a key the caller excluded.
    fn met(&self) -> bool {
        match (self.front.last(), self.back.last()) {
            (Some(f), Some(b)) => f.key > b.key,
            _ => true,
        }
    }

    /// Drop both stacks, so every later call is `None`.
    fn finish(&mut self) {
        self.front.clear();
        self.back.clear();
    }
}

impl<'a, T: Ord> Iterator for Range<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.met() {
            self.finish();
            return None;
        }
        let n = self.front.pop().expect("met() excludes an empty front");
        self.push_left_spine(&n.right);
        self.upper = self.upper.saturating_sub(1);
        Some(&n.key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.upper))
    }
}

impl<'a, T: Ord> DoubleEndedIterator for Range<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        if self.met() {
            self.finish();
            return None;
        }
        let n = self.back.pop().expect("met() excludes an empty back");
        self.push_right_spine(&n.left);
        self.upper = self.upper.saturating_sub(1);
        Some(&n.key)
    }
}

// Hand-written, as `Iter`'s is.
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

impl<T> Llrb<T> {
    /// The keys in a sub-range, in order, lazily — `std`'s ordered-set idiom.
    ///
    /// ```
    /// # use algodesign::searching::llrb::Llrb;
    /// let t: Llrb<i32> = (1..=9).map(|k| k * 10).collect();
    /// assert_eq!(t.range(35..=60).copied().collect::<Vec<_>>(), vec![40, 50, 60]);
    /// assert_eq!(t.range(..=35).next_back(), Some(&30)); // floor(35)
    /// assert_eq!(t.range(35..).next(), Some(&40)); // ceiling(35)
    /// ```
    ///
    /// Cost: two `O(log n)` descents, then `O(1)` amortised per key.
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
        let (start, end) = check_bounds(&range, "Llrb::range");

        let n = self.len();
        let stack = || Vec::with_capacity(height_bound(n));
        let mut it = Range {
            front: stack(),
            back: stack(),
            upper: n,
        };

        // The forward seed: a node below the lower bound skips its whole left subtree.
        let mut cur = self;
        while let Llrb(Some(n)) = cur {
            let above_start = match start {
                Bound::Unbounded => true,
                Bound::Included(s) => n.key.borrow() >= s,
                Bound::Excluded(s) => n.key.borrow() > s,
            };
            if above_start {
                it.front.push(n);
                cur = &n.left;
            } else {
                cur = &n.right;
            }
        }

        // The backward seed, mirrored.
        let mut cur = self;
        while let Llrb(Some(n)) = cur {
            let below_end = match end {
                Bound::Unbounded => true,
                Bound::Included(e) => n.key.borrow() <= e,
                Bound::Excluded(e) => n.key.borrow() < e,
            };
            if below_end {
                it.back.push(n);
                cur = &n.right;
            } else {
                cur = &n.left;
            }
        }

        it
    }
}

impl<T: Ord> FromIterator<T> for Llrb<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut t = Llrb::default();
        t.extend(iter);
        t
    }
}

impl<T: Ord> Extend<T> for Llrb<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

#[cfg(test)]
#[path = "unit_tests/llrb.rs"]
mod tests;
