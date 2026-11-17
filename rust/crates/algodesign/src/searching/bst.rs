// SPDX-License-Identifier: Apache-2.0
//! Binary search tree: a plain (unbalanced) BST of keys, a `Set` with no values, each node
//! caching its subtree's key count so `len`, `rank` and `select` cost the height, not `n`.
//!
//! Two deletions: [`Bst::delete`] is CLRS §12.3's `TRANSPLANT`, [`Bst::delete_hibbard`] copies
//! the successor's key up (Hibbard). They build the same tree and differ only in which node is
//! freed. Every walk is iterative, since sorted input makes the tree a path.
//!
//! Lean counterpart: `AlgoDesign.Searching.BST` (`lean/AlgoDesign/Searching/BST/`).
//!
//! **Against the Python, and how fast.** The same TRANSPLANT and Hibbard deletions, with the sizes
//! kept another way: `insert` counts the newcomer into every size on the way down and undoes that
//! on a duplicate, where the Python counts after hanging the key; `delete` subtracts on the way
//! down and restores the counts on a miss, where the Python finds the key first. Every walk is a
//! loop; the Python's queries recurse. One allocation a key, and `len`, `rank` and `select` read
//! the cached sizes. `cargo bench -p algodesign --bench structures -- bst` times build, lookup and
//! delete against `std::collections::BTreeSet`.

use crate::searching::check_bounds;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Bound, RangeBounds};

/// A binary search tree of keys, no associated values. Mirrors Lean's `BST`.
///
/// `==` compares shape, not only contents. To compare contents, compare `iter()`.
///
/// ```
/// use algodesign::searching::bst::Bst;
///
/// let balanced: Bst<i32> = [2, 1, 3].into_iter().collect();
/// let path: Bst<i32> = [1, 2, 3].into_iter().collect();
/// assert!(balanced.iter().eq(path.iter())); // the same keys...
/// assert_ne!(balanced, path); // ...in different shapes
/// // Every node knows how many keys hang below it, which is what `len`, `rank` and `select`
/// // read instead of walking.
/// assert_eq!(balanced.as_node().map(|n| n.size), Some(3));
/// assert_eq!(balanced.rank(&3), 2);
/// assert_eq!(balanced.select(1), Some(&2));
/// ```
///
/// `from_parts_unchecked`, which checks no order and no count, exists only behind the `unchecked`
/// feature, for tests that build a broken tree on purpose: `cargo test --features unchecked`.
// `Debug`, `Clone` and `PartialEq` are hand-written: the derived ones recurse.
#[derive(Eq)]
pub struct Bst<T>(Option<Box<Node<T>>>);

// Not derived: the derive would add a `T: Default` bound.
impl<T> Default for Bst<T> {
    fn default() -> Self {
        Bst(None)
    }
}

/// What a non-empty `Bst` holds. Mirrors the three arguments of Lean's `BST.node`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T> {
    /// Everything ordered before `key`.
    pub left: Bst<T>,
    /// The key this node holds.
    pub key: T,
    /// Everything ordered after `key`.
    pub right: Bst<T>,
    /// How many keys hang below this node, counting its own: what `len`, `rank` and `select`
    /// read instead of walking.
    pub size: usize,
}

impl<T> Bst<T> {
    /// `BST.node l k r`, with the allocation this representation needs.
    fn node(left: Bst<T>, key: T, right: Bst<T>) -> Self {
        let size = left.len() + right.len() + 1;
        Bst(Some(Box::new(Node {
            left,
            key,
            right,
            size,
        })))
    }

    /// `BST.node l k r` with `size` stored as its count, **checking no order and no count**, for
    /// tests that must hand the predicates illegal trees. Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts_unchecked(left: Bst<T>, key: T, right: Bst<T>, size: usize) -> Self {
        Bst(Some(Box::new(Node {
            left,
            key,
            right,
            size,
        })))
    }
}

/// The slot holding the leftmost node of a non-empty tree, for a caller about to remove it.
/// Lowers the cached `size` of every node passed on the way down.
fn leftmost_removing<T>(mut t: &mut Bst<T>) -> &mut Bst<T> {
    while t
        .0
        .as_ref()
        .expect("leftmost_removing is only called on a non-empty tree")
        .left
        .0
        .is_some()
    {
        let n = t.0.as_mut().expect("checked in the condition");
        n.size -= 1;
        t = &mut n.left;
    }
    t
}

#[cfg(test)]
thread_local! {
    /// Nodes the deletions' search has visited on this thread, counting a visit on the way down
    /// and another on a miss's way back.
    static STEPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The slot holding `a`, for a caller about to remove it, or `None` if absent. Lowers the cached
/// `size` of every node above the target; the target's own count is the caller's to adjust.
/// On `None` the caller must call `restore_counts`.
fn descend_removing<'a, T, Q>(t: &'a mut Bst<T>, a: &Q) -> Option<&'a mut Bst<T>>
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    let mut cur = t;
    loop {
        let ord = a.cmp(cur.0.as_ref()?.key.borrow());
        #[cfg(test)]
        STEPS.with(|c| c.set(c.get() + 1));
        if ord == Ordering::Equal {
            return Some(cur);
        }
        let n = cur.0.as_mut().expect("compared against it above");
        n.size -= 1;
        cur = if ord == Ordering::Less {
            &mut n.left
        } else {
            &mut n.right
        };
    }
}

/// Undo `descend_removing` after it found no node holding `a`: walk the same search path again
/// and give every node on it back the key it was charged for.
fn restore_counts<T, Q>(t: &mut Bst<T>, a: &Q)
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    let mut cur = t;
    while let Some(n) = cur.0.as_mut() {
        #[cfg(test)]
        STEPS.with(|c| c.set(c.get() + 1));
        n.size += 1;
        // Never `Equal`: this runs only after a miss.
        cur = if a < n.key.borrow() {
            &mut n.left
        } else {
            &mut n.right
        };
    }
}

// Iterative drop: the derived one recurses.
impl<T> Drop for Bst<T> {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        if let Some(n) = self.0.take() {
            stack.push(n);
        }
        while let Some(mut n) = stack.pop() {
            if let Some(l) = n.left.0.take() {
                stack.push(l);
            }
            if let Some(r) = n.right.0.take() {
                stack.push(r);
            }
            // `n` is dropped here holding two empty subtrees, so nothing recurses.
        }
    }
}

impl<T> Bst<T> {
    /// The empty tree. Mirrors `BST.leaf`.
    #[must_use]
    pub fn new() -> Self {
        Bst(None)
    }

    /// Number of keys in the tree. `O(1)`, from the root's cached [`Node::size`].
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.size)
    }

    /// Is this the empty tree?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// The root node, or `None` for the empty tree, for callers that walk the structure.
    #[must_use]
    pub fn as_node(&self) -> Option<&Node<T>> {
        self.0.as_deref()
    }

    /// The keys in order, collected (`iter().collect()`). Mirrors `BST.inorder`.
    #[must_use]
    pub fn in_order(&self) -> Vec<&T> {
        self.iter().collect()
    }
}

impl<T: Ord> Bst<T> {
    /// Insert `a`; returns `false` (and changes nothing) if it was already present. Mirrors
    /// `BST.insert` (`mem_insert`, `sorted_insert`).
    #[allow(
        clippy::missing_panics_doc,
        reason = "each expect re-borrows a node matched one line above; it cannot fire"
    )]
    pub fn insert(&mut self, a: T) -> bool {
        // Count the newcomer in on the way down; only a duplicate pays a second descent to undo.
        {
            let mut cur = &mut *self;
            loop {
                let ord = match cur.0.as_ref() {
                    None => {
                        *cur = Bst::node(Bst(None), a, Bst(None));
                        return true;
                    }
                    Some(n) => a.cmp(&n.key),
                };
                if ord == Ordering::Equal {
                    break;
                }
                let n = cur.0.as_mut().expect("compared against it above");
                n.size += 1;
                cur = if ord == Ordering::Less {
                    &mut n.left
                } else {
                    &mut n.right
                };
            }
        }
        // A duplicate: undo the counts raised above.
        let mut cur = &mut *self;
        loop {
            let ord = match cur.0.as_ref() {
                None => break,
                Some(n) => a.cmp(&n.key),
            };
            if ord == Ordering::Equal {
                break;
            }
            let n = cur.0.as_mut().expect("compared against it above");
            n.size -= 1;
            cur = if ord == Ordering::Less {
                &mut n.left
            } else {
                &mut n.right
            };
        }
        false
    }

    /// Does `a` occur in the tree? Mirrors `BST.search` (`search_correct`).
    #[must_use]
    pub fn search<Q>(&self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        while let Bst(Some(n)) = cur {
            match a.cmp(n.key.borrow()) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
                Ordering::Equal => return true,
            }
        }
        false
    }

    /// Is `a` a key? The `std` spelling of [`Bst::search`].
    #[must_use]
    pub fn contains<Q>(&self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.search(a)
    }

    /// The smallest key, if any. Mirrors `BST.min?` (`min?_correct`).
    #[must_use]
    pub fn min(&self) -> Option<&T> {
        let mut cur = self;
        let mut best = None;
        while let Bst(Some(n)) = cur {
            best = Some(&n.key);
            cur = &n.left;
        }
        best
    }

    /// The largest key, if any. Mirrors `BST.max?` (`max?_correct`).
    #[must_use]
    pub fn max(&self) -> Option<&T> {
        let mut cur = self;
        let mut best = None;
        while let Bst(Some(n)) = cur {
            best = Some(&n.key);
            cur = &n.right;
        }
        best
    }

    /// The largest key `<= a`, if any. Mirrors `BST.floor?` (`floor?_correct`).
    #[must_use]
    pub fn floor<Q>(&self, a: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        // Every key passed on a right turn is `<= a`, each larger than the last.
        let mut best = None;
        while let Bst(Some(n)) = cur {
            match a.cmp(n.key.borrow()) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => {
                    best = Some(&n.key);
                    cur = &n.right;
                }
                Ordering::Equal => return Some(&n.key),
            }
        }
        best
    }

    /// The smallest key `>= a`, if any. Mirrors `BST.ceiling?` (`ceiling?_correct`).
    #[must_use]
    pub fn ceiling<Q>(&self, a: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        let mut best = None;
        while let Bst(Some(n)) = cur {
            match a.cmp(n.key.borrow()) {
                Ordering::Greater => cur = &n.right,
                Ordering::Less => {
                    best = Some(&n.key);
                    cur = &n.left;
                }
                Ordering::Equal => return Some(&n.key),
            }
        }
        best
    }

    /// How many keys are strictly less than `a` (0-indexed). `O(height)`. Mirrors `BST.rank`
    /// (`rank_select?`, `select?_rank`).
    #[must_use]
    pub fn rank<Q>(&self, a: &Q) -> usize
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        let mut rank = 0;
        while let Bst(Some(n)) = cur {
            match a.cmp(n.key.borrow()) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => {
                    rank += n.left.len() + 1;
                    cur = &n.right;
                }
                Ordering::Equal => return rank + n.left.len(),
            }
        }
        rank
    }

    /// The key at position `i` (0-indexed, in sorted order), if any. `O(height)`. Mirrors
    /// `BST.select?`; inverse of [`Bst::rank`] on present keys.
    #[must_use]
    pub fn select(&self, i: usize) -> Option<&T> {
        let mut cur = self;
        let mut i = i;
        while let Bst(Some(n)) = cur {
            let lsize = n.left.len();
            match i.cmp(&lsize) {
                Ordering::Less => cur = &n.left,
                Ordering::Equal => return Some(&n.key),
                Ordering::Greater => {
                    i -= lsize + 1;
                    cur = &n.right;
                }
            }
        }
        None
    }

    /// Remove and return the minimum key by promoting its right subtree (CLRS's
    /// `TRANSPLANT(y, y.right)`); `None` iff empty.
    fn splice_min(&mut self) -> Option<T> {
        self.splice_min_node().map(|n| {
            let Node { key, .. } = *n;
            key
        })
    }

    /// [`Bst::splice_min`], returning the unhooked node itself, for `TRANSPLANT` to reuse.
    fn splice_min_node(&mut self) -> Option<Box<Node<T>>> {
        self.0.as_ref()?;
        let cur = leftmost_removing(self);
        let mut n = cur
            .0
            .take()
            .expect("leftmost of a non-empty tree is a node");
        *cur = std::mem::replace(&mut n.right, Bst(None));
        Some(n)
    }

    /// Delete `a` by **copying the in-order successor's key up** (Hibbard; Weiss §4.3.4); returns
    /// whether it was present. Frees the successor's node, not the deleted key's. Mirrors
    /// `BST.deleteHibbard` (`deleteHibbardSpec`, `deleteHibbard_eq_delete`).
    #[allow(
        clippy::missing_panics_doc,
        reason = "each expect re-borrows a node matched one line above; it cannot fire"
    )]
    pub fn delete_hibbard<Q>(&mut self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let Some(cur) = descend_removing(self, a) else {
            restore_counts(self, a);
            return false;
        };
        let n = cur.0.as_mut().expect("the descent lands on a node");
        if !n.left.is_empty() && !n.right.is_empty() {
            n.size -= 1;
            n.key = n.right.splice_min().expect("checked non-empty just above");
            return true;
        }
        let n = cur.0.take().expect("still the node the descent landed on");
        let Node { left, right, .. } = *n;
        *cur = if left.is_empty() { right } else { left };
        true
    }

    /// Delete `a` by **moving the in-order successor's node** into the gap: CLRS §12.3's
    /// `TRANSPLANT`, three cases; returns whether it was present. Mirrors
    /// `BST.delete`/`transplantAt`/`spliceMin` (`deleteSpec`).
    #[allow(
        clippy::missing_panics_doc,
        reason = "each expect re-borrows a node matched one line above; it cannot fire"
    )]
    pub fn delete<Q>(&mut self, a: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let Some(cur) = descend_removing(self, a) else {
            restore_counts(self, a);
            return false;
        };
        if cur
            .0
            .as_ref()
            .expect("the descent lands on a node")
            .left
            .is_empty()
        {
            let n = cur.0.take().expect("still the node the descent landed on");
            *cur = n.right;
            return true;
        }
        if cur
            .0
            .as_ref()
            .expect("the descent lands on a node")
            .right
            .is_empty()
        {
            let n = cur.0.take().expect("still the node the descent landed on");
            *cur = n.left;
            return true;
        }
        // Two children: stand the successor's own node where the deleted one stood.
        let mut gone = cur.0.take().expect("still the node the descent landed on");
        let mut successor = gone
            .right
            .splice_min_node()
            .expect("the right subtree is non-empty, so it has a minimum");
        successor.left = std::mem::replace(&mut gone.left, Bst(None));
        successor.right = std::mem::replace(&mut gone.right, Bst(None));
        successor.size = gone.size - 1;
        *cur = Bst(Some(successor));
        true
    }

    /// The Lean `Sorted`, box invariant 1: everything left of a key is smaller, everything
    /// right of it is larger, so a duplicate fails. Iterative; each node is checked against all
    /// its ancestors' bounds.
    #[must_use]
    pub fn is_sorted(&self) -> bool {
        let mut stack: Vec<(&Bst<T>, Option<&T>, Option<&T>)> = vec![(self, None, None)];
        while let Some((t, lo, hi)) = stack.pop() {
            let Some(n) = t.0.as_ref() else { continue };
            if lo.is_some_and(|l| l >= &n.key) || hi.is_some_and(|h| &n.key >= h) {
                return false;
            }
            stack.push((&n.left, lo, Some(&n.key)));
            stack.push((&n.right, Some(&n.key), hi));
        }
        true
    }

    /// Layout check (no Lean counterpart): every node's cached `size` is one more than its two
    /// children's. Checked arithmetic, so a corrupt count answers `false` instead of overflowing.
    #[must_use]
    pub fn sizes_add_up(&self) -> bool {
        let mut stack: Vec<&Bst<T>> = vec![self];
        while let Some(t) = stack.pop() {
            let Some(n) = t.0.as_ref() else { continue };
            if n.left
                .len()
                .checked_add(n.right.len())
                .and_then(|s| s.checked_add(1))
                != Some(n.size)
            {
                return false;
            }
            stack.push(&n.left);
            stack.push(&n.right);
        }
        true
    }

    /// The Lean `Valid`, `Sorted`, then the layout check [`Bst::sizes_add_up`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Bst::is_valid`] with the first failed check named.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (sorted)"` or `"layout (sizes_add_up)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_sorted() {
            return Err("invariant 1 (sorted)");
        }
        if !self.sizes_add_up() {
            return Err("layout (sizes_add_up)");
        }
        Ok(())
    }
}

impl<T: PartialEq> PartialEq for Bst<T> {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a.0.as_ref(), b.0.as_ref()) {
                (None, None) => {}
                (Some(x), Some(y)) => {
                    if x.key != y.key {
                        return false;
                    }
                    stack.push((&x.left, &y.left));
                    stack.push((&x.right, &y.right));
                }
                _ => return false,
            }
        }
        true
    }
}

impl<T: Clone> Clone for Bst<T> {
    fn clone(&self) -> Self {
        // Record (node, right, left) order, then replay it backwards: post-order, so each node's
        // subtrees are the top two entries of `built`.
        let mut order: Vec<Option<&Node<T>>> = Vec::new();
        let mut pending: Vec<&Bst<T>> = vec![self];
        while let Some(t) = pending.pop() {
            match t.0.as_ref() {
                None => order.push(None),
                Some(n) => {
                    order.push(Some(n));
                    pending.push(&n.left);
                    pending.push(&n.right);
                }
            }
        }
        let mut built: Vec<Bst<T>> = Vec::with_capacity(order.len());
        for entry in order.into_iter().rev() {
            match entry {
                None => built.push(Bst(None)),
                Some(n) => {
                    let right = built
                        .pop()
                        .expect("post-order visits a node after its subtrees");
                    let left = built
                        .pop()
                        .expect("post-order visits a node after its subtrees");
                    built.push(Bst::node(left, n.key.clone(), right));
                }
            }
        }
        built.pop().expect("the root is the last entry replayed")
    }
}

// `.` for the empty tree and `(left key right)` for a node.
impl<T: fmt::Debug> fmt::Debug for Bst<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Step<'a, T> {
            Tree(&'a Bst<T>),
            Key(&'a T),
            Close,
        }
        f.write_str("Bst")?;
        let mut stack = vec![Step::Tree(self)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Tree(t) => match t.0.as_ref() {
                    None => f.write_str(".")?,
                    Some(n) => {
                        f.write_str("(")?;
                        stack.push(Step::Close);
                        stack.push(Step::Tree(&n.right));
                        stack.push(Step::Key(&n.key));
                        stack.push(Step::Tree(&n.left));
                    }
                },
                Step::Key(k) => write!(f, " {k:?} ")?,
                Step::Close => f.write_str(")")?,
            }
        }
        Ok(())
    }
}

/// In-order iterator over the keys; `next` is `O(1)` amortised.
pub struct Iter<'a, T> {
    stack: Vec<&'a Bst<T>>,
    /// How many keys are still owed.
    remaining: usize,
}

impl<'a, T> Iter<'a, T> {
    fn push_left_spine(&mut self, mut t: &'a Bst<T>) {
        while let Bst(Some(n)) = t {
            self.stack.push(t);
            t = &n.left;
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let node = self.stack.pop()?;
        let Bst(Some(n)) = node else {
            unreachable!("only nodes are pushed")
        };
        self.push_left_spine(&n.right);
        self.remaining -= 1;
        Some(&n.key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

// Not derived: the derive would demand `T: Clone`.
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

impl<T> Bst<T> {
    /// The keys in order, lazily.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        let mut it = Iter {
            stack: Vec::new(),
            remaining: self.len(),
        };
        it.push_left_spine(self);
        it
    }
}

impl<'a, T> IntoIterator for &'a Bst<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// A sub-range of the keys, in order, lazily — what [`Bst::range`] returns.
///
/// Two stacks, one seeded above the lower bound and one below the upper.
pub struct Range<'a, T> {
    front: Vec<&'a Node<T>>,
    back: Vec<&'a Node<T>>,
    /// Upper bound for `size_hint`: the tree's count, lowered per key yielded.
    upper: usize,
}

impl<'a, T> Range<'a, T> {
    /// Push the left spine of `t`, the nodes whose keys `next` now owes in order.
    fn push_left_spine(&mut self, mut t: &'a Bst<T>) {
        while let Bst(Some(n)) = t {
            self.front.push(n);
            t = &n.left;
        }
    }

    /// The mirror: the right spine, which `next_back` owes in reverse order.
    fn push_right_spine(&mut self, mut t: &'a Bst<T>) {
        while let Bst(Some(n)) = t {
            self.back.push(n);
            t = &n.right;
        }
    }
}

impl<T: Ord> Range<'_, T> {
    /// Have the two ends met? An empty stack also ends the range. Equal tops are the same node.
    fn met(&self) -> bool {
        match (self.front.last(), self.back.last()) {
            (Some(f), Some(b)) => f.key > b.key,
            _ => true,
        }
    }

    /// Drop both stacks, so every later call is an `O(1)` `None` (fused).
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

// Not derived: the derive would demand `T: Clone`.
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

impl<T> Bst<T> {
    /// The keys in a sub-range, in order, lazily, as `BTreeSet::range`:
    ///
    /// ```
    /// # use algodesign::searching::bst::Bst;
    /// let t: Bst<i32> = (1..=9).map(|k| k * 10).collect();
    /// assert_eq!(t.range(35..=60).copied().collect::<Vec<_>>(), vec![40, 50, 60]);
    /// assert_eq!(t.range(..=35).next_back(), Some(&30)); // floor(35)
    /// assert_eq!(t.range(35..).next(), Some(&40)); // ceiling(35)
    /// ```
    ///
    /// Cost: two descents to start (`O(height)`), then `O(1)` amortised per key.
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
        let (start, end) = check_bounds(&range, "Bst::range");

        let mut it = Range {
            front: Vec::new(),
            back: Vec::new(),
            upper: self.len(),
        };

        // Forward seed: `ceiling`'s descent, with the whole path recorded.
        let mut cur = self;
        while let Bst(Some(n)) = cur {
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

        // The backward seed, mirrored: `floor`'s descent, path recorded.
        let mut cur = self;
        while let Bst(Some(n)) = cur {
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

impl<T: Ord> FromIterator<T> for Bst<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut t = Bst::default();
        t.extend(iter);
        t
    }
}

impl<T: Ord> Extend<T> for Bst<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

#[cfg(test)]
#[path = "unit_tests/bst.rs"]
mod tests;
