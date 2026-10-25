// SPDX-License-Identifier: Apache-2.0
//! Treap: a BST on keys that is also a max-heap on per-node `u64` priorities.
//!
//! Seidel & Aragon, as the chapter teaches it: insert as a BST leaf and **rotate the new node up**
//! while it strictly outranks its parent; delete **rotates the node down** to a leaf, lifting the
//! child of higher priority and the right one on a tie.
//!
//! Every operation is iterative: caller-chosen priorities ([`Treap::insert`]) can make a valid
//! treap a spine of `n` nodes.
//!
//! **Priorities.** [`Treap::insert`] takes the caller's. [`Treap::insert_random`] draws one: from
//! the tree's own `SplitMix64` stream if it was made by [`Treap::with_seed`], the generator every
//! seeded structure in the library uses, and from `rand` otherwise. One draw per call, a present
//! key included, so a seed and a sequence of calls give one tree, and the Python's
//! `Treap(seed=...)` gives the same one.
//!
//! **Rotations.** The chapter states fewer than two rotations per update on average.
//! [`Treap::insert_with_rotations`], [`Treap::insert_random_with_rotations`] and
//! [`Treap::delete_with_rotations`] return that count beside the answer. They run the same insert
//! and delete as the plain methods, made generic over what receives the count; the plain methods
//! give it nothing to receive, so they pay nothing for it.
//!
//! The rotate-up insert rotates inline; `rotate_left` and `rotate_right` serve the delete.
//!
//! Lean counterpart: `AlgoDesign.Searching.Treap`.

use crate::rng::SplitMix64;
use crate::searching::Count;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;

/// A treap node: left subtree, key, priority, right subtree. Lean: `Treap.node`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Node<T> {
    left: Tree<T>,
    key: T,
    priority: u64,
    right: Tree<T>,
}

/// A possibly-empty subtree; `None` is Lean's `Treap.leaf`.
type Tree<T> = Option<Box<Node<T>>>;

/// An ordered set kept balanced in expectation by random priorities: expected `O(log n)`
/// operations with no rebalancing bookkeeping.
///
/// `==` compares shape and priorities; to compare contents, compare `iter()`.
#[derive(Eq)]
pub struct Treap<T> {
    root: Tree<T>,
    /// Key count, maintained by `insert`/`delete` rather than walked.
    len: usize,
    /// Where `insert_random` draws priorities from: the seeded stream of `with_seed`, or `rand`.
    priorities: Option<SplitMix64>,
}

impl<T> Default for Treap<T> {
    fn default() -> Self {
        Treap {
            root: None,
            len: 0,
            priorities: None,
        }
    }
}

// Drop on a heap stack: the derived drop glue recurses per level and overflows on a spine.
impl<T> Drop for Treap<T> {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        if let Some(n) = self.root.take() {
            stack.push(n);
        }
        while let Some(mut n) = stack.pop() {
            if let Some(l) = n.left.take() {
                stack.push(l);
            }
            if let Some(r) = n.right.take() {
                stack.push(r);
            }
            // `n` is dropped here holding two empty subtrees, so nothing recurses.
        }
    }
}

// By hand on an explicit stack: the derived one recurses.
impl<T: PartialEq> PartialEq for Treap<T> {
    fn eq(&self, other: &Self) -> bool {
        let mut stack = vec![(&self.root, &other.root)];
        while let Some((a, b)) = stack.pop() {
            match (a.as_ref(), b.as_ref()) {
                (None, None) => {}
                (Some(x), Some(y)) => {
                    if x.key != y.key || x.priority != y.priority {
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

// `.` for the empty tree, `(left key/priority right)` for a node; iterative.
impl<T: fmt::Debug> fmt::Debug for Treap<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum Step<'a, T> {
            Tree(&'a Tree<T>),
            Key(&'a T, u64),
            Close,
        }
        f.write_str("Treap")?;
        let mut stack = vec![Step::Tree(&self.root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Tree(t) => match t.as_deref() {
                    None => f.write_str(".")?,
                    Some(n) => {
                        f.write_str("(")?;
                        stack.push(Step::Close);
                        stack.push(Step::Tree(&n.right));
                        stack.push(Step::Key(&n.key, n.priority));
                        stack.push(Step::Tree(&n.left));
                    }
                },
                Step::Key(k, p) => write!(f, " {k:?}/{p} ")?,
                Step::Close => f.write_str(")")?,
            }
        }
        Ok(())
    }
}

impl<T: Clone> Clone for Treap<T> {
    fn clone(&self) -> Self {
        // Record (node, right, left) order, then replay it backwards: post-order, so a node's
        // two subtrees are the top two entries of `built` when it is reached.
        let mut order: Vec<Option<&Node<T>>> = Vec::new();
        let mut pending: Vec<&Tree<T>> = vec![&self.root];
        while let Some(t) = pending.pop() {
            match t.as_deref() {
                None => order.push(None),
                Some(n) => {
                    order.push(Some(n));
                    pending.push(&n.left);
                    pending.push(&n.right);
                }
            }
        }
        let mut built: Vec<Tree<T>> = Vec::with_capacity(order.len());
        for entry in order.into_iter().rev() {
            match entry {
                None => built.push(None),
                Some(n) => {
                    let right = built
                        .pop()
                        .expect("post-order visits a node after its subtrees");
                    let left = built
                        .pop()
                        .expect("post-order visits a node after its subtrees");
                    built.push(Some(Box::new(Node {
                        left,
                        key: n.key.clone(),
                        priority: n.priority,
                        right,
                    })));
                }
            }
        }
        Treap {
            root: built.pop().expect("the root is the last entry replayed"),
            len: self.len,
            priorities: self.priorities.clone(),
        }
    }
}

impl<T> Treap<T> {
    /// The empty treap.
    #[must_use]
    pub fn new() -> Self {
        Treap::default()
    }

    /// The empty treap whose [`Treap::insert_random`] draws priorities from `SplitMix64` seeded
    /// with `seed`, as the Python's `Treap(seed=seed)` does: the same seed and the same calls
    /// build the same tree in both languages.
    ///
    /// ```
    /// use algodesign::searching::treap::Treap;
    ///
    /// let (mut a, mut b) = (Treap::with_seed(7), Treap::with_seed(7));
    /// for k in [5, 3, 8, 3, 1] {
    ///     a.insert_random(k);
    ///     b.insert_random(k);
    /// }
    /// assert_eq!(a, b); // same shape, same priorities
    /// ```
    #[must_use]
    pub fn with_seed(seed: u64) -> Self {
        Treap {
            root: None,
            len: 0,
            priorities: Some(SplitMix64::new(seed)),
        }
    }

    /// Number of keys in the treap. `O(1)`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is this treap empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T: Ord> Treap<T> {
    /// Insert `key` at the given `priority`, returning whether it was absent. A present key
    /// leaves the treap **unchanged, its priority included**. Lean: `Treap.insert`, `mem_insert`.
    ///
    /// ```
    /// use algodesign::searching::treap::Treap;
    ///
    /// let mut t = Treap::new();
    /// assert!(t.insert(5, 10));
    /// assert!(t.insert(3, 20));
    /// let before = t.clone();
    /// // A higher priority would lift 5 above 3; a present key is not moved.
    /// assert!(!t.insert(5, 99));
    /// assert_eq!(t, before);
    /// ```
    ///
    /// Caller-chosen priorities can make the depth `n`; [`Treap::insert_random`] draws one.
    pub fn insert(&mut self, key: T, priority: u64) -> bool {
        self.insert_counting(key, priority, &mut ())
    }

    /// [`Treap::insert`], and how many rotations it made: one per ancestor the new key outranks.
    ///
    /// ```
    /// use algodesign::searching::treap::Treap;
    ///
    /// let mut t = Treap::new();
    /// t.insert(5, 10);
    /// t.insert(3, 20); // 3 outranks 5: one rotation lifts it to the root
    /// assert_eq!(t.insert_with_rotations(4, 30), (true, 2));
    /// ```
    pub fn insert_with_rotations(&mut self, key: T, priority: u64) -> (bool, usize) {
        let mut rotations = 0;
        let added = self.insert_counting(key, priority, &mut rotations);
        (added, rotations)
    }

    fn insert_counting<C: Count>(&mut self, key: T, priority: u64, rotations: &mut C) -> bool {
        let added = insert(key, priority, &mut self.root, rotations);
        self.len += usize::from(added);
        added
    }

    /// The next priority for `insert_random`: the seeded stream's, or a fresh random `u64`.
    fn draw(&mut self) -> u64 {
        match &mut self.priorities {
            Some(stream) => stream.next_u64(),
            None => rand::random::<u64>(),
        }
    }

    /// Insert `key` with a drawn priority ([`Treap::with_seed`]'s stream, or random), returning
    /// whether it was absent. A priority is drawn even for a present key.
    pub fn insert_random(&mut self, key: T) -> bool {
        let priority = self.draw();
        self.insert(key, priority)
    }

    /// [`Treap::insert_random`], and how many rotations it made.
    pub fn insert_random_with_rotations(&mut self, key: T) -> (bool, usize) {
        let priority = self.draw();
        self.insert_with_rotations(key, priority)
    }

    /// Remove `key`, returning whether it was present: rotate its node down to a leaf, lifting
    /// the child of higher priority, **the right one on a tie**. Lean: `Treap.delete`,
    /// `removeRoot_eq_join`.
    pub fn delete<Q>(&mut self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.delete_counting(key, &mut ())
    }

    /// [`Treap::delete`], and how many rotations it made: one per level the node sinks.
    pub fn delete_with_rotations<Q>(&mut self, key: &Q) -> (bool, usize)
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut rotations = 0;
        let removed = self.delete_counting(key, &mut rotations);
        (removed, rotations)
    }

    fn delete_counting<Q, C>(&mut self, key: &Q, rotations: &mut C) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        C: Count,
    {
        let removed = delete(key, &mut self.root, rotations);
        self.len -= usize::from(removed);
        removed
    }

    /// Is `key` in the treap? Lean: `Mem`.
    #[must_use]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        contains(key, &self.root)
    }
}

/// Lazy in-order iteration on an explicit stack; `next` is `O(1)` amortised.
pub struct Iter<'a, T> {
    stack: Vec<&'a Node<T>>,
    /// How many keys are still owed.
    remaining: usize,
}

impl<'a, T> Iter<'a, T> {
    fn push_left_spine(&mut self, mut t: &'a Tree<T>) {
        while let Some(n) = t {
            self.stack.push(n);
            t = &n.left;
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let n = self.stack.pop()?;
        self.push_left_spine(&n.right);
        self.remaining -= 1;
        Some(&n.key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

// By hand: a derive would demand `T: Clone`.
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

impl<T> Treap<T> {
    /// The keys in ascending order, lazily.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        let mut it = Iter {
            stack: Vec::new(),
            remaining: self.len,
        };
        it.push_left_spine(&self.root);
        it
    }
}

impl<'a, T> IntoIterator for &'a Treap<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// Built with fresh random priorities; use [`Treap::insert`] for a reproducible shape.
impl<T: Ord> FromIterator<T> for Treap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut t = Treap::default();
        t.extend(iter);
        t
    }
}

impl<T: Ord> Extend<T> for Treap<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for k in iter {
            self.insert_random(k);
        }
    }
}

impl<T: Ord> Treap<T> {
    /// Keys strictly in order and every priority at least its children's. Lean: `Treap.Valid`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        fn heap<T>(root: &Tree<T>) -> bool {
            let mut stack: Vec<&Tree<T>> = vec![root];
            while let Some(t) = stack.pop() {
                let Some(n) = t else { continue };
                if n.left.as_ref().is_some_and(|l| l.priority > n.priority)
                    || n.right.as_ref().is_some_and(|r| r.priority > n.priority)
                {
                    return false;
                }
                stack.push(&n.left);
                stack.push(&n.right);
            }
            true
        }
        let mut prev: Option<&T> = None;
        for k in self {
            if prev.is_some_and(|p| p >= k) {
                return false;
            }
            prev = Some(k);
        }
        heap(&self.root)
    }
}

/// Rotate right: the left child becomes the root. Boxes are moved, never reallocated.
fn rotate_right<T>(t: &mut Tree<T>) {
    let mut y = t.take().expect("rotate_right on an empty tree");
    let mut x = y.left.take().expect("rotate_right without a left child");
    y.left = x.right.take();
    x.right = Some(y);
    *t = Some(x);
}

/// Rotate left, the mirror of [`rotate_right`].
fn rotate_left<T>(t: &mut Tree<T>) {
    let mut x = t.take().expect("rotate_left on an empty tree");
    let mut y = x.right.take().expect("rotate_left without a right child");
    x.right = y.left.take();
    y.left = Some(x);
    *t = Some(y);
}

/// The nodes an insert detached below its stop point, with the side each was left by.
struct Path<T> {
    inline: [Option<(Box<Node<T>>, Ordering)>; 8],
    len: usize,
    spill: Vec<(Box<Node<T>>, Ordering)>,
}

impl<T> Path<T> {
    fn new() -> Self {
        Path {
            inline: [const { None }; 8],
            len: 0,
            spill: Vec::new(),
        }
    }

    fn push(&mut self, entry: (Box<Node<T>>, Ordering)) {
        if self.len < self.inline.len() {
            self.inline[self.len] = Some(entry);
            self.len += 1;
        } else {
            self.spill.push(entry);
        }
    }

    fn pop(&mut self) -> Option<(Box<Node<T>>, Ordering)> {
        if let Some(entry) = self.spill.pop() {
            return Some(entry);
        }
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        self.inline[self.len].take()
    }
}

/// Insert `(a, pr)` by **rotating it up** (Seidel–Aragon, Weiss §12.3): a BST leaf insert, then
/// a rotation above each ancestor it strictly outranks. A present key leaves `t` unchanged.
/// The recursion is an explicit stack (`path`).
fn insert<T: Ord, C: Count>(a: T, pr: u64, t: &mut Tree<T>, rotations: &mut C) -> bool {
    // Nothing above the first node the newcomer outranks rotates, so walk that part in place.
    let mut slot: &mut Tree<T> = t;
    loop {
        let step = match slot.as_ref() {
            Some(node) if node.priority >= pr => Some(a.cmp(&node.key)),
            _ => None,
        };
        match step {
            Some(Ordering::Equal) => return false,
            Some(Ordering::Less) => slot = &mut slot.as_mut().expect("compared against it").left,
            Some(Ordering::Greater) => {
                slot = &mut slot.as_mut().expect("compared against it").right;
            }
            None => break,
        }
    }
    let t = slot;
    let mut path = Path::new();
    let mut cur = t.take();
    let mut present = None;
    while let Some(mut n) = cur {
        match a.cmp(&n.key) {
            Ordering::Equal => {
                present = Some(n);
                break;
            }
            Ordering::Less => {
                cur = n.left.take();
                path.push((n, Ordering::Less));
            }
            Ordering::Greater => {
                cur = n.right.take();
                path.push((n, Ordering::Greater));
            }
        }
    }
    let added = present.is_none();
    // The subtree being carried up: the new leaf, or, for a present key, its untouched node.
    let mut sub = present.unwrap_or_else(|| {
        Box::new(Node {
            left: None,
            key: a,
            priority: pr,
            right: None,
        })
    });
    while let Some((mut parent, side)) = path.pop() {
        if sub.priority > parent.priority {
            // The child outranks its parent: rotate it above; `sub` stays the carried root.
            rotations.add_one();
            if side == Ordering::Less {
                parent.left = sub.right.take();
                sub.right = Some(parent);
            } else {
                parent.right = sub.left.take();
                sub.left = Some(parent);
            }
        } else {
            if side == Ordering::Less {
                parent.left = Some(sub);
            } else {
                parent.right = Some(sub);
            }
            sub = parent;
        }
    }
    *t = Some(sub);
    added
}

/// Delete `a` from `t` in place, reporting whether it was there. A no-op if `a` is absent.
fn delete<T, Q, C>(a: &Q, t: &mut Tree<T>, rotations: &mut C) -> bool
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
    C: Count,
{
    let mut cur: &mut Tree<T> = t;
    loop {
        let ord = match cur.as_ref() {
            None => return false,
            Some(node) => a.cmp(node.key.borrow()),
        };
        match ord {
            Ordering::Equal => {
                remove_root(cur, rotations);
                return true;
            }
            Ordering::Less => cur = &mut cur.as_mut().expect("compared against it above").left,
            Ordering::Greater => cur = &mut cur.as_mut().expect("compared against it above").right,
        }
    }
}

/// Sink the root to a leaf and drop it, lifting the higher-priority child at each step.
fn remove_root<T, C: Count>(t: &mut Tree<T>, rotations: &mut C) {
    let mut cur: &mut Tree<T> = t;
    loop {
        let lift_left = {
            let node = cur.as_ref().expect("remove_root on an empty tree");
            match (node.left.as_ref(), node.right.as_ref()) {
                (None, None) => None,
                (Some(_), None) => Some(true),
                (None, Some(_)) => Some(false),
                // `>`, not `>=`: on a tie the right child comes up.
                (Some(l), Some(r)) => Some(l.priority > r.priority),
            }
        };
        match lift_left {
            None => {
                *cur = None;
                return;
            }
            Some(true) => {
                rotations.add_one();
                rotate_right(cur);
                cur = &mut cur.as_mut().expect("just rotated").right;
            }
            Some(false) => {
                rotations.add_one();
                rotate_left(cur);
                cur = &mut cur.as_mut().expect("just rotated").left;
            }
        }
    }
}

/// Is `a` a key of `t`? An ordinary BST search.
fn contains<T, Q>(a: &Q, t: &Tree<T>) -> bool
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    let mut cur = t;
    while let Some(node) = cur {
        match a.cmp(node.key.borrow()) {
            Ordering::Less => cur = &node.left,
            Ordering::Greater => cur = &node.right,
            Ordering::Equal => return true,
        }
    }
    false
}

/// How many rotations inserting `(a, pr)` into `t` would make: the nodes on `a`'s search path
/// with priority `< pr`.
#[cfg(test)]
fn rotation_count<T: Ord>(a: &T, pr: u64, t: &Tree<T>) -> usize {
    match t {
        None => 0,
        Some(node) => {
            let further = match a.cmp(&node.key) {
                Ordering::Less => rotation_count(a, pr, &node.left),
                Ordering::Greater => rotation_count(a, pr, &node.right),
                Ordering::Equal => 0,
            };
            if pr > node.priority {
                further + 1
            } else {
                further
            }
        }
    }
}

#[cfg(test)]
#[path = "unit_tests/treap.rs"]
mod tests;
