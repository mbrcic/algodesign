// SPDX-License-Identifier: Apache-2.0
//! Standard (either-leaning) red-black tree, the chapter appendix variant: CLRS 4th ed. ch. 13,
//! `RB-INSERT`/`RB-INSERT-FIXUP` and `RB-DELETE`/`RB-DELETE-FIXUP`.
//!
//! No parent pointers and no NIL sentinel: CLRS's walk up via `z.p` becomes the return from a
//! recursive call, and "is this subtree now short one black node?" is the returned `bool` on the
//! delete side. Each node caches its subtree size, so `len` is `O(1)`.
//!
//! Lean counterpart: `RedBlackStandard` (`RbTree`, `ins`, `insertFixupL`/`insertFixupR`, `Valid`).
//!
//! [`RbTree::insert_with_rotations`] and [`RbTree::delete_with_rotations`] return the rotations
//! an update made, CLRS's at most two and three. They run the same insert and delete, made
//! generic over what receives the count; [`RbTree::insert`] and [`RbTree::delete`] give it
//! nothing to receive, so they pay nothing for it.
//!
//! **Against the Python, and how fast.** The same CLRS cases in another shape: the Python is CLRS's
//! iterative code with parent pointers, and this is recursive, its fix-ups the Lean's
//! `insertFixupL`/`insertFixupR` with Case 3 folded into Case 4, so a fix ported from the Python
//! lands in a different branch. `len` is `O(1)` here, a walk in the Python.
//! `cargo bench -p algodesign --bench structures -- red_black_standard` times it against
//! `std::collections::BTreeSet`.

use crate::searching::{check_bounds, height_bound, Count};
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Bound, RangeBounds};

/// A node's color. Mirrors Lean `Color`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    /// Red.
    Red,
    /// Black; every NIL counts as black.
    Black,
}

impl Color {
    /// Red ↔ Black. Mirrors Lean `Color.flip`.
    #[must_use]
    pub fn flip(self) -> Color {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red,
        }
    }
}

/// A red-black tree of keys (a set). `None` is CLRS's NIL. Mirrors Lean `RbTree`.
///
/// `==` compares shape, not only contents; to compare contents, compare `iter()`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RbTree<T>(Option<Box<Node<T>>>);

// Not derived: the derive would add a `T: Default` bound.
impl<T> Default for RbTree<T> {
    fn default() -> Self {
        RbTree(None)
    }
}

/// What a non-empty `RbTree` holds. CLRS's NIL is `RbTree(None)`, implicitly black.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node<T> {
    /// This node's own color. CLRS colors the node; `Llrb` colors the link into it.
    pub color: Color,
    /// Everything ordered before `key`.
    pub left: RbTree<T>,
    /// The key this node holds.
    pub key: T,
    /// Everything ordered after `key`.
    pub right: RbTree<T>,
    /// How many keys hang below this node, counting its own, so `len()` is `O(1)`.
    pub size: usize,
}

impl<T> RbTree<T> {
    /// The node behind a non-empty tree, or `None` for NIL.
    #[must_use]
    pub fn as_node(&self) -> Option<&Node<T>> {
        self.0.as_deref()
    }

    fn as_node_mut(&mut self) -> Option<&mut Node<T>> {
        self.0.as_deref_mut()
    }
}

/// Build a boxed `Node` with its size computed.
fn node<T>(color: Color, left: RbTree<T>, key: T, right: RbTree<T>) -> RbTree<T> {
    let size = left.len() + right.len() + 1;
    RbTree(Some(Box::new(Node {
        color,
        left,
        key,
        right,
        size,
    })))
}

/// Recompute a node's cached count from its children's; run after anything that moves a subtree.
fn fix_size<T>(t: &mut RbTree<T>) {
    if let Some(n) = t.0.as_mut() {
        n.size = n.left.len() + n.right.len() + 1;
    }
}

/// `fix_size` for this node and both its children: the delete fix-ups rebuild two levels by
/// hand, bypassing `rotate_*_in_place`'s own count upkeep.
fn fix_sizes_two_levels<T>(t: &mut RbTree<T>) {
    if let Some(n) = t.0.as_mut() {
        fix_size(&mut n.left);
        fix_size(&mut n.right);
    }
    fix_size(t);
}

/// Is the node red? NIL is black. Mirrors Lean `isRed`.
fn is_red<T>(t: &RbTree<T>) -> bool {
    t.as_node().is_some_and(|n| n.color == Color::Red)
}

/// CLRS `LEFT-ROTATE` in place, reusing both boxes; colors untouched. Mirrors Lean `rotateLeft`.
fn rotate_left_in_place<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    if t.as_node().is_none_or(|n| n.right.is_empty()) {
        return;
    }
    rotations.add_one();
    let mut here = t.0.take().expect("checked Some just above");
    let mut up = here.right.0.take().expect("checked non-empty just above");
    here.right = std::mem::take(&mut up.left);
    up.left = RbTree(Some(here));
    *t = RbTree(Some(up));
    // The demoted node changed shape; recompute it before the new root, which reads it.
    if let Some(n) = t.0.as_mut() {
        fix_size(&mut n.left);
    }
    fix_size(t);
}
/// CLRS `RIGHT-ROTATE` in place. Symmetric to `rotate_left_in_place`.
fn rotate_right_in_place<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    if t.as_node().is_none_or(|n| n.left.is_empty()) {
        return;
    }
    rotations.add_one();
    let mut here = t.0.take().expect("checked Some just above");
    let mut up = here.left.0.take().expect("checked non-empty just above");
    here.left = std::mem::take(&mut up.right);
    up.right = RbTree(Some(here));
    *t = RbTree(Some(up));
    if let Some(n) = t.0.as_mut() {
        fix_size(&mut n.right);
    }
    fix_size(t);
}

/// Set a node's own color.
fn set_color<T>(t: &mut RbTree<T>, c: Color) {
    if let Some(n) = t.as_node_mut() {
        n.color = c;
    }
}

/// One step of `RB-INSERT-FIXUP` after inserting into the **left** child, at a black `z.p.p`
/// (CLRS's "`z.p` is `z.p.p.left`" branch). Mirrors Lean `insertFixupL` case for case.
fn insert_fixup_l<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    insert_fixup_l_inner(t, rotations);
    fix_size(t);
}

fn insert_fixup_l_inner<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    // Every test first, so the read borrow is finished before anything is rewritten.
    let (black_here, left_red, right_red, ll_red, lr_red) = {
        let Some(n) = t.as_node() else {
            return;
        };
        let (ll, lr) = match n.left.as_node() {
            Some(l) => (is_red(&l.left), is_red(&l.right)),
            None => (false, false),
        };
        (
            n.color == Color::Black,
            is_red(&n.left),
            is_red(&n.right),
            ll,
            lr,
        )
    };
    if !black_here || !left_red {
        return;
    }
    if !ll_red && !lr_red {
        return;
    }
    if right_red {
        // Case 1 (uncle red): recolor, pushing the violation up.
        let n = t.as_node_mut().expect("checked Some above");
        set_color(&mut n.left, Color::Black);
        set_color(&mut n.right, Color::Black);
        n.color = Color::Red;
        return;
    }
    // Case 2 (triangle): rotate at the child to turn it into a line, then fall through.
    if lr_red {
        let n = t.as_node_mut().expect("checked Some above");
        rotate_left_in_place(&mut n.left, rotations);
    }
    // Case 3 (line): recolor and rotate around this node.
    let n = t.as_node_mut().expect("checked Some above");
    set_color(&mut n.left, Color::Black);
    n.color = Color::Red;
    rotate_right_in_place(t, rotations);
}

/// Symmetric to `insert_fixup_l`, for the **right** child. Mirrors Lean `insertFixupR`.
fn insert_fixup_r<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    insert_fixup_r_inner(t, rotations);
    fix_size(t);
}

fn insert_fixup_r_inner<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) {
    let (black_here, right_red, left_red, rl_red, rr_red) = {
        let Some(n) = t.as_node() else {
            return;
        };
        let (rl, rr) = match n.right.as_node() {
            Some(r) => (is_red(&r.left), is_red(&r.right)),
            None => (false, false),
        };
        (
            n.color == Color::Black,
            is_red(&n.right),
            is_red(&n.left),
            rl,
            rr,
        )
    };
    if !black_here || !right_red {
        return;
    }
    if !rl_red && !rr_red {
        return;
    }
    if left_red {
        let n = t.as_node_mut().expect("checked Some above");
        set_color(&mut n.left, Color::Black);
        set_color(&mut n.right, Color::Black);
        n.color = Color::Red;
        return;
    }
    if rl_red {
        let n = t.as_node_mut().expect("checked Some above");
        rotate_right_in_place(&mut n.right, rotations);
    }
    let n = t.as_node_mut().expect("checked Some above");
    set_color(&mut n.right, Color::Black);
    n.color = Color::Red;
    rotate_left_in_place(t, rotations);
}

/// Insert `a` as a red leaf, running the fix-up on the way back up; a duplicate is a no-op. The
/// root is left for `RbTree::insert` to blacken. Mirrors Lean `ins`.
fn ins<T: Ord, C: Count>(t: &mut RbTree<T>, a: T, rotations: &mut C) -> bool {
    let Some(n) = t.as_node_mut() else {
        *t = node(Color::Red, RbTree::new(), a, RbTree::new());
        return true;
    };
    let (went, added) = match a.cmp(&n.key) {
        Ordering::Less => (Ordering::Less, ins(&mut n.left, a, rotations)),
        Ordering::Greater => (Ordering::Greater, ins(&mut n.right, a, rotations)),
        Ordering::Equal => (Ordering::Equal, false),
    };
    match went {
        Ordering::Less => insert_fixup_l(t, rotations),
        Ordering::Greater => insert_fixup_r(t, rotations),
        Ordering::Equal => {}
    }
    fix_size(t);
    added
}

/// One step of `RB-DELETE-FIXUP` when the **left** child is short one black node (CLRS 13.4's
/// "`x == x.p.left`" branch). Returns whether this subtree is now short in turn (CLRS's
/// `x = x.p`). The cases below carry CLRS's numbers.
fn delete_fixup_l<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> bool {
    let short = delete_fixup_l_inner(t, rotations);
    fix_sizes_two_levels(t);
    short
}

fn delete_fixup_l_inner<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> bool {
    let mut here =
        t.0.take()
            .expect("delete_fixup_l is only ever called on a Node");
    let mut sib = here
        .right
        .0
        .take()
        .expect("RB invariant violated: a short child's sibling must be a Node, not a Leaf");

    if sib.color == Color::Red {
        // Case 1: the red sibling comes up and the deficiency is re-attacked one level in.
        rotations.add_one();
        here.right = std::mem::take(&mut sib.left);
        here.color = Color::Red;
        let mut inner = RbTree(Some(here));
        let short = delete_fixup_l(&mut inner, rotations);
        sib.left = inner;
        sib.color = Color::Black;
        *t = RbTree(Some(sib));
        return short;
    }

    let rl_red = is_red(&sib.left);
    let rr_red = is_red(&sib.right);

    if !rl_red && !rr_red {
        // Case 2: recolor the sibling red and push the deficiency up.
        let c = here.color;
        sib.color = Color::Red;
        here.right = RbTree(Some(sib));
        here.color = Color::Black;
        *t = RbTree(Some(here));
        return c == Color::Black;
    }

    if rr_red {
        // Case 4: recolor and rotate here; always terminates.
        rotations.add_one();
        let c = here.color;
        set_color(&mut sib.right, Color::Black);
        here.right = std::mem::take(&mut sib.left);
        here.color = Color::Black;
        sib.left = RbTree(Some(here));
        sib.color = c;
        *t = RbTree(Some(sib));
        return false;
    }

    // Case 3 folded into Case 4: both rotations at once, reusing all three boxes.
    let mut nephew = sib
        .left
        .0
        .take()
        .expect("rl_red implies the near nephew is a Node");
    rotations.add_one();
    rotations.add_one();
    let c = here.color;
    here.right = std::mem::take(&mut nephew.left);
    here.color = Color::Black;
    sib.left = std::mem::take(&mut nephew.right);
    sib.color = Color::Black;
    nephew.left = RbTree(Some(here));
    nephew.right = RbTree(Some(sib));
    nephew.color = c;
    *t = RbTree(Some(nephew));
    false
}

/// Symmetric to `delete_fixup_l`, for a short **right** child.
fn delete_fixup_r<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> bool {
    let short = delete_fixup_r_inner(t, rotations);
    fix_sizes_two_levels(t);
    short
}

fn delete_fixup_r_inner<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> bool {
    let mut here =
        t.0.take()
            .expect("delete_fixup_r is only ever called on a Node");
    let mut sib = here
        .left
        .0
        .take()
        .expect("RB invariant violated: a short child's sibling must be a Node, not a Leaf");

    if sib.color == Color::Red {
        rotations.add_one();
        here.left = std::mem::take(&mut sib.right);
        here.color = Color::Red;
        let mut inner = RbTree(Some(here));
        let short = delete_fixup_r(&mut inner, rotations);
        sib.right = inner;
        sib.color = Color::Black;
        *t = RbTree(Some(sib));
        return short;
    }

    let ll_red = is_red(&sib.left);
    let lr_red = is_red(&sib.right);

    if !ll_red && !lr_red {
        let c = here.color;
        sib.color = Color::Red;
        here.left = RbTree(Some(sib));
        here.color = Color::Black;
        *t = RbTree(Some(here));
        return c == Color::Black;
    }

    if ll_red {
        rotations.add_one();
        let c = here.color;
        set_color(&mut sib.left, Color::Black);
        here.left = std::mem::take(&mut sib.right);
        here.color = Color::Black;
        sib.right = RbTree(Some(here));
        sib.color = c;
        *t = RbTree(Some(sib));
        return false;
    }

    let mut nephew = sib
        .right
        .0
        .take()
        .expect("lr_red implies the near nephew is a Node");
    rotations.add_one();
    rotations.add_one();
    let c = here.color;
    here.left = std::mem::take(&mut nephew.right);
    here.color = Color::Black;
    sib.right = std::mem::take(&mut nephew.left);
    sib.color = Color::Black;
    nephew.right = RbTree(Some(here));
    nephew.left = RbTree(Some(sib));
    nephew.color = c;
    *t = RbTree(Some(nephew));
    false
}

/// Remove and return the minimum (CLRS's successor `y` for `del`), and whether the tree is now
/// short one black node.
// A wrapper, so no early `return` can skip the `fix_size`.
fn delete_min<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> (T, bool) {
    let out = delete_min_inner(t, rotations);
    fix_size(t);
    out
}

fn delete_min_inner<T, C: Count>(t: &mut RbTree<T>, rotations: &mut C) -> (T, bool) {
    let Some(n) = t.as_node() else {
        panic!("delete_min called on an empty tree")
    };
    let color = n.color;
    if !n.left.is_empty() {
        let n = t.as_node_mut().expect("checked Some just above");
        let (min_key, short) = delete_min(&mut n.left, rotations);
        if short {
            return (min_key, delete_fixup_l(t, rotations));
        }
        return (min_key, false);
    }
    let here = t.0.take().expect("checked Some just above");
    let Node { key, right, .. } = *here;
    if right.is_empty() {
        return (key, color == Color::Black);
    }
    debug_assert_eq!(
        color,
        Color::Black,
        "RB invariant violated: a red node can't have exactly one leaf child"
    );
    *t = right;
    set_color(t, Color::Black);
    (key, false)
}

/// CLRS 13.4 `RB-DELETE` below `t`, fixing up on the way back; returns whether `t` is now short
/// one black node (harmless at the root).
fn del<T, Q, C: Count>(t: &mut RbTree<T>, key: &Q, found: &mut bool, rotations: &mut C) -> bool
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    let short = del_inner(t, key, found, rotations);
    fix_size(t);
    short
}

fn del_inner<T, Q, C: Count>(
    t: &mut RbTree<T>,
    key: &Q,
    found: &mut bool,
    rotations: &mut C,
) -> bool
where
    T: Ord + Borrow<Q>,
    Q: Ord + ?Sized,
{
    let Some(n) = t.as_node() else {
        return false;
    };
    let ord = key.cmp(n.key.borrow());
    let color = n.color;
    let l_leaf = n.left.is_empty();
    let r_leaf = n.right.is_empty();
    match ord {
        Ordering::Less => {
            let n = t.as_node_mut().expect("checked Some just above");
            let short = del(&mut n.left, key, found, rotations);
            if short {
                delete_fixup_l(t, rotations)
            } else {
                false
            }
        }
        Ordering::Greater => {
            let n = t.as_node_mut().expect("checked Some just above");
            let short = del(&mut n.right, key, found, rotations);
            if short {
                delete_fixup_r(t, rotations)
            } else {
                false
            }
        }
        Ordering::Equal => {
            *found = true;
            if l_leaf && r_leaf {
                *t = RbTree::new();
                return color == Color::Black;
            }
            if l_leaf || r_leaf {
                debug_assert_eq!(
                    color,
                    Color::Black,
                    "RB invariant violated: a red node can't have exactly one leaf child"
                );
                let here = t.0.take().expect("checked Some just above");
                let Node { left, right, .. } = *here;
                *t = if l_leaf { right } else { left };
                set_color(t, Color::Black);
                return false;
            }
            // Two children: the in-order successor comes up out of the right subtree.
            let n = t.as_node_mut().expect("checked Some just above");
            let (min_key, short) = delete_min(&mut n.right, rotations);
            n.key = min_key;
            if short {
                delete_fixup_r(t, rotations)
            } else {
                false
            }
        }
    }
}

impl<T> RbTree<T> {
    /// The empty tree. Mirrors Lean `leaf`.
    #[must_use]
    pub fn new() -> Self {
        RbTree(None)
    }

    /// Is this the empty tree — CLRS's NIL?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    /// How many keys the tree holds. `O(1)`: the root's [`Node::size`].
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |n| n.size)
    }

    /// **CLRS property 2**: is the root black (or the tree empty)? Mirrors Lean `RootBlack`.
    #[must_use]
    pub fn is_root_black(&self) -> bool {
        self.as_node().is_none_or(|n| n.color == Color::Black)
    }

    /// **CLRS property 4**: no red node has a red child. Mirrors Lean `NoRedRed`.
    #[must_use]
    pub fn is_no_red_red(&self) -> bool {
        self.as_node().is_none_or(|n| {
            let own_children_ok = n.color != Color::Red || (!is_red(&n.left) && !is_red(&n.right));
            own_children_ok && n.left.is_no_red_red() && n.right.is_no_red_red()
        })
    }

    /// **CLRS properties 3 and 5**: the black-height (NIL counts 1), or `None` where two
    /// root-to-leaf paths disagree. Mirrors Lean `blackHeight`.
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

    /// **CLRS properties 3 and 5** as a yes or no: every root-to-leaf path has the same number
    /// of black nodes. Mirrors Lean `BlackHeightOk`.
    #[must_use]
    pub fn is_black_height_ok(&self) -> bool {
        self.black_height().is_some()
    }

    /// In-order keys as a `Vec`.
    #[must_use]
    pub fn in_order(&self) -> Vec<&T> {
        self.iter().collect()
    }
}

impl<T: Ord> RbTree<T> {
    /// CLRS's `TREE-SEARCH`. Mirrors Lean `Mem`.
    #[must_use]
    pub fn get<Q>(&self, key: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self;
        while let Some(n) = cur.as_node() {
            match key.cmp(n.key.borrow()) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
                Ordering::Equal => return Some(&n.key),
            }
        }
        None
    }

    /// Is `key` a key of this tree? The `std` container spelling of [`RbTree::get`].
    #[must_use]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// In-order traversal is strictly ascending, by carrying bounds down: `O(n)`, no allocation.
    /// Mirrors Lean `Sorted`.
    #[must_use]
    pub fn is_sorted(&self) -> bool {
        fn within<T: Ord>(t: &RbTree<T>, lo: Option<&T>, hi: Option<&T>) -> bool {
            t.as_node().is_none_or(|n| {
                lo.is_none_or(|l| l < &n.key)
                    && hi.is_none_or(|h| &n.key < h)
                    && within(&n.left, lo, Some(&n.key))
                    && within(&n.right, Some(&n.key), hi)
            })
        }
        within(self, None, None)
    }

    /// A legal red-black tree: ordered, plus CLRS's color properties. Mirrors Lean `Valid`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`RbTree::is_valid`] with the first failed piece named: the five invariants in the order
    /// of the book's appendix and CLRS, then the search tree's order (the Lean `Valid` is
    /// `Sorted ∧ RootBlack ∧ NoRedRed ∧ BlackHeightOk`).
    ///
    /// # Errors
    ///
    /// `"invariant 2 (root_black)"`, `"invariant 4 (no_red_red)"`,
    /// `"invariant 5 (black_height_ok)"` or `"not in the box (sorted)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        // Invariant 1, every node red or black, is held by the type `Color`; invariant 3, every
        // empty spot counts as black, is how an empty subtree is read. Neither can be broken.
        if !self.is_root_black() {
            return Err("invariant 2 (root_black)");
        }
        if !self.is_no_red_red() {
            return Err("invariant 4 (no_red_red)");
        }
        if !self.is_black_height_ok() {
            return Err("invariant 5 (black_height_ok)");
        }
        if !self.is_sorted() {
            return Err("not in the box (sorted)");
        }
        Ok(())
    }

    /// CLRS `RB-INSERT`: insert `key` and blacken the root; `false` if it was already present.
    /// `O(log n)`, at most two rotations. Mirrors Lean `insert`.
    pub fn insert(&mut self, key: T) -> bool {
        self.insert_counting(key, &mut ())
    }

    /// [`RbTree::insert`], and how many rotations it made: at most two.
    ///
    /// ```
    /// use algodesign::searching::RbTree;
    ///
    /// let mut t: RbTree<i32> = [3, 2].into_iter().collect();
    /// assert_eq!(t.insert_with_rotations(1), (true, 1)); // Case 3: one rotation at 3
    /// ```
    pub fn insert_with_rotations(&mut self, key: T) -> (bool, usize) {
        let mut rotations = 0;
        let added = self.insert_counting(key, &mut rotations);
        (added, rotations)
    }

    fn insert_counting<C: Count>(&mut self, key: T, rotations: &mut C) -> bool {
        let added = ins(self, key, rotations);
        set_color(self, Color::Black);
        added
    }

    /// CLRS `RB-DELETE`: remove `key` and blacken the root; `false` if it was absent.
    /// `O(log n)`, at most three rotations.
    pub fn delete<Q>(&mut self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.delete_counting(key, &mut ())
    }

    /// [`RbTree::delete`], and how many rotations it made: at most three, the by-hand ones of
    /// the folded Case 3 and 4 counted as two.
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
        let mut found = false;
        del(self, key, &mut found, rotations);
        set_color(self, Color::Black);
        found
    }
}

/// In-order iterator over an explicit stack; `next` is `O(1)` amortised.
pub struct Iter<'a, T> {
    stack: Vec<&'a RbTree<T>>,
    /// Keys still owed; exact, from the root's size.
    remaining: usize,
}

impl<'a, T> Iter<'a, T> {
    fn push_left_spine(&mut self, mut t: &'a RbTree<T>) {
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

impl<T> RbTree<T> {
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

impl<'a, T> IntoIterator for &'a RbTree<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

/// A sub-range of the keys, in order, lazily — what [`RbTree::range`] returns.
///
/// Two stacks, one per end, each seeded by a descent to its own bound.
pub struct Range<'a, T> {
    front: Vec<&'a Node<T>>,
    back: Vec<&'a Node<T>>,
    /// Upper bound for `size_hint` only; like `std`'s ranges, no exact length.
    upper: usize,
}

impl<'a, T> Range<'a, T> {
    /// Push the left spine of `t`, the keys `next` now owes.
    fn push_left_spine(&mut self, mut t: &'a RbTree<T>) {
        while let RbTree(Some(n)) = t {
            self.front.push(n);
            t = &n.left;
        }
    }

    /// The mirror: the right spine, which `next_back` owes in reverse order.
    fn push_right_spine(&mut self, mut t: &'a RbTree<T>) {
        while let RbTree(Some(n)) = t {
            self.back.push(n);
            t = &n.right;
        }
    }
}

impl<T: Ord> Range<'_, T> {
    /// Have the two ends met? Either stack empty also ends the range: the other may still hold a
    /// key outside the bounds.
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

// Not derived, as for `Iter`.
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

impl<T> RbTree<T> {
    /// The keys in a sub-range, in order, lazily — `std`'s ordered-set idiom.
    ///
    /// ```
    /// # use algodesign::searching::red_black_standard::RbTree;
    /// let t: RbTree<i32> = (1..=9).map(|k| k * 10).collect();
    /// assert_eq!(t.range(35..=60).copied().collect::<Vec<_>>(), vec![40, 50, 60]);
    /// assert_eq!(t.range(..=35).next_back(), Some(&30)); // floor(35)
    /// assert_eq!(t.range(35..).next(), Some(&40)); // ceiling(35)
    /// ```
    ///
    /// Cost: two `O(log n)` descents, then `O(1)` amortised per key.
    ///
    /// # Panics
    ///
    /// If start > end, or both bounds exclude the same key.
    #[must_use]
    pub fn range<Q, R>(&self, range: R) -> Range<'_, T>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = check_bounds(&range, "RbTree::range");

        let n = self.len();
        let stack = || Vec::with_capacity(height_bound(n));
        let mut it = Range {
            front: stack(),
            back: stack(),
            upper: n,
        };

        // Forward seed: a key below the start skips its whole left subtree.
        let mut cur = self;
        while let RbTree(Some(n)) = cur {
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
        while let RbTree(Some(n)) = cur {
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

impl<T: Ord> FromIterator<T> for RbTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut t = RbTree::default();
        t.extend(iter);
        t
    }
}

impl<T: Ord> Extend<T> for RbTree<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

#[cfg(test)]
#[path = "unit_tests/red_black_standard.rs"]
mod tests;
