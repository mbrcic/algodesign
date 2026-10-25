//! The static range tree (dBCKO §5.1 in 1D, §5.3 in 2D): keys in the **leaves**, each inner node
//! holding a split key, the lower median of the keys below it. A 1D query walks to the **split
//! node** and down its two sides, reporting the whole subtrees between the two paths, in
//! `O(log n + k)`. Equal keys may sit on both sides of a split, since the build halves the sorted
//! keys by position; so the walk to the split node goes left only when `hi < split` (dBCKO:
//! `hi ≤ split`), and every copy is reported.
//!
//! The 1D tree's invariant is Lean `RangeTree1D.Valid` (`RangeTree/Spec.lean`): box invariant 1,
//! every inner key separates its two sides ([`RangeTree1D::is_keys_separate`], `KeysSeparate`), and
//! box invariant 2, every inner node splits the keys below it in half
//! ([`RangeTree1D::is_splits_halve`], `SplitsHalve`). Lean: `query_eq_filter`, `valid_build`,
//! `time_queryM_le`.
//!
//! The 2D tree is an x-tree whose inner nodes carry a 1D tree on the y-keys of their subtree
//! (`2DRANGEQUERY`), built by merging the children's y-lists (`O(n log n)`, dBCKO Theorem 5.8); a
//! 2D query reports unsorted, in `O(log² n + k)`. Lean: `RangeTree2D.query_build` proves the
//! answer (every stored point in the rectangle, each as often as stored) of a Lean model that
//! filters each node's y-sorted list; the cost is not modelled.
//!
//! **Against the Python, and how fast.** The same build and walks, compiled, with `Box` nodes and a
//! lazy `query_iter`; nothing else is done for speed, and no ratio is measured.
//! `cargo bench -p algodesign --bench geometry -- range_tree_2d` times the 2D build and query.

/// A node over a range of sorted positions: an `enum` with boxed children, because a leaf carries
/// data. The build bounds the height by `⌈log₂ n⌉`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Node<K> {
    /// One key, at this sorted position.
    Leaf { pos: usize },
    /// A split key and the sorted positions `[start, end)` below it.
    Internal {
        split: K,
        start: usize,
        end: usize,
        left: Box<Node<K>>,
        right: Box<Node<K>>,
    },
}

impl<K> Node<K> {
    /// The sorted positions below this node.
    fn range(&self) -> (usize, usize) {
        match self {
            Node::Leaf { pos } => (*pos, pos + 1),
            Node::Internal { start, end, .. } => (*start, *end),
        }
    }

    fn depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 0,
            Node::Internal { left, right, .. } => 1 + left.depth().max(right.depth()),
        }
    }
}

/// Build over the sorted positions `[start, end)`, nonempty: the first `⌈n/2⌉` go left, and the
/// split is the key at the last of them (Lean `half`, `build`).
fn build<K: Clone>(keys: &[K], start: usize, end: usize) -> Node<K> {
    if end - start == 1 {
        return Node::Leaf { pos: start };
    }
    let m = start + (end - start).div_ceil(2);
    Node::Internal {
        split: keys[m - 1].clone(),
        start,
        end,
        left: Box::new(build(keys, start, m)),
        right: Box::new(build(keys, m, end)),
    }
}

/// A 1D range tree's shape, as the Lean `RangeTree1D` spells it: a leaf holds a key, a node its
/// split key and two subtrees. Public for tests; not part of the API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape1D<K> {
    /// The Lean `leaf k`.
    Leaf(K),
    /// The Lean `node split l r`.
    Node(K, Box<Shape1D<K>>, Box<Shape1D<K>>),
}

/// A 2D range tree's shape: a leaf holds its point's id, a node its split x, the ids of its
/// points in its associated tree's order, and two subtrees. Public for tests; not part of the
/// API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape2D<K> {
    /// A leaf: its point's id.
    Leaf(usize),
    /// A node: its split x, its points' ids in its associated tree's order, its sides.
    Node {
        /// The largest x on the left side.
        split: K,
        /// The ids of the points below, in the associated tree's order.
        ids: Vec<usize>,
        /// The left side.
        left: Box<Shape2D<K>>,
        /// The right side.
        right: Box<Shape2D<K>>,
    },
}

/// A static 1D range tree over keys of any ordered type. Its build keeps
/// [`RangeTree1D::is_valid`]; only `from_shape_unchecked` (feature `unchecked`, for tests that
/// break a tree on purpose: `cargo test --features unchecked`) can break it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeTree1D<K> {
    /// The keys, sorted (stably, so equal keys keep their input order).
    keys: Vec<K>,
    /// `order[p]` is the id of the key at sorted position `p`.
    order: Vec<usize>,
    root: Option<Box<Node<K>>>,
}

impl<K: Ord + Clone> RangeTree1D<K> {
    /// Build from `keys`, in any order, repeats allowed.
    #[must_use]
    pub fn new(keys: Vec<K>) -> Self {
        let mut pairs: Vec<(K, usize)> = keys.into_iter().zip(0..).collect();
        pairs.sort_by(|a, b| a.0.cmp(&b.0));
        let (keys, order): (Vec<K>, Vec<usize>) = pairs.into_iter().unzip();
        let root = (!keys.is_empty()).then(|| Box::new(build(&keys, 0, keys.len())));
        RangeTree1D { keys, order, root }
    }

    /// Build from keys already in order, without sorting them, and `order[p]`, the id each key
    /// reports as: the associated trees of the 2D build, whose keys arrive merged and report
    /// their points' ids directly.
    pub(crate) fn from_sorted(keys: Vec<K>, order: Vec<usize>) -> Self {
        debug_assert_eq!(keys.len(), order.len());
        let root = (!keys.is_empty()).then(|| Box::new(build(&keys, 0, keys.len())));
        RangeTree1D { keys, order, root }
    }

    /// The number of keys.
    #[must_use]
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Whether there are no keys.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// The tree's height: 0 for one key, and at most `⌈log₂ n⌉`.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.root.as_ref().map_or(0, |r| r.depth())
    }

    /// The ids of the keys in `[lo, hi]`, in key order, equal keys in input order;
    /// empty if `lo > hi`. `O(log n + k)` for `k` reported: [`RangeTree1D::query_iter`],
    /// collected. Lean: `query_eq_filter` (the answer), `time_queryM_le` (the cost).
    #[must_use]
    pub fn query(&self, lo: &K, hi: &K) -> Vec<usize> {
        self.query_iter(lo, hi).collect()
    }

    /// [`RangeTree1D::query`], lazily: the walk's `O(log n)` subtrees are found at once, and their
    /// ids are yielded one at a time, in key order. Lean: `query_eq_filter`.
    pub fn query_iter(&self, lo: &K, hi: &K) -> impl Iterator<Item = usize> + '_ {
        let mut ranges = self.canonical_subtrees(lo, hi);
        ranges.sort_unstable();
        ranges
            .into_iter()
            .flat_map(move |(s, e)| self.order[s..e].iter().copied())
    }

    /// The keys in `[lo, hi]`, in order, in `O(log n + k)`.
    #[must_use]
    pub fn query_keys(&self, lo: &K, hi: &K) -> Vec<&K> {
        let mut ranges = self.canonical_subtrees(lo, hi);
        ranges.sort_unstable();
        ranges
            .into_iter()
            .flat_map(|(s, e)| &self.keys[s..e])
            .collect()
    }

    /// The tree's shape, each leaf with its key and each node with its split key; `None` for no
    /// keys, which the Lean `RangeTree1D` cannot express. Public for tests; not part of the
    /// API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn shape(&self) -> Option<Shape1D<K>> {
        fn walk<K: Clone>(keys: &[K], v: &Node<K>) -> Shape1D<K> {
            match v {
                Node::Leaf { pos } => Shape1D::Leaf(keys[*pos].clone()),
                Node::Internal {
                    split, left, right, ..
                } => Shape1D::Node(
                    split.clone(),
                    Box::new(walk(keys, left)),
                    Box::new(walk(keys, right)),
                ),
            }
        }
        self.root.as_ref().map(|r| walk(&self.keys, r))
    }

    /// The tree `shape` writes out, everything as given, unchecked: its keys are its leaves, left
    /// to right, at ids `0, 1, …`. Feature `unchecked`.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_shape_unchecked(shape: &Shape1D<K>) -> Self {
        fn walk<K: Clone>(s: &Shape1D<K>, keys: &mut Vec<K>) -> Node<K> {
            let start = keys.len();
            match s {
                Shape1D::Leaf(k) => {
                    keys.push(k.clone());
                    Node::Leaf { pos: start }
                }
                Shape1D::Node(split, l, r) => {
                    let left = Box::new(walk(l, keys));
                    let right = Box::new(walk(r, keys));
                    Node::Internal {
                        split: split.clone(),
                        start,
                        end: keys.len(),
                        left,
                        right,
                    }
                }
            }
        }
        let mut keys = Vec::new();
        let root = Box::new(walk(shape, &mut keys));
        let order = (0..keys.len()).collect();
        RangeTree1D {
            keys,
            order,
            root: Some(root),
        }
    }

    /// The inner nodes, each once.
    fn inner_nodes(&self) -> Vec<&Node<K>> {
        let mut out = Vec::new();
        let mut stack: Vec<&Node<K>> = self.root.iter().map(AsRef::as_ref).collect();
        while let Some(node) = stack.pop() {
            if let Node::Internal { left, right, .. } = node {
                out.push(node);
                stack.push(left);
                stack.push(right);
            }
        }
        out
    }

    /// Box invariant 1: every inner key separates its two sides: nothing on its left is larger,
    /// nothing on its right is smaller. At every inner node, every key below the left side is
    /// `≤` the split, and every key below the right `≥` it. Lean: `KeysSeparate`.
    #[must_use]
    pub fn is_keys_separate(&self) -> bool {
        let below = |child: &Node<K>| {
            let (start, end) = child.range();
            self.keys.get(start..end)
        };
        self.inner_nodes().into_iter().all(|node| match node {
            Node::Internal {
                split, left, right, ..
            } => {
                below(left).is_some_and(|ks| ks.iter().all(|k| k <= split))
                    && below(right).is_some_and(|ks| ks.iter().all(|k| split <= k))
            }
            Node::Leaf { .. } => true,
        })
    }

    /// Box invariant 2: every inner node splits the keys below it in half. At every inner node the
    /// left side holds `⌈n/2⌉` of the node's `n` keys and the right side the rest: the right count
    /// is at most the left, and the left at most one more. Lean: `SplitsHalve`.
    #[must_use]
    pub fn is_splits_halve(&self) -> bool {
        let count = |n: &Node<K>| {
            let (start, end) = n.range();
            end.saturating_sub(start)
        };
        self.inner_nodes().into_iter().all(|node| match node {
            Node::Internal { left, right, .. } => {
                let (l, r) = (count(left), count(right));
                r <= l && l <= r + 1
            }
            Node::Leaf { .. } => true,
        })
    }

    /// Lean `RangeTree1D.Valid`: [`RangeTree1D::is_keys_separate`] and
    /// [`RangeTree1D::is_splits_halve`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`RangeTree1D::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (keys_separate)"` or `"invariant 2 (splits_halve)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_keys_separate() {
            return Err("invariant 1 (keys_separate)");
        }
        if !self.is_splits_halve() {
            return Err("invariant 2 (splits_halve)");
        }
        Ok(())
    }

    /// The canonical subtrees `FINDSPLITNODE` and `1DRANGEQUERY` report, as the sorted-position
    /// range each covers.
    fn canonical_subtrees(&self, lo: &K, hi: &K) -> Vec<(usize, usize)> {
        let mut ranges = Vec::new();
        let Some(root) = &self.root else {
            return ranges;
        };
        if lo > hi {
            return ranges;
        }
        let mut v = root.as_ref();
        while let Node::Internal {
            split, left, right, ..
        } = v
        {
            if hi < split {
                v = left;
            } else if lo > split {
                v = right;
            } else {
                break;
            }
        }
        self.walk_from_split(v, lo, hi, &mut ranges);
        ranges
    }

    /// `1DRANGEQUERY` from the split node `v`.
    fn walk_from_split<'a>(
        &'a self,
        v: &'a Node<K>,
        lo: &K,
        hi: &K,
        out: &mut Vec<(usize, usize)>,
    ) {
        let (left, right) = match v {
            Node::Leaf { .. } => return self.report_leaf(v, lo, hi, out),
            Node::Internal { left, right, .. } => (left.as_ref(), right.as_ref()),
        };
        let mut w = left;
        loop {
            match w {
                Node::Leaf { .. } => break self.report_leaf(w, lo, hi, out),
                Node::Internal {
                    split, left, right, ..
                } => {
                    if lo <= split {
                        out.push(right.range());
                        w = left;
                    } else {
                        w = right;
                    }
                }
            }
        }
        let mut w = right;
        loop {
            match w {
                Node::Leaf { .. } => break self.report_leaf(w, lo, hi, out),
                Node::Internal {
                    split, left, right, ..
                } => {
                    if split <= hi {
                        out.push(left.range());
                        w = right;
                    } else {
                        w = left;
                    }
                }
            }
        }
    }

    fn report_leaf(&self, v: &Node<K>, lo: &K, hi: &K, out: &mut Vec<(usize, usize)>) {
        let (s, e) = v.range();
        if lo <= &self.keys[s] && &self.keys[s] <= hi {
            out.push((s, e));
        }
    }
}

impl<K> Default for RangeTree1D<K> {
    /// The tree with no keys.
    fn default() -> Self {
        RangeTree1D {
            keys: Vec::new(),
            order: Vec::new(),
            root: None,
        }
    }
}

impl<K: Ord + Clone> FromIterator<K> for RangeTree1D<K> {
    /// [`RangeTree1D::new`] on the keys in iteration order.
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        Self::new(iter.into_iter().collect())
    }
}

/// A node of the 2D tree: the x-tree's node, with the associated y-tree of its subtree.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Node2<K> {
    Leaf {
        pos: usize,
    },
    Internal {
        split: K,
        /// The y-keys of this subtree's points, as a 1D tree whose `order` holds the points' ids,
        /// so a query on it reports them directly.
        assoc: RangeTree1D<K>,
        left: Box<Node2<K>>,
        right: Box<Node2<K>>,
    },
}

/// A static 2D range tree: an x-tree with associated y-trees (dBCKO §5.3).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeTree2D<K> {
    /// The points sorted by x (stably), with their ids.
    sorted: Vec<((K, K), usize)>,
    root: Option<Box<Node2<K>>>,
}

impl<K: Ord + Clone> RangeTree2D<K> {
    /// The tree's shape; `None` for no points. Public for tests; not part of the
    /// API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn shape(&self) -> Option<Shape2D<K>> {
        fn walk<K: Clone>(sorted: &[((K, K), usize)], v: &Node2<K>) -> Shape2D<K> {
            match v {
                Node2::Leaf { pos } => Shape2D::Leaf(sorted[*pos].1),
                Node2::Internal {
                    split,
                    assoc,
                    left,
                    right,
                } => Shape2D::Node {
                    split: split.clone(),
                    ids: assoc.order.clone(),
                    left: Box::new(walk(sorted, left)),
                    right: Box::new(walk(sorted, right)),
                },
            }
        }
        self.root.as_ref().map(|r| walk(&self.sorted, r))
    }

    /// Build from points `(x, y)`, in any order, repeats allowed.
    #[must_use]
    pub fn new(points: Vec<(K, K)>) -> Self {
        let mut sorted: Vec<((K, K), usize)> = points.into_iter().zip(0..).collect();
        sorted.sort_by(|a, b| a.0 .0.cmp(&b.0 .0));
        let root = (!sorted.is_empty()).then(|| Box::new(Self::build(&sorted, 0, sorted.len()).0));
        RangeTree2D { sorted, root }
    }

    /// The subtree over x-sorted positions `[start, end)`, and its points' `(y, id)` in
    /// y order, equal y in x order: the list its parent merges.
    fn build(sorted: &[((K, K), usize)], start: usize, end: usize) -> (Node2<K>, Vec<(K, usize)>) {
        if end - start == 1 {
            let ((_, y), id) = &sorted[start];
            return (Node2::Leaf { pos: start }, vec![(y.clone(), *id)]);
        }
        let m = start + (end - start).div_ceil(2);
        let (left, from_left) = Self::build(sorted, start, m);
        let (right, from_right) = Self::build(sorted, m, end);
        let by_y = merge_by_y(from_left, from_right);
        let node = Node2::Internal {
            split: sorted[m - 1].0 .0.clone(),
            assoc: RangeTree1D::from_sorted(
                by_y.iter().map(|p| p.0.clone()).collect(),
                by_y.iter().map(|p| p.1).collect(),
            ),
            left: Box::new(left),
            right: Box::new(right),
        };
        (node, by_y)
    }

    /// The number of points.
    #[must_use]
    pub fn len(&self) -> usize {
        self.sorted.len()
    }

    /// Whether there are no points.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.sorted.is_empty()
    }

    /// The x-tree's height.
    #[must_use]
    pub fn depth(&self) -> usize {
        fn d<K>(n: &Node2<K>) -> usize {
            match n {
                Node2::Leaf { .. } => 0,
                Node2::Internal { left, right, .. } => 1 + d(left).max(d(right)),
            }
        }
        self.root.as_ref().map_or(0, |r| d(r))
    }

    /// The x-sorted positions of the points below `v`, left to right.
    fn below(v: &Node2<K>, out: &mut Vec<usize>) {
        match v {
            Node2::Leaf { pos } => out.push(*pos),
            Node2::Internal { left, right, .. } => {
                Self::below(left, out);
                Self::below(right, out);
            }
        }
    }

    /// Whether `holds` is true at every inner node, given the node, its split, its tree on y and
    /// the positions below its two sides. The x-tree is balanced, so this recurses `log₂ n` deep.
    fn every_inner<F>(&self, holds: F) -> bool
    where
        F: Fn(&K, &RangeTree1D<K>, &[usize], &[usize]) -> bool,
    {
        fn go<K: Ord + Clone, F>(v: &Node2<K>, holds: &F) -> bool
        where
            F: Fn(&K, &RangeTree1D<K>, &[usize], &[usize]) -> bool,
        {
            match v {
                Node2::Leaf { .. } => true,
                Node2::Internal {
                    split,
                    assoc,
                    left,
                    right,
                } => {
                    let (mut l, mut r) = (Vec::new(), Vec::new());
                    RangeTree2D::below(left, &mut l);
                    RangeTree2D::below(right, &mut r);
                    holds(split, assoc, &l, &r) && go(left, holds) && go(right, holds)
                }
            }
        }
        self.root.as_ref().is_none_or(|r| go(r, &holds))
    }

    /// Box invariant 1, on the x-tree: every inner key separates its two sides: no point on its
    /// left has a larger x, none on its right a smaller one.
    #[must_use]
    pub fn is_keys_separate(&self) -> bool {
        let x = |p: usize| self.sorted.get(p).map(|((x, _), _)| x);
        self.every_inner(|split, _, l, r| {
            l.iter().all(|&p| x(p).is_some_and(|x| x <= split))
                && r.iter().all(|&p| x(p).is_some_and(|x| split <= x))
        })
    }

    /// Box invariant 2, on the x-tree: every inner node splits the points below it in half,
    /// `⌈n/2⌉` of its `n` points on the left and the rest on the right.
    #[must_use]
    pub fn is_splits_halve(&self) -> bool {
        self.every_inner(|_, _, l, r| r.len() <= l.len() && l.len() <= r.len() + 1)
    }

    /// Not in the box: every inner node's tree on y holds exactly the points below the
    /// node, sorted by y, each with its id, and is itself a valid 1D range tree. This is what
    /// lets a query read a whole subtree off its tree on y.
    #[must_use]
    pub fn is_y_trees_hold_subtrees(&self) -> bool {
        self.every_inner(|_, assoc, l, r| {
            let mut below: Option<Vec<(&K, usize)>> = l
                .iter()
                .chain(r)
                .map(|&p| self.sorted.get(p).map(|((_, y), id)| (y, *id)))
                .collect();
            let mut stored: Vec<(&K, usize)> =
                assoc.keys.iter().zip(assoc.order.iter().copied()).collect();
            let sorted_by_y = assoc.keys.windows(2).all(|w| w[0] <= w[1]);
            stored.sort_unstable();
            if let Some(b) = below.as_mut() {
                b.sort_unstable();
            }
            assoc.keys.len() == assoc.order.len()
                && sorted_by_y
                && below.is_some_and(|b| b == stored)
                && assoc.is_valid()
        })
    }

    /// [`RangeTree2D::is_keys_separate`], [`RangeTree2D::is_splits_halve`] and
    /// [`RangeTree2D::is_y_trees_hold_subtrees`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`RangeTree2D::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (keys_separate)"`, `"invariant 2 (splits_halve)"` or
    /// `"not in the box (y_trees_hold_subtrees)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        let pieces = [
            (
                Self::is_keys_separate as fn(&Self) -> bool,
                "invariant 1 (keys_separate)",
            ),
            (Self::is_splits_halve, "invariant 2 (splits_halve)"),
            (
                Self::is_y_trees_hold_subtrees,
                "not in the box (y_trees_hold_subtrees)",
            ),
        ];
        match pieces.iter().find(|(holds, _)| !holds(self)) {
            Some(&(_, name)) => Err(name),
            None => Ok(()),
        }
    }

    /// The ids of the points with `lo.0 ≤ x ≤ hi.0` and `lo.1 ≤ y ≤ hi.1`, each once, in the
    /// order the walk reports them (`2DRANGEQUERY`); sort them if order matters.
    /// `O(log² n + k)` for `k` reported. Lean: `RangeTree2D.query_build` (`Query2DSpec`: every
    /// stored point in the rectangle, each as often as stored, in some order).
    #[must_use]
    pub fn query(&self, lo: (&K, &K), hi: (&K, &K)) -> Vec<usize> {
        let mut out = Vec::new();
        let Some(root) = &self.root else { return out };
        if lo.0 > hi.0 || lo.1 > hi.1 {
            return out;
        }
        let mut v = root.as_ref();
        while let Node2::Internal {
            split, left, right, ..
        } = v
        {
            if hi.0 < split {
                v = left;
            } else if lo.0 > split {
                v = right;
            } else {
                break;
            }
        }
        match v {
            Node2::Leaf { .. } => self.report_leaf(v, lo, hi, &mut out),
            Node2::Internal { left, right, .. } => {
                let mut w = left.as_ref();
                loop {
                    match w {
                        Node2::Leaf { .. } => break self.report_leaf(w, lo, hi, &mut out),
                        Node2::Internal {
                            split, left, right, ..
                        } => {
                            if lo.0 <= split {
                                self.report_subtree(right, lo, hi, &mut out);
                                w = left;
                            } else {
                                w = right;
                            }
                        }
                    }
                }
                let mut w = right.as_ref();
                loop {
                    match w {
                        Node2::Leaf { .. } => break self.report_leaf(w, lo, hi, &mut out),
                        Node2::Internal {
                            split, left, right, ..
                        } => {
                            if split <= hi.0 {
                                self.report_subtree(left, lo, hi, &mut out);
                                w = right;
                            } else {
                                w = left;
                            }
                        }
                    }
                }
            }
        }
        out
    }

    /// A canonical subtree: its x-range is inside the query, so query its associated y-tree.
    fn report_subtree(&self, v: &Node2<K>, lo: (&K, &K), hi: (&K, &K), out: &mut Vec<usize>) {
        match v {
            Node2::Leaf { .. } => self.report_leaf(v, lo, hi, out),
            Node2::Internal { assoc, .. } => out.extend(assoc.query_iter(lo.1, hi.1)),
        }
    }

    fn report_leaf(&self, v: &Node2<K>, lo: (&K, &K), hi: (&K, &K), out: &mut Vec<usize>) {
        if let Node2::Leaf { pos } = v {
            let ((x, y), id) = &self.sorted[*pos];
            if lo.0 <= x && x <= hi.0 && lo.1 <= y && y <= hi.1 {
                out.push(*id);
            }
        }
    }
}

impl<K> Default for RangeTree2D<K> {
    /// The tree with no points.
    fn default() -> Self {
        RangeTree2D {
            sorted: Vec::new(),
            root: None,
        }
    }
}

impl<K: Ord + Clone> FromIterator<(K, K)> for RangeTree2D<K> {
    /// [`RangeTree2D::new`] on the points in iteration order.
    fn from_iter<I: IntoIterator<Item = (K, K)>>(iter: I) -> Self {
        Self::new(iter.into_iter().collect())
    }
}

/// Two y-sorted lists as one, the left's first on equal y: one comparison per element taken.
fn merge_by_y<K: Ord>(left: Vec<(K, usize)>, right: Vec<(K, usize)>) -> Vec<(K, usize)> {
    let mut out = Vec::with_capacity(left.len() + right.len());
    let (mut l, mut r) = (left.into_iter().peekable(), right.into_iter().peekable());
    while let (Some(a), Some(b)) = (l.peek(), r.peek()) {
        if b.0 < a.0 {
            out.extend(r.next());
        } else {
            out.extend(l.next());
        }
    }
    out.extend(l);
    out.extend(r);
    out
}

#[cfg(test)]
#[path = "unit_tests/range_tree.rs"]
mod tests;
