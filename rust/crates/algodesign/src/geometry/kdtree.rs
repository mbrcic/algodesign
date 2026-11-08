//! The k-d tree in de Berg et al.'s form (dBCKO §5.2, `BUILDKDTREE` p. 100 and `SEARCHKDTREE`
//! p. 103; Bentley 1975): points in the leaves, in buckets of at most `bucket` (Friedman, Bentley
//! and Finkel 1977; 1 is dBCKO's tree; [`KdTree::new`] uses [`DEFAULT_BUCKET`]), and in each
//! internal node a splitting line on axis
//! `depth mod d` at the lower median of the points below. Points equal to a split may sit on
//! either side, so the tree stays balanced however many share a coordinate.
//!
//! The tree's invariant is Lean `KDTree.Valid` (`KDTree/Spec.lean`): box invariant 1, every cut
//! divides the points below it ([`KdTree::is_cuts_separate`], `CutsSeparate`), and box invariant
//! 2, every cut splits them in half ([`KdTree::is_cuts_halve`], `CutsHalve`). Nearest neighbors
//! come by best-first search (Hjaltason–Samet 1999), which stops when the nearest waiting region
//! is strictly farther than the `k`-th best. It takes a region off the queue and walks down its
//! nearer sides to a leaf, queueing each farther side on the way (Arya et al. 1998's priority
//! search, §5): the nearer side's bound is the region's own, the least waiting, so this opens the
//! regions the queue would, without putting each nearer side in and taking it straight out. The
//! book's Python queues both sides, as the chapter traces; the Rust descends for speed. A run of
//! it, the tree, the query and a [`SearchState`] (Lean `BestFirst.Run`), keeps Lean
//! `BestFirst.Valid` (`KDTree/Search.lean`): box invariant 3, [`is_nothing_closer_skipped`], and
//! three pieces not in the box, [`is_queued_cuts_separate`], [`is_offsets_bound`] and
//! [`is_each_point_once`].
//!
//! **Against the Python, and how fast.** Four differences. Leaves hold [`DEFAULT_BUCKET`] = 8
//! points where the Python's default is 1, so the same points give different trees and different
//! [`SearchStats`]: build both with `with_bucket(points, 1)` to compare. The search descends the
//! nearer sides, as above, and `search_states` records a state after each leaf, where the Python's
//! records one after each region opened. The median is selected in linear time
//! (`select_nth_unstable_by`), and the two trees then agree up to which tied points go left.
//! [`KdTree::range`] reports in walk order; the Python's `range` sorts.
//! `cargo bench -p algodesign --bench geometry -- kdtree` times both leaf sizes beside the scan.

use crate::geometry::{
    point::{check_query, sq_dist, sum4, Points},
    scan::{Neighbor, TopK},
};
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// The leaf size [`KdTree::new`] uses. dBCKO's tree has one point per leaf; a leaf of 8 keeps its
/// points together in memory, scanned in one pass, and the tree has about an eighth of the nodes.
pub const DEFAULT_BUCKET: usize = 8;

/// A node over the positions `[start, end)` of the tree's permutation: an `enum` with boxed
/// children, because a leaf carries data. The build bounds the height by `⌈log₂ n⌉`.
#[derive(Debug, Clone, PartialEq)]
enum Node {
    /// A bucket of points.
    Leaf { start: usize, end: usize },
    /// A splitting line `x[axis] = split`.
    Internal {
        axis: usize,
        split: f64,
        start: usize,
        end: usize,
        left: Box<Node>,
        right: Box<Node>,
    },
}

impl Node {
    fn range(&self) -> (usize, usize) {
        match self {
            Node::Leaf { start, end } | Node::Internal { start, end, .. } => (*start, *end),
        }
    }

    fn depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 0,
            Node::Internal { left, right, .. } => 1 + left.depth().max(right.depth()),
        }
    }
}

/// A k-d tree's shape, as the Lean `KDTree` spells it: a node holds its axis and split value; a
/// leaf lists the ids of the points in its bucket (one, in dBCKO's tree, where the Lean leaf holds
/// that point). Public for tests; not part of the API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq)]
pub enum KdShape {
    /// A bucket: the ids of its points.
    Leaf(Vec<usize>),
    /// A splitting line `x[axis] = split`.
    Node {
        /// The coordinate the node splits on.
        axis: usize,
        /// The split value, the lower median of that coordinate below the node.
        split: f64,
        /// The points with `x[axis] ≤ split`.
        left: Box<KdShape>,
        /// The points with `x[axis] ≥ split`.
        right: Box<KdShape>,
    },
}

/// What a search did: the points it measured and the regions it opened.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SearchStats {
    /// Points measured: those whose distance to the query was computed.
    pub points_measured: usize,
    /// Regions opened: every node the search stands on, whether taken from the queue or reached
    /// by walking down a nearer side (the count of the Lean's steps).
    pub regions_opened: usize,
}

/// One step down the tree, to a node's left or right child.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    /// The child with `x[axis] ≤ split`.
    Left,
    /// The child with `x[axis] ≥ split`.
    Right,
}

/// A region waiting in a best-first search: the subtree reached from the root along `path`, and
/// the query's per-axis offsets from it. Lean `BestFirst.Region`.
#[derive(Debug, Clone, PartialEq)]
pub struct Region {
    /// The way down from the root to the region's subtree.
    pub path: Vec<Side>,
    /// How far the query is from the region along each axis (signed; only the square is used).
    pub offsets: Vec<f64>,
}

/// A best-first search's running state: the ids measured so far, in the order
/// measured, and the regions waiting, in the order they were queued. Lean `BestFirst.State`; with
/// the tree and the query it is a Lean `BestFirst.Run`, the three arguments every search piece
/// below takes.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct SearchState {
    /// The points whose distance to the query has been computed.
    pub measured: Vec<usize>,
    /// The regions waiting to be opened.
    pub queue: Vec<Region>,
}

/// A k-d tree over a [`Points`] set. Its build keeps [`KdTree::is_valid`]; only
/// `from_shape_unchecked` (feature `unchecked`) can break it, and only `search_states` (the
/// same feature) shows a search's running state. The feature is for tests that break or watch the
/// tree on purpose: `cargo test --features unchecked`.
#[derive(Debug, Clone, PartialEq)]
pub struct KdTree {
    points: Points,
    /// The point ids, ordered so that every node's points are a contiguous range.
    perm: Vec<usize>,
    root: Node,
    bucket: usize,
}

impl KdTree {
    /// Build with leaves of at most [`DEFAULT_BUCKET`] points (`with_bucket(points, 1)` is
    /// dBCKO's tree).
    #[must_use]
    pub fn new(points: Points) -> Self {
        KdTree::with_bucket(points, DEFAULT_BUCKET)
    }

    /// Build with leaves of at most `bucket` points.
    ///
    /// # Panics
    /// If `bucket == 0`.
    #[must_use]
    pub fn with_bucket(points: Points, bucket: usize) -> Self {
        assert!(bucket > 0, "a k-d tree's bucket size must be at least 1");
        let mut perm: Vec<usize> = (0..points.len()).collect();
        let root = build(&points, &mut perm, 0, 0, bucket);
        KdTree {
            points,
            perm,
            root,
            bucket,
        }
    }

    /// The number of points.
    #[must_use]
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Whether there are no points.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// The dimension.
    #[must_use]
    pub fn dim(&self) -> usize {
        self.points.dim()
    }

    /// The leaf size the tree was built with.
    #[must_use]
    pub fn bucket(&self) -> usize {
        self.bucket
    }

    /// The tree's height: at most `⌈log₂ n⌉`.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.root.depth()
    }

    /// The tree's shape, each leaf listing the ids of its bucket (an empty tree is one
    /// empty leaf). Public for tests; not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn shape(&self) -> KdShape {
        fn walk(perm: &[usize], v: &Node) -> KdShape {
            match v {
                Node::Leaf { start, end } => KdShape::Leaf(perm[*start..*end].to_vec()),
                Node::Internal {
                    axis,
                    split,
                    left,
                    right,
                    ..
                } => KdShape::Node {
                    axis: *axis,
                    split: *split,
                    left: Box::new(walk(perm, left)),
                    right: Box::new(walk(perm, right)),
                },
            }
        }
        walk(&self.perm, &self.root)
    }

    /// The tree `shape` writes out over `points`, everything as given, unchecked; its bucket is
    /// its largest leaf. Feature `unchecked`.
    ///
    /// # Panics
    /// If a leaf names an id outside `points`, or a node an axis outside its dimension.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_shape_unchecked(points: Points, shape: &KdShape) -> Self {
        fn walk(points: &Points, s: &KdShape, perm: &mut Vec<usize>, bucket: &mut usize) -> Node {
            let start = perm.len();
            match s {
                KdShape::Leaf(ix) => {
                    assert!(
                        ix.iter().all(|&i| i < points.len()),
                        "a leaf names a point outside the set"
                    );
                    perm.extend(ix);
                    *bucket = (*bucket).max(ix.len());
                    Node::Leaf {
                        start,
                        end: perm.len(),
                    }
                }
                KdShape::Node {
                    axis,
                    split,
                    left,
                    right,
                } => {
                    assert!(*axis < points.dim(), "a node splits outside the dimension");
                    let left = Box::new(walk(points, left, perm, bucket));
                    let right = Box::new(walk(points, right, perm, bucket));
                    Node::Internal {
                        axis: *axis,
                        split: *split,
                        start,
                        end: perm.len(),
                        left,
                        right,
                    }
                }
            }
        }
        let mut perm = Vec::new();
        let mut bucket = 1;
        let root = walk(&points, shape, &mut perm, &mut bucket);
        KdTree {
            points,
            perm,
            root,
            bucket,
        }
    }

    /// The points the tree was built from.
    #[must_use]
    pub fn points(&self) -> &Points {
        &self.points
    }

    /// The ids of the points below `node`, or `None` if its range lies outside the
    /// permutation.
    fn below(&self, node: &Node) -> Option<&[usize]> {
        let (start, end) = node.range();
        self.perm.get(start..end)
    }

    /// Coordinate `axis` of point `i`, or `None` outside the set or the dimension.
    fn coord(&self, i: usize, axis: usize) -> Option<f64> {
        (i < self.points.len() && axis < self.dim()).then(|| self.points.get(i)[axis])
    }

    /// Box invariant 1: every cut divides the points below it: none on its left lies past the
    /// cut, none on its right lies before it. At every internal node, every point below the left
    /// side has the node's coordinate `≤` the split, and every point below the right `≥` it.
    /// Lean: `CutsSeparate`.
    #[must_use]
    pub fn is_cuts_separate(&self) -> bool {
        self.cuts_separate_below(&self.root)
    }

    /// [`KdTree::is_cuts_separate`] on the subtree at `top`.
    fn cuts_separate_below(&self, top: &Node) -> bool {
        let mut stack = vec![top];
        while let Some(node) = stack.pop() {
            if let Node::Internal {
                axis,
                split,
                left,
                right,
                ..
            } = node
            {
                let side = |child: &Node, holds: fn(f64, f64) -> bool| {
                    self.below(child).is_some_and(|ix| {
                        ix.iter()
                            .all(|&i| self.coord(i, *axis).is_some_and(|x| holds(x, *split)))
                    })
                };
                if !side(left, |x, s| x <= s) || !side(right, |x, s| s <= x) {
                    return false;
                }
                stack.push(left);
                stack.push(right);
            }
        }
        true
    }

    /// Box invariant 2: every cut splits the points below it in half. At every internal node the
    /// left side holds `⌈n/2⌉` of the node's `n` points and the right side the rest: the right
    /// count is at most the left, and the left at most one more. Lean: `CutsHalve`.
    #[must_use]
    pub fn is_cuts_halve(&self) -> bool {
        let count = |n: &Node| {
            let (start, end) = n.range();
            end.saturating_sub(start)
        };
        let mut stack = vec![&self.root];
        while let Some(node) = stack.pop() {
            if let Node::Internal { left, right, .. } = node {
                let (l, r) = (count(left), count(right));
                if r > l || l > r + 1 {
                    return false;
                }
                stack.push(left);
                stack.push(right);
            }
        }
        true
    }

    /// Lean `KDTree.Valid`: [`KdTree::is_cuts_separate`] and [`KdTree::is_cuts_halve`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`KdTree::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (cuts_separate)"` or `"invariant 2 (cuts_halve)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_cuts_separate() {
            return Err("invariant 1 (cuts_separate)");
        }
        if !self.is_cuts_halve() {
            return Err("invariant 2 (cuts_halve)");
        }
        Ok(())
    }

    /// The node at the end of `path`, or `None` if the path leaves the tree.
    fn node_at(&self, path: &[Side]) -> Option<&Node> {
        let mut node = &self.root;
        for side in path {
            node = match (node, side) {
                (Node::Internal { left, .. }, Side::Left) => left,
                (Node::Internal { right, .. }, Side::Right) => right,
                (Node::Leaf { .. }, _) => return None,
            };
        }
        Some(node)
    }

    /// The ids of the points inside the box `[lo, hi]`, inclusive, each once, in the order the
    /// walk reports them (`SEARCHKDTREE`: a region inside the box is reported whole, never sorted).
    /// `O(n^(1−1/d) + k)` for `k` reported, dBCKO's bound (§5.2). Sort the answer if you need it
    /// in id order; the Python's `range` returns it sorted, for teaching. Lean:
    /// `rangeQuery_perm_filter`.
    ///
    /// # Panics
    /// If `lo` or `hi` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn range(&self, lo: &[f64], hi: &[f64]) -> Vec<usize> {
        check_query(self.dim(), lo);
        check_query(self.dim(), hi);
        let mut out = Vec::new();
        let mut rlo = vec![f64::NEG_INFINITY; self.dim()];
        let mut rhi = vec![f64::INFINITY; self.dim()];
        self.search_kd_tree(&self.root, lo, hi, &mut rlo, &mut rhi, &mut out);
        out
    }

    fn search_kd_tree(
        &self,
        node: &Node,
        lo: &[f64],
        hi: &[f64],
        rlo: &mut [f64],
        rhi: &mut [f64],
        out: &mut Vec<usize>,
    ) {
        let (start, end) = node.range();
        let contained = (0..lo.len()).all(|a| lo[a] <= rlo[a] && rhi[a] <= hi[a]);
        if contained {
            out.extend_from_slice(&self.perm[start..end]);
            return;
        }
        match node {
            Node::Leaf { .. } => {
                for &i in &self.perm[start..end] {
                    let p = self.points.get(i);
                    if (0..lo.len()).all(|a| lo[a] <= p[a] && p[a] <= hi[a]) {
                        out.push(i);
                    }
                }
            }
            Node::Internal {
                axis,
                split,
                left,
                right,
                ..
            } => {
                let a = *axis;
                if lo[a] <= *split {
                    let saved = rhi[a];
                    rhi[a] = *split;
                    self.search_kd_tree(left, lo, hi, rlo, rhi, out);
                    rhi[a] = saved;
                }
                if *split <= hi[a] {
                    let saved = rlo[a];
                    rlo[a] = *split;
                    self.search_kd_tree(right, lo, hi, rlo, rhi, out);
                    rlo[a] = saved;
                }
            }
        }
    }

    /// The id of a nearest point, the one stored first on ties.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn nearest(&self, q: &[f64]) -> Option<usize> {
        self.k_nearest(q, 1).first().map(|n| n.id)
    }

    /// The `min(k, n)` nearest points, best first, ranked by squared distance and then id:
    /// the scan's answer, found by best-first search.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn k_nearest(&self, q: &[f64], k: usize) -> Vec<Neighbor> {
        self.k_nearest_with_stats(q, k).0
    }

    /// [`KdTree::k_nearest`], with the counts of what the search did. The search keeps Lean
    /// `BestFirst.Valid` (`valid_start`, `valid_visit`) and answers the scan
    /// (`search_kNearest_eq_scan`).
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn k_nearest_with_stats(&self, q: &[f64], k: usize) -> (Vec<Neighbor>, SearchStats) {
        self.k_nearest_observed(q, k, |_, _, _| {})
    }

    /// The running state of [`KdTree::k_nearest`]'s search: first the start, then the state after
    /// each leaf it measured (on the way down to a leaf, a nearer side is in hand, neither queued
    /// nor measured). Empty when `k == 0` or the tree is. Behind the `unchecked` feature.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn search_states(&self, q: &[f64], k: usize) -> Vec<SearchState> {
        let mut states = Vec::new();
        let mut measured = Vec::new();
        let dim = self.dim();
        let _ = self.k_nearest_observed(q, k, |queue, offs, now| {
            measured.extend_from_slice(now);
            let mut waiting: Vec<&QueueEntry> = queue.iter().collect();
            waiting.sort_by_key(|r| r.seq);
            let queue = waiting
                .iter()
                .map(|r| Region {
                    path: self.path_to(r.node),
                    offsets: offs[r.off..r.off + dim].to_vec(),
                })
                .collect();
            states.push(SearchState {
                measured: measured.clone(),
                queue,
            });
        });
        states
    }

    /// The way down from the root to `target`, found by its address.
    #[cfg(any(test, feature = "unchecked"))]
    fn path_to(&self, target: &Node) -> Vec<Side> {
        let mut stack = vec![(&self.root, Vec::new())];
        while let Some((node, path)) = stack.pop() {
            if std::ptr::eq(node, target) {
                return path;
            }
            if let Node::Internal { left, right, .. } = node {
                for (child, side) in [(left, Side::Left), (right, Side::Right)] {
                    let mut p = path.clone();
                    p.push(side);
                    stack.push((child, p));
                }
            }
        }
        unreachable!("a queued region is a node of this tree")
    }

    /// The best-first search, calling `seen` with the queue, the offsets arena its regions index
    /// and the ids just measured, once at the start and once after each leaf it measures.
    ///
    /// The regions' offsets live in one arena per search, `dim` entries per slot, so a far side
    /// costs a copy, not an allocation. A region keeps its slot while it is queued and while its
    /// walk goes down the near sides (which keep the parent's offsets); the slot is free again
    /// when the walk reaches its leaf, so the arena holds at most one slot per queued region plus
    /// the one walking.
    fn k_nearest_observed(
        &self,
        q: &[f64],
        k: usize,
        mut seen: impl FnMut(&BinaryHeap<QueueEntry<'_>>, &[f64], &[usize]),
    ) -> (Vec<Neighbor>, SearchStats) {
        check_query(self.dim(), q);
        let mut stats = SearchStats::default();
        if k == 0 || self.is_empty() {
            return (Vec::new(), stats);
        }
        let mut top = TopK::new(k);
        let mut queue = BinaryHeap::new();
        let mut offs = Offsets::new(self.dim());
        let mut seq = 0;
        queue.push(QueueEntry {
            bound: 0.0,
            seq,
            node: &self.root,
            off: 0,
        });
        seen(&queue, &offs.arena, &[]);
        while let Some(QueueEntry {
            bound: b,
            mut node,
            off,
            ..
        }) = queue.pop()
        {
            if top.is_full() && top.worst().is_some_and(|w| b > w.sq_dist) {
                break;
            }
            loop {
                stats.regions_opened += 1;
                match node {
                    Node::Leaf { start, end } => {
                        for &id in &self.perm[*start..*end] {
                            stats.points_measured += 1;
                            top.offer(Neighbor {
                                id,
                                sq_dist: sq_dist(self.points.get(id), q),
                            });
                        }
                        offs.release(off);
                        seen(&queue, &offs.arena, &self.perm[*start..*end]);
                        break;
                    }
                    Node::Internal {
                        axis,
                        split,
                        left,
                        right,
                        ..
                    } => {
                        let (near, far) = if q[*axis] <= *split {
                            (left, right)
                        } else {
                            (right, left)
                        };
                        let far_off = offs.far(off, *axis, *split, q);
                        seq += 1;
                        queue.push(QueueEntry {
                            bound: bound(offs.get(far_off)),
                            seq,
                            node: far,
                            off: far_off,
                        });
                        node = near;
                    }
                }
            }
        }
        (top.into_sorted(), stats)
    }
}

/// The queued region's subtree and the ids below it, or `None` if its path leaves the
/// tree or its offsets have the wrong dimension.
fn region_of<'a>(tree: &'a KdTree, r: &Region) -> Option<(&'a Node, &'a [usize])> {
    let node = tree.node_at(&r.path)?;
    (r.offsets.len() == tree.dim())
        .then(|| tree.below(node).map(|ix| (node, ix)))
        .flatten()
}

/// Box invariant 3: the search never skips a region that could hold a point closer than the best
/// found so far. Every stored point is already measured, or sits in a queued region whose bound is
/// at most its squared distance to `q`. Lean: `BestFirst.NothingCloserSkipped`.
#[must_use]
pub fn is_nothing_closer_skipped(tree: &KdTree, q: &[f64], state: &SearchState) -> bool {
    if q.len() != tree.dim() {
        return false;
    }
    tree.perm.iter().all(|&i| {
        let held = |r: &Region| {
            region_of(tree, r).is_some_and(|(_, ix)| {
                ix.contains(&i) && bound(&r.offsets) <= sq_dist(tree.points.get(i), q)
            })
        };
        i < tree.len() && (state.measured.contains(&i) || state.queue.iter().any(held))
    })
}

/// Not in the box: every queued region's cuts separate its points. Lean:
/// `BestFirst.QueuedCutsSeparate`.
#[must_use]
pub fn is_queued_cuts_separate(tree: &KdTree, q: &[f64], state: &SearchState) -> bool {
    q.len() == tree.dim()
        && state
            .queue
            .iter()
            .all(|r| region_of(tree, r).is_some_and(|(node, _)| tree.cuts_separate_below(node)))
}

/// Not in the box: every queued region's offsets are at most each of its points' distances
/// from `q`, axis by axis. Lean: `BestFirst.OffsetsBound`.
#[must_use]
pub fn is_offsets_bound(tree: &KdTree, q: &[f64], state: &SearchState) -> bool {
    q.len() == tree.dim()
        && state.queue.iter().all(|r| {
            region_of(tree, r).is_some_and(|(_, ix)| {
                ix.iter().all(|&i| {
                    (0..q.len()).all(|a| {
                        tree.coord(i, a)
                            .is_some_and(|x| r.offsets[a] * r.offsets[a] <= (x - q[a]) * (x - q[a]))
                    })
                })
            })
        })
}

/// Not in the box: the measured points and the queued regions' points are the stored
/// points, each once. Lean: `BestFirst.EachPointOnce`, which compares points; this compares
/// ids.
#[must_use]
pub fn is_each_point_once(tree: &KdTree, q: &[f64], state: &SearchState) -> bool {
    if q.len() != tree.dim() {
        return false;
    }
    let mut seen = state.measured.clone();
    for r in &state.queue {
        match tree.node_at(&r.path).and_then(|node| tree.below(node)) {
            Some(ix) => seen.extend_from_slice(ix),
            None => return false,
        }
    }
    let mut stored = tree.perm.clone();
    seen.sort_unstable();
    stored.sort_unstable();
    seen == stored
}

/// Lean `BestFirst.Valid`: [`is_nothing_closer_skipped`], [`is_queued_cuts_separate`],
/// [`is_offsets_bound`] and [`is_each_point_once`].
#[must_use]
pub fn is_search_valid(tree: &KdTree, q: &[f64], state: &SearchState) -> bool {
    check_search_valid(tree, q, state).is_ok()
}

/// [`is_search_valid`], naming the first piece that fails.
///
/// # Errors
///
/// `"invariant 3 (nothing_closer_skipped)"`, `"not in the box (queued_cuts_separate)"`,
/// `"not in the box (offsets_bound)"` or `"not in the box (each_point_once)"`.
pub fn check_search_valid(
    tree: &KdTree,
    q: &[f64],
    state: &SearchState,
) -> Result<(), &'static str> {
    if !is_nothing_closer_skipped(tree, q, state) {
        return Err("invariant 3 (nothing_closer_skipped)");
    }
    if !is_queued_cuts_separate(tree, q, state) {
        return Err("not in the box (queued_cuts_separate)");
    }
    if !is_offsets_bound(tree, q, state) {
        return Err("not in the box (offsets_bound)");
    }
    if !is_each_point_once(tree, q, state) {
        return Err("not in the box (each_point_once)");
    }
    Ok(())
}

/// Build over `perm`, whose positions start at `offset` in the whole permutation. Splits by
/// position: the first `⌈n/2⌉` points by the axis coordinate go left, and the split is the
/// largest of them, the lower median.
fn build(points: &Points, perm: &mut [usize], offset: usize, depth: usize, bucket: usize) -> Node {
    let n = perm.len();
    if n <= bucket {
        return Node::Leaf {
            start: offset,
            end: offset + n,
        };
    }
    let axis = depth % points.dim();
    let m = n.div_ceil(2);
    let coord = |i: &usize| points.get(*i)[axis];
    perm.select_nth_unstable_by(m - 1, |i, j| coord(i).total_cmp(&coord(j)));
    let split = coord(&perm[m - 1]);
    let (l, r) = perm.split_at_mut(m);
    Node::Internal {
        axis,
        split,
        start: offset,
        end: offset + n,
        left: Box::new(build(points, l, offset, depth + 1, bucket)),
        right: Box::new(build(points, r, offset + m, depth + 1, bucket)),
    }
}

/// One search's region offsets: slots of `dim` entries in one arena, the root's (all zero) at
/// slot 0, and the slots freed for reuse.
struct Offsets {
    dim: usize,
    arena: Vec<f64>,
    free: Vec<usize>,
}

impl Offsets {
    fn new(dim: usize) -> Self {
        Offsets {
            dim,
            arena: vec![0.0; dim],
            free: Vec::new(),
        }
    }

    /// The offsets in the slot starting at `slot`.
    fn get(&self, slot: usize) -> &[f64] {
        &self.arena[slot..slot + self.dim]
    }

    /// The far child's per-axis offsets, from its parent's at `parent`: along `axis`, the query
    /// is `split − q[axis]` away from the far side (signed; only its square is used), and the
    /// other axes keep the parent's offsets. Written to a freed slot if there is one, else to a
    /// new one at the arena's end; returns the slot.
    fn far(&mut self, parent: usize, axis: usize, split: f64, q: &[f64]) -> usize {
        let slot = if let Some(slot) = self.free.pop() {
            self.arena.copy_within(parent..parent + self.dim, slot);
            slot
        } else {
            let slot = self.arena.len();
            self.arena.extend_from_within(parent..parent + self.dim);
            slot
        };
        self.arena[slot + axis] = split - q[axis];
        slot
    }

    /// Free `slot` for reuse.
    fn release(&mut self, slot: usize) {
        self.free.push(slot);
    }
}

/// A region's lower bound: the sum of its squared offsets, in the order [`sq_dist`] sums.
/// Recomputed from the offsets, never updated incrementally: each offset is at most its axis's
/// part of a point's distance and rounding is monotone, so the bound never exceeds the computed
/// distance of a point in the region (Lean `far_side_bound`, `far_side_bound_left`,
/// `boxSqDist_le`).
fn bound(off: &[f64]) -> f64 {
    sum4(off, off, |o, _| o * o)
}

/// A [`Region`] as the best-first queue holds it: its node, its bound and where its offsets sit
/// in the search's arena, ordered so the `BinaryHeap` pops the smallest bound first (ties in push
/// order, for determinism).
struct QueueEntry<'a> {
    bound: f64,
    seq: usize,
    node: &'a Node,
    /// The start of its `dim` offsets in the search's arena.
    off: usize,
}

impl PartialEq for QueueEntry<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for QueueEntry<'_> {}

impl PartialOrd for QueueEntry<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QueueEntry<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .bound
            .total_cmp(&self.bound)
            .then(other.seq.cmp(&self.seq))
    }
}

#[cfg(test)]
#[path = "unit_tests/kdtree.rs"]
mod tests;
