use super::*;
use proptest::prelude::*;

/// The in-range input indices, in key order, ties in input order: the specification
/// (Lean `query_eq_filter`).
fn filter_1d(keys: &[i32], lo: i32, hi: i32) -> Vec<usize> {
    let mut v: Vec<(i32, usize)> = keys
        .iter()
        .copied()
        .zip(0..)
        .filter(|(k, _)| lo <= *k && *k <= hi)
        .collect();
    v.sort();
    v.into_iter().map(|x| x.1).collect()
}

/// de Berg's walk, unchanged (`hi ≤ split` sends it left), as a reference for distinct keys.
fn de_berg_query<K: Ord + Clone>(t: &RangeTree1D<K>, lo: &K, hi: &K) -> Vec<usize> {
    let mut ranges = Vec::new();
    if let Some(root) = &t.root {
        if lo <= hi {
            let mut v = root.as_ref();
            while let Node::Internal {
                split, left, right, ..
            } = v
            {
                if hi <= split {
                    v = left;
                } else if lo > split {
                    v = right;
                } else {
                    break;
                }
            }
            t.walk_from_split(v, lo, hi, &mut ranges);
        }
    }
    ranges.sort_unstable();
    ranges
        .into_iter()
        .flat_map(|(s, e)| t.order[s..e].iter().copied())
        .collect()
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean range-tree examples
    let t = RangeTree1D::new(vec![1, 3, 5, 7]);
    assert_eq!(t.query_keys(&3, &5), vec![&3, &5]);
    assert!(t.query(&6, &4).is_empty());
    assert_eq!(t.query_keys(&3, &3), vec![&3]);
    assert_eq!(t.query_keys(&0, &9), vec![&1, &3, &5, &7]);
    let d = RangeTree1D::new(vec![1, 3, 3, 5]);
    assert_eq!(d.query_keys(&3, &3), vec![&3, &3]);
}

#[test]
fn copies_of_the_split_at_both_ends_are_all_reported() {
    // The root's split is 3, copies of 3 sit on both sides, and lo or hi equals 3 at the split.
    let keys = vec![3, 3, 3, 3, 3, 1, 5];
    let t = RangeTree1D::new(keys.clone());
    for (lo, hi) in [(3, 3), (1, 3), (3, 5), (2, 4), (0, 3)] {
        assert_eq!(
            t.query(&lo, &hi),
            filter_1d(&keys, lo, hi),
            "range [{lo}, {hi}]"
        );
    }
}

#[test]
fn identical_keys_build_a_shallow_tree() {
    let t = RangeTree1D::new(vec![7; 1000]);
    assert!(t.depth() <= 11, "depth {}", t.depth());
    assert_eq!(t.query(&7, &7).len(), 1000);
    let t2 = RangeTree2D::new(vec![(2, 2); 1000]);
    assert!(t2.depth() <= 11);
    assert_eq!(t2.query((&2, &2), (&2, &2)).len(), 1000);
}

#[test]
fn empty_trees_answer_nothing() {
    let t: RangeTree1D<i32> = RangeTree1D::new(vec![]);
    assert!(t.is_empty() && t.query(&0, &9).is_empty());
    let t2: RangeTree2D<i32> = RangeTree2D::new(vec![]);
    assert!(t2.is_empty() && t2.query((&0, &0), (&9, &9)).is_empty());
}

#[test]
fn default_and_from_iter_are_the_constructors() {
    assert_eq!(RangeTree1D::<i32>::default(), RangeTree1D::new(vec![]));
    assert_eq!(RangeTree2D::<i32>::default(), RangeTree2D::new(vec![]));
    let t: RangeTree1D<i32> = [3, 1, 2, 1].into_iter().collect();
    assert_eq!(t, RangeTree1D::new(vec![3, 1, 2, 1]));
    assert_ne!(t, RangeTree1D::new(vec![1, 1, 2, 3]));
    let t2: RangeTree2D<i32> = [(1, 2), (0, 5)].into_iter().collect();
    assert_eq!(t2, RangeTree2D::new(vec![(1, 2), (0, 5)]));
}

#[test]
fn query_iter_is_lazy_query() {
    let t = RangeTree1D::new(vec![5, 3, 8, 3, 1, 9, 3]);
    let mut it = t.query_iter(&3, &8);
    assert_eq!(it.next(), Some(1));
    assert_eq!(it.collect::<Vec<_>>(), vec![3, 6, 0, 2]);
    assert_eq!(t.query(&3, &8), vec![1, 3, 6, 0, 2]);
    assert_eq!(t.query_iter(&9, &3).count(), 0);
}

#[test]
fn each_piece_fails_alone() {
    // Lean: KeysSeparate, SplitsHalve -- a split below its left side breaks only the first
    let t = RangeTree1D {
        keys: vec![1, 2],
        order: vec![0, 1],
        root: Some(Box::new(Node::Internal {
            split: 0,
            start: 0,
            end: 2,
            left: Box::new(Node::Leaf { pos: 0 }),
            right: Box::new(Node::Leaf { pos: 1 }),
        })),
    };
    assert!(!t.is_keys_separate() && t.is_splits_halve());
    assert_eq!(t.check_valid(), Err("invariant 1 (keys_separate)"));
    // one key on the left of three, the split separating: breaks only the second
    let t = RangeTree1D {
        keys: vec![1, 2, 3],
        order: vec![0, 1, 2],
        root: Some(Box::new(Node::Internal {
            split: 1,
            start: 0,
            end: 3,
            left: Box::new(Node::Leaf { pos: 0 }),
            right: Box::new(Node::Internal {
                split: 2,
                start: 1,
                end: 3,
                left: Box::new(Node::Leaf { pos: 1 }),
                right: Box::new(Node::Leaf { pos: 2 }),
            }),
        })),
    };
    assert!(t.is_keys_separate() && !t.is_splits_halve());
    assert_eq!(t.check_valid(), Err("invariant 2 (splits_halve)"));
}

#[test]
fn build_is_valid() {
    // Lean: valid_build -- everything on the left ≤ split ≤ everything on the right, and every
    // node sends ⌈n/2⌉ left; read here by a walk of its own and by `check_valid`
    for keys in [
        vec![5, 1, 3, 3, 3, 9, 0, 3],
        vec![2; 17],
        (0..50).rev().collect(),
    ] {
        let t = RangeTree1D::new(keys);
        assert_eq!(t.check_valid(), Ok(()));
        let Some(root) = &t.root else { continue };
        let mut stack = vec![root.as_ref()];
        while let Some(n) = stack.pop() {
            if let Node::Internal {
                split, left, right, ..
            } = n
            {
                let (ls, le) = left.range();
                let (rs, re) = right.range();
                assert!(t.keys[ls..le].iter().all(|k| k <= split));
                assert!(t.keys[rs..re].iter().all(|k| split <= k));
                stack.push(left);
                stack.push(right);
            }
        }
    }
}

#[test]
fn split_is_left_max() {
    // Lean: build_split_mem -- the split is the key at the left range's last position
    let t = RangeTree1D::new(vec![4, 8, 15, 16, 23, 42, 42]);
    let mut stack = vec![t.root.as_deref().unwrap()];
    while let Some(n) = stack.pop() {
        if let Node::Internal {
            split, left, right, ..
        } = n
        {
            assert_eq!(&t.keys[left.range().1 - 1], split);
            stack.push(left);
            stack.push(right);
        }
    }
}

proptest! {
    #[test]
    fn query_is_the_filter(keys in prop::collection::vec(-20i32..20, 0..80), lo in -25i32..25, hi in -25i32..25) {
        // Lean: query_eq_filter (in key order, ties in input order), valid_build
        let t = RangeTree1D::new(keys.clone());
        prop_assert_eq!(t.query(&lo, &hi), filter_1d(&keys, lo, hi));
    }

    #[test]
    fn distinct_keys_answer_as_de_berg(keys in prop::collection::btree_set(-40i32..40, 0..40), lo in -45i32..45, hi in -45i32..45) {
        // With distinct keys the walk going left only when `hi < split` returns de Berg's answer, also
        // when a bound equals a stored key; only the node the walk stops at may differ.
        let t = RangeTree1D::new(keys.into_iter().collect());
        prop_assert_eq!(t.query(&lo, &hi), de_berg_query(&t, &lo, &hi));
    }

    #[test]
    fn query_2d_is_the_box_filter(
        pts in prop::collection::vec((-10i32..10, -10i32..10), 0..60),
        x in (-12i32..12, -12i32..12), y in (-12i32..12, -12i32..12),
    ) {
        let t = RangeTree2D::new(pts.clone());
        let want: Vec<usize> = (0..pts.len())
            .filter(|&i| x.0 <= pts[i].0 && pts[i].0 <= x.1 && y.0 <= pts[i].1 && pts[i].1 <= y.1)
            .collect();
        // The query reports in de Berg's walk order, not sorted (sorting k ids would add
        // O(k log k) to O(log² n + k)): compare as sorted lists, which also checks each id once.
        let mut got = t.query((&x.0, &y.0), (&x.1, &y.1));
        got.sort_unstable();
        prop_assert_eq!(got, want);
    }

    #[test]
    fn the_merged_build_is_the_sorted_build(
        pts in prop::collection::vec((-6i32..6, -6i32..6), 1..80),
    ) {
        // dBCKO §5.3: merging the children's y-lists (left first on equal y) gives exactly the
        // associated trees that stably sorting each node's x-slice by y gives.
        prop_assert_eq!(RangeTree2D::new(pts.clone()), sorting_each_slice(pts));
    }

    #[test]
    fn the_2d_build_is_valid(pts in prop::collection::vec((-6i32..6, -6i32..6), 0..60)) {
        prop_assert_eq!(RangeTree2D::new(pts).check_valid(), Ok(()));
    }
}

/// The root of a 2D tree, to break one piece by hand.
fn root2(t: &mut RangeTree2D<i32>) -> &mut Node2<i32> {
    t.root.as_deref_mut().expect("a tree with points")
}

#[test]
fn each_2d_piece_fails_alone() {
    // A split below its left side breaks only the first piece.
    let mut t = RangeTree2D::new(vec![(1, 5), (2, 4), (3, 6), (4, 3)]);
    if let Node2::Internal { split, .. } = root2(&mut t) {
        *split = 0;
    }
    assert!(!t.is_keys_separate() && t.is_splits_halve() && t.is_y_trees_hold_subtrees());
    assert_eq!(t.check_valid(), Err("invariant 1 (keys_separate)"));

    // One point on the left of three breaks only the second.
    let mut t = RangeTree2D::new(vec![(1, 5), (2, 4), (3, 6)]);
    let right = Node2::Internal {
        split: 2,
        assoc: RangeTree1D::from_sorted(vec![4, 6], vec![1, 2]),
        left: Box::new(Node2::Leaf { pos: 1 }),
        right: Box::new(Node2::Leaf { pos: 2 }),
    };
    *root2(&mut t) = Node2::Internal {
        split: 1,
        assoc: RangeTree1D::from_sorted(vec![4, 5, 6], vec![1, 0, 2]),
        left: Box::new(Node2::Leaf { pos: 0 }),
        right: Box::new(right),
    };
    assert!(t.is_keys_separate() && t.is_y_trees_hold_subtrees());
    assert_eq!(t.check_valid(), Err("invariant 2 (splits_halve)"));

    // A tree on y naming one point twice breaks only the third.
    let mut t = RangeTree2D::new(vec![(1, 5), (2, 4), (3, 6), (4, 3)]);
    if let Node2::Internal { assoc, .. } = root2(&mut t) {
        assoc.order[0] = assoc.order[1];
    }
    assert!(t.is_keys_separate() && t.is_splits_halve());
    assert_eq!(
        t.check_valid(),
        Err("not in the box (y_trees_hold_subtrees)")
    );
}

/// The 2D build without the merge: every associated tree sorts its node's points by y
/// again. The reference the merged build must equal.
fn sorting_each_slice(points: Vec<(i32, i32)>) -> RangeTree2D<i32> {
    fn build(sorted: &[((i32, i32), usize)], start: usize, end: usize) -> Node2<i32> {
        if end - start == 1 {
            return Node2::Leaf { pos: start };
        }
        let m = start + (end - start).div_ceil(2);
        let mut below: Vec<(i32, usize)> =
            sorted[start..end].iter().map(|p| (p.0 .1, p.1)).collect();
        below.sort_by_key(|p| p.0);
        Node2::Internal {
            split: sorted[m - 1].0 .0,
            assoc: RangeTree1D::from_sorted(
                below.iter().map(|p| p.0).collect(),
                below.iter().map(|p| p.1).collect(),
            ),
            left: Box::new(build(sorted, start, m)),
            right: Box::new(build(sorted, m, end)),
        }
    }
    let mut sorted: Vec<((i32, i32), usize)> = points.into_iter().zip(0..).collect();
    sorted.sort_by_key(|p| p.0 .0);
    let root = Some(Box::new(build(&sorted, 0, sorted.len())));
    RangeTree2D { sorted, root }
}

thread_local! {
    static COMPARISONS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// A key that counts its comparisons.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Counted(u32);

impl PartialOrd for Counted {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Counted {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        COMPARISONS.with(|c| c.set(c.get() + 1));
        self.0.cmp(&other.0)
    }
}

#[test]
fn the_2d_build_makes_o_n_log_n_comparisons() {
    // dBCKO §5.3 (Theorem 5.8): O(n log n) by merging the children's y-lists. Measured at
    // n = 4096: the merged build makes 100 604 comparisons; re-sorting each node's
    // points instead would make 382 520. The bound is 3 n log₂ n = 147 456.
    let n = 4096_u32;
    let pts: Vec<(Counted, Counted)> = (0..n)
        .map(|i| {
            (
                Counted(i.wrapping_mul(2_654_435_761) % n),
                Counted(i.wrapping_mul(40_503) % n),
            )
        })
        .collect();
    COMPARISONS.with(|c| c.set(0));
    let t = RangeTree2D::new(pts);
    let used = COMPARISONS.with(std::cell::Cell::get);
    assert_eq!(t.len(), 4096);
    assert!(used <= 3 * 4096 * 12, "{used} comparisons");
}

/// The shape the Lean–Rust comparison sends to the Lean: on `[1, 2, 2, 3, 5]` the first `⌈n/2⌉`
/// keys go left at every node and the split is the last of them, the lower median, exactly as
/// the Lean `RangeTree1D.build` makes it (`build_split_mem`).
#[cfg(feature = "unchecked")]
#[test]
fn the_unchecked_shape_is_the_lean_build() {
    use Shape1D::{Leaf, Node};
    let n = |s, l, r| Node(s, Box::new(l), Box::new(r));
    let t = RangeTree1D::new(vec![5, 2, 1, 3, 2]);
    let want = n(
        2,
        n(2, n(1, Leaf(1), Leaf(2)), Leaf(2)),
        n(3, Leaf(3), Leaf(5)),
    );
    assert_eq!(t.shape(), Some(want));
    assert_eq!(RangeTree1D::new(vec![7]).shape(), Some(Leaf(7)));
    assert_eq!(RangeTree1D::<i32>::new(vec![]).shape(), None);
}

#[test]
fn query_on_two_equal_keys_with_both_bounds_on_them_returns_both() {
    // Both bounds on a repeated key: the query reports every copy, as the filter does.
    let keys = vec![-20, -20];
    let t = RangeTree1D::new(keys.clone());
    assert_eq!(t.query(&-20, &-20), filter_1d(&keys, -20, -20));
}
