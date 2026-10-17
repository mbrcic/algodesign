use super::*;
use crate::geometry::{
    point::{sq_dist, Points},
    scan,
};
use proptest::prelude::*;

fn pts(rows: &[[f64; 2]]) -> Points {
    Points::from_rows(2, rows).unwrap()
}

fn subtree_points(t: &KdTree, n: &Node) -> Vec<usize> {
    let (s, e) = n.range();
    t.perm[s..e].to_vec()
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean k-d examples (points on the split, both sides)
    // Leaf size 1, the Lean tree's: one point per leaf, so the queries cross splits.
    let p = pts(&[[2.0, 1.0], [1.0, 5.0], [3.0, 0.0], [2.0, 3.0]]);
    let t = KdTree::with_bucket(p, 1);
    assert_eq!(t.range(&[2.0, 0.0], &[4.0, 4.0]), vec![0, 2, 3]);
    assert_eq!(t.range(&[0.0, 0.0], &[2.0, 3.0]), vec![0, 3]);
}

#[test]
fn identical_points_stay_shallow_and_are_all_found() {
    let p = Points::new(2, [1.5, -2.0].repeat(1000)).unwrap();
    let t = KdTree::new(p);
    assert!(t.depth() <= 11, "depth {}", t.depth());
    assert_eq!(t.range(&[1.5, -2.0], &[1.5, -2.0]).len(), 1000);
    assert_eq!(t.nearest(&[1.5, -2.0]), Some(0));
    let got: Vec<usize> = t.k_nearest(&[0.0, 0.0], 3).iter().map(|n| n.id).collect();
    assert_eq!(got, vec![0, 1, 2]);
}

#[test]
fn empty_and_k_edge_cases() {
    let t = KdTree::new(Points::new(3, vec![]).unwrap());
    assert!(t.is_empty());
    assert_eq!(t.nearest(&[0.0, 0.0, 0.0]), None);
    assert!(t.range(&[0.0; 3], &[1.0; 3]).is_empty());
    let t = KdTree::new(pts(&[[0.0, 0.0], [1.0, 1.0]]));
    assert!(t.k_nearest(&[0.0, 0.0], 0).is_empty());
    assert_eq!(t.k_nearest(&[0.0, 0.0], 9).len(), 2);
    assert_eq!(t.nearest(&[1.0, 1.0]), Some(1));
}

#[test]
fn the_default_leaf_size_is_eight() {
    // dBCKO's tree has one point per leaf; `DEFAULT_BUCKET`'s doc says why this one has eight.
    assert_eq!(DEFAULT_BUCKET, 8);
}

#[test]
#[should_panic(expected = "bucket")]
fn bucket_zero_is_rejected() {
    let _ = KdTree::with_bucket(pts(&[[0.0, 0.0]]), 0);
}

#[test]
fn pruning_bound_both_sides() {
    // Lean: far_side_bound, far_side_bound_left -- across a split at s, any point is at least
    // (q_axis − s)² away, on either side, with points equal to s on both sides
    let s = 2.0;
    let q = [0.0, 0.0];
    for x in [[2.0, 9.0], [3.0, -1.0], [2.0, 0.0]] {
        assert!((s - q[0]) * (s - q[0]) <= sq_dist(&x, &q));
    }
    let q = [5.0, 1.0];
    for x in [[2.0, 1.0], [-1.0, 4.0]] {
        assert!((q[0] - s) * (q[0] - s) <= sq_dist(&x, &q));
    }
}

#[test]
fn stats_count_the_work() {
    let rows: Vec<[f64; 2]> = (0..400)
        .map(|i| [f64::from(i % 20), f64::from(i / 20)])
        .collect();
    let t = KdTree::new(pts(&rows));
    let (nn, stats) = t.k_nearest_with_stats(&[7.2, 9.1], 1);
    assert_eq!(nn[0].id, 9 * 20 + 7);
    assert!(stats.points_measured >= 1 && stats.points_measured < 400);
    // Each opened leaf measures at most a bucket of points.
    assert!(stats.points_measured <= t.bucket() * stats.regions_opened);
}

proptest! {
    #[test]
    fn the_build_cuts_separate_and_halve(rows in prop::collection::vec([-4i32..4, -4i32..4, -4i32..4], 1..120), bucket in 1usize..6) {
        // Lean: KDTree.Valid -- CutsSeparate (left ≤ split ≤ right on the node's axis, repeats on
        // both sides) and CutsHalve, read here by a walk of its own and by `check_valid`
        let rows: Vec<[f64; 3]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let t = KdTree::with_bucket(Points::from_rows(3, &rows).unwrap(), bucket);
        prop_assert_eq!(t.check_valid(), Ok(()));
        let mut stack = vec![&t.root];
        while let Some(n) = stack.pop() {
            if let Node::Internal { axis, split, left, right, .. } = n {
                for i in subtree_points(&t, left) { prop_assert!(t.points.get(i)[*axis] <= *split); }
                for i in subtree_points(&t, right) { prop_assert!(*split <= t.points.get(i)[*axis]); }
                let (l, r) = (subtree_points(&t, left).len(), subtree_points(&t, right).len());
                prop_assert!(r <= l && l <= r + 1);
                stack.push(left);
                stack.push(right);
            } else if let Node::Leaf { start, end } = n {
                prop_assert!(end - start <= bucket);
            }
        }
    }

    #[test]
    fn region_bound_is_a_lower_bound(
        rows in prop::collection::vec([-6i32..6, -6i32..6], 1..80), q in [-7i32..7, -7i32..7],
    ) {
        // Lean: boxSqDist_le -- every region's bound is ≤ the distance to each point inside it
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let t = KdTree::with_bucket(pts(&rows), 1);
        let q = q.map(f64::from);
        let mut offs = Offsets::new(2);
        let mut stack = vec![(&t.root, 0)];
        while let Some((n, off)) = stack.pop() {
            let b = bound(offs.get(off));
            for i in subtree_points(&t, n) { prop_assert!(b <= sq_dist(t.points.get(i), &q)); }
            if let Node::Internal { axis, split, left, right, .. } = n {
                let (near, far) = if q[*axis] <= *split { (left, right) } else { (right, left) };
                stack.push((near, off));
                stack.push((far, offs.far(off, *axis, *split, &q)));
            }
        }
    }

    #[test]
    fn four_lane_bound_and_search_hold_on_real_coordinates(
        rows in prop::collection::vec(prop::collection::vec(-1e3f64..1e3, 7), 1..120),
        q in prop::collection::vec(-1e3f64..1e3, 7), k in 1usize..6, bucket in 1usize..9,
    ) {
        // At d = 7 (four lanes and a three-term tail) with real coordinates, where rounding
        // happens: every region's bound stays below the distance of each point inside it, and
        // the search's answer is the scan's.
        let p = Points::new(7, rows.concat()).unwrap();
        let t = KdTree::with_bucket(p.clone(), bucket);
        let mut offs = Offsets::new(7);
        let mut stack = vec![(&t.root, 0)];
        while let Some((n, off)) = stack.pop() {
            let b = bound(offs.get(off));
            for i in subtree_points(&t, n) { prop_assert!(b <= sq_dist(t.points.get(i), &q)); }
            if let Node::Internal { axis, split, left, right, .. } = n {
                let (near, far) = if q[*axis] <= *split { (left, right) } else { (right, left) };
                stack.push((near, off));
                stack.push((far, offs.far(off, *axis, *split, &q)));
            }
        }
        prop_assert_eq!(t.k_nearest(&q, k), scan::k_nearest(&p, &q, k));
    }

    #[test]
    fn the_bound_sums_in_the_distance_s_lanes(
        p in prop::collection::vec(-1e3f64..1e3, 7), q in prop::collection::vec(-1e3f64..1e3, 7),
        far in prop::collection::vec(any::<bool>(), 7),
    ) {
        // A point on the corner of its region: its offsets are its own differences from q on
        // the far axes (as Offsets::far computes them, the cut being its coordinate), 0 elsewhere.
        // The bound sums them in sq_dist's four lanes, so it is at most the distance, and equal
        // when every axis is far; any other summation order could differ from it in the last bit.
        let off: Vec<f64> = (0..7).map(|i| if far[i] { p[i] - q[i] } else { 0.0 }).collect();
        prop_assert!(bound(&off) <= sq_dist(&p, &q));
        let every: Vec<f64> = (0..7).map(|i| p[i] - q[i]).collect();
        prop_assert_eq!(bound(&every), sq_dist(&p, &q));
    }

    #[test]
    fn range_is_the_box_filter(
        rows in prop::collection::vec([-6i32..6, -6i32..6, -6i32..6], 0..120), bucket in 1usize..6,
        a in [-7i32..7, -7i32..7, -7i32..7], b in [-7i32..7, -7i32..7, -7i32..7],
    ) {
        // Lean: rangeQuery_perm_filter -- the box filter in some order, each point once
        let rows: Vec<[f64; 3]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = Points::from_rows(3, &rows).unwrap();
        let (lo, hi) = (a.map(f64::from), b.map(f64::from));
        let mut found = KdTree::with_bucket(p.clone(), bucket).range(&lo, &hi);
        found.sort_unstable();
        prop_assert_eq!(found, scan::in_box(&p, &lo, &hi));
    }

    #[test]
    fn best_first_is_the_scan(
        rows in prop::collection::vec([-6i32..6, -6i32..6], 0..150), q in [-7i32..7, -7i32..7],
        k in 0usize..10, bucket in 1usize..6,
    ) {
        // Integer coordinates: many exact ties, so the lowest-index rule is exercised.
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let q = q.map(f64::from);
        let t = KdTree::with_bucket(p.clone(), bucket);
        prop_assert_eq!(t.k_nearest(&q, k), scan::k_nearest(&p, &q, k));
        prop_assert_eq!(t.nearest(&q), scan::nearest(&p, &q));
    }

    #[test]
    fn best_first_is_the_scan_on_real_coordinates(
        rows in prop::collection::vec([-1e3f64..1e3, -1e3f64..1e3, -1e3f64..1e3], 0..150),
        q in [-1e3f64..1e3, -1e3f64..1e3, -1e3f64..1e3], k in 0usize..6,
    ) {
        let p = Points::from_rows(3, &rows).unwrap();
        prop_assert_eq!(KdTree::new(p.clone()).k_nearest(&q, k), scan::k_nearest(&p, &q, k));
    }
}

#[test]
fn a_huge_k_returns_every_point() {
    let t = KdTree::new(pts(&[[0.0, 0.0], [1.0, 0.0], [2.0, 0.0]]));
    for k in [1usize << 40, usize::MAX] {
        assert_eq!(t.k_nearest(&[0.0, 0.0], k).len(), 3);
    }
}

/// The shape the Lean–Rust comparison sends to the Lean, on six points with distinct coordinates
/// (so the lower median is unambiguous): the axis cycles with the depth, the first `⌈n/2⌉` points
/// by that coordinate go left, the split is the largest of them, and each bucket-1 leaf lists the
/// input index of its point.
#[cfg(feature = "unchecked")]
#[test]
fn the_unchecked_shape_lists_axes_splits_and_leaf_indices() {
    use KdShape::{Leaf, Node};
    let n = |axis, split, l, r| Node {
        axis,
        split,
        left: Box::new(l),
        right: Box::new(r),
    };
    let t = KdTree::with_bucket(
        pts(&[
            [5.0, 1.0],
            [2.0, 6.0],
            [8.0, 3.0],
            [1.0, 4.0],
            [7.0, 9.0],
            [3.0, 2.0],
        ]),
        1,
    );
    let want = n(
        0,
        3.0,
        n(
            1,
            4.0,
            n(0, 1.0, Leaf(vec![3]), Leaf(vec![5])),
            Leaf(vec![1]),
        ),
        n(
            1,
            3.0,
            n(0, 5.0, Leaf(vec![0]), Leaf(vec![2])),
            Leaf(vec![4]),
        ),
    );
    assert_eq!(t.shape(), want);
    // A bucket lists its points; the empty tree is one empty leaf.
    assert_eq!(
        KdTree::new(pts(&[[0.0, 0.0], [1.0, 1.0]])).shape(),
        Leaf(vec![0, 1])
    );
    assert_eq!(KdTree::new(pts(&[])).shape(), Leaf(vec![]));
}

#[test]
fn best_first_k_zero_on_a_leaf_of_identical_points_is_the_scan() {
    // A leaf of identical points (thirteen copies of the origin) at bucket 1. Asked for no
    // neighbors, the tree answers nothing, as the scan does, and its nearest point is the scan's.
    let mut rows = vec![[0.0, 0.0], [0.0, -6.0], [1.0, -5.0]];
    rows.extend([[0.0, 0.0]; 12]);
    let p = pts(&rows);
    let q = [1.0, -6.0];
    let t = KdTree::with_bucket(p.clone(), 1);
    assert_eq!(t.k_nearest(&q, 0), scan::k_nearest(&p, &q, 0));
    assert_eq!(t.nearest(&q), scan::nearest(&p, &q));
}

/// A tree written node by node over one-dimensional points, for the sole-failure cases.
fn by_hand(xs: &[f64], root: Node) -> KdTree {
    let rows: Vec<[f64; 1]> = xs.iter().map(|&x| [x]).collect();
    KdTree {
        points: Points::from_rows(1, &rows).unwrap(),
        perm: (0..xs.len()).collect(),
        root,
        bucket: 2,
    }
}

fn internal(split: f64, start: usize, mid: usize, end: usize) -> Node {
    Node::Internal {
        axis: 0,
        split,
        start,
        end,
        left: Box::new(Node::Leaf { start, end: mid }),
        right: Box::new(Node::Leaf { start: mid, end }),
    }
}

#[test]
fn each_tree_piece_fails_alone() {
    // The split below the left point: the cut does not divide, the counts still halve.
    let t = by_hand(&[0.0, 1.0], internal(-1.0, 0, 1, 2));
    assert!(!t.is_cuts_separate() && t.is_cuts_halve());
    assert_eq!(t.check_valid(), Err("invariant 1 (cuts_separate)"));
    // Three equal points, one left and two right: the cut divides, the counts do not halve.
    let t = by_hand(&[0.0, 0.0, 0.0], internal(0.0, 0, 1, 3));
    assert!(t.is_cuts_separate() && !t.is_cuts_halve());
    assert_eq!(t.check_valid(), Err("invariant 2 (cuts_halve)"));
    // Both broken: the first in the Lean's order is named.
    let t = by_hand(&[0.0, 1.0, 2.0], internal(-1.0, 0, 1, 3));
    assert_eq!(t.check_valid(), Err("invariant 1 (cuts_separate)"));
    // The pieces read the internal nodes over buckets: a bucket of 2 under each side.
    let t = by_hand(&[0.0, 0.0, 1.0, 1.0], internal(0.0, 0, 2, 4));
    assert_eq!(t.check_valid(), Ok(()));
}

#[test]
fn the_search_states_of_a_two_point_tree() {
    // Lean: BestFirst.start, BestFirst.visit -- the search walks down to the near leaf, queueing
    // the far side at bound 0, measures point 0, then opens the far side and measures point 1.
    // Each state is one the Lean's steps reach: opening the root, then the near leaf.
    let t = KdTree::with_bucket(Points::from_rows(1, &[[0.0], [1.0]]).unwrap(), 1);
    let region = |path: Vec<Side>, off: f64| Region {
        path,
        offsets: vec![off],
    };
    let states = t.search_states(&[0.0], 1);
    let want = vec![
        SearchState {
            measured: vec![],
            queue: vec![region(vec![], 0.0)],
        },
        SearchState {
            measured: vec![0],
            queue: vec![region(vec![Side::Right], 0.0)],
        },
        SearchState {
            measured: vec![0, 1],
            queue: vec![],
        },
    ];
    assert_eq!(states, want);
    assert!(t.search_states(&[0.0], 0).is_empty());
}

#[test]
fn each_search_piece_fails_where_it_should() {
    // One point (1, 3), the query at the origin: the whole tree is the root leaf.
    let t = KdTree::with_bucket(pts(&[[1.0, 3.0]]), 1);
    let q = [0.0, 0.0];
    let queued = |off: Vec<f64>| SearchState {
        measured: vec![],
        queue: vec![Region {
            path: vec![],
            offsets: off,
        }],
    };
    assert_eq!(check_search_valid(&t, &q, &queued(vec![0.0, 0.0])), Ok(()));
    // Offsets (2, 0): axis 0 overshoots (4 > 1), the bound 4 is still below the distance 10.
    let s = queued(vec![2.0, 0.0]);
    assert!(is_nothing_closer_skipped(&t, &q, &s) && is_each_point_once(&t, &q, &s));
    assert_eq!(
        check_search_valid(&t, &q, &s),
        Err("not in the box (offsets_bound)")
    );
    // Measured twice: the point is not once.
    let s = SearchState {
        measured: vec![0, 0],
        queue: vec![],
    };
    assert!(is_nothing_closer_skipped(&t, &q, &s) && is_offsets_bound(&t, &q, &s));
    assert_eq!(
        check_search_valid(&t, &q, &s),
        Err("not in the box (each_point_once)")
    );
    // A root cut that does not separate (split moved below the left point): the search's start,
    // the root queued at offsets zero, fails only `queued_cuts_separate`.
    let mut broken = KdTree::with_bucket(pts(&[[0.0, 0.0], [1.0, 0.0]]), 1);
    if let Node::Internal { split, .. } = &mut broken.root {
        *split -= 1.0;
    }
    let start = queued(vec![0.0, 0.0]);
    assert!(
        is_nothing_closer_skipped(&broken, &q, &start)
            && is_offsets_bound(&broken, &q, &start)
            && is_each_point_once(&broken, &q, &start)
            && !is_queued_cuts_separate(&broken, &q, &start)
    );
    assert_eq!(
        check_search_valid(&broken, &q, &start),
        Err("not in the box (queued_cuts_separate)")
    );
    assert!(is_queued_cuts_separate(&t, &q, &start));
    // Invariant 3 has no sole failure: `offsets_bound` and `each_point_once` imply it (the bound is
    // the sum of the squared offsets, each at most its axis's part of the distance, and every
    // point is measured or queued). It fails beside one of them: here the point is forgotten,
    // and here its region's bound passes its distance.
    let s = SearchState::default();
    assert!(!is_nothing_closer_skipped(&t, &q, &s) && !is_each_point_once(&t, &q, &s));
    assert_eq!(
        check_search_valid(&t, &q, &s),
        Err("invariant 3 (nothing_closer_skipped)")
    );
    let s = queued(vec![2.0, 3.0]);
    assert!(!is_nothing_closer_skipped(&t, &q, &s) && !is_offsets_bound(&t, &q, &s));
    // A region off the tree, offsets or a query of the wrong dimension, an index outside the set:
    // false, never a panic.
    let lost = SearchState {
        measured: vec![],
        queue: vec![Region {
            path: vec![Side::Left],
            offsets: vec![0.0, 0.0],
        }],
    };
    assert!(!is_search_valid(&t, &q, &lost) && !is_each_point_once(&t, &q, &lost));
    assert!(!is_offsets_bound(&t, &q, &queued(vec![0.0])));
    assert!(!is_nothing_closer_skipped(
        &t,
        &[0.0],
        &queued(vec![0.0, 0.0])
    ));
    let outside = SearchState {
        measured: vec![7],
        queue: vec![],
    };
    assert!(!is_search_valid(&t, &q, &outside));
}

proptest! {
    #[test]
    fn every_search_step_is_valid(
        rows in prop::collection::vec([-6i32..6, -6i32..6], 1..80), q in [-7i32..7, -7i32..7],
        k in 1usize..6, bucket in 1usize..6,
    ) {
        // Lean: BestFirst.valid_start, BestFirst.valid_visit -- every piece after every leaf, for
        // k = 1 and k > 1; each leaf measures something new, and the last state has measured
        // exactly what the search counted
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let t = KdTree::with_bucket(pts(&rows), bucket);
        let q = q.map(f64::from);
        let states = t.search_states(&q, k);
        prop_assert!(!states.is_empty());
        for s in &states {
            prop_assert_eq!(check_search_valid(&t, &q, s), Ok(()));
        }
        let (_, stats) = t.k_nearest_with_stats(&q, k);
        for w in states.windows(2) {
            prop_assert!(w[0].measured.len() < w[1].measured.len());
        }
        prop_assert!(states.len() <= stats.regions_opened + 1);
        prop_assert_eq!(states.last().unwrap().measured.len(), stats.points_measured);
    }

    #[test]
    fn every_search_step_is_valid_on_real_coordinates(
        rows in prop::collection::vec([-1e3f64..1e3, -1e3f64..1e3, -1e3f64..1e3], 1..120),
        q in [-1e3f64..1e3, -1e3f64..1e3, -1e3f64..1e3], k in 1usize..6,
    ) {
        // Rounding: the recomputed bound never passes a computed distance in its region.
        let t = KdTree::new(Points::from_rows(3, &rows).unwrap());
        for s in &t.search_states(&q, k) {
            prop_assert_eq!(check_search_valid(&t, &q, s), Ok(()));
        }
    }

    #[test]
    fn the_extras_imply_nothing_closer_skipped(
        rows in prop::collection::vec([-4i32..4, -4i32..4], 1..30), q in [-5i32..5, -5i32..5],
        k in 1usize..4, step in 0usize..64, drop in 0usize..8, push in 0usize..8,
        axis in 0usize..2, off in -6i32..6,
    ) {
        // A step's state, perturbed: a measured point dropped or repeated, an offset moved.
        // Whenever offsets_bound and each_point_once hold, invariant 3 holds.
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let t = KdTree::with_bucket(pts(&rows), 1);
        let q = q.map(f64::from);
        let states = t.search_states(&q, k);
        let mut s = states[step % states.len()].clone();
        if drop < s.measured.len() { s.measured.remove(drop); }
        if push < s.measured.len() { s.measured.push(s.measured[push]); }
        if let Some(r) = s.queue.first_mut() { r.offsets[axis] = f64::from(off); }
        if is_offsets_bound(&t, &q, &s) && is_each_point_once(&t, &q, &s) {
            prop_assert!(is_nothing_closer_skipped(&t, &q, &s));
        }
    }
}
