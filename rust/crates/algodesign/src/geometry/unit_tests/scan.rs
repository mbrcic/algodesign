use super::*;
use crate::geometry::point::{sq_dist, Points};
use proptest::prelude::*;

fn pts(rows: &[[f64; 2]]) -> Points {
    Points::from_rows(2, rows).unwrap()
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean scan examples, coordinate for coordinate
    assert_eq!(nearest(&Points::new(2, vec![]).unwrap(), &[0.0, 0.0]), None);
    assert_eq!(
        nearest(&pts(&[[5.0, 5.0], [1.0, 1.0], [9.0, 0.0]]), &[1.0, 1.0]),
        Some(1)
    );
    assert_eq!(
        nearest(&pts(&[[1.0, 0.0], [4.0, 4.0], [-1.0, 0.0]]), &[0.0, 0.0]),
        Some(0)
    );
    assert_eq!(
        nearest(&pts(&[[3.0, 3.0], [2.0, 2.0], [2.0, 2.0]]), &[2.0, 2.0]),
        Some(1)
    );
}

#[test]
fn empty_has_no_nearest() {
    // Lean: scanNearest_isSome_iff
    assert_eq!(nearest(&Points::new(3, vec![]).unwrap(), &[0.0; 3]), None);
    assert_eq!(nearest(&pts(&[[7.0, 7.0]]), &[0.0, 0.0]), Some(0));
}

#[test]
fn k_nearest_handles_zero_and_too_many() {
    let p = pts(&[[0.0, 0.0], [1.0, 0.0]]);
    assert!(k_nearest(&p, &[0.0, 0.0], 0).is_empty());
    assert_eq!(k_nearest(&p, &[0.0, 0.0], 5).len(), 2);
    assert!(k_nearest(&Points::new(2, vec![]).unwrap(), &[0.0, 0.0], 3).is_empty());
}

#[test]
fn ties_in_k_nearest_go_to_the_lower_index() {
    let p = pts(&[[1.0, 0.0], [0.0, 1.0], [-1.0, 0.0], [5.0, 5.0]]);
    let got: Vec<usize> = k_nearest(&p, &[0.0, 0.0], 2).iter().map(|n| n.id).collect();
    assert_eq!(got, vec![0, 1]);
}

#[test]
fn in_box_is_inclusive_and_ascending() {
    let p = pts(&[[2.0, 2.0], [0.0, 0.0], [1.0, 3.0], [2.0, 0.0]]);
    assert_eq!(in_box(&p, &[0.0, 0.0], &[2.0, 2.0]), vec![0, 1, 3]);
    assert!(in_box(&p, &[3.0, 0.0], &[1.0, 5.0]).is_empty());
}

#[test]
fn k_nearest_among_ranks_only_the_candidates() {
    let p = pts(&[[0.0, 0.0], [1.0, 0.0], [2.0, 0.0], [1.0, 0.0]]);
    let got: Vec<usize> = k_nearest_among(&p, &[3, 2, 1], &[0.0, 0.0], 2)
        .iter()
        .map(|n| n.id)
        .collect();
    assert_eq!(got, vec![1, 3]);
}

proptest! {
    #[test]
    fn nearest_is_argmin_with_lowest_index(
        rows in prop::collection::vec([-5i32..5, -5i32..5], 0..40), qx in -5i32..5, qy in -5i32..5,
    ) {
        // Lean: scanNearest_le, scanNearest_lowest, scanNearest_mem, scanNearest_isSome_iff
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let q = [f64::from(qx), f64::from(qy)];
        match nearest(&p, &q) {
            None => prop_assert!(p.is_empty()),
            Some(i) => {
                prop_assert!(i < p.len());
                let d = sq_dist(p.get(i), &q);
                for j in 0..p.len() {
                    prop_assert!(d <= sq_dist(p.get(j), &q));
                    if j < i { prop_assert!(d < sq_dist(p.get(j), &q)); }
                }
            }
        }
    }

    #[test]
    fn k_nearest_is_the_sorted_prefix(
        rows in prop::collection::vec([-5i32..5, -5i32..5], 0..40), k in 0usize..50,
    ) {
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let mut all: Vec<(f64, usize)> =
            (0..p.len()).map(|i| (sq_dist(p.get(i), &[0.0, 0.0]), i)).collect();
        all.sort_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));
        let want: Vec<usize> = all.iter().take(k).map(|x| x.1).collect();
        let got: Vec<usize> = k_nearest(&p, &[0.0, 0.0], k).iter().map(|n| n.id).collect();
        prop_assert_eq!(got, want);
    }
}

#[test]
fn a_huge_k_returns_every_point_without_allocating_for_k() {
    // `TopK` must not preallocate `k + 1` slots: at k = 2^40 that aborts the process.
    let p = pts(&[[0.0, 0.0], [1.0, 0.0], [2.0, 0.0]]);
    for k in [1usize << 40, usize::MAX] {
        assert_eq!(k_nearest(&p, &[0.0, 0.0], k).len(), 3);
        assert_eq!(k_nearest_among(&p, &[2, 0], &[0.0, 0.0], k).len(), 2);
    }
}

#[test]
fn scan_tie_on_two_identical_points_keeps_the_lower_index() {
    // Two copies of one point tie on distance; the scan answers the lower index.
    let p = pts(&[[4.0, 1.0], [4.0, 1.0]]);
    let q = [0.0, 0.0];
    let i = nearest(&p, &q).unwrap();
    let d = sq_dist(p.get(i), &q);
    for j in 0..p.len() {
        assert!(d <= sq_dist(p.get(j), &q));
        if j < i {
            assert!(d < sq_dist(p.get(j), &q));
        }
    }
    assert_eq!(i, 0);
}

#[test]
fn k_nearest_tie_on_equidistant_points_is_in_index_order() {
    // Two points at the same distance from the query; the one nearest is the lower index.
    let p = pts(&[[-1.0, -2.0], [-1.0, 2.0]]);
    let got: Vec<usize> = k_nearest(&p, &[0.0, 0.0], 1).iter().map(|n| n.id).collect();
    assert_eq!(got, vec![0]);
}
