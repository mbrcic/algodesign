use super::*;
use crate::geometry::point::{sq_dist, Points, PointsError};
use crate::geometry::rng::SplitMix64;

#[test]
fn projection_is_linear() {
    // Lean: dot_add -- each output coordinate is a dot product, so shadows of sums are sums
    let g = GaussianProjection::new(5, 3, 1);
    let (u, v) = ([1.0, -2.0, 0.5, 3.0, 0.0], [0.0, 4.0, -1.0, 2.0, 7.0]);
    let sum: Vec<f64> = u.iter().zip(&v).map(|(a, b)| a + b).collect();
    for ((s, a), b) in g.project(&sum).iter().zip(g.project(&u)).zip(g.project(&v)) {
        assert!((s - (a + b)).abs() < 1e-12);
    }
}

#[test]
fn the_seed_fixes_the_matrix() {
    assert_eq!(
        GaussianProjection::new(10, 4, 9).project(&[1.0; 10]),
        GaussianProjection::new(10, 4, 9).project(&[1.0; 10])
    );
    assert_ne!(
        GaussianProjection::new(10, 4, 9).project(&[1.0; 10]),
        GaussianProjection::new(10, 4, 10).project(&[1.0; 10])
    );
}

#[test]
fn shapes() {
    let g = GaussianProjection::new(7, 3, 2);
    assert_eq!((g.d_in(), g.k()), (7, 3));
    let p = Points::from_rows(7, &[[1.0; 7], [2.0; 7]]).unwrap();
    let q = g.project_all(&p).unwrap();
    assert_eq!((q.len(), q.dim()), (2, 3));
    assert_eq!(q.get(1), g.project(&[2.0; 7]).as_slice());
}

#[test]
fn pairwise_distances_survive_within_epsilon() {
    // Statistical (JL, Dasgupta–Gupta): 60 points in d = 400 projected to k = 400. The JL bound
    // is not proved in Lean; this test is what holds it. For k = 400,
    // ε = 0.3, the per-pair failure probability is ≤ 2·exp(−k(ε²/2 − ε³/3)/2) ≈ 1.5e-3, so
    // over 1770 pairs we allow 2% to exceed it. The seed is fixed, so the outcome is too.
    let mut r = SplitMix64::new(3);
    let p = Points::new(400, (0..60 * 400).map(|_| r.standard_normal()).collect()).unwrap();
    let g = GaussianProjection::new(400, 400, 11);
    let q = g.project_all(&p).unwrap();
    let (mut bad, mut pairs) = (0, 0);
    for i in 0..60 {
        for j in i + 1..60 {
            let ratio = sq_dist(q.get(i), q.get(j)) / sq_dist(p.get(i), p.get(j));
            pairs += 1;
            if !(0.7..=1.3).contains(&ratio) {
                bad += 1;
            }
        }
    }
    assert!(
        bad * 50 <= pairs,
        "{bad} of {pairs} pairs distorted beyond 30%"
    );
}

#[test]
fn an_image_that_overflows_is_an_error_not_a_panic() {
    // The image of finite points can overflow: `project_all` reports it, it does not panic.
    let g = GaussianProjection::new(4, 3, 1);
    let p = Points::from_rows(4, &[[1.0; 4], [1.7e308; 4]]).unwrap();
    assert_eq!(g.project_all(&p), Err(PointsError::NonFinite { id: 1 }));
}

#[test]
#[should_panic(expected = "overflows usize")]
fn a_matrix_too_large_to_index_panics() {
    let _ = GaussianProjection::new(usize::MAX / 2, 3, 0);
}
