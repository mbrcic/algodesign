use super::*;

#[test]
fn rejects_zero_dimension() {
    assert_eq!(Points::new(0, vec![]), Err(PointsError::ZeroDimension));
}

#[test]
fn rejects_ragged_coordinates() {
    assert_eq!(
        Points::new(2, vec![1.0, 2.0, 3.0]),
        Err(PointsError::Ragged { len: 3, dim: 2 })
    );
}

#[test]
fn rejects_non_finite_coordinates() {
    assert_eq!(
        Points::new(2, vec![0.0, 0.0, f64::NAN, 1.0]),
        Err(PointsError::NonFinite { id: 1 })
    );
    assert_eq!(
        Points::new(1, vec![f64::INFINITY]),
        Err(PointsError::NonFinite { id: 0 })
    );
}

#[test]
fn stores_rows_in_order() {
    let p = Points::from_rows(2, &[[1.0, 2.0], [3.0, 4.0]]).unwrap();
    assert_eq!((p.len(), p.dim()), (2, 2));
    assert_eq!(p.get(1), &[3.0, 4.0]);
    assert!(Points::new(3, vec![]).unwrap().is_empty());
}

#[test]
fn normalizing_a_zero_vector_is_an_error() {
    let p = Points::from_rows(2, &[[3.0, 4.0], [0.0, 0.0]]).unwrap();
    assert_eq!(p.normalized(), Err(PointsError::ZeroVector { id: 1 }));
    let u = Points::from_rows(2, &[[3.0, 4.0]])
        .unwrap()
        .normalized()
        .unwrap();
    assert_eq!(u.get(0), &[0.6, 0.8]);
}

#[test]
fn squared_distance_is_symmetric_and_axis_bounded() {
    // Lean: sqDist_comm, sq_axis_le_sqDist
    let (a, b): ([f64; 3], [f64; 3]) = ([1.0, 5.0, -2.0], [4.0, 1.0, 0.0]);
    assert_eq!(sq_dist(&a, &b), 29.0);
    assert_eq!(sq_dist(&a, &b), sq_dist(&b, &a));
    for i in 0..3 {
        assert!((a[i] - b[i]).powi(2) <= sq_dist(&a, &b));
    }
}

#[test]
#[should_panic(expected = "query has dimension 3 but the points have 2")]
fn a_query_of_the_wrong_dimension_panics() {
    check_query(2, &[0.0, 0.0, 0.0]);
}

#[test]
#[should_panic(expected = "query coordinate 1 is not finite")]
fn a_non_finite_query_panics() {
    check_query(2, &[0.0, f64::NAN]);
}

#[test]
fn normalizing_survives_extreme_magnitudes() {
    // The norm as sqrt(dot(p, p)) overflows near 1e200 (the zero vector, returned as Ok) and
    // underflows near 1e-200 (a nonzero vector called zero). Scaling by the largest coordinate
    // first keeps both in range.
    let p = Points::from_rows(2, &[[1e200, 1e200], [1e-200, 0.0], [-3e-310, 4e-310]]).unwrap();
    let u = p.normalized().unwrap();
    let h = std::f64::consts::FRAC_1_SQRT_2;
    assert!((u.get(0)[0] - h).abs() < 1e-15 && (u.get(0)[1] - h).abs() < 1e-15);
    assert_eq!(u.get(1), &[1.0, 0.0]);
    assert!((u.get(2)[0] + 0.6).abs() < 1e-12 && (u.get(2)[1] - 0.8).abs() < 1e-12);
}
