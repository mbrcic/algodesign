use super::*;
use crate::geometry::{orientation::orient2d, point::Points, rng::SplitMix64, scan};
use proptest::prelude::*;

fn pts(rows: &[[f64; 2]]) -> Points {
    Points::from_rows(2, rows).unwrap()
}

/// One SimHash table with the two axis directions: a key is the point's quadrant. The Lean
/// examples' family, as a `HashFamily`.
#[derive(Debug, Clone)]
struct Quadrant;

impl HashFamily for Quadrant {
    type Key = (bool, bool);
    fn dim(&self) -> usize {
        2
    }
    fn tables(&self) -> usize {
        1
    }
    fn key(&self, _: usize, v: &[f64]) -> (bool, bool) {
        (sim_bit(&[1.0, 0.0], v), sim_bit(&[0.0, 1.0], v))
    }
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean LSH examples
    let idx = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    assert_eq!(idx.nearest(&[4.0, 4.0]), Some(0)); // the true neighbor collides: exact
    assert_eq!(idx.nearest(&[1.0, 1.0]), Some(0)); // the honest half: the true one (1) is missed
    assert_eq!(idx.nearest(&[10.0, 10.0]), Some(2)); // a stored query finds itself
    let empty = LshIndex::new(Points::new(2, vec![]).unwrap(), Quadrant);
    assert_eq!(empty.nearest(&[1.0, 1.0]), None);
    assert!(!sim_bit(&[1.0, 0.0], &[-3.0, 7.0]));
}

#[test]
fn a_point_on_the_hyperplane_gets_bit_one() {
    // Lean: simBit is `decide (0 ≤ dot r p)`, so the boundary counts as the positive side.
    assert!(sim_bit(&[1.0, 0.0], &[0.0, 5.0]));
}

#[test]
fn same_cell_means_close_shadows() {
    // Lean: pStableKey_eq, and the Lean examples' cells (direction (1, 0), offset 0, width 2)
    let a = [1.0, 0.0];
    assert_eq!(p_stable_cell(&a, 0.0, 2.0, &[3.0, 0.0]), 1);
    assert_eq!(p_stable_cell(&a, 0.0, 2.0, &[2.0, 5.0]), 1);
    assert_eq!(p_stable_cell(&a, 0.0, 2.0, &[4.0, 0.0]), 2);
    assert_eq!(p_stable_cell(&a, 0.0, 2.0, &[-0.5, 0.0]), -1);
}

#[test]
fn sim_bit_is_orientation_in_the_plane() {
    // Lean: simBit_eq_orient -- the bit for normal r is the orientation of p against the line
    // through the origin along (r1, −r0)
    let mut g = SplitMix64::new(5);
    for _ in 0..1000 {
        let r = [g.standard_normal(), g.standard_normal()];
        let p = [g.standard_normal(), g.standard_normal()];
        assert_eq!(
            sim_bit(&r, &p),
            orient2d([0.0, 0.0], [r[1], -r[0]], p) >= 0.0
        );
    }
}

#[test]
fn simhash_collides_at_rate_one_minus_angle_over_pi() {
    // Statistical (Charikar 2002): the collision probability is not proved in Lean; this test
    // holds it. Two unit vectors at angle θ = π/3 share a bit
    // with probability 1 − θ/π = 2/3. Over 20 000 seeded planes the standard error is 0.0033;
    // 0.015 is over four of them.
    let theta = std::f64::consts::FRAC_PI_3;
    let (u, v) = ([1.0, 0.0, 0.0], [theta.cos(), theta.sin(), 0.0]);
    let h = SimHash::new(3, 1, 20_000, 17);
    let same = (0..20_000)
        .filter(|&t| h.key(t, &u) == h.key(t, &v))
        .count() as f64
        / 20_000.0;
    assert!((same - 2.0 / 3.0).abs() < 0.015, "rate {same}");
}

#[test]
fn p_stable_collides_at_the_datar_rate() {
    // Statistical (Datar et al. 2004, the Gaussian case): two points at distance c share a cell
    // with probability p(c) = 1 − 2Φ(−w/c) − 2/(√(2π)·w/c)·(1 − exp(−(w/c)²/2)). At w/c = 4,
    // p ≈ 0.8006. Over 20 000 seeded tables the standard error is 0.0028.
    let (w, c) = (4.0, 1.0);
    let h = PStable::new(2, 1, 20_000, w, 23);
    let (u, v) = ([0.0, 0.0], [c, 0.0]);
    let same = (0..20_000)
        .filter(|&t| h.key(t, &u) == h.key(t, &v))
        .count() as f64
        / 20_000.0;
    assert!(
        (same - datar_rate(w / c)).abs() < 0.015,
        "rate {same}, formula {}",
        datar_rate(w / c)
    );
}

/// Abramowitz–Stegun 7.1.26, |error| < 1.5e-7.
fn erf(x: f64) -> f64 {
    let t = 1.0 / (1.0 + 0.327_591_1 * x.abs());
    let poly = 0.254_829_592
        + t * (-0.284_496_736 + t * (1.421_413_741 + t * (-1.453_152_027 + t * 1.061_405_429)));
    let y = 1.0 - t * poly * (-x * x).exp();
    if x >= 0.0 {
        y
    } else {
        -y
    }
}

fn datar_rate(r: f64) -> f64 {
    let phi = |x: f64| 0.5 * (1.0 + erf(x / std::f64::consts::SQRT_2));
    1.0 - 2.0 * phi(-r)
        - 2.0 / ((2.0 * std::f64::consts::PI).sqrt() * r) * (1.0 - (-r * r / 2.0).exp())
}

#[test]
fn shapes_and_keys() {
    let h = SimHash::new(4, 10, 3, 1);
    assert_eq!((h.dim(), h.tables()), (4, 3));
    assert!(h.key(0, &[1.0, 2.0, 3.0, 4.0]) < 1 << 10);
    let p = PStable::new(4, 5, 2, 1.5, 1);
    assert_eq!(p.key(1, &[0.0; 4]).len(), 5);
}

#[test]
#[should_panic(expected = "bits")]
fn simhash_bits_are_bounded() {
    let _ = SimHash::new(4, 65, 1, 0);
}

#[test]
#[should_panic(expected = "w")]
fn p_stable_width_is_positive() {
    let _ = PStable::new(4, 1, 1, 0.0, 0);
}

proptest! {
    #[test]
    fn exact_when_the_neighbor_collides(
        rows in prop::collection::vec([-8i32..8, -8i32..8], 1..60), q in [-8i32..8, -8i32..8], seed in any::<u64>(),
    ) {
        // Lean: lshQuery_eq_scanNearest -- whenever the scan's answer is a candidate, LSH returns it
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let q = q.map(f64::from);
        let idx = LshIndex::new(p.clone(), SimHash::new(2, 2, 3, seed));
        let truth = scan::nearest(&p, &q).unwrap();
        if idx.candidates(&q).contains(&truth) {
            prop_assert_eq!(idx.nearest(&q), Some(truth));
        }
    }

    #[test]
    fn answer_beats_every_candidate(
        rows in prop::collection::vec([-8i32..8, -8i32..8], 1..60), q in [-8i32..8, -8i32..8],
        seed in any::<u64>(), k in 0usize..6,
    ) {
        // Lean: lshQuery_le_candidates -- the re-rank is the scan over the candidates
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let q = q.map(f64::from);
        let idx = LshIndex::new(p.clone(), PStable::new(2, 2, 3, 3.0, seed));
        let cands = idx.candidates(&q);
        prop_assert!(cands.windows(2).all(|w| w[0] < w[1]));
        prop_assert_eq!(idx.k_nearest(&q, k), scan::k_nearest_among(&p, &cands, &q, k));
    }

    #[test]
    fn a_stored_query_is_its_own_candidate(
        rows in prop::collection::vec([-8i32..8, -8i32..8], 1..60), i in any::<prop::sample::Index>(), seed in any::<u64>(),
    ) {
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let i = i.index(p.len());
        let idx = LshIndex::new(p.clone(), SimHash::new(2, 3, 2, seed));
        prop_assert!(idx.candidates(p.get(i)).contains(&i));
        prop_assert_eq!(idx.k_nearest(p.get(i), 1)[0].sq_dist, 0.0);
    }
}

#[test]
fn a_huge_k_returns_every_candidate() {
    let idx = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    for k in [1usize << 40, usize::MAX] {
        assert_eq!(idx.k_nearest(&[4.0, 4.0], k).len(), 2);
    }
}

#[cfg(feature = "unchecked")]
#[test]
fn the_unchecked_constructors_take_the_parameters_new_draws() {
    // The same parameters as `new` draws give the same family.
    let s = SimHash::new(3, 4, 2, 7);
    assert_eq!(SimHash::from_planes(3, 4, 2, s.planes.clone()), s);
    let p = PStable::new(3, 2, 3, 1.5, 7);
    assert_eq!(
        PStable::from_params(3, 2, 3, 1.5, p.a.clone(), p.b.clone()),
        p
    );
    // Given normals: table 0 is the axes, table 1 their negations. Bit i is plane i's side, a
    // point on a plane on the non-negative side.
    let s = SimHash::from_planes(2, 2, 2, vec![1.0, 0.0, 0.0, 1.0, -1.0, 0.0, 0.0, -1.0]);
    assert_eq!(s.key(0, &[1.0, -1.0]), 0b01);
    assert_eq!(s.key(1, &[1.0, -1.0]), 0b10);
    assert_eq!(s.key(0, &[0.0, 0.0]), 0b11);
    // Given directions and offsets: table 1's cells are ⌊(a·p + b) / w⌋ for its two (a, b).
    let p = PStable::from_params(
        1,
        2,
        2,
        2.0,
        vec![1.0, -1.0, 1.0, 2.0],
        vec![0.0, 0.0, 1.0, 3.0],
    );
    assert_eq!(p.key(0, &[3.0]), vec![1, -2]);
    assert_eq!(p.key(1, &[3.0]), vec![2, 4]);
}

#[cfg(feature = "unchecked")]
#[test]
#[should_panic(expected = "plane entries")]
fn the_unchecked_simhash_needs_tables_times_bits_normals() {
    let _ = SimHash::from_planes(2, 2, 1, vec![1.0, 0.0]);
}

#[cfg(feature = "unchecked")]
#[test]
#[should_panic(expected = "w")]
fn the_unchecked_p_stable_width_is_positive() {
    let _ = PStable::from_params(1, 1, 1, 0.0, vec![1.0], vec![0.0]);
}

#[cfg(feature = "unchecked")]
#[test]
#[should_panic(expected = "offsets")]
fn the_unchecked_p_stable_needs_one_offset_per_direction() {
    let _ = PStable::from_params(1, 1, 2, 1.0, vec![1.0, 1.0], vec![0.0]);
}

/// The Lean examples' index with its one table's buckets replaced.
fn quadrant_with(buckets: &[((bool, bool), &[u32])]) -> LshIndex<Quadrant> {
    let mut idx = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    idx.buckets = vec![buckets.iter().map(|(k, ids)| (*k, ids.to_vec())).collect()];
    idx
}

#[test]
fn in_its_bucket_fails_alone_on_each_defect() {
    // Lean: the AlgoDesignTests/Geometry.lean `lshWith` examples
    let good = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    assert!(good.is_in_its_bucket() && good.is_valid());
    assert_eq!(good.buckets[0][&(true, true)], vec![0, 2]);
    let broken = [
        quadrant_with(&[((true, true), &[0]), ((false, true), &[1, 2])]), // another key's bucket
        quadrant_with(&[((true, true), &[0, 2, 3]), ((false, true), &[1])]), // past the points
        quadrant_with(&[((true, true), &[0]), ((false, true), &[1])]),    // a point missing
    ];
    for idx in &broken {
        assert!(!idx.is_in_its_bucket());
        assert_eq!(idx.check_valid(), Err("invariant 1 (in_its_bucket)"));
    }
    let mut no_table = good.clone();
    no_table.buckets.clear();
    assert!(!no_table.is_in_its_bucket());
}

#[test]
fn the_pieces_not_in_the_box_fail_alone() {
    // Lean: OneBucketPerKey, EachPointOncePerTable
    let good = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    assert!(good.is_one_bucket_per_key() && good.is_each_point_once_per_table());
    // an empty bucket under a key no point has: only one_bucket_per_key fails
    let empty = quadrant_with(&[
        ((true, true), &[0, 2]),
        ((false, true), &[1]),
        ((false, false), &[]),
    ]);
    assert!(empty.is_in_its_bucket() && empty.is_each_point_once_per_table());
    assert!(!empty.is_one_bucket_per_key());
    assert_eq!(
        empty.check_valid(),
        Err("not in the box (one_bucket_per_key)")
    );
    // a point stored twice in its own bucket: only each_point_once_per_table fails
    let twice = quadrant_with(&[((true, true), &[0, 2, 0]), ((false, true), &[1])]);
    assert!(twice.is_in_its_bucket() && twice.is_one_bucket_per_key());
    assert!(!twice.is_each_point_once_per_table());
    assert_eq!(
        twice.check_valid(),
        Err("not in the box (each_point_once_per_table)")
    );
}

#[test]
fn equal_indexes_compare_equal() {
    let rows = [[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]];
    let a = LshIndex::new(pts(&rows), SimHash::new(2, 3, 2, 7));
    assert_eq!(a, LshIndex::new(pts(&rows), SimHash::new(2, 3, 2, 7)));
    assert_ne!(a, LshIndex::new(pts(&rows), SimHash::new(2, 3, 2, 8)));
}

#[test]
#[should_panic(expected = "overflows usize")]
fn a_family_too_large_to_index_panics() {
    let _ = SimHash::new(usize::MAX / 2, 64, 1, 0);
}

#[test]
#[should_panic(expected = "overflows usize")]
fn a_p_stable_family_too_large_to_index_panics() {
    let _ = PStable::new(usize::MAX / 2, 3, 1, 1.0, 0);
}

#[test]
fn measured_exactly_on_the_lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean `MeasuredExactly` examples
    let idx = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    let q = [9.0, 9.0];
    assert!(is_measured_exactly(&idx, &q, 1, &[2]));
    assert!(!is_measured_exactly(&idx, &q, 1, &[0])); // a farther candidate
    assert!(!is_measured_exactly(&idx, &q, 2, &[2, 2])); // a repeat
    assert!(!is_measured_exactly(&idx, &q, 2, &[2])); // short
    assert!(!is_measured_exactly(&idx, &q, 1, &[1])); // not a candidate
    assert!(!is_measured_exactly(&idx, &[9.0], 1, &[2])); // wrong dimension: false, no panic
    assert!(!is_measured_exactly(&idx, &[f64::NAN, 0.0], 1, &[2]));
    assert!(is_measured_exactly(&idx, &q, 0, &[]));
    // a candidate past the points cannot be measured: every answer fails, the one right on the
    // stored points included
    let past = quadrant_with(&[((true, true), &[0, 2, 7]), ((false, true), &[1])]);
    assert!(!is_measured_exactly(&past, &[1.0, 1.0], 1, &[7]));
    assert!(!is_measured_exactly(&past, &[1.0, 1.0], 1, &[0]));
}

proptest! {
    #[test]
    fn the_build_and_every_answer_keep_the_box(
        rows in prop::collection::vec([-8i32..8, -8i32..8], 0..40), q in [-8i32..8, -8i32..8],
        seed in any::<u64>(), k in 0usize..6,
    ) {
        // Lean: valid_build, measuredExactly_kNearest
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let q = q.map(f64::from);
        let sim = LshIndex::new(pts(&rows), SimHash::new(2, 2, 3, seed));
        let pst = LshIndex::new(pts(&rows), PStable::new(2, 1, 2, 2.0, seed));
        prop_assert!(sim.is_valid() && pst.is_valid());
        let ids = |v: Vec<Neighbor>| v.iter().map(|n| n.id).collect::<Vec<_>>();
        prop_assert!(is_measured_exactly(&sim, &q, k, &ids(sim.k_nearest(&q, k))));
        prop_assert!(is_measured_exactly(&pst, &q, k, &ids(pst.k_nearest(&q, k))));
        prop_assert!(is_measured_exactly(&sim, &q, 1, &sim.nearest(&q).into_iter().collect::<Vec<_>>()));
    }
}

/// The Lean examples' family, but hashing points of dimension 3.
#[derive(Debug, Clone)]
struct Quadrant3;

impl HashFamily for Quadrant3 {
    type Key = (bool, bool);
    fn dim(&self) -> usize {
        3
    }
    fn tables(&self) -> usize {
        1
    }
    fn key(&self, _: usize, v: &[f64]) -> (bool, bool) {
        (sim_bit(&[1.0, 0.0], &v[..2]), sim_bit(&[0.0, 1.0], &v[..2]))
    }
}

#[test]
fn measured_exactly_reads_the_points_dimension() {
    // An unchecked index whose family hashes dimension 3 over points of dimension 2: the query's
    // dimension is checked against the points', as in the Python.
    let good = LshIndex::new(pts(&[[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]]), Quadrant);
    let odd = LshIndex {
        points: good.points().clone(),
        family: Quadrant3,
        buckets: good.buckets.clone(),
    };
    assert!(!is_measured_exactly(&odd, &[9.0, 9.0, 0.0], 1, &[2]));
    assert!(is_measured_exactly(&odd, &[9.0, 9.0], 1, &[2]));
}
