use super::*;
use crate::geometry::{
    hnsw::{Hnsw, HnswParams},
    point::{sq_dist, Points},
    rng::SplitMix64,
    scan,
};

/// `n` standard-normal points in `d` dimensions, seeded.
fn gaussian(n: usize, d: usize, seed: u64) -> Points {
    let mut r = SplitMix64::new(seed);
    Points::new(d, (0..n * d).map(|_| r.standard_normal()).collect()).unwrap()
}

#[test]
fn the_rotation_is_orthogonal() {
    let r = Rabitq::new(&gaussian(10, 32, 1), 7);
    let pt = r.rotation_transposed();
    for i in 0..32 {
        for j in 0..32 {
            let d: f64 = (0..32).map(|k| pt[i * 32 + k] * pt[j * 32 + k]).sum();
            assert!(
                (d - if i == j { 1.0 } else { 0.0 }).abs() < 1e-9,
                "({i}, {j}): {d}"
            );
        }
    }
}

#[test]
fn the_estimator_is_unbiased_in_the_mean() {
    // Statistical (Theorem 3.2, Eq. 13). Data {o, −o} has centroid 0, so o is its own normalized
    // vector; o = e1 and q = 0.6·e1 + 0.8·e2, so ⟨o, q⟩ = 0.6 exactly. Averaged over 400 seeded
    // rotations (D = 64; one estimate errs by about 0.1, so the mean's standard error is about
    // 0.005), RaBitQ's estimate is within 0.03 of 0.6. The uncorrected sign code, which is not
    // rotated, gives ⟨(1, …, 1)/8, q⟩ = 0.175 for every seed: biased by 0.425.
    let d = 64;
    let mut o = vec![0.0; d];
    o[0] = 1.0;
    let neg: Vec<f64> = o.iter().map(|x| -x).collect();
    let p = Points::from_rows(d, &[o.clone(), neg]).unwrap();
    let mut q = vec![0.0; d];
    q[0] = 0.6;
    q[1] = 0.8;
    let mean = (0..400)
        .map(|seed| {
            let r = Rabitq::new(&p, seed);
            r.estimate_inner(&r.prepare(&q), 0)
        })
        .sum::<f64>()
        / 400.0;
    assert!((mean - 0.6).abs() < 0.03, "RaBitQ mean {mean}");
    let s = SignCodes::new(&p, 0);
    let plain = s.estimate_inner(&s.prepare(&q), 0);
    assert!(
        (plain - 0.6).abs() > 0.3,
        "the uncorrected code should be biased here: {plain}"
    );
}

#[test]
fn a_vector_at_the_centroid_is_estimated_exactly() {
    let p = Points::from_rows(2, &[[1.0, 1.0], [-1.0, -1.0], [0.0, 0.0]]).unwrap();
    let r = Rabitq::new(&p, 1);
    let q = [3.0, 4.0];
    assert!((r.estimate_sq_dist(&r.prepare(&q), 2) - 25.0).abs() < 1e-12);
}

#[test]
fn estimates_track_distances() {
    // Not a bound (that is probabilistic, Theorem 3.2): on 500 Gaussian points in D = 128 the
    // estimated squared distances correlate with the exact ones; measured 0.850 (seeds as
    // here). The estimate's error on ⟨o, q⟩ is O(1/√D) ≈ 0.09, scaled by 2‖o‖‖q‖ ≈ 256,
    // comparable to the exact distances' own spread, so a correlation near 0.85 is what the
    // estimator gives here, not a defect. The floor 0.8 catches a broken code.
    let p = gaussian(500, 128, 3);
    let q = gaussian(1, 128, 4);
    let r = Rabitq::new(&p, 5);
    let rq = r.prepare(q.get(0));
    let est: Vec<f64> = (0..500).map(|i| r.estimate_sq_dist(&rq, i)).collect();
    let exact: Vec<f64> = (0..500).map(|i| sq_dist(p.get(i), q.get(0))).collect();
    let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len() as f64;
    let (me, mx) = (mean(&est), mean(&exact));
    let cov: f64 = est
        .iter()
        .zip(&exact)
        .map(|(a, b)| (a - me) * (b - mx))
        .sum();
    let var = |v: &[f64], m: f64| v.iter().map(|a| (a - m) * (a - m)).sum::<f64>();
    let corr = cov / (var(&est, me) * var(&exact, mx)).sqrt();
    assert!(corr > 0.8, "correlation {corr}");
}

#[test]
fn reranking_makes_the_answer_exact_on_the_candidates() {
    // The box's claim: a cheap filter, then an exact check. The returned distances are exact.
    let p = gaussian(1500, 32, 4).normalized().unwrap();
    let h = Hnsw::build(p.clone(), HnswParams::new(16));
    let codes = Rabitq::new(&p, 9);
    let q = gaussian(1, 32, 5).normalized().unwrap();
    for n in h.search_quantized(q.get(0), 10, 200, &codes) {
        assert_eq!(n.sq_dist, sq_dist(p.get(n.id), q.get(0)));
    }
    let truth = scan::nearest(&p, q.get(0)).unwrap();
    assert_eq!(h.search_quantized(q.get(0), 1, 200, &codes)[0].id, truth);
    assert!(h.search_quantized(q.get(0), 0, 200, &codes).is_empty());
}

#[test]
fn a_huge_k_returns_every_point() {
    let p = gaussian(40, 8, 6).normalized().unwrap();
    let h = Hnsw::build(p.clone(), HnswParams::new(4));
    let codes = Rabitq::new(&p, 1);
    for k in [1usize << 40, usize::MAX] {
        assert_eq!(h.search_quantized(p.get(3), k, 10, &codes).len(), 40);
    }
}

#[test]
fn sign_codes_drive_the_same_search() {
    // Sign codes steer the same traversal as RaBitQ's codes, and their answers are re-ranked
    // exactly too.
    let p = gaussian(1500, 32, 4).normalized().unwrap();
    let h = Hnsw::build(p.clone(), HnswParams::new(16));
    let codes = SignCodes::new(&p, 9);
    let q = gaussian(1, 32, 5).normalized().unwrap();
    let found = h.search_quantized(q.get(0), 10, 200, &codes);
    assert_eq!(found.len(), 10);
    for n in found {
        assert_eq!(n.sq_dist, sq_dist(p.get(n.id), q.get(0)));
    }
}

#[test]
fn bytes_per_vector_counts_the_code_and_its_factors() {
    // D = 100: two 64-bit words of code; RaBitQ adds ‖o_r − c‖ and ⟨ō, o⟩, the baseline only
    // ‖o_r − c‖.
    let p = gaussian(10, 100, 1);
    assert_eq!(Rabitq::new(&p, 1).bytes_per_vector(), 32);
    assert_eq!(SignCodes::new(&p, 1).bytes_per_vector(), 24);
    assert_eq!(DistanceEstimator::len(&Rabitq::new(&p, 1)), 10);
}

/// `⟨x̄, v⟩` for point `i`'s code, coordinate by coordinate: the definition the fast paths are
/// checked against.
fn code_inner(codes: &Codes, i: usize, v: &[f64]) -> f64 {
    let words = codes.code(i);
    let scale = 1.0 / (codes.dim as f64).sqrt();
    v.iter()
        .enumerate()
        .map(|(j, &x)| {
            let bit = words[j / 64] >> (j % 64) & 1;
            if bit == 1 {
                x * scale
            } else {
                -x * scale
            }
        })
        .sum()
}

#[test]
fn the_query_is_quantized_to_b_q_bits() {
    // §3.3.1, Eq. 18: q̄_u[i] = ⌊(q'[i] − v_l)/Δ + u_i⌋, Δ = (v_r − v_l)/(2^B_q − 1), B_q = 4.
    let p = gaussian(50, 100, 11);
    let r = Rabitq::new(&p, 3);
    let rq = r.prepare(gaussian(1, 100, 12).get(0));
    assert_eq!(B_Q, 4);
    assert_eq!(rq.q_u.len(), 100);
    assert!(rq.q_u.iter().all(|&v| v < 16));
    let (lo, hi) =
        rq.q.iter()
            .fold((f64::MAX, f64::MIN), |(a, b), &x| (a.min(x), b.max(x)));
    assert_eq!(rq.v_l, lo);
    assert!((rq.delta - (hi - lo) / 15.0).abs() < 1e-15);
    // Randomized rounding moves each coordinate by less than one step, to a neighboring level.
    for (&u, &x) in rq.q_u.iter().zip(&rq.q) {
        let level = (x - rq.v_l) / rq.delta;
        assert!((f64::from(u) - level).abs() < 1.0 + 1e-9, "{u} vs {level}");
    }
}

#[test]
fn the_bit_planes_compute_eqs_19_to_22() {
    // ⟨x̄, q̄⟩ from B_q AND-and-popcounts equals the coordinate-by-coordinate inner product with
    // q̄ = Δ·q̄_u + v_l·1.
    let p = gaussian(50, 100, 11);
    let r = Rabitq::new(&p, 3);
    let rq = r.prepare(gaussian(1, 100, 12).get(0));
    let q_bar: Vec<f64> = rq
        .q_u
        .iter()
        .map(|&u| rq.delta * f64::from(u) + rq.v_l)
        .collect();
    for i in 0..50 {
        let direct = code_inner(&r.codes, i, &q_bar);
        let fast = r.codes.inner_bits(&rq, r.codes.code(i));
        assert!(
            (direct - fast).abs() < 1e-9,
            "point {i}: {direct} vs {fast}"
        );
    }
}

#[test]
fn quantizing_the_query_costs_little_accuracy() {
    // §3.3.1: with B_q = 4 the quantization's error is small beside the estimator's own, which
    // is O(1/√D). On 500 Gaussian points in D = 128: the mean |⟨x̄, q̄⟩ − ⟨x̄, q'⟩| against the
    // mean error of the estimate itself.
    let p = gaussian(500, 128, 3);
    let q = gaussian(1, 128, 4);
    let r = Rabitq::new(&p, 5);
    let rq = r.prepare(q.get(0));
    let (mut quant, mut est) = (0.0, 0.0);
    for i in 0..500 {
        let exact_q = code_inner(&r.codes, i, &rq.q);
        quant += (r.codes.inner_bits(&rq, r.codes.code(i)) - exact_q).abs();
        let (o, _) = r.codes.normalize(p.get(i));
        let truth: f64 = o.iter().zip(&rq.q).map(|(a, b)| a * b).sum();
        est += (r.estimate_inner(&rq, i) - truth).abs();
    }
    let (quant, est) = (quant / 500.0, est / 500.0);
    assert!(
        quant < est / 4.0,
        "quantization error {quant}, estimator error {est}"
    );
}

#[test]
fn preparing_a_query_is_deterministic() {
    let p = gaussian(50, 100, 11);
    let r = Rabitq::new(&p, 3);
    let q = gaussian(1, 100, 12);
    let (a, b) = (r.prepare(q.get(0)), r.prepare(q.get(0)));
    assert_eq!(a, b);
}

#[cfg(feature = "unchecked")]
#[test]
fn stored_lays_out_what_the_index_phase_kept() {
    // D = 70 puts each code across two words, so the unpacking crosses a word boundary.
    let p = gaussian(9, 70, 21);
    let r = Rabitq::new(&p, 4);
    let s = r.stored();
    let rows: Vec<Vec<f64>> = r
        .rotation_transposed()
        .chunks_exact(70)
        .map(<[f64]>::to_vec)
        .collect();
    assert_eq!(s.rotation, rows);
    assert_eq!(s.centroid, r.codes.centroid);
    assert_eq!(
        (s.norms.clone(), s.dots.clone()),
        (
            (0..9).map(|i| r.codes.norm(i)).collect(),
            (0..9).map(|i| r.codes.dot(i)).collect()
        )
    );
    for (i, code) in s.bits.iter().enumerate() {
        let (y, _) = r.codes.normalize(p.get(i));
        let signs: Vec<bool> = y.iter().map(|&v| v >= 0.0).collect();
        assert_eq!(code, &signs, "point {i}");
    }
    let sc = SignCodes::new(&p, 4);
    let b = sc.stored();
    assert!(b.rotation.is_empty());
    assert_eq!(b.centroid, s.centroid);
    assert_eq!(
        (b.norms.clone(), b.dots.clone()),
        (
            (0..9).map(|i| sc.codes.norm(i)).collect(),
            (0..9).map(|i| sc.codes.dot(i)).collect()
        )
    );
    assert_eq!(b.bits.len(), 9);
    for (i, code) in b.bits.iter().enumerate() {
        // No rotation: the code is the sign of each coordinate of o − c itself.
        let signs: Vec<bool> = p
            .get(i)
            .iter()
            .zip(&b.centroid)
            .map(|(x, c)| x - c >= 0.0)
            .collect();
        assert_eq!(code, &signs, "point {i}");
    }
}

#[test]
fn the_stored_dot_divides_by_sqrt_d() {
    // ⟨ō, o⟩ = Σ|y_i| / √D, divided as the paper's x̄ = (2x̄_b − 1)/√D and the Python divide, not
    // multiplied by a rounded 1/√D: at D = 3 the two differ in the last bit. The pinned value is
    // the Python's for the same points, point 0, seed 3.
    let rows: Vec<[f64; 3]> = (0..60_i64)
        .map(|i| {
            [
                ((7 * i) % 13) as f64,
                ((5 * i) % 11) as f64,
                ((3 * i + i * i) % 17) as f64,
            ]
        })
        .collect();
    let p = Points::from_rows(3, &rows).unwrap();
    let r = Rabitq::new(&p, 3);
    assert_eq!(
        r.codes.dot(0).to_bits(),
        0.911_974_086_391_518_9_f64.to_bits()
    );
}
