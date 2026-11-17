//! RaBitQ, transcribed from Gao–Long 2024 §3 (Algorithm 1, the index phase; Algorithm 2, the
//! query phase): one bit per coordinate after a seeded random orthogonal rotation, and an
//! **unbiased** estimator of the inner product (Eq. 13, Theorem 3.2), used as a cheap filter
//! before an exact re-rank, as an option of the graph index ([`Hnsw::search_quantized`]); the
//! Python twin leaves the query unquantized. [`Rabitq`] lists the steps. Theorem 3.2's error
//! bound is probabilistic and not proved in the Lean. [`SignCodes`] is the biased baseline: sign
//! bits of `o − c` with no rotation and `⟨o, q⟩ ≈ ⟨x̄, q⟩`, through the same quantized query and
//! bitwise inner product.
//!
//! On the graph index the combination is this book's, not the paper's: Gao–Long run RaBitQ inside
//! an inverted-file index (§4) and leave graph indexes to future work (§7). Here one centroid
//! serves the whole dataset, the walk ranks nodes by the estimated distance, and every candidate
//! in its final `ef` is re-checked exactly. So the answer has exact distances and exact order
//! among those candidates, but it is not guaranteed to contain the true nearest neighbors: the
//! paper's re-ranking guarantee does not transfer to the walk. The paper's bound-based skip (§4: a
//! candidate whose lower bound, Eq. 16 with ε₀ = 1.9, exceeds the k-th exact distance is not
//! re-checked) is left out: the walk, not the re-check, is where
//! a query's time goes. The AGPL implementation of RaBitQ is not a dependency.
//!
//! **Against the Python, and how fast.** The Python leaves the query unquantized, so its estimates,
//! and the walk they steer, differ from these: the speed is the `B_Q`-bit query and its ANDs and
//! popcounts.

use crate::geometry::{
    hnsw::Hnsw,
    point::{check_query, dot, Points},
    rng::SplitMix64,
    scan::{k_nearest_among, Neighbor},
};

/// Estimated squared distances to encoded points: what [`Hnsw::search_quantized`] traverses
/// with, so [`Rabitq`] and [`SignCodes`] can be compared through the same search.
pub trait DistanceEstimator {
    /// A query prepared for estimation.
    type Query;
    /// The number of encoded points.
    fn len(&self) -> usize;
    /// Whether no points are encoded.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Prepare `q` for estimation.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    fn prepare(&self, q: &[f64]) -> Self::Query;
    /// The estimate of point `i`'s squared distance to the query.
    fn estimate_sq_dist(&self, query: &Self::Query, i: usize) -> f64;
    /// The bytes stored per encoded point: the code, and the per-point factors the estimate
    /// reads.
    fn bytes_per_vector(&self) -> usize;
}

/// One-bit codes with RaBitQ's rotation and unbiased estimator.
///
/// - Every vector is normalized around the centroid `c`: `o = (o_r − c)/‖o_r − c‖` (§3.1.1).
/// - `P` is a seeded random orthogonal matrix (§3.1.2), from modified Gram–Schmidt run twice on a
///   Gaussian `D × D` matrix. Its transpose is stored.
/// - The code is the sign of each coordinate of `Pᵀo` (§3.1.3): `x̄ = (2x̄_b − 1)/√D`.
/// - Precomputed per vector: `‖o_r − c‖` and `⟨ō, o⟩ = ⟨x̄, Pᵀo⟩` (Algorithm 1, line 4).
/// - The estimate of `⟨o, q⟩` is `⟨ō, q⟩ / ⟨ō, o⟩` (Eq. 13, Theorem 3.2), with
///   `⟨ō, q⟩ = ⟨x̄, q'⟩`, `q' = Pᵀq` (Eq. 17), and the distance follows by Eq. (2):
///   `‖o_r − q_r‖² = ‖o_r − c‖² + ‖q_r − c‖² − 2‖o_r − c‖‖q_r − c‖⟨o, q⟩`.
/// - **The query is quantized too** (Algorithm 2 line 2, §3.3.1): each coordinate of `q'` becomes
///   a [`B_Q`]-bit unsigned integer by randomized uniform scalar quantization (Eq. 18),
///   `q̄_u[i] = ⌊(q'[i] − v_l)/Δ + u_i⌋` with `v_l = min q'`, `Δ = (max q' − v_l)/(2^B_Q − 1)`
///   and `u_i` uniform in `[0, 1)`, so the rounding is unbiased.
/// - **`⟨x̄, q̄⟩` is then bitwise** (§3.3.2, Eqs. 19–22): `q̄_u` is split into `B_Q` bit planes,
///   and `⟨x̄_b, q̄_u⟩ = Σ_j 2^j · popcount(x̄_b AND q̄_u^(j))`, so each estimate is `B_Q` ANDs and
///   popcounts per 64 coordinates instead of `D` floating-point operations.
#[derive(Debug, Clone, PartialEq)]
pub struct Rabitq {
    codes: Codes,
}

/// One-bit codes without rotation or correction: the biased baseline.
#[derive(Debug, Clone, PartialEq)]
pub struct SignCodes {
    codes: Codes,
}

/// The bits per coordinate of the quantized query: the paper's `B_q = 4` (§3.3.1, verified in
/// §5.2.5), at which the quantization's error is negligible beside the estimator's.
pub const B_Q: usize = 4;

/// A query prepared for estimation (Algorithm 2, lines 1–2): its distance to the centroid, its
/// quantized coordinates and their bit planes.
#[derive(Debug, Clone, PartialEq)]
pub struct RabitqQuery {
    /// `q' = Pᵀ(q_r − c)/‖q_r − c‖`, before quantization.
    q: Vec<f64>,
    norm: f64,
    /// `v_l = min q'` and the step `Δ`.
    v_l: f64,
    delta: f64,
    /// `q̄_u`, one `B_Q`-bit value per coordinate.
    q_u: Vec<u8>,
    /// `Σ q̄_u[i]`.
    sum_q_u: f64,
    /// Bit plane `j` of `q̄_u` at `planes[j * words..(j + 1) * words]`.
    planes: Vec<u64>,
}

impl Rabitq {
    /// Encode `points`; the seed fixes the rotation.
    ///
    /// # Panics
    /// If there are no points.
    #[must_use]
    pub fn new(points: &Points, seed: u64) -> Self {
        Rabitq {
            codes: Codes::new(
                points,
                Some(random_orthogonal(points.dim(), seed)),
                true,
                seed,
            ),
        }
    }

    /// Normalize and rotate the query, then quantize it (Algorithm 2, lines 1–2).
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn prepare(&self, q: &[f64]) -> RabitqQuery {
        self.codes.prepare(q)
    }

    /// The estimate of `⟨o, q⟩` for point `i` (Eq. 13).
    #[must_use]
    pub fn estimate_inner(&self, query: &RabitqQuery, i: usize) -> f64 {
        self.codes.estimate_inner(query, i)
    }

    /// The estimate of point `i`'s squared distance to the query (Eq. 2).
    #[must_use]
    pub fn estimate_sq_dist(&self, query: &RabitqQuery, i: usize) -> f64 {
        self.codes.estimate_sq_dist(query, i)
    }

    /// The number of encoded points.
    #[must_use]
    pub fn len(&self) -> usize {
        self.codes.len()
    }

    /// Whether no points are encoded.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.codes.len() == 0
    }

    /// `Pᵀ`, `D × D` row-major.
    #[cfg(test)]
    fn rotation_transposed(&self) -> &[f64] {
        self.codes.rotation.as_deref().unwrap_or(&[])
    }

    /// What the index phase stored: the rotation, the centroid, every code and both factors.
    /// Public for tests; not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn stored(&self) -> StoredCodes {
        self.codes.stored()
    }
}

/// What [`Rabitq`] or [`SignCodes`] stored, laid out for comparison: `rotation` holds the rows
/// of `Pᵀ` (each code coordinate is a row times the normalized vector) and is empty for
/// [`SignCodes`]; `bits[i][j]` is bit `j` of point `i`'s code; `norms` is `‖o_r − c‖` and `dots`
/// is `⟨ō, o⟩`, per point. Public for tests; not part of the API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq)]
pub struct StoredCodes {
    /// The rows of `Pᵀ`, or none.
    pub rotation: Vec<Vec<f64>>,
    /// The centroid `c`.
    pub centroid: Vec<f64>,
    /// One bit per coordinate, per point.
    pub bits: Vec<Vec<bool>>,
    /// `‖o_r − c‖` per point.
    pub norms: Vec<f64>,
    /// `⟨ō, o⟩` per point.
    pub dots: Vec<f64>,
}

impl SignCodes {
    /// Encode `points` by the signs of `o − c`; the seed fixes the query's randomized rounding.
    ///
    /// # Panics
    /// If there are no points.
    #[must_use]
    pub fn new(points: &Points, seed: u64) -> Self {
        SignCodes {
            codes: Codes::new(points, None, false, seed),
        }
    }

    /// Normalize and quantize the query.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn prepare(&self, q: &[f64]) -> RabitqQuery {
        self.codes.prepare(q)
    }

    /// The uncorrected estimate `⟨x̄, q⟩` of `⟨o, q⟩` for point `i`.
    #[must_use]
    pub fn estimate_inner(&self, query: &RabitqQuery, i: usize) -> f64 {
        self.codes.estimate_inner(query, i)
    }

    /// The estimate of point `i`'s squared distance to the query, by Eq. (2) with the
    /// uncorrected inner product.
    #[must_use]
    pub fn estimate_sq_dist(&self, query: &RabitqQuery, i: usize) -> f64 {
        self.codes.estimate_sq_dist(query, i)
    }

    /// What the index phase stored, as for [`Rabitq`]'s; the rotation is empty. Public for tests;
    /// not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn stored(&self) -> StoredCodes {
        self.codes.stored()
    }
}

impl DistanceEstimator for Rabitq {
    type Query = RabitqQuery;

    fn len(&self) -> usize {
        Rabitq::len(self)
    }

    fn prepare(&self, q: &[f64]) -> RabitqQuery {
        Rabitq::prepare(self, q)
    }

    fn estimate_sq_dist(&self, query: &RabitqQuery, i: usize) -> f64 {
        Rabitq::estimate_sq_dist(self, query, i)
    }

    /// The code, `‖o_r − c‖` and `⟨ō, o⟩`.
    fn bytes_per_vector(&self) -> usize {
        self.codes.words * 8 + 16
    }
}

impl DistanceEstimator for SignCodes {
    type Query = RabitqQuery;

    fn len(&self) -> usize {
        self.codes.len()
    }

    fn prepare(&self, q: &[f64]) -> RabitqQuery {
        SignCodes::prepare(self, q)
    }

    fn estimate_sq_dist(&self, query: &RabitqQuery, i: usize) -> f64 {
        SignCodes::estimate_sq_dist(self, query, i)
    }

    /// The code and `‖o_r − c‖`; the uncorrected estimate never reads `⟨ō, o⟩`.
    fn bytes_per_vector(&self) -> usize {
        self.codes.words * 8 + 8
    }
}

impl Hnsw {
    /// The `min(k, n)` nearest of the candidates HNSW keeps when its walk ranks nodes by estimated
    /// distances ([`Rabitq`]'s, or the [`SignCodes`] baseline's): a cheap filter, then an exact
    /// check of every candidate in the final `ef`, so the returned distances and their order are
    /// exact. Whether the true nearest points are among the candidates is not guaranteed (see the
    /// module documentation: this combination is the book's, not the paper's).
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate, or `codes` encodes a different
    /// number of points.
    #[must_use]
    pub fn search_quantized<E: DistanceEstimator>(
        &self,
        q: &[f64],
        k: usize,
        ef: usize,
        codes: &E,
    ) -> Vec<Neighbor> {
        check_query(self.points().dim(), q);
        assert_eq!(
            codes.len(),
            self.len(),
            "the codes do not encode this index's points"
        );
        if k == 0 || self.is_empty() {
            return Vec::new();
        }
        let rq = codes.prepare(q);
        let est = |i: u32| codes.estimate_sq_dist(&rq, i as usize);
        let ids: Vec<usize> = self
            .beam_by(&est, ef.max(k))
            .into_iter()
            .map(|(_, i)| i as usize)
            .collect();
        k_nearest_among(self.points(), &ids, q, k)
    }
}

/// The codes both types share.
#[derive(Debug, Clone, PartialEq)]
struct Codes {
    dim: usize,
    centroid: Vec<f64>,
    /// `Pᵀ`, `D × D` row-major, or `None` for no rotation.
    rotation: Option<Vec<f64>>,
    /// Divide by `⟨ō, o⟩` (RaBitQ) or not (the baseline).
    corrected: bool,
    words: usize,
    /// One record of `stride` words per point, so an estimate reads one place per point: the code
    /// (bit `i` is set iff coordinate `i` of the rotated vector is `≥ 0`), then `‖o_r − c‖` and,
    /// when corrected, `⟨ō, o⟩`, as their bits (`⟨ō, o⟩` is 1 for a point at the centroid, whose
    /// estimate does not use it).
    records: Vec<u64>,
    /// `words + 2` when corrected, else `words + 1`: the baseline never reads `⟨ō, o⟩`, so its
    /// records stay as small as the code and the norm.
    stride: usize,
    /// `⟨ō, o⟩` per point for the baseline, kept apart for `stored` only; empty when
    /// corrected.
    unread_dots: Vec<f64>,
    /// Mixed with each query's coordinates to seed its randomized rounding, so preparing the
    /// same query twice gives the same codes.
    seed: u64,
}

impl Codes {
    fn new(points: &Points, rotation: Option<Vec<f64>>, corrected: bool, seed: u64) -> Self {
        assert!(!points.is_empty(), "RaBitQ needs at least one point");
        let dim = points.dim();
        let n = points.len() as f64;
        let mut centroid = vec![0.0; dim];
        for p in points.iter() {
            for (c, x) in centroid.iter_mut().zip(p) {
                *c += x;
            }
        }
        centroid.iter_mut().for_each(|c| *c /= n);
        let words = dim.div_ceil(64);
        let stride = words + 1 + usize::from(corrected);
        let mut codes = Codes {
            dim,
            centroid,
            rotation,
            corrected,
            words,
            records: Vec::with_capacity(points.len() * stride),
            stride,
            unread_dots: Vec::new(),
            seed,
        };
        // Divided, not multiplied by a rounded `1/√D`: `x̄ = (2x̄_b − 1)/√D`, as the Python divides
        // (the tests compare the two bit for bit). Build time only, one division per vector.
        let sqrt_d = (dim as f64).sqrt();
        for p in points.iter() {
            let (y, norm) = codes.normalize(p);
            let mut word = vec![0u64; words];
            for (i, &yi) in y.iter().enumerate() {
                if yi >= 0.0 {
                    word[i / 64] |= 1 << (i % 64);
                }
            }
            let ob_o: f64 = y.iter().map(|v| v.abs()).sum::<f64>() / sqrt_d;
            let dot = if norm == 0.0 { 1.0 } else { ob_o };
            codes.records.extend_from_slice(&word);
            codes.records.push(norm.to_bits());
            if corrected {
                codes.records.push(dot.to_bits());
            } else {
                codes.unread_dots.push(dot);
            }
        }
        codes
    }

    /// The number of encoded points.
    fn len(&self) -> usize {
        self.records.len() / self.stride
    }

    /// Point `i`'s record: its code, then `‖o_r − c‖` and, when corrected, `⟨ō, o⟩`, as bits.
    fn record(&self, i: usize) -> &[u64] {
        &self.records[i * self.stride..(i + 1) * self.stride]
    }

    /// Point `i`'s code.
    #[cfg(any(test, feature = "unchecked"))]
    fn code(&self, i: usize) -> &[u64] {
        &self.record(i)[..self.words]
    }

    /// Point `i`'s `‖o_r − c‖`.
    #[cfg(feature = "unchecked")]
    fn norm(&self, i: usize) -> f64 {
        f64::from_bits(self.record(i)[self.words])
    }

    /// Point `i`'s `⟨ō, o⟩`.
    #[cfg(any(test, feature = "unchecked"))]
    fn dot(&self, i: usize) -> f64 {
        if self.corrected {
            f64::from_bits(self.record(i)[self.words + 1])
        } else {
            self.unread_dots[i]
        }
    }

    #[cfg(feature = "unchecked")]
    fn stored(&self) -> StoredCodes {
        let rotation = self.rotation.as_ref().map_or_else(Vec::new, |pt| {
            pt.chunks_exact(self.dim).map(<[f64]>::to_vec).collect()
        });
        let n = self.len();
        let bits = (0..n)
            .map(|i| {
                let code = self.code(i);
                (0..self.dim)
                    .map(|j| code[j / 64] >> (j % 64) & 1 == 1)
                    .collect()
            })
            .collect();
        StoredCodes {
            rotation,
            centroid: self.centroid.clone(),
            bits,
            norms: (0..n).map(|i| self.norm(i)).collect(),
            dots: (0..n).map(|i| self.dot(i)).collect(),
        }
    }

    /// `(Pᵀ(v − c)/‖v − c‖, ‖v − c‖)`; the zero vector and 0 if `v` is the centroid.
    fn normalize(&self, v: &[f64]) -> (Vec<f64>, f64) {
        let diff: Vec<f64> = v.iter().zip(&self.centroid).map(|(a, c)| a - c).collect();
        let norm = dot(&diff, &diff).sqrt();
        if norm == 0.0 {
            return (vec![0.0; self.dim], 0.0);
        }
        let unit: Vec<f64> = diff.iter().map(|x| x / norm).collect();
        let y = match &self.rotation {
            Some(pt) => pt
                .chunks_exact(self.dim)
                .map(|row| dot(row, &unit))
                .collect(),
            None => unit,
        };
        (y, norm)
    }

    /// Algorithm 2, lines 1–2: normalize and rotate (`q'`), then quantize by Eq. 18.
    fn prepare(&self, q_r: &[f64]) -> RabitqQuery {
        check_query(self.dim, q_r);
        let (q, norm) = self.normalize(q_r);
        let levels = (1_u32 << B_Q) - 1;
        let v_l = q.iter().copied().fold(f64::INFINITY, f64::min);
        let v_r = q.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        let delta = (v_r - v_l) / f64::from(levels);
        let mut rng = SplitMix64::new(q_r.iter().fold(self.seed, |h, x| {
            (h ^ x.to_bits()).wrapping_mul(0x9e37_79b9_7f4a_7c15)
        }));
        let q_u: Vec<u8> = q
            .iter()
            .map(|&x| {
                if delta == 0.0 {
                    return 0;
                }
                let level = ((x - v_l) / delta + rng.next_f64()).floor();
                // Clamped: rounding in `(x − v_l)/Δ` can land a hair outside `[0, 2^B_Q − 1]`.
                level.clamp(0.0, f64::from(levels)) as u8
            })
            .collect();
        let mut planes = vec![0_u64; B_Q * self.words];
        for (i, &u) in q_u.iter().enumerate() {
            for j in 0..B_Q {
                if u >> j & 1 == 1 {
                    planes[j * self.words + i / 64] |= 1 << (i % 64);
                }
            }
        }
        let sum_q_u = q_u.iter().map(|&u| f64::from(u)).sum();
        RabitqQuery {
            q,
            norm,
            v_l,
            delta,
            q_u,
            sum_q_u,
            planes,
        }
    }

    /// `⟨x̄, q̄⟩` by Eqs. 19–22: `B_Q` ANDs and popcounts per word of the code.
    fn inner_bits(&self, query: &RabitqQuery, code: &[u64]) -> f64 {
        let mut x_dot_q = 0_u32;
        for j in 0..B_Q {
            let plane = &query.planes[j * self.words..(j + 1) * self.words];
            let ones: u32 = code
                .iter()
                .zip(plane)
                .map(|(c, p)| (c & p).count_ones())
                .sum();
            x_dot_q += ones << j;
        }
        let x_ones: u32 = code.iter().map(|c| c.count_ones()).sum();
        let sqrt_d = (self.dim as f64).sqrt();
        (2.0 * query.delta * f64::from(x_dot_q) + 2.0 * query.v_l * f64::from(x_ones)
            - query.delta * query.sum_q_u)
            / sqrt_d
            - sqrt_d * query.v_l
    }

    /// `⟨x̄, q̄⟩`, divided by `⟨ō, o⟩` when corrected (Eq. 13).
    fn estimate_inner(&self, query: &RabitqQuery, i: usize) -> f64 {
        self.inner_of(query, self.record(i))
    }

    /// [`Codes::estimate_inner`] from a point's record.
    fn inner_of(&self, query: &RabitqQuery, record: &[u64]) -> f64 {
        let ob_q = self.inner_bits(query, &record[..self.words]);
        if self.corrected {
            ob_q / f64::from_bits(record[self.words + 1])
        } else {
            ob_q
        }
    }

    /// Eq. (2), with the estimated inner product; one record read.
    fn estimate_sq_dist(&self, query: &RabitqQuery, i: usize) -> f64 {
        let record = self.record(i);
        let (o, q) = (f64::from_bits(record[self.words]), query.norm);
        o * o + q * q - 2.0 * o * q * self.inner_of(query, record)
    }
}

/// A seeded random orthogonal `d × d` matrix, row-major, rows orthonormal: modified Gram–Schmidt,
/// run twice for numerical orthogonality, on seeded Gaussian rows. A row that collapses (an event
/// of probability 0) is redrawn.
fn random_orthogonal(d: usize, seed: u64) -> Vec<f64> {
    let mut rng = SplitMix64::new(seed);
    let mut rows: Vec<Vec<f64>> = Vec::with_capacity(d);
    while rows.len() < d {
        let mut v: Vec<f64> = (0..d).map(|_| rng.standard_normal()).collect();
        for _ in 0..2 {
            for r in &rows {
                let proj = dot(r, &v);
                v.iter_mut().zip(r).for_each(|(x, y)| *x -= proj * y);
            }
        }
        let norm = dot(&v, &v).sqrt();
        if norm > 1e-6 {
            v.iter_mut().for_each(|x| *x /= norm);
            rows.push(v);
        }
    }
    rows.concat()
}

#[cfg(test)]
#[path = "unit_tests/rabitq.rs"]
mod tests;
