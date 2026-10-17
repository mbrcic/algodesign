//! Random projection: multiply by a `k × d` matrix of independent N(0, 1/k) entries, drawn from a
//! seed (Dasgupta–Gupta 2003; BHK §2.9; Wright–Ma Thm 3.19). The Johnson–Lindenstrauss lemma says
//! that with `k = O(log n / ε²)` every pairwise distance among `n` points survives within a factor
//! `1 ± ε` with high probability. The matrix is dense: `k · d` multiplications per point.
//!
//! Lean: `LSH/Families.lean`, `dot_add`: each output coordinate is a dot product, so the
//! projection is linear. The JL bound itself is not proved there; a seeded statistical test
//! holds it.

use crate::geometry::{
    point::{check_query, dot, Points, PointsError},
    rng::SplitMix64,
};

/// A seeded `k × d_in` Gaussian projection.
#[derive(Debug, Clone, PartialEq)]
pub struct GaussianProjection {
    d_in: usize,
    k: usize,
    /// Row-major, `k` rows of `d_in` entries, each N(0, 1/k).
    matrix: Vec<f64>,
}

impl GaussianProjection {
    /// A projection from `d_in` to `k` dimensions; the same seed gives the same matrix.
    ///
    /// # Panics
    /// If `d_in == 0` or `k == 0`, or if `k × d_in` overflows `usize`.
    #[must_use]
    pub fn new(d_in: usize, k: usize, seed: u64) -> Self {
        assert!(d_in > 0 && k > 0, "a projection needs d_in ≥ 1 and k ≥ 1");
        let entries = k
            .checked_mul(d_in)
            .expect("a projection's k × d_in overflows usize");
        let mut rng = SplitMix64::new(seed);
        let scale = 1.0 / (k as f64).sqrt();
        let matrix = (0..entries)
            .map(|_| rng.standard_normal() * scale)
            .collect();
        GaussianProjection { d_in, k, matrix }
    }

    /// The input dimension.
    #[must_use]
    pub fn d_in(&self) -> usize {
        self.d_in
    }

    /// The output dimension.
    #[must_use]
    pub fn k(&self) -> usize {
        self.k
    }

    /// The image of `v`.
    ///
    /// # Panics
    /// If `v` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn project(&self, v: &[f64]) -> Vec<f64> {
        check_query(self.d_in, v);
        self.matrix
            .chunks_exact(self.d_in)
            .map(|row| dot(row, v))
            .collect()
    }

    /// The images of all points, in order.
    ///
    /// # Errors
    /// [`PointsError::NonFinite`] for the first point whose image overflows `f64` (coordinates
    /// near `1e308` can).
    ///
    /// # Panics
    /// If the points' dimension is not `d_in`.
    pub fn project_all(&self, p: &Points) -> Result<Points, PointsError> {
        assert_eq!(
            p.dim(),
            self.d_in,
            "points of dimension {} into a projection from {}",
            p.dim(),
            self.d_in
        );
        let coords: Vec<f64> = p.iter().flat_map(|v| self.project(v)).collect();
        Points::new(self.k, coords)
    }
}

#[cfg(test)]
#[path = "unit_tests/projection.rs"]
mod tests;
