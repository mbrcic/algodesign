//! Points with `f64` coordinates, stored row-major in one `Vec<f64>`, and the squared Euclidean
//! distance every structure in [`crate::geometry`] compares by.
//!
//! Distances are compared **squared**: that orders points exactly as distances do and needs no
//! square root. Lean: `Point.lean` states `sqDist` and its lemmas over any ordered commutative
//! ring, so they hold of real coordinates; `f64` rounds, and that rounding is where the Rust
//! departs from the Lean, held to it by tests rather than proofs.

use std::fmt;

/// A set of points of one dimension, stored row-major.
///
/// There is no `Default`: a point set has a dimension of at least 1, and an empty set still has
/// one, so there is no natural default value.
#[derive(Debug, Clone, PartialEq)]
pub struct Points {
    dim: usize,
    coords: Vec<f64>,
}

/// Why a point set was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointsError {
    /// The dimension is 0.
    ZeroDimension,
    /// The number of coordinates is not a multiple of the dimension.
    Ragged {
        /// The number of coordinates given.
        len: usize,
        /// The dimension.
        dim: usize,
    },
    /// A coordinate of this point is `NaN` or infinite.
    NonFinite {
        /// The point's number in the input, counting from 0.
        id: usize,
    },
    /// This point is the zero vector, which has no direction to normalize to.
    ZeroVector {
        /// The point's number in the input, counting from 0.
        id: usize,
    },
}

impl fmt::Display for PointsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PointsError::ZeroDimension => write!(f, "points must have at least one dimension"),
            PointsError::Ragged { len, dim } => {
                write!(
                    f,
                    "{len} coordinates do not divide into points of dimension {dim}"
                )
            }
            PointsError::NonFinite { id } => {
                write!(f, "point {id} has a non-finite coordinate")
            }
            PointsError::ZeroVector { id } => write!(f, "point {id} is the zero vector"),
        }
    }
}

impl std::error::Error for PointsError {}

impl Points {
    /// Points of dimension `dim` from `coords`, row-major. Checks, in this order: `dim > 0`, the
    /// length, then that every coordinate is finite (reporting the first offending point).
    ///
    /// # Errors
    /// [`PointsError::ZeroDimension`], [`PointsError::Ragged`] or [`PointsError::NonFinite`].
    pub fn new(dim: usize, coords: Vec<f64>) -> Result<Points, PointsError> {
        if dim == 0 {
            return Err(PointsError::ZeroDimension);
        }
        if coords.len() % dim != 0 {
            return Err(PointsError::Ragged {
                len: coords.len(),
                dim,
            });
        }
        if let Some(i) = coords.iter().position(|x| !x.is_finite()) {
            return Err(PointsError::NonFinite { id: i / dim });
        }
        Ok(Points { dim, coords })
    }

    /// Points of dimension `dim` from rows.
    ///
    /// # Errors
    /// As [`Points::new`]; a row of the wrong length is [`PointsError::Ragged`].
    pub fn from_rows<R: AsRef<[f64]>>(dim: usize, rows: &[R]) -> Result<Points, PointsError> {
        let mut coords = Vec::with_capacity(rows.len() * dim);
        for r in rows {
            let r = r.as_ref();
            if r.len() != dim {
                return Err(PointsError::Ragged { len: r.len(), dim });
            }
            coords.extend_from_slice(r);
        }
        Points::new(dim, coords)
    }

    /// The dimension.
    #[must_use]
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// The number of points.
    #[must_use]
    pub fn len(&self) -> usize {
        self.coords.len() / self.dim
    }

    /// Whether there are no points.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.coords.is_empty()
    }

    /// Point `i`.
    ///
    /// # Panics
    /// If `i >= self.len()`.
    #[must_use]
    pub fn get(&self, i: usize) -> &[f64] {
        &self.coords[i * self.dim..(i + 1) * self.dim]
    }

    /// The points in input order.
    pub fn iter(&self) -> impl Iterator<Item = &[f64]> {
        self.coords.chunks_exact(self.dim)
    }

    /// Every point scaled to unit length, so that squared Euclidean distance ranks as cosine
    /// similarity does.
    ///
    /// # Errors
    /// [`PointsError::ZeroVector`] for the first zero point.
    pub fn normalized(&self) -> Result<Points, PointsError> {
        let mut coords = Vec::with_capacity(self.coords.len());
        for (i, p) in self.iter().enumerate() {
            // Scale by the largest coordinate before squaring, so the norm neither overflows
            // (coordinates near 1e200) nor underflows (near 1e-200).
            let big = p.iter().fold(0.0_f64, |m, x| m.max(x.abs()));
            if big == 0.0 {
                return Err(PointsError::ZeroVector { id: i });
            }
            let scaled: Vec<f64> = p.iter().map(|x| x / big).collect();
            let norm = dot(&scaled, &scaled).sqrt();
            coords.extend(scaled.iter().map(|x| x / norm));
        }
        Ok(Points {
            dim: self.dim,
            coords,
        })
    }
}

/// Squared Euclidean distance, summed as `sum4` does. Lean: `sqDist`.
///
/// `a` and `b` must have the same length; the caller keeps that promise, as every structure here
/// does by checking a query's dimension once ([`Points`] and the query checks). It is checked
/// only in debug builds, so a release build pays for no check on every distance. Given slices of different lengths, a release build returns a meaningless number
/// without panicking.
#[must_use]
pub fn sq_dist(a: &[f64], b: &[f64]) -> f64 {
    debug_assert_eq!(a.len(), b.len());
    sum4(a, b, |x, y| (x - y) * (x - y))
}

/// The dot product, in one running sum, in order, as the Python sums. It builds what is stored
/// (normalized points, the RaBitQ rotation and codes, projections) and the LSH keys, where the
/// last bit can decide a bucket; a search's distances come from [`sq_dist`]. Lean: `dot`.
///
/// `a` and `b` must have the same length, a promise checked only in debug builds, as for
/// [`sq_dist`]; a release build sums over the shorter length.
#[must_use]
pub fn dot(a: &[f64], b: &[f64]) -> f64 {
    debug_assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

/// `Σ f(a[i], b[i])` in four running sums, so the compiler can keep them in vector registers:
/// sum `j` takes coordinates `j, j + 4, j + 8, …`, the four are added as `(s0 + s1) + (s2 + s3)`,
/// and the last `len mod 4` terms are added in order. Below four coordinates it is the plain sum
/// in order. Rounding differs from one running sum in the last bits; the Python sums in one chain.
/// The k-d tree's region bound sums in this same order, so it stays below every distance it bounds.
pub(crate) fn sum4(a: &[f64], b: &[f64], f: impl Fn(f64, f64) -> f64) -> f64 {
    let mut s = [0.0_f64; 4];
    let (ca, cb) = (a.chunks_exact(4), b.chunks_exact(4));
    let (ra, rb) = (ca.remainder(), cb.remainder());
    for (x, y) in ca.zip(cb) {
        s[0] += f(x[0], y[0]);
        s[1] += f(x[1], y[1]);
        s[2] += f(x[2], y[2]);
        s[3] += f(x[3], y[3]);
    }
    let mut t = (s[0] + s[1]) + (s[2] + s[3]);
    for (x, y) in ra.iter().zip(rb) {
        t += f(*x, *y);
    }
    t
}

/// Panics unless `q` is a finite query of dimension `dim`; every query entry point calls it.
pub(crate) fn check_query(dim: usize, q: &[f64]) {
    assert!(
        q.len() == dim,
        "query has dimension {} but the points have {dim}",
        q.len()
    );
    if let Some(i) = q.iter().position(|x| !x.is_finite()) {
        panic!("query coordinate {i} is not finite");
    }
}

#[cfg(test)]
#[path = "unit_tests/point.rs"]
mod tests;
