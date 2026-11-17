//! Checking every point: the chapter's specification of nearest-neighbor and box queries, and
//! the oracle every other structure in [`crate::geometry`] is tested against.
//!
//! The nearest neighbor is the stored point at the least squared distance from the query, and
//! among equally near points **the one stored first**.
//! `k_nearest` keeps a bounded max-heap of `k` entries ordered by `(squared distance, id)`.
//!
//! Lean: `Scan.lean`, `scanNearest_le`, `scanNearest_lowest`, `scanNearest_mem` and
//! `scanNearest_isSome_iff`.

use crate::geometry::point::{check_query, sq_dist, Points};
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// A point's id and its squared distance from the query.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Neighbor {
    /// The point's number in the input, counting from 0.
    pub id: usize,
    /// Its squared Euclidean distance from the query.
    pub sq_dist: f64,
}

/// The order every answer in [`crate::geometry`] is ranked by: squared distance, then id.
pub(crate) fn rank_cmp(a: &Neighbor, b: &Neighbor) -> Ordering {
    a.sq_dist.total_cmp(&b.sq_dist).then(a.id.cmp(&b.id))
}

/// Whether `a` ranks strictly before `b`.
pub(crate) fn closer(a: &Neighbor, b: &Neighbor) -> bool {
    rank_cmp(a, b) == Ordering::Less
}

/// A [`Neighbor`] ordered by [`rank_cmp`], so a `BinaryHeap` of them keeps the worst on top.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Ranked(pub(crate) Neighbor);

impl Eq for Ranked {}

impl PartialOrd for Ranked {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Ranked {
    fn cmp(&self, other: &Self) -> Ordering {
        rank_cmp(&self.0, &other.0)
    }
}

/// The best `k` offered so far, worst on top. Shared by the scan, the k-d tree, LSH and HNSW.
/// The heap grows with what it holds, never with `k`: a caller may pass any `k`, `usize::MAX`
/// included, and gets at most the points offered.
#[derive(Debug, Clone)]
pub(crate) struct TopK {
    k: usize,
    heap: BinaryHeap<Ranked>,
}

impl TopK {
    pub(crate) fn new(k: usize) -> Self {
        TopK {
            k,
            heap: BinaryHeap::new(),
        }
    }

    /// Offer a candidate; it is kept if fewer than `k` are held or it ranks before the worst.
    pub(crate) fn offer(&mut self, n: Neighbor) {
        if self.k == 0 {
            return;
        }
        if self.heap.len() < self.k {
            self.heap.push(Ranked(n));
        } else if let Some(mut worst) = self.heap.peek_mut() {
            if closer(&n, &worst.0) {
                // Replaced in place: one sift-down when `worst` drops, where a pop and a push
                // sift twice. The heap holds the same entries either way.
                *worst = Ranked(n);
            }
        }
    }

    /// Whether `k` candidates are held.
    pub(crate) fn is_full(&self) -> bool {
        self.heap.len() >= self.k
    }

    /// The worst candidate held, if any.
    pub(crate) fn worst(&self) -> Option<Neighbor> {
        self.heap.peek().map(|r| r.0)
    }

    /// The candidates, best first.
    pub(crate) fn into_sorted(self) -> Vec<Neighbor> {
        self.heap
            .into_sorted_vec()
            .into_iter()
            .map(|r| r.0)
            .collect()
    }
}

/// The id of a nearest point, the one stored first on ties, or `None` if there are no points.
///
/// # Panics
/// If `q` has the wrong dimension or a non-finite coordinate.
#[must_use]
pub fn nearest(points: &Points, q: &[f64]) -> Option<usize> {
    k_nearest(points, q, 1).first().map(|n| n.id)
}

/// The `min(k, n)` nearest points, best first, ranked by squared distance and then id.
///
/// # Panics
/// If `q` has the wrong dimension or a non-finite coordinate.
#[must_use]
pub fn k_nearest(points: &Points, q: &[f64], k: usize) -> Vec<Neighbor> {
    check_query(points.dim(), q);
    let mut top = TopK::new(k);
    for (id, p) in points.iter().enumerate() {
        top.offer(Neighbor {
            id,
            sq_dist: sq_dist(p, q),
        });
    }
    top.into_sorted()
}

/// [`k_nearest`] restricted to `candidates` (any order, no repeats): the exact re-rank LSH and
/// RaBitQ end with.
///
/// # Panics
/// If `q` has the wrong dimension or a non-finite coordinate, or a candidate is out of range.
#[must_use]
pub fn k_nearest_among(
    points: &Points,
    candidates: &[usize],
    q: &[f64],
    k: usize,
) -> Vec<Neighbor> {
    check_query(points.dim(), q);
    let mut top = TopK::new(k);
    for &id in candidates {
        top.offer(Neighbor {
            id,
            sq_dist: sq_dist(points.get(id), q),
        });
    }
    top.into_sorted()
}

/// The ids, ascending, of the points inside the box `[lo, hi]` (inclusive on every axis);
/// empty if `lo > hi` on some axis. The oracle for both trees' range queries.
///
/// # Panics
/// If `lo` or `hi` has the wrong dimension or a non-finite coordinate.
#[must_use]
pub fn in_box(points: &Points, lo: &[f64], hi: &[f64]) -> Vec<usize> {
    check_query(points.dim(), lo);
    check_query(points.dim(), hi);
    points
        .iter()
        .enumerate()
        .filter(|(_, p)| p.iter().zip(lo).zip(hi).all(|((x, l), h)| l <= x && x <= h))
        .map(|(i, _)| i)
        .collect()
}

#[cfg(test)]
#[path = "unit_tests/scan.rs"]
mod tests;
