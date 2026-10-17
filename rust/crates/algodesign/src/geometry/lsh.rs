//! Locality-sensitive hashing: each table hashes every point to a key, and a query re-ranks,
//! exactly, the stored points that share its key in some table (MMDS Ch. 3, the AND–OR
//! construction: `K` hash values make one key, `L` tables). One framework, [`HashFamily`], for
//! every family, because the guarantees hold for any of them. The chapter's two:
//!
//! - **SimHash** (Charikar 2002 §3): a bit is *which side* of a random hyperplane through the
//!   origin a point lies on; `K` bits make a key ([`SimHash`]).
//! - **p-stable LSH** (Datar et al. 2004 §3.2), the grid on a line: project onto a random Gaussian
//!   direction, shift by a random offset, and cut the line into cells of width `w` ([`PStable`]).
//!
//! Lean: `LSH/Spec.lean`. The index keeps `LSH.Valid` ([`LshIndex::is_valid`]); an answer keeps
//! box invariant 2 ([`is_measured_exactly`]). For any family, **if the scan's answer is a
//! candidate, LSH returns exactly it** (`LSH.nearest_eq_scanNearest`).
//! Collision probabilities (`1 − θ/π`; Datar et al.'s `p(c)`) are held by seeded statistical
//! tests. `K` is `bits` in [`SimHash`] and `k` in [`PStable`]; `L` is `tables` in both.
//!
//! **Against the Python, and how fast.** The Python's algorithm, on flat arrays; the same seed
//! gives the same hyperplanes in both. A query costs `L` keys of `K` bits, `O(K L d)`, plus one
//! exact distance per candidate, `O(d)` each; `K` and `L` set how many candidates there are.
//! `PStable::key` allocates a `Vec` per table.

use crate::geometry::{
    point::{check_query, dot, sq_dist, Points},
    rng::SplitMix64,
    scan::{k_nearest_among, Neighbor},
};
use std::collections::HashMap;
use std::hash::Hash;

/// A family of hash functions, one per table. A table is its hash function.
pub trait HashFamily {
    /// A table's key.
    type Key: Eq + Hash + Clone;
    /// The dimension of the points it hashes.
    fn dim(&self) -> usize;
    /// The number of tables.
    fn tables(&self) -> usize;
    /// Table `table`'s key for `v`.
    fn key(&self, table: usize, v: &[f64]) -> Self::Key;
}

/// One SimHash bit: is `p` on the non-negative side of the hyperplane with normal `r`? A point on
/// the hyperplane counts as non-negative, as in Lean's `simBit` (`0 ≤ dot r p`).
#[must_use]
pub fn sim_bit(r: &[f64], p: &[f64]) -> bool {
    dot(r, p) >= 0.0
}

/// SimHash: `tables` tables of `bits` sign bits each, the hyperplanes' normals Gaussian and
/// seeded. The key is a `u64` whose bit `i` is [`sim_bit`] for plane `i`.
#[derive(Debug, Clone, PartialEq)]
pub struct SimHash {
    dim: usize,
    bits: usize,
    tables: usize,
    /// `tables × bits` normals of `dim` entries, row-major.
    planes: Vec<f64>,
}

impl SimHash {
    /// A seeded SimHash family.
    ///
    /// # Panics
    /// Unless `dim ≥ 1` and `1 ≤ bits ≤ 64`, or if `tables × bits × dim` overflows `usize`.
    #[must_use]
    pub fn new(dim: usize, bits: usize, tables: usize, seed: u64) -> Self {
        assert!(dim > 0, "SimHash needs dim ≥ 1");
        assert!(
            (1..=64).contains(&bits),
            "SimHash needs 1 ≤ bits ≤ 64, got {bits}"
        );
        let entries = tables
            .checked_mul(bits)
            .and_then(|x| x.checked_mul(dim))
            .expect("SimHash's tables × bits × dim overflows usize");
        let mut rng = SplitMix64::new(seed);
        let planes = (0..entries).map(|_| rng.standard_normal()).collect();
        SimHash {
            dim,
            bits,
            tables,
            planes,
        }
    }

    /// A SimHash family on given normals, `tables × bits` of them of `dim` entries each,
    /// row-major, the layout `new` draws them in, for tests that hand the Lean the same normals
    /// so it can compute the keys itself. Not part of the API.
    ///
    /// # Panics
    /// Unless `dim ≥ 1`, `1 ≤ bits ≤ 64` and there are `tables × bits × dim` plane entries.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_planes(dim: usize, bits: usize, tables: usize, planes: Vec<f64>) -> Self {
        assert!(dim > 0, "SimHash needs dim ≥ 1");
        assert!(
            (1..=64).contains(&bits),
            "SimHash needs 1 ≤ bits ≤ 64, got {bits}"
        );
        assert_eq!(
            planes.len(),
            tables * bits * dim,
            "SimHash needs tables × bits × dim plane entries"
        );
        SimHash {
            dim,
            bits,
            tables,
            planes,
        }
    }
}

impl HashFamily for SimHash {
    type Key = u64;
    fn dim(&self) -> usize {
        self.dim
    }
    fn tables(&self) -> usize {
        self.tables
    }
    fn key(&self, table: usize, v: &[f64]) -> u64 {
        let base = table * self.bits * self.dim;
        (0..self.bits).fold(0u64, |key, i| {
            let r = &self.planes[base + i * self.dim..base + (i + 1) * self.dim];
            key | (u64::from(sim_bit(r, v)) << i)
        })
    }
}

/// The p-stable cell of `p` along direction `a`, with offset `b` and width `w`:
/// `⌊(a·p + b) / w⌋` (Lean `pStableKey`). Saturates at the ends of `i64`.
#[must_use]
pub fn p_stable_cell(a: &[f64], b: f64, w: f64, p: &[f64]) -> i64 {
    // `as` saturates for out-of-range floats, which is the documented behavior.
    ((dot(a, p) + b) / w).floor() as i64
}

/// p-stable LSH: `tables` tables of `k` cells each; directions Gaussian, offsets uniform in
/// `[0, w)`, all seeded. The key is the `k` cell indices.
#[derive(Debug, Clone, PartialEq)]
pub struct PStable {
    dim: usize,
    k: usize,
    tables: usize,
    w: f64,
    /// `tables × k` directions of `dim` entries, row-major.
    a: Vec<f64>,
    /// `tables × k` offsets.
    b: Vec<f64>,
}

impl PStable {
    /// A seeded p-stable family with cell width `w`.
    ///
    /// # Panics
    /// Unless `dim ≥ 1`, `k ≥ 1` and `w > 0` is finite, or if `tables × k × dim` overflows
    /// `usize`.
    #[must_use]
    pub fn new(dim: usize, k: usize, tables: usize, w: f64, seed: u64) -> Self {
        assert!(dim > 0 && k > 0, "p-stable LSH needs dim ≥ 1 and k ≥ 1");
        assert!(
            w > 0.0 && w.is_finite(),
            "p-stable LSH needs a finite cell width w > 0, got {w}"
        );
        let cells = tables
            .checked_mul(k)
            .expect("p-stable LSH's tables × k overflows usize");
        let entries = cells
            .checked_mul(dim)
            .expect("p-stable LSH's tables × k × dim overflows usize");
        let mut rng = SplitMix64::new(seed);
        let a = (0..entries).map(|_| rng.standard_normal()).collect();
        let b = (0..cells).map(|_| rng.next_f64() * w).collect();
        PStable {
            dim,
            k,
            tables,
            w,
            a,
            b,
        }
    }

    /// A p-stable family on given directions (`tables × k` of them of `dim` entries each,
    /// row-major), offsets (`tables × k`) and width, the layout `new` draws them in, for tests
    /// that hand the Lean the same parameters so it can compute the keys itself. Not part of the
    /// API.
    ///
    /// # Panics
    /// Unless `dim ≥ 1`, `k ≥ 1`, `w > 0` is finite, and the directions and offsets have those
    /// lengths.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_params(
        dim: usize,
        k: usize,
        tables: usize,
        w: f64,
        a: Vec<f64>,
        b: Vec<f64>,
    ) -> Self {
        assert!(dim > 0 && k > 0, "p-stable LSH needs dim ≥ 1 and k ≥ 1");
        assert!(
            w > 0.0 && w.is_finite(),
            "p-stable LSH needs a finite cell width w > 0, got {w}"
        );
        assert_eq!(
            a.len(),
            tables * k * dim,
            "p-stable LSH needs tables × k × dim direction entries"
        );
        assert_eq!(b.len(), tables * k, "p-stable LSH needs tables × k offsets");
        PStable {
            dim,
            k,
            tables,
            w,
            a,
            b,
        }
    }
}

impl HashFamily for PStable {
    type Key = Vec<i64>;
    fn dim(&self) -> usize {
        self.dim
    }
    fn tables(&self) -> usize {
        self.tables
    }
    fn key(&self, table: usize, v: &[f64]) -> Vec<i64> {
        (0..self.k)
            .map(|i| {
                let j = table * self.k + i;
                p_stable_cell(
                    &self.a[j * self.dim..(j + 1) * self.dim],
                    self.b[j],
                    self.w,
                    v,
                )
            })
            .collect()
    }
}

/// An LSH index: the points, a hash family, and each table's buckets of point ids. Its build
/// keeps [`LshIndex::is_valid`]; only `from_buckets_unchecked` (feature `unchecked`) can break
/// it, and only `buckets` (the same feature) shows the stored buckets. The feature is for tests
/// that break the index on purpose: `cargo test --features unchecked`.
#[derive(Debug, Clone, PartialEq)]
pub struct LshIndex<H: HashFamily> {
    points: Points,
    family: H,
    /// One map per table from key to the ids, ascending, of the points with that key.
    buckets: Vec<HashMap<H::Key, Vec<u32>>>,
}

impl<H: HashFamily> LshIndex<H> {
    /// Hash every point into every table.
    ///
    /// # Panics
    /// If the family's dimension is not the points', or there are more than `u32::MAX` points.
    #[must_use]
    pub fn new(points: Points, family: H) -> Self {
        assert_eq!(
            family.dim(),
            points.dim(),
            "the hash family's dimension is not the points'"
        );
        let n = u32::try_from(points.len()).expect("an LSH index holds at most u32::MAX points");
        let mut buckets = vec![HashMap::new(); family.tables()];
        for (t, table) in buckets.iter_mut().enumerate() {
            for i in 0..n {
                let key = family.key(t, points.get(i as usize));
                table.entry(key).or_insert_with(Vec::new).push(i);
            }
        }
        LshIndex {
            points,
            family,
            buckets,
        }
    }

    /// The ids, ascending and without repeats, of the points sharing `q`'s key in at least
    /// one table.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn candidates(&self, q: &[f64]) -> Vec<usize> {
        check_query(self.points.dim(), q);
        let mut out: Vec<usize> = Vec::new();
        for (t, table) in self.buckets.iter().enumerate() {
            if let Some(ids) = table.get(&self.family.key(t, q)) {
                out.extend(ids.iter().map(|&i| i as usize));
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The `min(k, candidates)` nearest candidates, ranked exactly, best first, with the scan's
    /// tie rule.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn k_nearest(&self, q: &[f64], k: usize) -> Vec<Neighbor> {
        k_nearest_among(&self.points, &self.candidates(q), q, k)
    }

    /// The nearest candidate, if any.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn nearest(&self, q: &[f64]) -> Option<usize> {
        self.k_nearest(q, 1).first().map(|n| n.id)
    }

    /// Each table's buckets: key to the point ids stored under it, in insertion order. Public for
    /// tests; not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn buckets(&self) -> &[HashMap<H::Key, Vec<u32>>] {
        &self.buckets
    }

    /// An index with the given buckets, everything as given, unchecked. Feature `unchecked`.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_buckets_unchecked(
        points: Points,
        family: H,
        buckets: Vec<HashMap<H::Key, Vec<u32>>>,
    ) -> Self {
        LshIndex {
            points,
            family,
            buckets,
        }
    }

    /// Box invariant 1: every stored point sits in the bucket its key names, in every table. There
    /// is one bucket map per table of the family; in each, every stored id names a point whose
    /// key is its bucket's, and every point is found in the bucket its key names. Lean:
    /// `InItsBucket`.
    #[must_use]
    pub fn is_in_its_bucket(&self) -> bool {
        let n = self.points.len();
        self.buckets.len() == self.family.tables()
            && self.buckets.iter().enumerate().all(|(t, table)| {
                let mut found = vec![false; n];
                for (key, ids) in table {
                    for &i in ids {
                        let i = i as usize;
                        if i >= n || self.family.key(t, self.points.get(i)) != *key {
                            return false;
                        }
                        found[i] = true;
                    }
                }
                found.iter().all(|&f| f)
            })
    }

    /// Not in the box: in each table, every key has one bucket, and no bucket is empty.
    /// A map holds one bucket per key by its type, and the build never stores an empty one, so
    /// this checks the second half only. Lean: `OneBucketPerKey`.
    #[must_use]
    pub fn is_one_bucket_per_key(&self) -> bool {
        self.buckets
            .iter()
            .all(|table| table.values().all(|ids| !ids.is_empty()))
    }

    /// Not in the box: in each table, every point is stored exactly once (the bucket its
    /// key names holds it, by box invariant 1, and no other bucket does). Lean:
    /// `EachPointOncePerTable`.
    #[must_use]
    pub fn is_each_point_once_per_table(&self) -> bool {
        let n = self.points.len();
        self.buckets.iter().all(|table| {
            let mut seen = vec![0usize; n];
            for &i in table.values().flatten() {
                if let Some(c) = seen.get_mut(i as usize) {
                    *c += 1;
                }
            }
            seen.iter().all(|&c| c == 1)
        })
    }

    /// Lean `LSH.Valid`: [`LshIndex::is_in_its_bucket`], [`LshIndex::is_one_bucket_per_key`] and
    /// [`LshIndex::is_each_point_once_per_table`]. Every build keeps it (Lean `LSH.valid_build`).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`LshIndex::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (in_its_bucket)"`, `"not in the box (one_bucket_per_key)"` or
    /// `"not in the box (each_point_once_per_table)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_in_its_bucket() {
            return Err("invariant 1 (in_its_bucket)");
        }
        if !self.is_one_bucket_per_key() {
            return Err("not in the box (one_bucket_per_key)");
        }
        if !self.is_each_point_once_per_table() {
            return Err("not in the box (each_point_once_per_table)");
        }
        Ok(())
    }

    /// The points the index was built from.
    #[must_use]
    pub fn points(&self) -> &Points {
        &self.points
    }

    /// The hash family.
    #[must_use]
    pub fn family(&self) -> &H {
        &self.family
    }
}

/// Box invariant 2: a shared bucket only makes a point a candidate: every candidate is measured
/// exactly before one is reported. Every candidate of `index` for `q` names a stored point, and
/// `result`, the answer to a query for `k` points, holds `min(k, candidates)` of them, each once,
/// none farther from `q` than a candidate left out. Total: `false` for a query not of the points'
/// dimension (whatever the family's) or with a non-finite coordinate, and for a candidate past the
/// points, which cannot be measured. Lean: `MeasuredExactly`, on the answer (`Answer`).
#[must_use]
pub fn is_measured_exactly<H: HashFamily>(
    index: &LshIndex<H>,
    q: &[f64],
    k: usize,
    result: &[usize],
) -> bool {
    let points = &index.points;
    if q.len() != points.dim() || !q.iter().all(|x| x.is_finite()) {
        return false;
    }
    let mut cands: Vec<usize> = Vec::new();
    for (t, table) in index.buckets.iter().enumerate().take(index.family.tables()) {
        if let Some(ids) = table.get(&index.family.key(t, q)) {
            cands.extend(ids.iter().map(|&i| i as usize));
        }
    }
    cands.sort_unstable();
    cands.dedup();
    if cands.iter().any(|&c| c >= points.len()) {
        return false;
    }
    let dist = |i: usize| sq_dist(points.get(i), q);
    let mut sorted = result.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    if sorted.len() != result.len()
        || result.len() != k.min(cands.len())
        || !result.iter().all(|r| cands.binary_search(r).is_ok())
    {
        return false;
    }
    let worst = result
        .iter()
        .map(|&r| dist(r))
        .fold(f64::NEG_INFINITY, f64::max);
    cands
        .iter()
        .filter(|c| sorted.binary_search(c).is_err())
        .all(|&c| worst <= dist(c))
}

#[cfg(test)]
#[path = "unit_tests/lsh.rs"]
mod tests;
