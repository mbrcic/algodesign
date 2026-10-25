//! HNSW, the hierarchical navigable small world graph (Malkov–Yashunin 2020, Algorithms 1, 2, 4
//! and 5). Every point is a node with a random level; it keeps a few neighbors on layer 0 and on
//! each layer up to its own level (`m0 = 2m` on layer 0, `m` above, levels `⌊−ln u · m_L⌋` with
//! `m_L = 1/ln M`). A search walks greedily down the upper layers, runs a beam of width `ef` on
//! layer 0, and ends with [`finish`]: the beam sorted by exact distance, `k` kept. The flat graph
//! is this code with every node at level 0 ([`HnswParams::flat`]; Munyampirwa et al. 2024 measure
//! it level with the layered graph).
//!
//! Neighbors are picked by Alg. 4's heuristic with both options off: candidates nearest first,
//! each skipped if a neighbor already picked is strictly nearer to it than the node is; a tie
//! keeps it, as hnswlib does. No search guarantee is claimed: recall is measured.
//!
//! Lean: `GraphIndex/Spec.lean`, whose `HNSW.Valid` and `HNSW.WellFormed` are [`Hnsw::is_valid`]
//! and whose `PicksDiverse` is [`is_picks_diverse`]; `HNSW.contract` in `GraphIndex.lean`.
//!
//! **Against the Python, and how fast.** The same build and search: `u32` ids, the points in one
//! flat coordinate vector, a pooled visited set, and the watch on a walk compiled away; distances
//! are summed in another order, so links can differ from the Python's where two distances differ
//! only in their last bits. `cargo bench -p algodesign --bench geometry -- hnsw` times a small
//! graph beside the scan.

use crate::geometry::{
    point::{check_query, sq_dist, Points},
    rng::SplitMix64,
    scan::Neighbor,
};
use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::sync::Mutex;

/// HNSW's parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct HnswParams {
    /// Neighbors kept per node on the layers above 0, and selected for a new node on every layer.
    pub m: usize,
    /// Neighbors kept per node on layer 0.
    pub m0: usize,
    /// The beam width while building.
    pub ef_construction: usize,
    /// The level normalization `m_L`.
    pub ml: f64,
    /// The seed of the level draws.
    pub seed: u64,
    /// Every node at level 0: the flat graph.
    pub flat: bool,
}

impl HnswParams {
    /// The paper's recommendations for `m`: `M₀ = 2M`, `m_L = 1/ln M`, and `ef_construction = 200`
    /// (hnswlib's default), seed 0, layered.
    ///
    /// # Panics
    /// If `m < 2` (`m_L = 1/ln M` needs `M > 1`).
    #[must_use]
    pub fn new(m: usize) -> Self {
        assert!(m >= 2, "HNSW needs M ≥ 2, got M = {m}");
        HnswParams {
            m,
            m0: 2 * m,
            ef_construction: 200,
            ml: 1.0 / (m as f64).ln(),
            seed: 0,
            flat: false,
        }
    }

    /// The same parameters with every node at level 0.
    #[must_use]
    pub fn flat(self) -> Self {
        HnswParams { flat: true, ..self }
    }
}

/// An HNSW index. Its build keeps [`Hnsw::is_valid`]; only `from_links_unchecked` (feature
/// `unchecked`) can break it, and only `build_with_pickings`, `search_beam` and `search_walk`
/// (the same feature) show its pickings, its search's beam and its search's walk; the picking and
/// the greedy step, `select_neighbors` and `greedy_step`, are behind it too. The feature is for
/// tests that break or watch the index on purpose: `cargo test --features unchecked`.
pub struct Hnsw {
    params: HnswParams,
    points: Points,
    /// `links[v][l]`: node `v`'s neighbors on layer `l`, for `l ≤ level(v)`.
    links: Vec<Vec<Vec<u32>>>,
    entry: Option<u32>,
    max_level: usize,
    /// Reusable visited marks, so a search allocates nothing of size `n`.
    visited: Mutex<Vec<Visited>>,
}

impl Clone for Hnsw {
    fn clone(&self) -> Self {
        Hnsw {
            params: self.params.clone(),
            points: self.points.clone(),
            links: self.links.clone(),
            entry: self.entry,
            max_level: self.max_level,
            visited: Mutex::new(Vec::new()),
        }
    }
}

impl std::fmt::Debug for Hnsw {
    /// Every field but the pool of visited marks, which is scratch space of `n` entries per search.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Hnsw")
            .field("params", &self.params)
            .field("points", &self.points)
            .field("links", &self.links)
            .field("entry", &self.entry)
            .field("max_level", &self.max_level)
            .finish_non_exhaustive()
    }
}

impl PartialEq for Hnsw {
    /// The same parameters, points, links and entry point; the pool of visited marks is scratch
    /// space and is not compared.
    fn eq(&self, other: &Self) -> bool {
        self.params == other.params
            && self.points == other.points
            && self.links == other.links
            && self.entry == other.entry
            && self.max_level == other.max_level
    }
}

impl Hnsw {
    /// Insert every point, in input order (Alg. 1).
    ///
    /// # Panics
    /// If there are more than `u32::MAX` points, if `params.m0 < params.m` (a new node's
    /// layer-0 list holds up to `m`, and layer 0 keeps at most `m0`), if `params.ml` is not finite
    /// and `≥ 0`, or if `params.ef_construction` is 0.
    #[must_use]
    pub fn build(points: Points, params: HnswParams) -> Self {
        Self::build_observed(points, params, &mut |_, _, _, _| {})
    }

    /// [`Hnsw::build`], with every picking reported: the base node, its candidates nearest first,
    /// the cap and the picks.
    fn build_observed(points: Points, params: HnswParams, on_pick: &mut OnPick<'_>) -> Self {
        let n = u32::try_from(points.len()).expect("HNSW holds at most u32::MAX points");
        assert!(
            params.m <= params.m0,
            "HNSW needs m ≤ m0, got m = {} and m0 = {}",
            params.m,
            params.m0
        );
        assert!(
            params.ml.is_finite() && params.ml >= 0.0,
            "HNSW needs a finite m_L ≥ 0, got {}",
            params.ml
        );
        assert!(
            params.ef_construction >= 1,
            "HNSW needs ef_construction ≥ 1"
        );
        let mut h = Hnsw {
            params,
            points,
            links: Vec::with_capacity(n as usize),
            entry: None,
            max_level: 0,
            visited: Mutex::new(Vec::new()),
        };
        let mut rng = SplitMix64::new(h.params.seed);
        let mut visited = Visited::new(n as usize);
        for v in 0..n {
            let level = if h.params.flat {
                0
            } else {
                draw_level(&mut rng, h.params.ml)
            };
            h.insert(v, level, &mut visited, on_pick);
        }
        h
    }

    /// [`Hnsw::build`], and every picking it made, in order: each new node's list on each of its
    /// layers, and each re-pick of a list a back-link overfilled. Behind the `unchecked` feature.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn build_with_pickings(points: Points, params: HnswParams) -> (Self, Vec<Picking>) {
        let mut pickings = Vec::new();
        let h = Self::build_observed(points, params, &mut |base, cands, m, picked| {
            pickings.push(Picking {
                base,
                candidates: cands.iter().map(|&(_, c)| c).collect(),
                m,
                picked: picked.to_vec(),
            });
        });
        (h, pickings)
    }

    /// The node every search starts from (`None` on no points). Public for tests; not part of the
    /// API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn entry_point(&self) -> Option<u32> {
        self.entry
    }

    /// The graph `links` and `entry` write out over `points`, everything as given, unchecked (one
    /// list of layers per point included); the search's top layer is the entry's. Feature
    /// `unchecked`.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_links_unchecked(
        points: Points,
        params: HnswParams,
        links: Vec<Vec<Vec<u32>>>,
        entry: Option<u32>,
    ) -> Self {
        let max_level = entry
            .and_then(|e| links.get(e as usize))
            .map_or(0, |l| l.len().saturating_sub(1));
        Hnsw {
            params,
            points,
            links,
            entry,
            max_level,
            visited: Mutex::new(Vec::new()),
        }
    }

    /// Alg. 1, INSERT.
    fn insert(&mut self, v: u32, level: usize, visited: &mut Visited, on_pick: &mut OnPick<'_>) {
        self.links.push(vec![Vec::new(); level + 1]);
        let Some(entry) = self.entry else {
            self.entry = Some(v);
            self.max_level = level;
            return;
        };
        let q = self.points.get(v as usize).to_vec();
        let top = self.max_level;
        let mut new_links: Vec<(usize, Vec<u32>)> = Vec::new();
        {
            let dist = |i: u32| sq_dist(self.points.get(i as usize), &q);
            let mut ep = vec![(dist(entry), entry)];
            for lc in (level + 1..=top).rev() {
                let w = self.search_layer_with(&dist, &ep, 1, lc, visited, &mut ());
                ep = vec![w[0]];
            }
            for lc in (0..=level.min(top)).rev() {
                let w = self.search_layer_with(
                    &dist,
                    &ep,
                    self.params.ef_construction,
                    lc,
                    visited,
                    &mut (),
                );
                let picked = pick_neighbors(&self.points, &q, &w, self.params.m);
                on_pick(v, &w, self.params.m, &picked);
                new_links.push((lc, picked));
                ep = w;
            }
        }
        for (lc, neighbors) in new_links {
            let max = if lc == 0 {
                self.params.m0
            } else {
                self.params.m
            };
            for &e in &neighbors {
                self.links[e as usize][lc].push(v);
                if self.links[e as usize][lc].len() > max {
                    let base = self.points.get(e as usize);
                    let mut cands: Vec<(f64, u32)> = self.links[e as usize][lc]
                        .iter()
                        .map(|&c| (sq_dist(self.points.get(c as usize), base), c))
                        .collect();
                    cands.sort_by(by_distance);
                    let shrunk = pick_neighbors(&self.points, base, &cands, max);
                    on_pick(e, &cands, max, &shrunk);
                    self.links[e as usize][lc] = shrunk;
                }
            }
            self.links[v as usize][lc] = neighbors;
        }
        if level > top {
            self.entry = Some(v);
            self.max_level = level;
        }
    }

    /// The `min(k, n)` nearest points HNSW finds, best first, ranked by squared distance and then
    /// id (Alg. 5, K-NN-SEARCH, ending with [`finish`]). A beam narrower than `k` is widened to
    /// `k`, as hnswlib's `searchKnn` does (`std::max(ef_, k)`). Lean: `HNSW.promise_finish`.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[must_use]
    pub fn search(&self, q: &[f64], k: usize, ef: usize) -> Vec<Neighbor> {
        check_query(self.points.dim(), q);
        if k == 0 || self.is_empty() {
            return Vec::new();
        }
        let dist = |i: u32| sq_dist(self.points.get(i as usize), q);
        finish(self.beam_by(&dist, ef.max(k)), k)
    }

    /// The beam [`Hnsw::search`] ends its walk with, before [`finish`]: `(squared distance, node)`
    /// pairs in the order the beam's heap holds them. Behind the `unchecked` feature.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn search_beam(&self, q: &[f64], k: usize, ef: usize) -> Vec<(f64, u32)> {
        check_query(self.points.dim(), q);
        if k == 0 || self.is_empty() {
            return Vec::new();
        }
        let dist = |i: u32| sq_dist(self.points.get(i as usize), q);
        self.beam_by(&dist, ef.max(k))
    }

    /// [`Hnsw::search_beam`], and the walk that ended with it: the nodes the greedy descent stood
    /// on, layer by layer, the node the beam on layer 0 started from, and each node that beam
    /// expanded with the nodes it pushed. The walk is recorded by the code [`Hnsw::search`] runs,
    /// not by a copy of it. Behind the `unchecked` feature.
    ///
    /// # Panics
    /// If `q` has the wrong dimension or a non-finite coordinate.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn search_walk(&self, q: &[f64], k: usize, ef: usize) -> (Vec<(f64, u32)>, Walk) {
        check_query(self.points.dim(), q);
        let mut walk = Walk::default();
        if k == 0 || self.is_empty() {
            return (Vec::new(), walk);
        }
        let dist = |i: u32| sq_dist(self.points.get(i as usize), q);
        let beam = self.walk(&dist, ef.max(k), &mut walk);
        (beam, walk)
    }

    /// Alg. 5 under any distance: greedy descent of the upper layers, then a beam of `ef` on
    /// layer 0. Returns the beam's `(distance, node)` pairs, unsorted. RaBitQ's search passes its
    /// estimated distance here.
    pub(crate) fn beam_by(&self, dist: &dyn Fn(u32) -> f64, ef: usize) -> Vec<(f64, u32)> {
        self.walk(dist, ef, &mut ())
    }

    /// The walk of Alg. 5: greedy descent of the upper layers (SEARCH-LAYER with `ef = 1`), then
    /// a beam of `ef` on layer 0, reporting to `watch` as it goes. Returns the beam, unsorted.
    fn walk<W: Watch>(
        &self,
        dist: &dyn Fn(u32) -> f64,
        ef: usize,
        watch: &mut W,
    ) -> Vec<(f64, u32)> {
        let Some(entry) = self.entry else {
            return Vec::new();
        };
        let mut visited = self.take_visited();
        let mut ep = vec![(dist(entry), entry)];
        for lc in (1..=self.max_level).rev() {
            let w = self.search_layer_with(dist, &ep, 1, lc, &mut visited, watch);
            ep = vec![w[0]];
        }
        let w = self.search_layer_found(dist, &ep, ef, 0, &mut visited, watch);
        self.give_back(visited);
        w
    }

    /// Alg. 2, SEARCH-LAYER, for the tests: a fresh visited set.
    #[cfg(test)]
    pub(crate) fn search_layer(
        &self,
        dist: &dyn Fn(u32) -> f64,
        ep: &[(f64, u32)],
        ef: usize,
        lc: usize,
    ) -> Vec<(f64, u32)> {
        let mut visited = Visited::new(self.len());
        self.search_layer_with(dist, ep, ef, lc, &mut visited, &mut ())
    }

    /// Alg. 2, SEARCH-LAYER: from the entry points `ep`, the `ef` nearest nodes found on layer
    /// `lc`, ascending by distance and then node.
    fn search_layer_with<W: Watch>(
        &self,
        dist: &dyn Fn(u32) -> f64,
        ep: &[(f64, u32)],
        ef: usize,
        lc: usize,
        visited: &mut Visited,
        watch: &mut W,
    ) -> Vec<(f64, u32)> {
        let mut w = self.search_layer_found(dist, ep, ef, lc, visited, watch);
        w.sort_by(by_distance);
        w
    }

    /// [`Hnsw::search_layer_with`]'s nodes, in the order the heap holds them.
    fn search_layer_found<W: Watch>(
        &self,
        dist: &dyn Fn(u32) -> f64,
        ep: &[(f64, u32)],
        ef: usize,
        lc: usize,
        visited: &mut Visited,
        watch: &mut W,
    ) -> Vec<(f64, u32)> {
        visited.clear();
        let mut candidates: BinaryHeap<Reverse<Key>> = BinaryHeap::new();
        let mut found: BinaryHeap<Key> = BinaryHeap::new();
        for &(d, v) in ep {
            watch.start(lc, v);
            visited.insert(v);
            candidates.push(Reverse(Key(d, v)));
            found.push(Key(d, v));
        }
        while found.len() > ef {
            found.pop();
        }
        while let Some(Reverse(Key(dc, c))) = candidates.pop() {
            let farthest = found.peek().map_or(f64::INFINITY, |k| k.0);
            if dc > farthest {
                break;
            }
            watch.expand(lc, c);
            for &e in &self.links[c as usize][lc] {
                if visited.insert(e) {
                    let de = dist(e);
                    let farthest = found.peek().map_or(f64::INFINITY, |k| k.0);
                    if de < farthest || found.len() < ef {
                        watch.push(lc, e);
                        candidates.push(Reverse(Key(de, e)));
                        found.push(Key(de, e));
                        if found.len() > ef {
                            found.pop();
                        }
                    }
                }
            }
        }
        found.into_iter().map(|k| (k.0, k.1)).collect()
    }

    fn take_visited(&self) -> Visited {
        let pooled = self
            .visited
            .lock()
            .map(|mut pool| pool.pop())
            .unwrap_or(None);
        pooled.unwrap_or_else(|| Visited::new(self.len()))
    }

    fn give_back(&self, visited: Visited) {
        if let Ok(mut pool) = self.visited.lock() {
            pool.push(visited);
        }
    }

    /// The number of points.
    #[must_use]
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Whether there are no points.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// The highest level of any node.
    #[must_use]
    pub fn max_level(&self) -> usize {
        self.max_level
    }

    /// Node `v`'s level.
    ///
    /// # Panics
    /// If `v >= self.len()`.
    #[must_use]
    pub fn level(&self, v: usize) -> usize {
        self.links[v].len() - 1
    }

    /// Node `v`'s neighbors on layer `l`.
    ///
    /// # Panics
    /// If `v >= self.len()` or `l > self.level(v)`.
    #[must_use]
    pub fn neighbors(&self, v: usize, l: usize) -> &[u32] {
        &self.links[v][l]
    }

    /// The parameters the index was built with.
    #[must_use]
    pub fn params(&self) -> &HnswParams {
        &self.params
    }

    /// The points the index was built from.
    #[must_use]
    pub fn points(&self) -> &Points {
        &self.points
    }

    /// Box invariant 1: every point has at most a fixed number of neighbors. Every list on layer 0
    /// holds at most `m0` neighbors, every list above it at most `m`. Lean: `DegreeBounded`.
    #[must_use]
    pub fn is_degree_bounded(&self) -> bool {
        self.links.iter().all(|node| {
            node.iter().enumerate().all(|(l, ns)| {
                ns.len()
                    <= if l == 0 {
                        self.params.m0
                    } else {
                        self.params.m
                    }
            })
        })
    }

    /// Box invariant 3: with layers, every place on a layer is on every layer below it, and each
    /// layer up keeps a random few of the one below. A node is on layers `0..links[v].len()`, so
    /// the first half holds by the representation; this checks what can fail: every node is on
    /// layer 0, and every link on a layer reaches a node on that layer. The random few is the
    /// level draw's, not a property of one graph. Lean: `NestedLayers`.
    #[must_use]
    pub fn is_nested_layers(&self) -> bool {
        let on = |u: u32, l: usize| {
            self.links
                .get(u as usize)
                .is_some_and(|node| l < node.len())
        };
        self.links.iter().all(|node| !node.is_empty())
            && self.links.iter().all(|node| {
                node.iter()
                    .enumerate()
                    .all(|(l, ns)| ns.iter().all(|&u| on(u, l)))
            })
    }

    /// Not in the box: no node is its own neighbor. Lean: `NoSelfLinks`.
    #[must_use]
    pub fn is_no_self_links(&self) -> bool {
        self.links
            .iter()
            .enumerate()
            .all(|(v, node)| node.iter().all(|ns| ns.iter().all(|&u| u as usize != v)))
    }

    /// Not in the box: no list names a neighbor twice. Lean: `NoRepeatedLinks`.
    #[must_use]
    pub fn is_no_repeated_links(&self) -> bool {
        self.links.iter().all(|node| {
            node.iter().all(|ns| {
                let mut s = ns.clone();
                s.sort_unstable();
                s.windows(2).all(|w| w[0] != w[1])
            })
        })
    }

    /// Not in the box: the entry point is a node on the top layer, so no node is on more
    /// layers than it is; `None` exactly when there are no nodes. Lean: `EntryOnTop`.
    #[must_use]
    pub fn is_entry_on_top(&self) -> bool {
        match self.entry {
            None => self.links.is_empty(),
            Some(e) => self
                .links
                .get(e as usize)
                .is_some_and(|top| self.links.iter().all(|node| node.len() <= top.len())),
        }
    }

    /// Not in the box: the graph carries its points, one node per stored point. Lean:
    /// `OneNodePerPoint`.
    #[must_use]
    pub fn is_one_node_per_point(&self) -> bool {
        self.links.len() == self.points.len()
    }

    /// Lean `HNSW.Valid` and `HNSW.WellFormed`: [`Hnsw::is_degree_bounded`],
    /// [`Hnsw::is_nested_layers`], [`Hnsw::is_no_self_links`], [`Hnsw::is_no_repeated_links`],
    /// [`Hnsw::is_entry_on_top`] and [`Hnsw::is_one_node_per_point`]. Every build keeps both (Lean
    /// `HNSW.valid_build`, `HNSW.wellFormed_build`).
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Hnsw::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (degree_bounded)"`, `"invariant 3 (nested_layers)"`, or `"not in the box
    /// (…)"` with `no_self_links`, `no_repeated_links`, `entry_on_top` or
    /// `one_node_per_point`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_degree_bounded() {
            return Err("invariant 1 (degree_bounded)");
        }
        if !self.is_nested_layers() {
            return Err("invariant 3 (nested_layers)");
        }
        if !self.is_no_self_links() {
            return Err("not in the box (no_self_links)");
        }
        if !self.is_no_repeated_links() {
            return Err("not in the box (no_repeated_links)");
        }
        if !self.is_entry_on_top() {
            return Err("not in the box (entry_on_top)");
        }
        if !self.is_one_node_per_point() {
            return Err("not in the box (one_node_per_point)");
        }
        Ok(())
    }
}

/// What a layer search reports as it runs. `()` reports nothing, so the search the API runs is
/// the same code with every report compiled away.
trait Watch {
    /// The search on layer `lc` starts from `node`.
    fn start(&mut self, _lc: usize, _node: u32) {}
    /// The search on layer `lc` pops `node` and reads its list there.
    fn expand(&mut self, _lc: usize, _node: u32) {}
    /// `node`, read from the list last expanded on layer `lc`, joins the beam.
    fn push(&mut self, _lc: usize, _node: u32) {}
}

impl Watch for () {}

/// A search's walk, as `Hnsw::search_walk` records it. Behind the `unchecked` feature.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Walk {
    /// Per upper layer, top first: the layer and the nodes the greedy descent stood on, in order.
    /// Each node after the first is where the step from the one before moved; the last is where
    /// the descent stopped on that layer.
    pub upper: Vec<(usize, Vec<u32>)>,
    /// The node the beam on layer 0 started from.
    pub start: Option<u32>,
    /// Layer 0, per node the beam expanded, in order: the node and the nodes of its list that
    /// joined the beam.
    pub level0: Vec<(u32, Vec<u32>)>,
}

#[cfg(any(test, feature = "unchecked"))]
impl Watch for Walk {
    fn start(&mut self, lc: usize, node: u32) {
        if lc == 0 {
            self.start = Some(node);
        }
    }

    fn expand(&mut self, lc: usize, node: u32) {
        if lc == 0 {
            self.level0.push((node, Vec::new()));
        } else {
            match self.upper.last_mut() {
                Some((l, nodes)) if *l == lc => nodes.push(node),
                _ => self.upper.push((lc, vec![node])),
            }
        }
    }

    fn push(&mut self, lc: usize, node: u32) {
        if lc == 0 {
            if let Some((_, pushed)) = self.level0.last_mut() {
                pushed.push(node);
            }
        }
    }
}

/// What the insertion reports at each picking: the base node, its candidates nearest first, the
/// cap, and the picks.
type OnPick<'a> = dyn FnMut(u32, &[(f64, u32)], usize, &[u32]) + 'a;

/// One picking the build made: `picked` is what [`select_neighbors`] kept for `base` from
/// `candidates` (nearest first) at cap `m`. Behind the `unchecked` feature.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq)]
pub struct Picking {
    /// The node whose list is picked.
    pub base: u32,
    /// The candidates, nearest to `base` first.
    pub candidates: Vec<u32>,
    /// The cap.
    pub m: usize,
    /// The picks, in order.
    pub picked: Vec<u32>,
}

/// The search's last step: sort the beam by squared distance and then node, keep `k`. The
/// distances are the exact ones the walk computed. Lean: `HNSW.finish`, `HNSW.promise_finish`.
#[must_use]
pub fn finish(mut beam: Vec<(f64, u32)>, k: usize) -> Vec<Neighbor> {
    beam.sort_by(by_distance);
    beam.truncate(k);
    beam.into_iter()
        .map(|(d, i)| Neighbor {
            id: i as usize,
            sq_dist: d,
        })
        .collect()
}

/// Box invariant 2: a point picks its neighbors nearest first, skipping any candidate that is
/// closer to one already picked than to the place. The `candidates` (ids into `points`) come
/// nearest to `base` first, and `picked` is what that rule keeps of them, at most `m`, a tie
/// with a neighbor already picked keeping the candidate. Picks are compared as points, as the
/// Lean compares them. Lean: `PicksDiverse`.
#[must_use]
pub fn is_picks_diverse(
    points: &Points,
    base: &[f64],
    candidates: &[u32],
    picked: &[u32],
    m: usize,
) -> bool {
    let n = points.len();
    if base.len() != points.dim() || candidates.iter().chain(picked).any(|&i| i as usize >= n) {
        return false;
    }
    let p = |i: u32| points.get(i as usize);
    if candidates
        .windows(2)
        .any(|w| sq_dist(p(w[0]), base) > sq_dist(p(w[1]), base))
    {
        return false;
    }
    let mut sofar: Vec<u32> = Vec::new();
    for &c in candidates {
        let to_base = sq_dist(p(c), base);
        if sofar.len() < m && sofar.iter().all(|&k| to_base <= sq_dist(p(k), p(c))) {
            if picked.get(sofar.len()).map(|&x| p(x)) != Some(p(c)) {
                return false;
            }
            sofar.push(c);
        }
    }
    sofar.len() == picked.len()
}

/// Lean `HNSW.Picking.Valid`: [`is_picks_diverse`], at every picking the insertion makes.
#[must_use]
pub fn is_picking_valid(
    points: &Points,
    base: &[f64],
    candidates: &[u32],
    picked: &[u32],
    m: usize,
) -> bool {
    check_picking_valid(points, base, candidates, picked, m).is_ok()
}

/// [`is_picking_valid`], naming the piece that fails.
///
/// # Errors
///
/// `"invariant 2 (picks_diverse)"`.
pub fn check_picking_valid(
    points: &Points,
    base: &[f64],
    candidates: &[u32],
    picked: &[u32],
    m: usize,
) -> Result<(), &'static str> {
    if !is_picks_diverse(points, base, candidates, picked, m) {
        return Err("invariant 2 (picks_diverse)");
    }
    Ok(())
}

/// Alg. 4, SELECT-NEIGHBORS-HEURISTIC, the picking the build runs, `pick_neighbors`. Behind
/// the `unchecked` feature, for tests that hold the picking to the Lean's; not part of the API.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn select_neighbors(
    points: &Points,
    base: &[f64],
    candidates: &[(f64, u32)],
    m: usize,
) -> Vec<u32> {
    pick_neighbors(points, base, candidates, m)
}

/// Alg. 4, SELECT-NEIGHBORS-HEURISTIC, with `extendCandidates` and `keepPrunedConnections` off:
/// from `candidates`, sorted nearest to `base` first, keep each unless a neighbor already kept
/// is strictly nearer to it than `base` is (a tie keeps it), until `m` are kept. Only the
/// candidates' order and ids are read; distances are recomputed from `base`. Lean:
/// `picksDiverse_selectNeighbors`.
fn pick_neighbors(points: &Points, base: &[f64], candidates: &[(f64, u32)], m: usize) -> Vec<u32> {
    let mut kept: Vec<u32> = Vec::with_capacity(m);
    for &(_, c) in candidates {
        if kept.len() >= m {
            break;
        }
        let pc = points.get(c as usize);
        let to_base = sq_dist(pc, base);
        if kept
            .iter()
            .all(|&k| to_base <= sq_dist(pc, points.get(k as usize)))
        {
            kept.push(c);
        }
    }
    kept
}

/// One greedy step (Lean `greedyStep`): move to the neighbor nearest `q` if it is strictly
/// nearer than `cur`, else stay. Behind the `unchecked` feature, for tests; not part of the API.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn greedy_step(points: &Points, q: &[f64], cur: u32, nbrs: &[u32]) -> u32 {
    let d = |i: u32| sq_dist(points.get(i as usize), q);
    nbrs.iter()
        .fold(cur, |best, &x| if d(x) < d(best) { x } else { best })
}

/// `⌊−ln(u)·m_L⌋` with `u` uniform in `(0, 1]`.
fn draw_level(rng: &mut SplitMix64, ml: f64) -> usize {
    let u = 1.0 - rng.next_f64();
    // A small non-negative number; `as` saturates in the impossible case it is not.
    (-u.ln() * ml).floor() as usize
}

/// Ascending by distance, then by node.
fn by_distance(a: &(f64, u32), b: &(f64, u32)) -> Ordering {
    a.0.total_cmp(&b.0).then(a.1.cmp(&b.1))
}

/// The order the index sorts `(distance, node)` candidates into before `pick_neighbors` reads
/// them: ascending by distance, then by node, for tests that sort candidates as the index does.
/// Not part of the API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[must_use]
pub fn by_distance_order(a: &(f64, u32), b: &(f64, u32)) -> Ordering {
    by_distance(a, b)
}

/// A `(distance, node)` pair ordered by [`by_distance`].
#[derive(Debug, Clone, Copy, PartialEq)]
struct Key(f64, u32);

impl Eq for Key {}

impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Key {
    fn cmp(&self, other: &Self) -> Ordering {
        by_distance(&(self.0, self.1), &(other.0, other.1))
    }
}

/// Visited marks by generation: `marks[v] == stamp` means visited in the current search, so
/// clearing is one increment.
#[derive(Debug, Clone)]
struct Visited {
    stamp: u32,
    marks: Vec<u32>,
}

impl Visited {
    fn new(n: usize) -> Self {
        Visited {
            stamp: 0,
            marks: vec![0; n],
        }
    }

    fn clear(&mut self) {
        self.stamp = self.stamp.wrapping_add(1);
        if self.stamp == 0 {
            self.marks.iter_mut().for_each(|m| *m = 0);
            self.stamp = 1;
        }
    }

    /// Mark `v`; whether it was unmarked.
    fn insert(&mut self, v: u32) -> bool {
        let m = &mut self.marks[v as usize];
        if *m == self.stamp {
            false
        } else {
            *m = self.stamp;
            true
        }
    }
}

#[cfg(test)]
#[path = "unit_tests/hnsw.rs"]
mod tests;
