// SPDX-License-Identifier: Apache-2.0
//! Log-structured merge tree: a memtable, then leveled compaction.
//!
//! Sources: O'Neil, Cheng, Gawlick & O'Neil; Luo & Carey (VLDB J 29(1), 2020). A memtable
//! buffers writes; a full one is filed whole as a sealed run in front of level 0, and the flush
//! that brings level 0 to `level0_runs` runs merges them into level 1. Every deeper level `i` is
//! one run of at most `capacity · ratio^i` entries. Only a merge with nothing older beneath it
//! drops tombstones.
//!
//! A [`Run`] is a key-sorted `Vec<(K, Option<V>)>`, `None` a tombstone; levels are *slots*, since a
//! level's index sets its budget. No Bloom filter, write-ahead log or background compaction. A
//! run is what the chapter's box calls a batch and its prose a file on disk, an `SSTable`.
//!
//! Lean counterpart: `AlgoDesign.Searching.LSM` (`LSM.Store` models this policy).
//!
//! **Against the Python, and how fast.** The same policy; the memtable is a `BTreeMap` where the
//! Python's is a `dict` sorted at the flush, and a merge allocates its run once. In memory, against
//! `std::collections::BTreeMap`, an LSM pays for writes that never seek and has no device to win
//! them back from. After a full compaction one sorted run is left.
//! `cargo bench -p algodesign --bench structures -- lsm` times `write` and `flush_and_cascade`.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;

/// Live entries in key order — see [`Lsm::iter`].
///
/// One cursor per source (`1 + R + L` of them); `next` picks the smallest with a linear scan.
pub struct Iter<'a, K, V> {
    memtable: std::iter::Peekable<std::collections::btree_map::Iter<'a, K, Option<V>>>,
    /// Newest run first, so a lower index wins a tie.
    levels: Vec<&'a [(K, Option<V>)]>,
}

// By hand: a derive would ask `K: Clone` and `V: Clone`, though only references are copied.
impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Iter {
            memtable: self.memtable.clone(),
            levels: self.levels.clone(),
        }
    }
}

/// The live entries not yet yielded, as `std`'s map iterators show themselves.
impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for Iter<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.clone()).finish()
    }
}

impl<'a, K: Ord, V> Iter<'a, K, V> {
    /// The smallest key any cursor is looking at, and where it lives. `None` when all are spent.
    fn smallest(&mut self) -> Option<(&'a K, usize)> {
        let mut best: Option<(&'a K, usize)> = None;
        if let Some((k, _)) = self.memtable.peek() {
            best = Some((k, 0));
        }
        for (i, run) in self.levels.iter().enumerate() {
            if let Some((k, _)) = run.first() {
                match best {
                    // Strictly smaller only: on a tie the earlier (newer) source keeps it.
                    Some((bk, _)) if *bk <= *k => {}
                    _ => best = Some((k, i + 1)),
                }
            }
        }
        best
    }
}

impl<'a, K: Ord, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        loop {
            let (key, source) = self.smallest()?;
            // Whoever holds the newest entry for this key decides whether it is live.
            let value: Option<&'a V> = if source == 0 {
                self.memtable.peek().and_then(|(_, v)| v.as_ref())
            } else {
                self.levels[source - 1]
                    .first()
                    .and_then(|(_, v)| v.as_ref())
            };
            // Every older cursor sitting on this key is shadowed, so step them all past it.
            if self.memtable.peek().is_some_and(|(k, _)| *k == key) {
                self.memtable.next();
            }
            for run in &mut self.levels {
                if run.first().is_some_and(|(k, _)| k == key) {
                    *run = &run[1..];
                }
            }
            if let Some(v) = value {
                return Some((key, v));
            }
            // A tombstone: the key is not live, so keep going.
        }
    }
}

// No `ExactSizeIterator`: the live-key count is what `len` has to walk for.
impl<K: Ord, V> std::iter::FusedIterator for Iter<'_, K, V> {}

impl<'a, K: Ord, V> IntoIterator for &'a Lsm<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<K: Ord, V> Extend<(K, V)> for Lsm<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.write(k, v);
        }
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for Lsm<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut s = Lsm::new();
        s.extend(iter);
        s
    }
}

/// Equal when the live contents are equal; layout and pending tombstones are not compared.
/// `O(n + m)`.
impl<K: Ord, V: PartialEq> PartialEq for Lsm<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<K: Ord, V: Eq> Eq for Lsm<K, V> {}

/// One immutable, key-sorted chunk of entries, `None` a tombstone. Lean: `Run α β`.
pub type Run<K, V> = Vec<(K, Option<V>)>;

/// Mirrors `Run.Sorted`: keys strictly increasing, so no duplicate keys within one run.
fn run_sorted<K: Ord, V>(run: &Run<K, V>) -> bool {
    run.windows(2).all(|w| w[0].0 < w[1].0)
}

/// Mirrors `Run.lookup`: `None` says nothing about `key`, `Some(None)` is a tombstone hit,
/// `Some(Some(v))` a live value. A binary search, `O(log r)`, since the run is sorted.
fn run_lookup<'a, K, V, Q>(key: &Q, run: &'a Run<K, V>) -> Option<Option<&'a V>>
where
    K: Borrow<Q>,
    Q: Ord + ?Sized,
{
    run.binary_search_by(|(k, _)| k.borrow().cmp(key))
        .ok()
        .map(|i| run[i].1.as_ref())
}

/// Two-pointer merge of two sorted runs, `newer` winning a tied key. Lean: `Run.mergeRuns`.
/// `O(n + m)`, one allocation; both runs are consumed.
#[deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::unreachable,
    clippy::todo,
    clippy::unimplemented,
    clippy::indexing_slicing
)]
fn merge_runs<K: Ord, V>(newer: Run<K, V>, older: Run<K, V>) -> Run<K, V> {
    let cap = newer.len() + older.len();
    let mut out = Vec::with_capacity(cap);
    let mut newer = newer.into_iter().peekable();
    let mut older = older.into_iter().peekable();
    loop {
        // Decide from the peeks, then act, so taking the entry needs no `unwrap`.
        let (take_newer, shadowed) = match (newer.peek(), older.peek()) {
            (Some(n), Some(o)) => match n.0.cmp(&o.0) {
                Ordering::Less => (true, false),
                Ordering::Greater => (false, false),
                // Same key: the newer entry wins and the older one is dropped unread.
                Ordering::Equal => (true, true),
            },
            (Some(_), None) => (true, false),
            (None, Some(_)) => (false, false),
            (None, None) => break,
        };
        if shadowed {
            older.next();
        }
        let source = if take_newer { &mut newer } else { &mut older };
        if let Some(entry) = source.next() {
            out.push(entry);
        }
    }
    out
}

/// How many entries the memtable holds before it is flushed into the levels.
pub const DEFAULT_MEMTABLE_CAPACITY: usize = 1024;

/// How much bigger each level may be than the one above it.
pub const DEFAULT_LEVEL_RATIO: usize = 10;

/// How many sealed flushes level 0 gathers before they are merged into level 1.
pub const DEFAULT_LEVEL0_RUNS: usize = 4;

/// A log-structured key/value store: a map, since "never written" and "written, then deleted"
/// differ. `delete` writes a tombstone; nothing is found-and-removed, only shadowed.
///
/// `from_parts_unchecked`, which checks no level, exists only behind the `unchecked` feature, for
/// tests that build a broken store on purpose: `cargo test --features unchecked`.
#[derive(Debug, Clone)]
pub struct Lsm<K, V> {
    /// The newest entries, kept in key order; a key written twice before a flush leaves one entry.
    memtable: std::collections::BTreeMap<K, Option<V>>,
    /// Level 0 first, each a list of sorted runs newest first: level 0 at most `level0_runs`
    /// (a flush leaves fewer, since the run that reaches `level0_runs` is merged down at once),
    /// every deeper level at most one.
    levels: Vec<Vec<Run<K, V>>>,
    memtable_capacity: usize,
    level_ratio: usize,
    level0_runs: usize,
}

/// The empty store at the default shape, as [`Lsm::new`]. By hand: a derived one would be all zeros.
impl<K: Ord, V> Default for Lsm<K, V> {
    fn default() -> Self {
        Lsm::new()
    }
}

impl<K: Ord, V> Lsm<K, V> {
    /// The empty store, at the default capacity and ratio.
    #[must_use]
    pub fn new() -> Self {
        Lsm::with_shape(
            DEFAULT_MEMTABLE_CAPACITY,
            DEFAULT_LEVEL_RATIO,
            DEFAULT_LEVEL0_RUNS,
        )
    }

    /// The empty store, with the three numbers that decide the layering.
    ///
    /// # Panics
    /// If `memtable_capacity` is zero, `level_ratio` is below two, or `level0_runs` is zero.
    #[must_use]
    pub fn with_shape(memtable_capacity: usize, level_ratio: usize, level0_runs: usize) -> Self {
        assert!(
            memtable_capacity > 0,
            "the memtable must hold at least one entry"
        );
        assert!(
            level_ratio >= 2,
            "each level must be at least twice the one above it"
        );
        assert!(level0_runs > 0, "level 0 must hold at least one run");
        Lsm {
            memtable: std::collections::BTreeMap::new(),
            levels: Vec::new(),
            memtable_capacity,
            level_ratio,
            level0_runs,
        }
    }

    /// The store with these levels, this shape and an empty memtable, **checking no level and
    /// not the shape**, for tests that must hand the predicates illegal stores, an unusable
    /// shape among them. Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts_unchecked(
        levels: Vec<Vec<Run<K, V>>>,
        memtable_capacity: usize,
        level_ratio: usize,
        level0_runs: usize,
    ) -> Self {
        Lsm {
            memtable: std::collections::BTreeMap::new(),
            levels,
            memtable_capacity,
            level_ratio,
            level0_runs,
        }
    }

    /// How many entries level `i` (1 or deeper) may hold before it is pushed down: the memtable's
    /// capacity multiplied by the ratio once per level. The deepest level is exempt.
    #[must_use]
    fn budget(&self, level: usize) -> usize {
        self.memtable_capacity.saturating_mul(
            self.level_ratio
                .saturating_pow(u32::try_from(level).unwrap_or(u32::MAX)),
        )
    }

    /// Every run in the store, newest first: level 0's sealed flushes, then each deeper level.
    fn runs(&self) -> impl DoubleEndedIterator<Item = &Run<K, V>> {
        self.levels.iter().flatten()
    }

    /// The Lean `Store.RunsSorted`, box invariant 1: every run strictly sorted by key. The
    /// memtable is a `BTreeMap`, sorted by its type.
    #[must_use]
    pub fn is_runs_sorted(&self) -> bool {
        self.runs().all(run_sorted)
    }

    /// The Lean `Store.FewBatches`, box invariant 2: level 0 at most `level0_runs` runs, every
    /// deeper level at most one, and every level from 1 down but the deepest within its budget.
    #[must_use]
    pub fn is_few_batches(&self) -> bool {
        let few_runs = self
            .levels
            .first()
            .is_none_or(|l0| l0.len() <= self.level0_runs)
            && self.levels.iter().skip(1).all(|level| level.len() <= 1);
        let deepest = self.levels.len().saturating_sub(1);
        few_runs
            && !self.levels.iter().enumerate().any(|(i, level)| {
                0 < i && i < deepest && level.first().is_some_and(|r| r.len() > self.budget(i))
            })
    }

    /// The Lean `Store.RunsNonEmpty`, not in the box: no run below the memtable is empty.
    #[must_use]
    pub fn is_runs_non_empty(&self) -> bool {
        self.runs().all(|r| !r.is_empty())
    }

    /// The Lean `Store.OldestRunClean`, not in the box: the oldest run below level 0
    /// holds no tombstone, so deletion eventually frees space.
    #[must_use]
    pub fn is_oldest_run_clean(&self) -> bool {
        self.levels
            .iter()
            .skip(1)
            .flatten()
            .next_back()
            .is_none_or(|r| r.iter().all(|(_, v)| v.is_some()))
    }

    /// The Lean `Store.ShapeUsable`, not in the box: the memtable holds at least one entry,
    /// each level is at least twice the one above, and level 0 holds at least one run.
    /// [`Lsm::with_shape`] refuses any other shape.
    #[must_use]
    pub fn is_shape_usable(&self) -> bool {
        self.memtable_capacity >= 1 && self.level_ratio >= 2 && self.level0_runs >= 1
    }

    /// The Lean `Store.Valid`, its five pieces in order. Lean: `Store.valid_of_reachable`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Lsm::is_valid`] with the first failed piece named, in the Lean `Store.Valid`'s order.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (runs_sorted)"`, `"invariant 2 (few_batches)"`,
    /// `"not in the box (runs_non_empty)"`,
    /// `"not in the box (oldest_run_clean)"` or
    /// `"not in the box (shape_usable)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_runs_sorted() {
            return Err("invariant 1 (runs_sorted)");
        }
        if !self.is_few_batches() {
            return Err("invariant 2 (few_batches)");
        }
        if !self.is_runs_non_empty() {
            return Err("not in the box (runs_non_empty)");
        }
        if !self.is_oldest_run_clean() {
            return Err("not in the box (oldest_run_clean)");
        }
        if !self.is_shape_usable() {
            return Err("not in the box (shape_usable)");
        }
        Ok(())
    }

    /// Newest-first shadowing: the memtable, then each run, stopping at the first that mentions
    /// `key`. `O(log m + (R + L) log n)`. Lean: `Store.lookup`.
    #[must_use]
    pub fn lookup<Q>(&self, key: &Q) -> Option<Option<&V>>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Some(v) = self.memtable.get(key) {
            return Some(v.as_ref());
        }
        self.runs().find_map(|run| run_lookup(key, run))
    }

    /// Record `key`'s new value in the memtable, flushing if that fills it. `O(1)` in the keys
    /// stored, reading nothing already stored. Lean: `Store.write`, `lookup_write_self`.
    pub fn write(&mut self, key: K, value: V) {
        self.memtable.insert(key, Some(value));
        self.flush_if_full();
    }

    /// Write a tombstone for `key`. Returns nothing: reporting the old value would cost a lookup.
    pub fn delete(&mut self, key: K) {
        self.memtable.insert(key, None);
        self.flush_if_full();
    }

    fn flush_if_full(&mut self) {
        if self.memtable.len() >= self.memtable_capacity {
            self.flush();
        }
    }

    /// File the memtable, tombstones and all, as a sealed run in front of level 0; when level 0
    /// reaches `level0_runs` runs, merge them into level 1 and cascade. No-op when empty.
    /// Lean: `Store.flush`, `Store.preservesGet_flush`.
    pub fn flush(&mut self) {
        if self.memtable.is_empty() {
            return;
        }
        let fresh: Run<K, V> = std::mem::take(&mut self.memtable).into_iter().collect();
        if self.levels.is_empty() {
            self.levels.push(Vec::new());
        }
        self.levels[0].insert(0, fresh);
        if self.levels[0].len() < self.level0_runs {
            return;
        }
        if self.levels.len() == 1 {
            self.levels.push(Vec::new());
        }
        let mut sealed = std::mem::take(&mut self.levels[0]).into_iter();
        let newest = sealed.next().unwrap_or_default();
        let merged = sealed.fold(newest, merge_runs);
        self.push_down(merged, 1);
        self.cascade();
    }

    /// Merge `newer` into the one run of level `into`, dropping tombstones if every slot beneath
    /// is empty. A merge that cancels out leaves the level empty, never holding an empty run.
    fn push_down(&mut self, newer: Run<K, V>, into: usize) {
        let older = self.levels[into].pop().unwrap_or_default();
        let merged = merge_runs(newer, older);
        let nothing_below = self.levels[into + 1..].iter().all(Vec::is_empty);
        let merged = if nothing_below {
            drop_tombstones(merged)
        } else {
            merged
        };
        self.levels[into] = if merged.is_empty() {
            Vec::new()
        } else {
            vec![merged]
        };
    }

    /// Push every level from 1 down that is over budget into the one below it, deepest-last so a
    /// level that receives an overflow is itself reconsidered.
    fn cascade(&mut self) {
        let mut i = 1;
        while i < self.levels.len() {
            let over = self.levels[i]
                .first()
                .is_some_and(|r| r.len() > self.budget(i));
            if !over {
                i += 1;
                continue;
            }
            if i + 1 == self.levels.len() {
                self.levels.push(Vec::new());
            }
            let newer = self.levels[i].pop().unwrap_or_default();
            self.push_down(newer, i + 1);
            i += 1;
        }
        // An emptied level stays as a slot: its index is what decides the budgets below it.
    }

    /// Merge everything into a single level, tombstones dropped.
    /// Lean: `Store.preservesGet_compactFully`.
    pub fn compact_fully(&mut self) {
        self.flush();
        // Oldest first, each newer run winning a tied key.
        let merged = std::mem::take(&mut self.levels)
            .into_iter()
            .flatten()
            .rev()
            .fold(Run::new(), |older, newer| merge_runs(newer, older));
        let cleaned = drop_tombstones(merged);
        if !cleaned.is_empty() {
            self.levels.push(vec![cleaned]);
        }
    }

    /// The client view of [`Lsm::lookup`]: `None` for both "never written" and "deleted".
    /// Compaction preserves it exactly. Lean: `Store.get`.
    #[must_use]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.lookup(key).flatten()
    }

    /// Is `key` live (present with a value, not a tombstone and not absent)? Lean: `Store.get`
    /// answers a value.
    #[must_use]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// The levels, level 0 first, each a list of runs newest first. Excludes the memtable.
    #[must_use]
    pub fn levels(&self) -> &[Vec<Run<K, V>>] {
        &self.levels
    }

    /// How many entries are buffered and not yet flushed.
    #[must_use]
    pub fn memtable_len(&self) -> usize {
        self.memtable.len()
    }

    /// How many levels the store currently holds. `O(1)`.
    #[must_use]
    pub fn level_count(&self) -> usize {
        self.levels.len()
    }

    /// How many keys are live. `O(n)`: a cached count would need a read on the write path.
    #[must_use]
    pub fn len(&self) -> usize {
        self.iter().count()
    }

    /// Are there no live keys? Stops at the first live key; `O(n)` only when the answer is `true`.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.iter().next().is_none()
    }

    /// Live entries, in key order, newest write winning and tombstones skipped: a k-way merge
    /// over the memtable and the `R + L` runs.
    #[must_use]
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            memtable: self.memtable.iter().peekable(),
            levels: self.runs().map(Vec::as_slice).collect(),
        }
    }
}

/// Drop tombstones from a run with nothing older beneath it, which have nothing left to shadow.
fn drop_tombstones<K, V>(mut run: Run<K, V>) -> Run<K, V> {
    run.retain(|(_, v)| v.is_some());
    run
}

#[cfg(test)]
#[path = "unit_tests/lsm.rs"]
mod tests;
