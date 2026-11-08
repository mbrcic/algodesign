// SPDX-License-Identifier: Apache-2.0
//! Criterion benchmarks for every `algodesign::searching` structure.
//!
//! **What this measures, and what it doesn't.** `insert`/`delete` take `&mut self` and change the
//! tree in place, so the previous version is not left readable: nothing here is persistent.
//!
//! Every update writes through `&mut` and reuses the boxes it is handed, which is what Sedgewick's
//! Java and CLRS's pseudocode do: exactly one allocation per inserted key on `Bst`, `Llrb` and `RbTree`,
//! 1.03 on `Treap` (its rotate-up path stack spills past eight levels), 0.152 on `BTree` at
//! `t = 6`, and nothing at all on any deletion. `tests/allocations.rs` checks every one of those
//! counts in `cargo test`.
//!
//! These benchmarks make that cost visible and trackable over time. The `baseline_std_btreeset`
//! group measures how these structures compare with `std`'s `BTreeSet`, over key sets of the same
//! sizes. The `btree` group runs at `t = 8`.
//!
//! Each structure gets an `insert` (build from empty) group and a `search`/`contains` group
//! (against a prebuilt structure of the given size, so lookup cost is isolated from build cost).
//! Balancing structures also get a `delete` group (delete every key, one at a time, from a
//! prebuilt structure, timed via `iter_batched` so the O(n) `Clone` needed to get a fresh input
//! each iteration isn't counted). Keys are `i64`, shuffled with a fixed seed for reproducibility
//! across runs.
//!
//! `Lsm` is the odd one out, and the one structure in this chapter where these numbers *are* the
//! pedagogical point: `write` should come out flat regardless of how many runs already exist (the
//! chapter's `O(1)`-hot-path claim, not just the same big-O every other structure's `insert`
//! gets), and `flush_and_cascade` should visibly grow with however many entries the merged runs
//! hold, making the Search chapter's LSM trade-off (cheap writes now, compaction later, and the
//! write amplification it costs) a number instead of an assertion. Its store flushes every
//! `inputs::LSM_MEMTABLE` writes, so every size has levels, and `tests/bench_inputs.rs` checks the
//! layout each LSM benchmark starts from.

#![allow(
    missing_docs,
    reason = "criterion_group! emits an undocumented pub fn; a bench exports nothing a reader uses"
)]

use algodesign::searching::{binary_search, sequential_search};
use criterion::measurement::WallTime;
use criterion::{
    criterion_group, criterion_main, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
use std::hint::black_box;

mod inputs;
use inputs::{
    baseline_group, bst_group, btree_group, llrb_group, lsm_group, red_black_group,
    sequential_search_keys, treap_group, Timer,
};

const SIZES: [usize; 3] = [100, 1_000, 10_000];
/// Minimum degree for `BTree` benchmarks (arbitrary, mid-sized fan-out).
const BTREE_T: usize = 8;

/// `inputs::Timer` on criterion: the one piece of the tree benchmarks that
/// `tests/bench_inputs.rs` cannot run, and so held by convention. `built` must use
/// `iter_with_large_drop`, since plain `iter` drops each tree it builds inside the timing and
/// would count an `O(n)` free as insertion; `mutated` must use `iter_batched_ref`, which drops
/// each fresh copy outside the timing. `scanned` and `rebuilt` time as `borrowed` and `mutated` do.
struct CriterionTimer<'a, 'b> {
    group: &'a mut BenchmarkGroup<'b, WallTime>,
    n: usize,
}

impl Timer for CriterionTimer<'_, '_> {
    fn built<S: 'static>(&mut self, id: &str, keys: &[i64], op: impl Fn(&[i64]) -> S) {
        self.group
            .bench_with_input(BenchmarkId::new(id, self.n), keys, |b, keys| {
                b.iter_with_large_drop(|| op(keys));
            });
    }

    fn borrowed<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S)) {
        self.group
            .bench_with_input(BenchmarkId::new(id, self.n), built, |b, built| {
                b.iter(|| op(built));
            });
    }

    fn mutated<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S)) {
        self.group
            .bench_with_input(BenchmarkId::new(id, self.n), built, |b, built| {
                b.iter_batched_ref(|| built.clone(), &op, BatchSize::SmallInput);
            });
    }

    fn scanned<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S)) {
        self.borrowed(id, built, op);
    }

    fn rebuilt<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S)) {
        self.mutated(id, built, op);
    }
}

/// One criterion group per tree, every size, each run by its `inputs::*_group` function.
fn tree_group(c: &mut Criterion, name: &str, run: impl Fn(&mut CriterionTimer<'_, '_>, usize)) {
    let mut group = c.benchmark_group(name);
    for &n in &SIZES {
        group.throughput(Throughput::Elements(n as u64));
        run(
            &mut CriterionTimer {
                group: &mut group,
                n,
            },
            n,
        );
    }
    group.finish();
}

fn bench_sequential_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("sequential_search");
    for &n in &SIZES {
        let keys = sequential_search_keys(n);
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("build", n), &keys, |b, keys| {
            b.iter(|| sequential_search::build(black_box(keys)));
        });
        let built = sequential_search::build(&keys);
        group.bench_with_input(BenchmarkId::new("contains_miss", n), &built, |b, built| {
            b.iter(|| sequential_search::contains(black_box(built), black_box(&-1)));
        });
    }
    group.finish();
}

fn bench_binary_search(c: &mut Criterion) {
    let mut group = c.benchmark_group("binary_search");
    for &n in &SIZES {
        let mut sorted: Vec<i64> = (0..n as i64).collect();
        sorted.sort_unstable();
        group.throughput(Throughput::Elements(n as u64));
        group.bench_with_input(BenchmarkId::new("search_hit", n), &sorted, |b, sorted| {
            let target = sorted[sorted.len() / 2];
            b.iter(|| binary_search::search(black_box(sorted), black_box(&target)));
        });
        group.bench_with_input(BenchmarkId::new("search_miss", n), &sorted, |b, sorted| {
            b.iter(|| binary_search::search(black_box(sorted), black_box(&-1)));
        });
    }
    group.finish();
}

fn bench_bst(c: &mut Criterion) {
    tree_group(c, "bst", |t, n| bst_group(t, n));
}

/// `std::collections::BTreeSet` over key sets of the same sizes (the very keys `llrb` uses), so
/// every group above has something to be read against. It is an in-place, arena-ish B-tree with
/// `B = 6`; nothing here is trying to beat it, but a reader is entitled to know how far off these
/// are, and which of them is not far off.
fn bench_baseline(c: &mut Criterion) {
    tree_group(c, "baseline_std_btreeset", |t, n| baseline_group(t, n));
}

fn bench_llrb(c: &mut Criterion) {
    tree_group(c, "llrb", |t, n| llrb_group(t, n));
}

fn bench_red_black_standard(c: &mut Criterion) {
    tree_group(c, "red_black_standard", |t, n| red_black_group(t, n));
}

/// `insert_random`, a lookup and `delete_all`, the last two on [`inputs::seeded_treap`].
fn bench_treap(c: &mut Criterion) {
    tree_group(c, "treap", |t, n| treap_group(t, n));
}

fn bench_btree(c: &mut Criterion) {
    tree_group(c, "btree", |t, n| btree_group(t, n, BTREE_T));
}

fn bench_lsm(c: &mut Criterion) {
    tree_group(c, "lsm", |t, n| lsm_group(t, n));
}

criterion_group!(
    benches,
    bench_baseline,
    bench_sequential_search,
    bench_binary_search,
    bench_bst,
    bench_llrb,
    bench_red_black_standard,
    bench_treap,
    bench_btree,
    bench_lsm,
);
criterion_main!(benches);
