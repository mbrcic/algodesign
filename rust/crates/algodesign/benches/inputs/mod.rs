//! The inputs the benchmarks run on, and the tree benchmarks themselves, in a module of their
//! own so `tests/bench_inputs.rs` can run them: the benchmarks are compiled in CI but never run,
//! so a fault in *what* they measure is invisible to every other gate.
//!
//! Twice it was one. `contains_hit` on the treap built its tree with `insert_random`, so every
//! run timed one key's depth in a freshly sampled random tree, a high-variance quantity that made
//! run-to-run comparison meaningless. And it moved the tree into the timed closure, so it timed
//! the tree's `O(n)` drop, which dwarfed the lookup.
//!
//! What pins what:
//! - **The keys.** Each group draws its keys here, from a fixed seed; nothing in
//!   `benches/structures.rs` draws any. The test runs every group twice and requires the same
//!   keys both times, a permutation of `0..n`.
//! - **Which tree each benchmark times.** Each `*_group` function builds its tree from those keys
//!   and hands the same tree to its lookup and its delete benchmark. The test checks the tree each
//!   benchmark received against the one its fixture should build: the treap's is
//!   [`seeded_treap`], a function of the keys alone.
//! - **That timed reads and deletes copy nothing and drop nothing.** Partly by the types: a read is
//!   timed through [`Timer::borrowed`], whose operation gets `&S`, and a delete through
//!   [`Timer::mutated`], whose operation gets `&mut S` to a fresh copy, so neither owns the tree.
//!   The types cannot stop an operation from cloning what it is handed, or from overwriting it
//!   through `&mut`. The test can: it runs every read and delete under a counting allocator and
//!   requires zero allocations, which a clone of a tree cannot make.
//! - **What the criterion adapter does with the trees**, in `benches/structures.rs`, is held by
//!   convention, since no test runs criterion: [`Timer::built`] must time with
//!   `iter_with_large_drop` (plain `iter` drops each built tree inside the timing, an `O(n)` free
//!   counted as insertion), and [`Timer::mutated`] with `iter_batched_ref`, which drops each copy
//!   after the timing stops.
//! - **The LSM-tree's layout.** The LSM benchmarks are about levels, flushes and merges, so the
//!   test also checks the store each one starts from: levels at every size, the deepest key in
//!   the deepest level, and, for `flush_and_cascade`, a store one write short of a level-0 merge.
//!   Its scan and its flush allocate by design, so they go through [`Timer::scanned`] and
//!   [`Timer::rebuilt`], which time the same way as [`Timer::borrowed`] and [`Timer::mutated`]
//!   without the zero-allocation check.

use std::collections::BTreeSet;
use std::hint::black_box;

use algodesign::searching::lsm::{Lsm, DEFAULT_LEVEL0_RUNS, DEFAULT_LEVEL_RATIO};
use algodesign::searching::{
    bst::Bst, btree::BTree, llrb::Llrb, red_black_standard::RbTree, treap::Treap,
};
use rand::seq::SliceRandom;
use rand::{rngs::StdRng, SeedableRng};

/// A fixed, key-derived priority, so benchmarks that need a *reproducible* treap shape get one.
pub fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// `0..n` shuffled with the given seed, so every run of one group sees the same keys. Groups pass
/// different seeds, so compare a group with itself across runs, not key-for-key with another.
fn shuffled_keys(n: usize, seed: u64) -> Vec<i64> {
    let mut keys: Vec<i64> = (0..n as i64).collect();
    let mut rng = StdRng::seed_from_u64(seed);
    keys.shuffle(&mut rng);
    keys
}

/// The treap the lookup and delete benchmarks start from: every key at a priority derived from
/// the key itself, so the same keys build the same tree on every run.
pub fn seeded_treap(keys: &[i64]) -> Treap<i64> {
    let mut t = Treap::new();
    for &k in keys {
        t.insert(k, splitmix64(k as u64));
    }
    t
}

/// The keys `sequential_search`'s benchmarks use: `0..n` shuffled with seed 1.
pub fn sequential_search_keys(n: usize) -> Vec<i64> {
    shuffled_keys(n, 1)
}

/// The keys `lsm`'s benchmarks use: `0..n` shuffled with seed 7.
pub fn lsm_keys(n: usize) -> Vec<i64> {
    shuffled_keys(n, 7)
}

/// What a benchmark asks of whatever times it. See the module doc for what each shape pins.
pub trait Timer {
    /// Time `op` building a structure from `keys`; the structure is dropped untimed.
    fn built<S: 'static>(&mut self, id: &str, keys: &[i64], op: impl Fn(&[i64]) -> S);
    /// Time `op` reading `built`, which the caller keeps.
    fn borrowed<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S));
    /// Time `op` changing a fresh copy of `built`, which the timer drops untimed.
    fn mutated<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S));
    /// [`Timer::borrowed`] for a read that allocates its cursors, such as a merging scan.
    fn scanned<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S));
    /// [`Timer::mutated`] for a change that allocates, such as a flush that merges runs.
    fn rebuilt<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S));
}

/// One lookup of the middle key, and deleting every key from a fresh copy.
fn reads_and_deletes<S: Clone + 'static>(
    timer: &mut impl Timer,
    lookup_id: &str,
    built: &S,
    keys: &[i64],
    lookup: impl Fn(&S, &i64) -> bool,
    delete: impl Fn(&mut S, &i64) -> bool,
) {
    let target = keys[keys.len() / 2];
    timer.borrowed(lookup_id, built, |t| {
        black_box(lookup(t, black_box(&target)));
    });
    timer.mutated("delete_all", built, |t| {
        for k in keys {
            black_box(delete(t, black_box(k)));
        }
    });
}

/// Insert every key into an empty structure, in order: the build benchmark of every tree group.
fn insert_all<S>(keys: &[i64], mut s: S, insert: impl Fn(&mut S, i64) -> bool) -> S {
    for &k in keys {
        black_box(insert(&mut s, black_box(k)));
    }
    s
}

/// `bst`: seed 2.
pub fn bst_group(timer: &mut impl Timer, n: usize) {
    let keys = shuffled_keys(n, 2);
    timer.built("insert", &keys, |keys| {
        insert_all(keys, Bst::new(), Bst::insert)
    });
    let built: Bst<i64> = keys.iter().copied().collect();
    reads_and_deletes(
        timer,
        "contains_hit",
        &built,
        &keys,
        Bst::contains,
        Bst::delete,
    );
}

/// `baseline_std_btreeset`: `std::collections::BTreeSet` over the `llrb` group's keys, seed 3.
pub fn baseline_group(timer: &mut impl Timer, n: usize) {
    let keys = shuffled_keys(n, 3);
    timer.built("insert", &keys, |keys| {
        insert_all(keys, BTreeSet::new(), BTreeSet::insert)
    });
    let built: BTreeSet<i64> = keys.iter().copied().collect();
    reads_and_deletes(
        timer,
        "contains_hit",
        &built,
        &keys,
        BTreeSet::contains,
        BTreeSet::remove,
    );
}

/// `llrb`: seed 3.
pub fn llrb_group(timer: &mut impl Timer, n: usize) {
    let keys = shuffled_keys(n, 3);
    timer.built("insert", &keys, |keys| {
        insert_all(keys, Llrb::new(), Llrb::insert)
    });
    let built: Llrb<i64> = keys.iter().copied().collect();
    reads_and_deletes(
        timer,
        "contains_hit",
        &built,
        &keys,
        Llrb::contains,
        Llrb::delete,
    );
}

/// `red_black_standard`: seed 4.
pub fn red_black_group(timer: &mut impl Timer, n: usize) {
    let keys = shuffled_keys(n, 4);
    timer.built("insert", &keys, |keys| {
        insert_all(keys, RbTree::new(), RbTree::insert)
    });
    let built: RbTree<i64> = keys.iter().copied().collect();
    reads_and_deletes(
        timer,
        "contains_hit",
        &built,
        &keys,
        RbTree::contains,
        RbTree::delete,
    );
}

/// `treap`: seed 5. The build benchmark draws its priorities with `insert_random`, the operation a
/// real caller reaches for; the lookup and the deletes run on [`seeded_treap`], never on a random
/// tree -- see the module doc.
pub fn treap_group(timer: &mut impl Timer, n: usize) {
    let keys = shuffled_keys(n, 5);
    timer.built("insert_random", &keys, |keys| {
        insert_all(keys, Treap::new(), Treap::insert_random)
    });
    let built = seeded_treap(&keys);
    reads_and_deletes(
        timer,
        "contains_hit",
        &built,
        &keys,
        Treap::contains,
        Treap::delete,
    );
}

/// `btree`: seed 6, at minimum degree `t`.
pub fn btree_group(timer: &mut impl Timer, n: usize, t: usize) {
    let keys = shuffled_keys(n, 6);
    timer.built("insert", &keys, |keys| {
        insert_all(keys, BTree::new(t), BTree::insert)
    });
    let mut built = BTree::new(t);
    built.extend(keys.iter().copied());
    reads_and_deletes(
        timer,
        "search_hit",
        &built,
        &keys,
        BTree::search,
        BTree::delete,
    );
}

/// The memtable capacity of the LSM benchmarks: small enough that every size they run, 100
/// included, has flushed into levels, so a lookup the memtable cannot answer reaches the runs.
pub const LSM_MEMTABLE: usize = 64;

/// The empty store every LSM benchmark starts from: [`LSM_MEMTABLE`] entries a flush, and the
/// default level ratio and level-0 run count.
pub fn lsm_store() -> Lsm<i64, i64> {
    Lsm::with_shape(LSM_MEMTABLE, DEFAULT_LEVEL_RATIO, DEFAULT_LEVEL0_RUNS)
}

/// The store `keys` leave, written in order and left alone: the state a caller finds it in, the
/// memtable holding what the last flush did not take and the levels as the cascade left them.
pub fn lsm_written(keys: &[i64]) -> Lsm<i64, i64> {
    let mut s = lsm_store();
    for &k in keys {
        s.write(black_box(k), k);
    }
    s
}

/// [`lsm_written`], topped up with fresh keys `n, n + 1, …` until level 0 holds one run short of a
/// merge and the memtable one entry short of full; and the next fresh key. Writing that key fills
/// the memtable, whose flush brings level 0 to its limit and merges it into level 1, cascading on
/// wherever that puts a level over its budget.
pub fn lsm_one_write_from_a_merge(keys: &[i64]) -> (Lsm<i64, i64>, i64) {
    let mut s = lsm_written(keys);
    let mut next = keys.len() as i64;
    while !(s.levels().first().map_or(0, Vec::len) == DEFAULT_LEVEL0_RUNS - 1
        && s.memtable_len() == LSM_MEMTABLE - 1)
    {
        s.write(next, next);
        next += 1;
    }
    (s, next)
}

/// `lsm`: seed 7. `write` builds from empty and should come out flat per element as `n` grows,
/// `O(log c)` in the memtable's fixed capacity plus the flushes amortised, not `O(log n)`.
/// `get_hit_deepest` looks up the first key written, which sits in the deepest level, so it costs
/// a binary search per run above it; `get_miss` touches every run; `iter` is a merge over one
/// cursor per run plus the memtable. `flush_and_cascade` times the one write that fills the
/// memtable and so merges level 0 into level 1, and on down where a level overflows.
pub fn lsm_group(timer: &mut impl Timer, n: usize) {
    let keys = lsm_keys(n);
    timer.built("write", &keys, lsm_written);
    let built = lsm_written(&keys);
    let deepest = keys[0];
    timer.borrowed("get_hit_deepest", &built, |s| {
        black_box(s.get(black_box(&deepest)));
    });
    timer.borrowed("get_miss", &built, |s| {
        black_box(s.get(black_box(&-1)));
    });
    timer.scanned("iter", &built, |s| {
        black_box(s.iter().count());
    });
    let (full, next) = lsm_one_write_from_a_merge(&keys);
    timer.rebuilt("flush_and_cascade", &full, |s| {
        s.write(black_box(next), next);
    });
}
