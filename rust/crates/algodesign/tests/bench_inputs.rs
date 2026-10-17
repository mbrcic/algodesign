// SPDX-License-Identifier: Apache-2.0
//! What the benchmarks measure stays fixed from run to run: CI compiles the benchmarks and never
//! runs them, so this is the only check on their inputs. See `benches/inputs/mod.rs` for the two
//! times it was wrong, and for what this pins and what is left to convention.
//!
//! `harness = false` (see `Cargo.toml`): the counting allocator is global to the process, so this
//! runs as a plain `main` on one thread, and a failed check panics, which fails `cargo test`.

#[path = "../benches/inputs/mod.rs"]
mod inputs;

use std::alloc::System;
use std::any::Any;
use std::collections::BTreeSet;

use algodesign::searching::lsm::{Lsm, DEFAULT_LEVEL0_RUNS};
use algodesign::searching::{
    bst::Bst, btree::BTree, llrb::Llrb, red_black_standard::RbTree, treap::Treap,
};
use inputs::{
    baseline_group, bst_group, btree_group, llrb_group, lsm_group, lsm_keys, lsm_written,
    red_black_group, seeded_treap, sequential_search_keys, splitmix64, treap_group, Timer,
    LSM_MEMTABLE,
};
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

/// Heap blocks `f` asked for, fresh or regrown.
fn allocations(f: impl FnOnce()) -> usize {
    let region = Region::new(GLOBAL);
    f();
    let s = region.change();
    s.allocations + s.reallocations
}

/// A `Timer` that times nothing. It keeps the keys each build was given and what it built, a copy
/// of the structure each read and delete was handed, and what a delete left of its copy; and it
/// runs each read and delete once under the counting allocator.
#[derive(Default)]
struct Recorder {
    ids: Vec<String>,
    keys: Vec<Vec<i64>>,
    built: Vec<Box<dyn Any>>,
    handed: Vec<Box<dyn Any>>,
    left: Vec<Box<dyn Any>>,
}

impl Timer for Recorder {
    fn built<S: 'static>(&mut self, id: &str, keys: &[i64], op: impl Fn(&[i64]) -> S) {
        self.ids.push(id.to_owned());
        self.keys.push(keys.to_vec());
        self.built.push(Box::new(op(keys)));
    }

    fn borrowed<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S)) {
        self.ids.push(id.to_owned());
        self.handed.push(Box::new(built.clone()));
        let made = allocations(|| op(built));
        assert_eq!(made, 0, "{id}: a timed read allocated {made} blocks");
    }

    fn mutated<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S)) {
        self.ids.push(id.to_owned());
        self.handed.push(Box::new(built.clone()));
        let mut copy = built.clone();
        let made = allocations(|| op(&mut copy));
        assert_eq!(made, 0, "{id}: a timed delete allocated {made} blocks");
        self.left.push(Box::new(copy));
    }

    fn scanned<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&S)) {
        self.ids.push(id.to_owned());
        self.handed.push(Box::new(built.clone()));
        op(built);
    }

    fn rebuilt<S: Clone + 'static>(&mut self, id: &str, built: &S, op: impl Fn(&mut S)) {
        self.ids.push(id.to_owned());
        self.handed.push(Box::new(built.clone()));
        let mut copy = built.clone();
        op(&mut copy);
        self.left.push(Box::new(copy));
    }
}

/// Run one group twice and check it: the same keys both times, a permutation of `0..n`; the build
/// benchmark builds `expected(keys)` (skipped for the treap's `insert_random`); the read and the
/// delete are both handed `expected(keys)`; and the delete leaves its copy `empty`.
fn check<S: PartialEq + 'static>(
    ids: [&str; 3],
    n: usize,
    run: impl Fn(&mut Recorder),
    expected: impl Fn(&[i64]) -> S,
    build_is_deterministic: bool,
    empty: &S,
) {
    let (mut first, mut second) = (Recorder::default(), Recorder::default());
    run(&mut first);
    run(&mut second);
    assert_eq!(first.ids, ids);
    let [keys] = &first.keys[..] else {
        panic!("one build benchmark per group")
    };
    assert_eq!(
        &second.keys, &first.keys,
        "{}: keys differ between runs",
        ids[0]
    );
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    assert!(sorted.into_iter().eq(0..n as i64));
    let want = expected(keys);
    if build_is_deterministic {
        assert!(
            first.built[0].downcast_ref::<S>() == Some(&want),
            "{}",
            ids[0]
        );
    }
    for (id, handed) in ids[1..].iter().zip(&first.handed) {
        assert!(
            handed.downcast_ref::<S>() == Some(&want),
            "{id} was handed another structure"
        );
    }
    let [left] = &first.left[..] else {
        panic!("one delete benchmark per group")
    };
    assert!(left.downcast_ref::<S>() == Some(empty));
}

/// Every tree group, at two sizes. The treap is where "which tree" is a claim about randomness:
/// built with `insert_random`, a second build of the same keys differs in shape with overwhelming
/// probability.
fn every_group_times_the_tree_its_fixture_builds() {
    let reads = ["insert", "contains_hit", "delete_all"];
    for n in [100, 1_000] {
        check(
            reads,
            n,
            |r| bst_group(r, n),
            |k| k.iter().copied().collect::<Bst<_>>(),
            true,
            &Bst::new(),
        );
        check(
            reads,
            n,
            |r| baseline_group(r, n),
            |k| k.iter().copied().collect::<BTreeSet<_>>(),
            true,
            &BTreeSet::new(),
        );
        check(
            reads,
            n,
            |r| llrb_group(r, n),
            |k| k.iter().copied().collect::<Llrb<_>>(),
            true,
            &Llrb::new(),
        );
        check(
            reads,
            n,
            |r| red_black_group(r, n),
            |k| k.iter().copied().collect::<RbTree<_>>(),
            true,
            &RbTree::new(),
        );
        // By hand, not through `seeded_treap`: the priorities are the key-derived ones.
        let by_hand = |keys: &[i64]| {
            let mut t = Treap::new();
            for &k in keys {
                t.insert(k, splitmix64(k as u64));
            }
            assert!(t == seeded_treap(keys));
            t
        };
        check(
            ["insert_random", "contains_hit", "delete_all"],
            n,
            |r| treap_group(r, n),
            by_hand,
            false,
            &Treap::new(),
        );
        check(
            ["insert", "search_hit", "delete_all"],
            n,
            |r| btree_group(r, n, 8),
            |k| {
                let mut t = BTree::new(8);
                t.extend(k.iter().copied());
                t
            },
            true,
            &BTree::new(8),
        );
    }
}

/// Runs per level, level 0 first.
fn runs(s: &Lsm<i64, i64>) -> Vec<usize> {
    s.levels().iter().map(Vec::len).collect()
}

/// The LSM group, at every size the benchmark runs: the keys are fixed, the reads are handed the
/// store `write` builds, that store has levels with the first key written in the deepest one, and
/// `flush_and_cascade` starts one write short of a level-0 merge and ends with that merge done.
fn the_lsm_group_times_the_layout_its_comments_claim() {
    for n in [100, 1_000, 10_000] {
        let (mut first, mut second) = (Recorder::default(), Recorder::default());
        lsm_group(&mut first, n);
        lsm_group(&mut second, n);
        assert_eq!(
            first.ids,
            [
                "write",
                "get_hit_deepest",
                "get_miss",
                "iter",
                "flush_and_cascade"
            ]
        );
        assert_eq!(first.keys, second.keys, "lsm: keys differ between runs");
        let keys = &first.keys[0];
        assert_eq!(keys, &lsm_keys(n));

        let built = first.built[0]
            .downcast_ref::<Lsm<i64, i64>>()
            .expect("an Lsm");
        let want = lsm_written(keys);
        assert!(
            built.levels() == want.levels() && built.memtable_len() == want.memtable_len(),
            "lsm/write at {n} built another layout"
        );
        for (id, handed) in first.ids[1..4].iter().zip(&first.handed) {
            let handed = handed.downcast_ref::<Lsm<i64, i64>>().expect("an Lsm");
            assert!(
                handed.levels() == want.levels() && handed.memtable_len() == want.memtable_len(),
                "lsm/{id} at {n} was handed another store"
            );
        }
        assert!(
            !want.levels().is_empty(),
            "lsm at {n}: no level, so no run is read"
        );
        let deepest = want
            .levels()
            .iter()
            .rev()
            .find(|l| !l.is_empty())
            .expect("a level");
        assert!(
            deepest
                .iter()
                .any(|run| run.iter().any(|(k, _)| *k == keys[0])),
            "lsm at {n}: the first key written is not in the deepest level"
        );

        let full = first.handed[3]
            .downcast_ref::<Lsm<i64, i64>>()
            .expect("an Lsm");
        assert_eq!(
            full.memtable_len(),
            LSM_MEMTABLE - 1,
            "lsm/flush_and_cascade at {n}"
        );
        assert_eq!(
            full.levels()[0].len(),
            DEFAULT_LEVEL0_RUNS - 1,
            "lsm/flush_and_cascade at {n}"
        );
        let after = first.left[0]
            .downcast_ref::<Lsm<i64, i64>>()
            .expect("an Lsm");
        assert_eq!(
            after.memtable_len(),
            0,
            "lsm/flush_and_cascade at {n}: no flush"
        );
        assert!(
            after.levels()[0].is_empty() && runs(after)[1..].iter().all(|&r| r <= 1),
            "lsm/flush_and_cascade at {n}: level 0 was not merged down, runs {:?}",
            runs(after)
        );
        assert!(after.is_valid(), "lsm/flush_and_cascade at {n}");
    }
}

/// The sequential-search group, which does not go through a `Timer`, draws its keys here too;
/// both it and the LSM group's keys are fixed, a permutation of `0..n`, and not each other's.
fn the_other_groups_keys_are_fixed() {
    for keys in [sequential_search_keys, lsm_keys] {
        let a = keys(1_000);
        assert_eq!(a, keys(1_000));
        let mut sorted = a.clone();
        sorted.sort_unstable();
        assert!(sorted.into_iter().eq(0..1_000));
    }
    assert_ne!(sequential_search_keys(1_000), lsm_keys(1_000));
}

fn main() {
    every_group_times_the_tree_its_fixture_builds();
    the_lsm_group_times_the_layout_its_comments_claim();
    the_other_groups_keys_are_fixed();
}
