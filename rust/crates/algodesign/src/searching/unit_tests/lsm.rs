// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;
use std::collections::BTreeMap;

// ---------------------------------------------------------------------------------------
// Unit tests: edge cases per operation.
// ---------------------------------------------------------------------------------------

thread_local! {
    /// Key comparisons made on this thread by `Counted`, of either kind.
    static COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A key that counts every comparison made on it, `==` as well as `cmp`, so a linear scan
/// written with `find(|(k, _)| k == key)` is counted as surely as a binary search.
#[derive(Debug)]
struct Counted(u32);

impl PartialEq for Counted {
    fn eq(&self, other: &Self) -> bool {
        COMPARISONS.with(|c| c.set(c.get() + 1));
        self.0 == other.0
    }
}
impl Eq for Counted {}
impl PartialOrd for Counted {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Counted {
    fn cmp(&self, other: &Self) -> Ordering {
        COMPARISONS.with(|c| c.set(c.get() + 1));
        self.0.cmp(&other.0)
    }
}

/// `run_lookup` settles every key of a 4096-entry run, present or absent, in at most
/// `2 * lg(n + 1)` comparisons; a linear scan needs up to 4096.
#[test]
fn run_lookup_makes_logarithmic_comparisons() {
    let n: u32 = 4096;
    let run: Run<Counted, u32> = (0..n).map(|i| (Counted(2 * i + 1), Some(i))).collect();
    let bound = 2 * (usize::BITS - (n as usize).leading_zeros()) as usize;
    for probe in 0..=2 * n + 1 {
        COMPARISONS.with(|c| c.set(0));
        let got = run_lookup(&Counted(probe), &run);
        let made = COMPARISONS.with(std::cell::Cell::get);
        let expected = (probe % 2 == 1 && probe / 2 < n).then_some(probe / 2);
        assert_eq!(
            got.map(|v| v.copied()),
            expected.map(Some),
            "run_lookup({probe})"
        );
        assert!(
            made <= bound,
            "run_lookup({probe}) made {made} comparisons, bound {bound}"
        );
    }
}

/// The same bound through `get`: on a fully compacted store, one run of 4096, at most 26
/// comparisons.
#[test]
fn get_makes_logarithmic_comparisons_per_run() {
    fn lg_bound(len: usize) -> usize {
        2 * (usize::BITS - len.leading_zeros()) as usize
    }
    fn check(s: &Lsm<Counted, u32>, n: u32) {
        let bound: usize = s.runs().map(|r| lg_bound(r.len())).sum();
        for probe in 0..=2 * n + 1 {
            COMPARISONS.with(|c| c.set(0));
            let got = s.get(&Counted(probe)).copied();
            let made = COMPARISONS.with(std::cell::Cell::get);
            let expected = (probe % 2 == 1 && probe / 2 < n).then_some(probe / 2);
            assert_eq!(got, expected, "get({probe})");
            assert!(
                made <= bound,
                "get({probe}) made {made} comparisons, bound {bound}"
            );
        }
    }
    let n: u32 = 4096;
    let mut s: Lsm<Counted, u32> = Lsm::with_shape(64, 4, 4);
    // 37 is odd, so `i * 37 mod 4096` visits every key once, out of order.
    for i in 0..n {
        let k = (i * 37) % n;
        s.write(Counted(2 * k + 1), k);
    }
    s.flush(); // empty the memtable, so every probe reaches the runs
    assert!(
        s.runs().count() > 1,
        "a layered store: several runs to search"
    );
    check(&s, n);
    s.compact_fully();
    assert_eq!(s.runs().count(), 1);
    check(&s, n);
}

/// `Default` is `new`: a store built by `Lsm::default()` takes writes.
#[test]
fn default_is_new_and_takes_writes() {
    let mut s: Lsm<i32, i32> = Lsm::default();
    for k in 0..5000 {
        s.write(k, k);
    }
    assert_eq!(s.get(&4999), Some(&4999));
    assert!(s.is_valid());
}

/// `==` compares live contents, whatever the layout; one differing value is unequal.
#[test]
fn eq_compares_live_contents_not_layout() {
    let mut a: Lsm<i32, i32> = Lsm::with_shape(2, 2, 2);
    let mut b: Lsm<i32, i32> = Lsm::new();
    for k in 0..40 {
        a.write(k, k * 10);
        b.write(k, k * 10);
    }
    a.write(99, 1);
    a.delete(99); // a tombstone in `a` only; `b` never saw the key
    assert!(a.level_count() > 1 && b.level_count() == 0); // different layouts
    assert_eq!(a, b);
    a.flush();
    assert_eq!(a, b);
    b.compact_fully();
    assert_eq!(a, b);

    b.write(7, 71);
    assert_ne!(a, b); // one newer value differs
    b.write(7, 70);
    assert_eq!(a, b); // and the newest write is what counts
    b.delete(0);
    assert_ne!(a, b); // a key live in one only

    assert_eq!(Lsm::<i32, i32>::new(), Lsm::with_shape(1, 2, 1));
}

#[test]
fn empty_store() {
    let s: Lsm<i32, i32> = Lsm::new();
    assert_eq!(s.get(&0), None);
    assert!(!s.contains(&0));
    assert_eq!(s.level_count(), 0);
    assert_eq!(s.memtable_len(), 0);
    assert!(s.is_valid());
    let mut s = s;
    s.flush(); // no-op, must not panic
    assert_eq!(s.level_count(), 0);
}

#[test]
fn single_write_stays_in_the_memtable() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.write(1, 100);
    assert_eq!(s.get(&1), Some(&100));
    assert!(s.contains(&1));
    assert_eq!(s.get(&2), None);
    // A write does not touch the levels: that is the point of buffering it.
    assert_eq!(s.memtable_len(), 1);
    assert_eq!(s.level_count(), 0);
}

#[test]
fn write_then_delete_leaves_a_tombstone_not_absence() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.write(1, 100);
    s.delete(1);
    assert_eq!(s.get(&1), None);
    assert!(!s.contains(&1));
    // Still a recorded deletion, until a merge reaches the bottom.
    assert_eq!(s.lookup(&1), Some(None));
}

#[test]
fn a_tombstone_with_nothing_beneath_it_is_collected() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.write(1, 100);
    s.delete(1);
    s.compact_fully();
    // The deepest level has nothing older to shadow, so the tombstone has no work left.
    assert_eq!(s.lookup(&1), None);
    assert!(s.is_valid());
    assert_eq!(s.len(), 0);
}

#[test]
fn rewrite_coalesces_in_the_memtable() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.write(1, 100);
    s.write(1, 200);
    assert_eq!(s.get(&1), Some(&200));
    // One entry, not two: the second write overwrote the first before either reached a level.
    assert_eq!(s.memtable_len(), 1);
}

#[test]
fn flush_on_an_empty_memtable_is_a_noop() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.flush();
    assert_eq!(s.level_count(), 0);
    s.write(1, 1);
    s.flush();
    assert_eq!(s.level_count(), 1);
    assert_eq!(s.memtable_len(), 0);
    s.flush();
    assert_eq!(s.level_count(), 1);
    assert_eq!(s.get(&1), Some(&1));
}

/// A merge that cancels out (a value and its tombstone, nothing beneath) leaves level 1 an
/// empty slot, not a slot holding an empty run. The next deletion is filed in level 0 as it is,
/// and the merge that carries it into level 1, with nothing below, drops it.
#[test]
fn a_merge_that_cancels_out_leaves_its_level_empty() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(1, 2, 2);
    s.write(1, 1);
    s.delete(1);
    let empty: &[Vec<Run<i32, i32>>] = &[vec![], vec![]];
    assert_eq!(s.levels(), empty);
    assert!(s.is_valid());
    s.delete(2);
    let filed: &[Vec<Run<i32, i32>>] = &[vec![vec![(2, None)]], vec![]];
    assert_eq!(s.levels(), filed);
    assert_eq!(s.lookup(&2), Some(None));
    assert_eq!(s.get(&1), None);
    assert_eq!(s.len(), 0);
    assert!(s.is_valid());
    // And a store that goes on from there builds its levels as before.
    s.write(3, 3);
    let merged: &[Vec<Run<i32, i32>>] = &[vec![], vec![vec![(3, Some(3))]]];
    assert_eq!(s.levels(), merged);
    assert_eq!(s.lookup(&2), None);
    s.write(4, 4);
    assert_eq!(s.get(&3), Some(&3));
    assert!(s.is_valid());
}

/// A flush drops no deletion, even with nothing older to shadow: the tombstone waits in
/// level 0 for a merge with nothing below.
#[test]
fn a_flush_into_an_empty_store_keeps_its_tombstones() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    s.delete(1);
    s.write(2, 2);
    s.flush();
    let filed: &[Vec<Run<i32, i32>>] = &[vec![vec![(1, None), (2, Some(2))]]];
    assert_eq!(s.levels(), filed);
    assert_eq!(s.lookup(&1), Some(None));
    assert!(s.is_valid());
}

/// Level 0 is merged down by the flush that brings it to `level0_runs` runs: three flushes
/// wait side by side, and the fourth merges all four into level 1.
#[test]
fn level_0_merges_when_it_reaches_its_run_count() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(1, DEFAULT_LEVEL_RATIO, DEFAULT_LEVEL0_RUNS);
    for k in 1..=3 {
        s.write(k, k);
    }
    assert_eq!(s.levels().len(), 1);
    assert_eq!(s.levels()[0].len(), 3);
    s.write(4, 4);
    let merged: &[Vec<Run<i32, i32>>] = &[
        vec![],
        vec![vec![(1, Some(1)), (2, Some(2)), (3, Some(3)), (4, Some(4))]],
    ];
    assert_eq!(s.levels(), merged);
    assert!(s.is_valid());
}

/// `is_valid` refuses an empty run.
#[test]
fn an_empty_run_is_not_valid() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(1, 2, 1);
    s.levels = vec![vec![], vec![Vec::new()]];
    assert!(!s.is_valid());
    s.levels = vec![vec![], vec![]];
    assert!(s.is_valid());
}

/// "Nothing below" means every slot below, not the next one: with level 2 empty and the value
/// in level 3, a tombstone merged into level 1 must survive.
#[test]
fn a_tombstone_survives_above_an_empty_slot_with_an_older_value_below_it() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(1, 2, 2);
    s.levels = vec![vec![], vec![], vec![], vec![vec![(0, Some(7))]]];
    assert!(s.is_valid());
    s.delete(0); // filed in level 0, above the value
    s.write(5, 5); // level 0 reaches two runs: both merge into level 1
    assert_eq!(s.levels()[1], vec![vec![(0, None), (5, Some(5))]]);
    assert_eq!(s.get(&0), None);
    assert_eq!(s.lookup(&0), Some(None));
    assert!(s.is_valid());
}

/// A tombstone merged into level 1 above a slot emptied by a cancelling merge has nothing
/// beneath it, and is dropped as it would be at the bottom.
#[test]
fn a_tombstone_above_an_emptied_level_is_dropped() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(1, 2, 2);
    for k in 1..=4 {
        s.write(k, k);
    }
    assert_eq!(s.levels().len(), 3);
    assert!(s.levels()[2].first().is_some_and(|r| r.len() == 4));
    for k in 1..=4 {
        s.delete(k);
    }
    assert!(s.levels().iter().all(Vec::is_empty));
    s.write(5, 5);
    s.delete(5);
    assert!(s.levels().iter().all(Vec::is_empty), "{:?}", s.levels());
    assert_eq!(s.lookup(&5), None);
    assert!(s.is_valid());
}

/// The Search chapter's trace: Page 2 filed in front of Page 1 without touching it, the four
/// questions answered as the chapter's table answers them, and compaction.
#[test]
fn the_chapters_two_pages_are_two_sealed_runs() {
    let mut s: Lsm<&str, &str> = Lsm::with_shape(3, DEFAULT_LEVEL_RATIO, DEFAULT_LEVEL0_RUNS);
    s.write("charger", "desk drawer");
    s.write("passport", "top shelf");
    s.write("scissors", "kitchen drawer"); // full: one trip, Page 1
    s.write("charger", "bedside table");
    s.delete("scissors");
    s.write("umbrella", "hallway hook"); // full: one trip, Page 2
    assert_eq!(s.memtable_len(), 0);
    assert_eq!(s.level_count(), 1);
    let page_1: Run<&str, &str> = vec![
        ("charger", Some("desk drawer")),
        ("passport", Some("top shelf")),
        ("scissors", Some("kitchen drawer")),
    ];
    let page_2: Run<&str, &str> = vec![
        ("charger", Some("bedside table")),
        ("scissors", None),
        ("umbrella", Some("hallway hook")),
    ];
    assert_eq!(s.levels()[0], vec![page_2, page_1]); // newest first
    assert_eq!(s.lookup(&"charger"), Some(Some(&"bedside table")));
    assert_eq!(s.lookup(&"scissors"), Some(None));
    assert_eq!(s.lookup(&"passport"), Some(Some(&"top shelf")));
    assert_eq!(s.lookup(&"bicycle pump"), None);
    assert!(s.is_valid());

    s.compact_fully();
    let merged: Run<&str, &str> = vec![
        ("charger", Some("bedside table")),
        ("passport", Some("top shelf")),
        ("umbrella", Some("hallway hook")),
    ];
    assert_eq!(s.levels(), &[vec![merged]]);
    assert_eq!(s.lookup(&"scissors"), None);
}

#[test]
fn a_full_memtable_flushes_itself() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(8, 10, 4);
    for k in 0..8 {
        s.write(k, k * 10);
    }
    // The eighth write filled it, so it went down on its own.
    assert_eq!(s.memtable_len(), 0);
    assert_eq!(s.level_count(), 1);
    assert_eq!(
        s.levels()[0].len(),
        1,
        "one flush, one sealed run in level 0"
    );
    assert_eq!(s.levels()[0][0].len(), 8);
    for k in 0..8 {
        assert_eq!(s.get(&k), Some(&(k * 10)));
    }
    assert!(s.is_valid());
}

#[test]
fn a_level_over_budget_is_pushed_into_the_next() {
    // Capacity 4, ratio 2, level 0 merged at three runs: level 1 may hold 8 entries, level 2
    // sixteen.
    let mut s: Lsm<i32, i32> = Lsm::with_shape(4, 2, 3);
    for k in 0..40 {
        s.write(k, k);
    }
    s.flush();
    assert!(
        s.level_count() >= 2,
        "40 keys at this shape must reach a second level"
    );
    assert!(s.levels()[0].len() <= 2, "level 0 holds at most two runs");
    for (i, level) in s.levels().iter().enumerate().skip(1) {
        assert!(level.len() <= 1, "level {i} holds more than one run");
        if let Some(run) = level.first() {
            if i + 1 < s.level_count() {
                assert!(
                    run.len() <= 4 * 2usize.pow(i as u32),
                    "level {i} is over budget"
                );
            }
            assert!(
                run.windows(2).all(|w| w[0].0 < w[1].0),
                "level {i} is not sorted"
            );
        }
    }
    assert!(s.is_valid());
    for k in 0..40 {
        assert_eq!(s.get(&k), Some(&k));
    }
}

/// Only a merge with nothing below it may drop a tombstone: one merged into level 1 while the
/// value it deletes sits two levels further down must survive.
#[test]
fn a_tombstone_above_an_older_value_survives_a_merge_that_is_not_the_deepest() {
    fn level_holding(s: &Lsm<i32, i32>, key: i32) -> Option<(usize, Option<i32>)> {
        s.levels().iter().enumerate().find_map(|(i, level)| {
            level
                .iter()
                .find_map(|run| run.iter().find(|(k, _)| *k == key).map(|(_, v)| (i, *v)))
        })
    }
    // Level 0 merged at two runs, so the second flush merges four entries into level 1, exactly
    // its budget.
    let mut s: Lsm<i32, i32> = Lsm::with_shape(2, 2, 2);
    let mut filler = 1..1000;
    s.write(0, 7);
    // Bury the value at level 2 or deeper.
    while !level_holding(&s, 0).is_some_and(|(i, _)| i >= 2) {
        let f = filler
            .next()
            .expect("the value reaches level 2 within the filler");
        s.write(f, f);
    }
    s.delete(0);
    // Then write until the tombstone has been merged into level 1, and stop there.
    while !level_holding(&s, 0).is_some_and(|(i, _)| i == 1) {
        let f = filler
            .next()
            .expect("the tombstone reaches level 1 within the filler");
        s.write(f, f);
    }
    assert_eq!(
        level_holding(&s, 0),
        Some((1, None)),
        "a tombstone, in level 1"
    );
    let deeper = s.levels()[2..]
        .iter()
        .flatten()
        .flatten()
        .find(|(k, _)| *k == 0)
        .map(|(_, v)| *v);
    assert_eq!(deeper, Some(Some(7)), "the value it deletes, further down");
    assert_eq!(s.lookup(&0), Some(None));
    assert_eq!(s.get(&0), None);
    assert!(s.is_valid());
}

#[test]
fn compact_resolves_a_duplicate_key_in_favour_of_the_newer_entry() {
    let mut s: Lsm<i32, i32> = Lsm::with_shape(2, 2, 4);
    s.write(1, 100);
    s.write(9, 9); // fills the memtable, flushing both to level 0
    s.write(1, 200);
    s.compact_fully();
    assert_eq!(s.level_count(), 1);
    assert_eq!(s.get(&1), Some(&200));
}

#[test]
fn compact_fully_matches_direct_lookup() {
    let mut s: Lsm<i32, i32> = Lsm::new();
    for (k, v) in [(3, 30), (1, 10), (4, 40), (1, 11), (2, 20)] {
        s.write(k, v);
    }
    let before: Vec<Option<i32>> = (0..6).map(|k| s.get(&k).copied()).collect();
    s.compact_fully();
    assert_eq!(s.level_count(), 1);
    let after: Vec<Option<i32>> = (0..6).map(|k| s.get(&k).copied()).collect();
    assert_eq!(before, after);
    assert_eq!(
        before,
        vec![None, Some(11), Some(20), Some(30), Some(40), None]
    );
}

// ---------------------------------------------------------------------------------------
// Property tests: the empirical counterparts of what `LSM/` states or proves.
// ---------------------------------------------------------------------------------------

fn keys() -> impl Strategy<Value = i32> {
    -50..50
}
fn values() -> impl Strategy<Value = i32> {
    -1000..1000
}

#[derive(Debug, Clone)]
enum Op {
    Write(i32, i32),
    Delete(i32),
    Flush,
}

fn ops() -> impl Strategy<Value = Vec<Op>> {
    prop::collection::vec(
        prop_oneof![
            (keys(), values()).prop_map(|(k, v)| Op::Write(k, v)),
            keys().prop_map(Op::Delete),
            Just(Op::Flush),
        ],
        0..80,
    )
}

/// Replays `ops` against both the real `Lsm` and a plain `BTreeMap` (tombstones as key
/// absence).
fn apply(ops: &[Op]) -> (Lsm<i32, i32>, BTreeMap<i32, i32>) {
    apply_to(Lsm::new(), ops)
}

/// [`apply`], on a store of the caller's shape.
fn apply_to(mut store: Lsm<i32, i32>, ops: &[Op]) -> (Lsm<i32, i32>, BTreeMap<i32, i32>) {
    let mut reference = BTreeMap::new();
    for op in ops {
        match *op {
            Op::Write(k, v) => {
                store.write(k, v);
                reference.insert(k, v);
            }
            Op::Delete(k) => {
                store.delete(k);
                reference.remove(&k);
            }
            Op::Flush => store.flush(),
        }
    }
    (store, reference)
}

proptest! {
    /// `lookup_write_self`: writing `(key, value)` makes it the immediate answer.
    #[test]
    fn write_then_get_returns_the_value_written(key in keys(), value in values()) {
        let mut s = Lsm::new();
        s.write(key, value);
        prop_assert_eq!(s.get(&key), Some(&value));
    }

    /// `lookup_write_other`: writing `key` never changes what an *unrelated* key looks up to.
    #[test]
    fn write_does_not_change_lookup_of_a_different_key(
        key in keys(), value in values(), other in keys(),
    ) {
        let mut s: Lsm<i32, i32> = Lsm::new();
        let before = s.get(&other).copied();
        s.write(key, value);
        if key != other {
            prop_assert_eq!(s.get(&other).copied(), before);
        }
    }

    /// `runsSorted_write` and `Store.valid_of_reachable`, empirically: every store the API
    /// builds is valid.
    #[test]
    fn store_stays_valid_after_any_op_sequence(ops in ops()) {
        let (store, _) = apply(&ops);
        prop_assert!(store.is_valid());
    }

    /// The store agrees with a plain `BTreeMap` on every key after the whole sequence.
    #[test]
    fn get_matches_map_with_tombstone_reference(ops in ops()) {
        let (store, reference) = apply(&ops);
        for k in -50..50 {
            prop_assert_eq!(store.get(&k).copied(), reference.get(&k).copied());
            prop_assert_eq!(store.contains(&k), reference.contains_key(&k));
        }
    }

    /// The same agreement at shapes small enough to build several levels within 200
    /// operations.
    #[test]
    fn get_matches_map_at_shapes_that_build_several_levels(
        ops in prop::collection::vec(
            prop_oneof![
                (keys(), values()).prop_map(|(k, v)| Op::Write(k, v)),
                keys().prop_map(Op::Delete),
                Just(Op::Flush),
            ],
            0..200,
        ),
        shape in prop_oneof![Just((2, 2, 2)), Just((2, 2, 3)), Just((4, 2, 3))],
    ) {
        let (store, reference) = apply_to(Lsm::with_shape(shape.0, shape.1, shape.2), &ops);
        prop_assert!(store.is_valid());
        for k in -50..50 {
            prop_assert_eq!(store.get(&k).copied(), reference.get(&k).copied());
        }
    }

    /// `PreservesGet`, and `PreservesLookup` up to tombstone collection, across a `flush`
    /// after an arbitrary prefix, for every key in `ops` plus two that never appear.
    #[test]
    fn compact_preserves_every_answer_a_client_can_get(ops in ops()) {
        let (before, _) = apply(&ops);
        let mut after = before.clone();
        after.flush();

        let mut keys: Vec<i32> = ops
            .iter()
            .filter_map(|op| match op {
                Op::Write(k, _) | Op::Delete(k) => Some(*k),
                Op::Flush => None,
            })
            .collect();
        keys.push(-999);
        keys.push(999);
        for k in keys {
            // `get` is exactly preserved.
            prop_assert_eq!(before.get(&k).copied(), after.get(&k).copied());
            // `lookup` is preserved up to tombstone collection: "written, then deleted" may
            // become "never written", and nothing else changes.
            match (before.lookup(&k), after.lookup(&k)) {
                (Some(None), None) => {}
                (b, a) => prop_assert_eq!(b, a),
            }
        }
    }
}

// The merging iterator against a `BTreeMap` model: the same live view.
proptest! {
    #[test]
    fn iter_agrees_with_a_map_model(
        ops in prop::collection::vec((0..12i32, prop::option::of(0..100i32)), 0..60),
        compactions in 0..6usize,
    ) {
        use std::collections::BTreeMap;
        let mut store: Lsm<i32, i32> = Lsm::new();
        let mut model: BTreeMap<i32, i32> = BTreeMap::new();
        for (k, v) in &ops {
            match v {
                Some(v) => { store.write(*k, *v); model.insert(*k, *v); }
                None => { store.delete(*k); model.remove(k); }
            }
        }
        for _ in 0..compactions {
            store.flush();
        }
        let got: Vec<(i32, i32)> = store.iter().map(|(k, v)| (*k, *v)).collect();
        let want: Vec<(i32, i32)> = model.iter().map(|(k, v)| (*k, *v)).collect();
        prop_assert_eq!(got, want);
        prop_assert_eq!(store.len(), model.len());
        prop_assert_eq!(store.is_empty(), model.is_empty());
    }

    /// Compaction does not change what iteration sees.
    #[test]
    fn compaction_preserves_the_live_view(
        ops in prop::collection::vec((0..12i32, prop::option::of(0..100i32)), 0..60),
    ) {
        let mut store: Lsm<i32, i32> = Lsm::new();
        for (k, v) in &ops {
            match v {
                Some(v) => store.write(*k, *v),
                None => store.delete(*k),
            }
        }
        let before: Vec<(i32, i32)> = store.iter().map(|(k, v)| (*k, *v)).collect();
        store.compact_fully();
        let after: Vec<(i32, i32)> = store.iter().map(|(k, v)| (*k, *v)).collect();
        prop_assert_eq!(before, after);
        prop_assert!(store.is_valid());
    }
}

// ---------------------------------------------------------------------------------------
// `check_valid`: one store per piece, breaking that piece alone.
// ---------------------------------------------------------------------------------------

/// A store of shape capacity 2, ratio 2, two runs on level 0, with these levels.
fn store(levels: Vec<Vec<Run<u32, u32>>>) -> Lsm<u32, u32> {
    let mut s = Lsm::with_shape(2, 2, 2);
    s.levels = levels;
    s
}

#[test]
fn check_valid_names_each_piece() {
    let live = |ks: &[u32]| ks.iter().map(|&k| (k, Some(k))).collect::<Run<u32, u32>>();
    assert_eq!(
        store(vec![vec![live(&[1])], vec![live(&[2, 3])]]).check_valid(),
        Ok(())
    );
    let cases = [
        (vec![vec![live(&[2, 1])]], "invariant 1 (runs_sorted)"),
        (
            vec![vec![live(&[1]), live(&[2]), live(&[3])]],
            "invariant 2 (few_batches)",
        ),
        // Level 1, not the deepest, over its budget of 2 · 2 = 4.
        (
            vec![vec![], vec![live(&[1, 2, 3, 4, 5])], vec![live(&[6])]],
            "invariant 2 (few_batches)",
        ),
        (vec![vec![Vec::new()]], "not in the box (runs_non_empty)"),
        (
            vec![vec![], vec![vec![(1, None)]]],
            "not in the box (oldest_run_clean)",
        ),
    ];
    for (levels, label) in cases {
        let s = store(levels);
        assert_eq!(s.check_valid(), Err(label));
        assert!(!s.is_valid());
    }
}

/// `ShapeUsable` breaks alone on a valid store whose shape `with_shape` would refuse: one store
/// per condition, each the empty store.
#[test]
fn check_valid_names_an_unusable_shape() {
    assert!(Lsm::<u32, u32>::new().is_shape_usable());
    for (capacity, ratio, level0_runs) in [(0, 2, 2), (2, 1, 2), (2, 2, 0)] {
        let mut s = store(Vec::new());
        s.memtable_capacity = capacity;
        s.level_ratio = ratio;
        s.level0_runs = level0_runs;
        assert!(!s.is_shape_usable());
        assert!(s.is_runs_sorted() && s.is_few_batches() && s.is_runs_non_empty());
        assert!(s.is_oldest_run_clean());
        assert_eq!(s.check_valid(), Err("invariant 2 (shape_usable)"));
    }
}

/// `MemtableWithinCapacity` breaks alone on the empty store once its memtable holds one entry
/// more than its capacity; at the capacity it holds. A write never leaves it so: a write that
/// fills the memtable flushes it.
#[test]
fn check_valid_names_a_memtable_over_capacity() {
    let mut s = store(Vec::new());
    s.memtable.extend([(1, Some(1)), (2, Some(2))]);
    assert!(s.is_memtable_within_capacity() && s.is_valid());
    s.memtable.insert(3, Some(3));
    assert!(!s.is_memtable_within_capacity());
    assert!(s.is_runs_sorted() && s.is_few_batches() && s.is_runs_non_empty());
    assert!(s.is_oldest_run_clean() && s.is_shape_usable());
    assert_eq!(
        s.check_valid(),
        Err("not in the box (memtable_within_capacity)")
    );
    let mut w = Lsm::with_shape(2, 2, 2);
    for k in 0..50_u32 {
        w.write(k % 7, k);
        assert!(w.memtable_len() < 2 && w.is_valid());
    }
}
