// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;
use std::collections::BTreeSet;

// ---------------------------------------------------------------------------------------
// Cost: `len`, `rank` and `select` read the cached subtree counts.
// ---------------------------------------------------------------------------------------

/// `0..n` in the order that makes a perfectly balanced tree: each range's median first.
fn median_first(lo: u32, hi: u32, out: &mut Vec<u32>) {
    if lo < hi {
        let mid = lo + (hi - lo) / 2;
        out.push(mid);
        median_first(lo, mid, out);
        median_first(mid + 1, hi, out);
    }
}

/// The tree holding `0..n` with every range's median at its root.
fn balanced(n: u32) -> Bst<u32> {
    let mut order = Vec::new();
    median_first(0, n, &mut order);
    order.into_iter().collect()
}

/// The slot holding a non-empty tree's root node, for the tests below to overwrite its count.
fn root_mut<T>(t: &mut Bst<T>) -> &mut Node<T> {
    t.0.as_mut().expect("a non-empty tree")
}

/// `len` answers from the root's cached count, whatever that count says.
#[test]
fn len_reads_the_cached_count() {
    let mut t = balanced(7);
    root_mut(&mut t).size = 1_000;
    assert_eq!(t.len(), 1_000);
}

/// `rank` and `select` steer by the left subtree's cached count: with that count overwritten,
/// both follow the overwritten number.
#[test]
fn rank_and_select_read_the_cached_counts() {
    let mut t = balanced(7); // root 3, left {0, 1, 2}, right {4, 5, 6} rooted at 5
    root_mut(&mut t)
        .left
        .0
        .as_mut()
        .expect("3 has a left child")
        .size = 100;
    assert_eq!(t.rank(&5), 102); // 100 on the left, the root, then 4 below 5
    assert_eq!(t.select(101), Some(&4)); // skip 100 and the root, then the least on the right
}

// ---------------------------------------------------------------------------------------
// `is_valid`: hand-built trees that break one promise each.
// ---------------------------------------------------------------------------------------

/// A leaf, with its count right.
fn leaf(k: u32) -> Bst<u32> {
    Bst::node(Bst::new(), k, Bst::new())
}

#[test]
fn is_valid_accepts_what_insert_builds() {
    assert!(Bst::<u32>::new().is_valid());
    assert!(balanced(15).is_valid());
    assert!((0..50u32).collect::<Bst<u32>>().is_valid());
}

/// `5`, left child `2`, and `7` as the right child of `2`: every parent-child pair is in
/// order, yet `7` sits in `5`'s left subtree.
#[test]
fn is_valid_rejects_a_grandchild_on_the_wrong_side() {
    let t = Bst::node(Bst::node(Bst::new(), 2, leaf(7)), 5, Bst::new());
    assert!(t.as_node().is_some_and(|n| n.size == 3)); // the counts are right
    assert!(!t.is_valid());
}

/// `Sorted` is strict on both sides: a set holds each key once.
#[test]
fn is_valid_rejects_a_duplicate_key() {
    assert!(!Bst::node(leaf(4), 4, Bst::new()).is_valid());
    assert!(!Bst::node(Bst::new(), 4, leaf(4)).is_valid());
}

/// Keys in order, one count wrong on an inner node, with the root's count raised to agree.
#[test]
fn is_valid_rejects_a_stale_count_below_the_root() {
    let mut t = balanced(7); // root 3, right child 5 over {4, 6}
    assert!(t.is_valid());
    let root = root_mut(&mut t);
    root.right.0.as_mut().expect("3 has a right child").size = 4;
    root.size = 8; // 3 on the left + the (wrong) 4 on the right + 1
    assert!(!t.is_valid());

    // A count so large the sum it is checked against would overflow is still just `false`.
    let mut u = balanced(3);
    root_mut(&mut u)
        .left
        .0
        .as_mut()
        .expect("1 has a left child")
        .size = usize::MAX;
    assert!(!u.is_valid());
}

thread_local! {
    /// Key comparisons made on this thread by `Counted`.
    static COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A key that counts every comparison made on it.
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

/// `rank` is one descent: on a balanced tree of 1023 keys, ten levels deep, it compares the
/// key at most once per level, present or absent.
#[test]
fn rank_compares_once_per_level() {
    let mut order = Vec::new();
    median_first(0, 1023, &mut order);
    let t: Bst<Counted> = order.into_iter().map(|k| Counted(2 * k + 1)).collect();
    for probe in 0..=2047 {
        COMPARISONS.with(|c| c.set(0));
        let r = t.rank(&Counted(probe));
        let made = COMPARISONS.with(std::cell::Cell::get);
        assert_eq!(r, (probe as usize) / 2, "rank({probe})");
        assert!(
            made <= 10,
            "rank({probe}) made {made} comparisons on a 10-level tree"
        );
    }
}

// ---------------------------------------------------------------------------------------
// Unit tests: edge cases per operation.
// ---------------------------------------------------------------------------------------

#[test]
fn empty_tree_basics() {
    let mut t: Bst<i32> = Bst::new();
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
    assert_eq!(t.min(), None);
    assert_eq!(t.max(), None);
    assert!(!t.contains(&0));
    assert!(!t.search(&0));
    assert_eq!(t.floor(&0), None);
    assert_eq!(t.ceiling(&0), None);
    assert_eq!(t.select(0), None);
    assert_eq!(t.rank(&0), 0);
    assert!(t.in_order().is_empty());
    assert!(
        !t.delete_hibbard(&0),
        "deleting from the empty tree removes nothing"
    );
    assert!(t.is_empty());
}

#[test]
fn single_node() {
    let mut t = Bst::from_iter([5]);
    assert!(!t.is_empty());
    assert_eq!(t.len(), 1);
    assert!(t.contains(&5));
    assert!(!t.contains(&6));
    assert_eq!(t.min(), Some(&5));
    assert_eq!(t.max(), Some(&5));
    assert_eq!(t.floor(&5), Some(&5));
    assert_eq!(t.floor(&10), Some(&5));
    assert_eq!(t.floor(&0), None);
    assert_eq!(t.ceiling(&5), Some(&5));
    assert_eq!(t.ceiling(&0), Some(&5));
    assert_eq!(t.ceiling(&10), None);
    assert_eq!(t.rank(&5), 0);
    assert_eq!(t.select(0), Some(&5));
    assert_eq!(t.select(1), None);

    t.delete_hibbard(&5);
    assert!(t.is_empty());
}

#[test]
fn insert_duplicate_is_noop() {
    let t = Bst::from_iter([5, 5, 5]);
    assert_eq!(t.len(), 1);
    assert_eq!(t.in_order(), vec![&5]);
}

#[test]
fn delete_root_zero_children() {
    let mut t = Bst::from_iter([5]);
    t.delete_hibbard(&5);
    assert!(t.is_empty());
}

#[test]
fn delete_root_one_child() {
    // Right child only.
    let mut t = Bst::from_iter([5, 8]);
    t.delete_hibbard(&5);
    assert_eq!(t.in_order(), vec![&8]);
    assert!(!t.contains(&5));

    // Left child only.
    let mut t = Bst::from_iter([5, 2]);
    t.delete_hibbard(&5);
    assert_eq!(t.in_order(), vec![&2]);
    assert!(!t.contains(&5));
}

#[test]
fn delete_root_two_children() {
    // Successor of 5 is min(right subtree) = 7.
    let mut t = Bst::new();
    for x in [5, 2, 8, 7, 9] {
        t.insert(x);
    }
    t.delete_hibbard(&5);
    assert_eq!(t.in_order(), vec![&2, &7, &8, &9]);
    assert!(!t.contains(&5));

    // Successor has its own right child, which must be promoted in its place.
    let mut t = Bst::new();
    for x in [5, 2, 8, 6, 9, 7] {
        t.insert(x);
    }
    t.delete_hibbard(&5);
    assert_eq!(t.in_order(), vec![&2, &6, &7, &8, &9]);
    assert!(!t.contains(&5));
}

#[test]
fn delete_non_root_node() {
    let mut t = Bst::new();
    for x in [5, 2, 8, 1, 3, 7, 9] {
        t.insert(x);
    }
    t.delete_hibbard(&2);
    assert_eq!(t.in_order(), vec![&1, &3, &5, &7, &8, &9]);
    assert!(!t.contains(&2));
}

#[test]
fn delete_absent_key_is_noop() {
    let mut t = Bst::new();
    for x in [5, 2, 8] {
        t.insert(x);
    }
    let before = t.clone();
    assert!(!t.delete_hibbard(&100), "an absent key removes nothing");
    assert_eq!(before, t, "and leaves the tree exactly as it was");
}

#[test]
fn rank_select_fixed_tree() {
    let mut t = Bst::new();
    for x in [5, 3, 8, 1, 4, 7, 9] {
        t.insert(x);
    }
    let sorted = [1, 3, 4, 5, 7, 8, 9];
    for (i, k) in sorted.iter().enumerate() {
        assert_eq!(t.rank(k), i, "rank of {k}");
        assert_eq!(t.select(i), Some(k), "select({i})");
    }
    assert_eq!(t.select(sorted.len()), None);
    assert_eq!(t.rank(&0), 0);
    assert_eq!(t.rank(&100), sorted.len());
}

#[test]
fn delete_and_delete_hibbard_build_the_same_tree() {
    // A node with no left child (15), and a two-child node whose successor has a right
    // subtree (50): the trees still agree.
    for (keys, target) in [(&[0, 15, 30, 16][..], 15), (&[50, 10, 70, 80, 74][..], 50)] {
        let build = || {
            let mut t = Bst::new();
            for &x in keys {
                t.insert(x);
            }
            t
        };
        let (mut by_copy, mut by_move) = (build(), build());
        assert!(by_copy.delete_hibbard(&target) && by_move.delete(&target));
        assert_eq!(by_copy, by_move);
        assert!(!by_copy.contains(&target));
    }
}

#[test]
fn delete_moves_the_successor_node_and_delete_hibbard_keeps_the_deleted_one() {
    // The chapter's two procedures, told apart by which allocation survives: TRANSPLANT puts
    // 60's own node where 50's stood; the copy-up keeps 50's node and writes 60 into it.
    fn node_at<T>(t: &Bst<T>) -> *const Node<T> {
        &**t.0.as_ref().expect("a node here")
    }
    let build = || {
        let mut t = Bst::new();
        for x in [50, 30, 70, 60, 80] {
            t.insert(x);
        }
        t
    };
    let mut moved = build();
    let root = moved.0.as_ref().expect("root");
    let successor = node_at(&root.right.0.as_ref().expect("70").left);
    moved.delete(&50);
    assert_eq!(
        node_at(&moved),
        successor,
        "delete must stand 60's own node in the gap"
    );

    let mut copied = build();
    let old_root = node_at(&copied);
    copied.delete_hibbard(&50);
    assert_eq!(
        node_at(&copied),
        old_root,
        "delete_hibbard keeps 50's node, relabelled"
    );
    assert_eq!(moved, copied, "and both leave the same tree");
}

/// Both deletions find a present key in one descent: a key at depth `d` costs exactly the
/// `d + 1` nodes on its path. A miss costs the path twice, down and back.
#[test]
fn delete_finds_a_present_key_in_one_descent() {
    fn path_len(t: &Bst<u64>, key: u64) -> (usize, bool) {
        let (mut cur, mut d) = (t, 0);
        while let Some(n) = cur.0.as_ref() {
            d += 1;
            match key.cmp(&n.key) {
                Ordering::Equal => return (d, true),
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
            }
        }
        (d, false)
    }
    let mut state = 0x2545_f491_4f6c_dd1d_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut t: Bst<u64> = Bst::new();
    for _ in 0..200 {
        t.insert(next() % 1000 * 2);
    }
    let mut hits = 0;
    for key in 0..2000 {
        let (len, present) = path_len(&t, key);
        for hibbard in [false, true] {
            let mut u = t.clone();
            STEPS.with(|c| c.set(0));
            let removed = if hibbard {
                u.delete_hibbard(&key)
            } else {
                u.delete(&key)
            };
            let steps = STEPS.with(std::cell::Cell::get);
            assert_eq!(removed, present);
            let expected = if present { len } else { 2 * len };
            assert_eq!(
                steps, expected,
                "key {key}, hibbard {hibbard}, present {present}"
            );
            assert!(sizes_consistent(&u), "cached sizes after deleting {key}");
        }
        hits += usize::from(present);
    }
    assert!(
        hits > 100,
        "the corpus must delete present keys at many depths"
    );
}

/// A literal transcription of `BST.deleteHibbard`, to check the production one against.
fn delete_hibbard_lean_ref<T: Ord>(mut t: Bst<T>, a: &T) -> Bst<T> {
    // `Bst` implements `Drop`, so the boxed node comes out of the slot.
    let Some(n) = t.0.take() else {
        return Bst(None);
    };
    let Node {
        left, key, right, ..
    } = *n;
    match a.cmp(&key) {
        Ordering::Less => Bst::node(delete_hibbard_lean_ref(left, a), key, right),
        Ordering::Greater => Bst::node(left, key, delete_hibbard_lean_ref(right, a)),
        Ordering::Equal if left.is_empty() => right,
        Ordering::Equal => match splice_min_lean_ref(right) {
            None => left,
            Some((m, r2)) => Bst::node(left, m, r2),
        },
    }
}

/// Every node's cached `size` equals the keys actually below it.
fn sizes_consistent<T>(t: &Bst<T>) -> bool {
    fn go<T>(t: &Bst<T>) -> Option<usize> {
        match t.0.as_ref() {
            None => Some(0),
            Some(n) => {
                let l = go(&n.left)?;
                let r = go(&n.right)?;
                (n.size == l + r + 1).then_some(n.size)
            }
        }
    }
    go(t).is_some()
}

/// `BST.spliceMin`, transcribed: at the leftmost node hand back its key with its right subtree
/// promoted into its place.
fn splice_min_lean_ref<T: Ord>(mut t: Bst<T>) -> Option<(T, Bst<T>)> {
    let n = t.0.take()?;
    let Node {
        left, key, right, ..
    } = *n;
    match splice_min_lean_ref(left) {
        None => Some((key, right)),
        Some((m, l2)) => Some((m, Bst::node(l2, key, right))),
    }
}

/// `BST.transplantAt`: CLRS's three cases, in CLRS's order.
fn transplant_at_lean_ref<T: Ord>(left: Bst<T>, right: Bst<T>) -> Bst<T> {
    if left.is_empty() {
        return right;
    }
    match splice_min_lean_ref(right) {
        None => left,
        Some((m, r2)) => Bst::node(left, m, r2),
    }
}

/// `BST.delete`, transcribed literally.
fn delete_lean_ref<T: Ord>(mut t: Bst<T>, a: &T) -> Bst<T> {
    let Some(n) = t.0.take() else {
        return Bst(None);
    };
    let Node {
        left, key, right, ..
    } = *n;
    match a.cmp(&key) {
        Ordering::Less => Bst::node(delete_lean_ref(left, a), key, right),
        Ordering::Greater => Bst::node(left, key, delete_lean_ref(right, a)),
        Ordering::Equal => transplant_at_lean_ref(left, right),
    }
}

#[test]
fn delete_hibbard_splices_a_node_with_no_left_child() {
    // 10 has no left child, so its right subtree takes its place whole.
    let mut t = Bst::new();
    for x in [10, 12, 20, 14] {
        t.insert(x);
    }
    let expected = delete_hibbard_lean_ref(t.clone(), &10);
    t.delete_hibbard(&10);
    assert_eq!(t, expected);
    assert_eq!(
        t,
        Bst::node(
            Bst(None),
            12,
            Bst::node(Bst::node(Bst(None), 14, Bst(None)), 20, Bst(None)),
        )
    );
}

// ---------------------------------------------------------------------------------------
// Property tests: exactly the statements `BST/` proves, checked empirically.
// ---------------------------------------------------------------------------------------

fn is_strictly_sorted<T: Ord>(v: &[T]) -> bool {
    v.windows(2).all(|w| w[0] < w[1])
}

#[derive(Debug, Clone)]
enum Op {
    Insert(i32),
    Delete(i32),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (-50..50i32).prop_map(Op::Insert),
        (-50..50i32).prop_map(Op::Delete),
    ]
}

proptest! {
    /// `insert` then `contains` finds the inserted key. Mirrors `mem_insert`.
    #[test]
    fn insert_then_contains_finds_key(
        xs in prop::collection::vec(-100..100i32, 0..50),
        y in -100..100i32,
    ) {
        let mut t = Bst::new();
        for x in &xs {
            t.insert(*x);
        }
        t.insert(y);
        prop_assert!(t.contains(&y));
    }

    /// `contains` on a key never inserted returns not-found. Mirrors `search_correct`.
    #[test]
    fn contains_absent_key_not_found(
        xs in prop::collection::vec(-100..100i32, 0..50),
        y in -200..-100i32,
    ) {
        let mut t = Bst::new();
        for x in &xs {
            t.insert(*x);
        }
        prop_assert!(!t.contains(&y));
    }

    /// `Sorted` survives any sequence of inserts and deletes, under both deletions. Mirrors
    /// `sorted_insert`/`sorted_delete`/`sorted_deleteHibbard`.
    #[test]
    fn stays_sorted_after_random_ops(ops in prop::collection::vec(op_strategy(), 0..200)) {
        let mut plain = Bst::new();
        let mut hibbard = Bst::new();
        for op in &ops {
            match op {
                Op::Insert(x) => {
                    plain.insert(*x);
                    hibbard.insert(*x);
                }
                Op::Delete(x) => {
                    plain.delete(x);
                    hibbard.delete_hibbard(x);
                }
            };
            prop_assert!(is_strictly_sorted(&plain.in_order()));
            prop_assert!(is_strictly_sorted(&hibbard.in_order()));
        }
    }

    /// Each production deletion agrees with its literal transcription of the Lean file:
    /// `delete` with [`delete_lean_ref`] (`BST.delete`) and `delete_hibbard` with
    /// [`delete_hibbard_lean_ref`] (`BST.deleteHibbard`), shape included.
    #[test]
    fn deletes_match_their_lean_references(
        xs in prop::collection::vec(-50..50i32, 0..50),
        target in -50..50i32,
    ) {
        let mut t = Bst::new();
        for x in &xs {
            t.insert(*x);
        }
        let mut plain = t.clone();
        let expected = delete_lean_ref(t.clone(), &target);
        plain.delete(&target);
        prop_assert_eq!(plain, expected);

        let expected = delete_hibbard_lean_ref(t.clone(), &target);
        t.delete_hibbard(&target);
        prop_assert_eq!(t, expected);
    }

    /// Every node's cached `size` is the number of keys actually below it, after every step
    /// of an arbitrary insert/delete mix, under both deletions.
    #[test]
    fn cached_sizes_stay_consistent(
        ops in prop::collection::vec((any::<bool>(), -40..40i32), 0..200),
    ) {
        let mut plain = Bst::new();
        let mut hibbard = Bst::new();
        let mut model = std::collections::BTreeSet::new();
        for (is_insert, k) in ops {
            if is_insert {
                let fresh = model.insert(k);
                prop_assert_eq!(plain.insert(k), fresh);
                prop_assert_eq!(hibbard.insert(k), fresh);
            } else {
                let present = model.remove(&k);
                prop_assert_eq!(plain.delete(&k), present);
                prop_assert_eq!(hibbard.delete_hibbard(&k), present);
            }
            for t in [&plain, &hibbard] {
                prop_assert!(sizes_consistent(t), "a node's size field is wrong");
                prop_assert!(t.is_valid(), "the public checker disagrees with the walk");
                prop_assert_eq!(t.len(), model.len());
                // `rank` and `select` read the field.
                for (i, k) in model.iter().enumerate() {
                    prop_assert_eq!(t.rank(k), i);
                    prop_assert_eq!(t.select(i), Some(k));
                }
            }
        }
    }

    /// `delete` and `delete_hibbard` each remove exactly the target key and no other.
    /// Mirrors `mem_delete` and `mem_deleteHibbard`.
    #[test]
    fn deletes_remove_exactly_target(
        xs in prop::collection::vec(-50..50i32, 0..50),
        target in -50..50i32,
    ) {
        let mut plain = Bst::new();
        for x in &xs {
            plain.insert(*x);
        }
        let mut hibbard = plain.clone();
        let others: BTreeSet<i32> = xs.iter().copied().filter(|&x| x != target).collect();
        plain.delete(&target);
        hibbard.delete_hibbard(&target);
        for t in [&plain, &hibbard] {
            prop_assert!(!t.contains(&target));
            for x in &others {
                prop_assert!(t.contains(x));
            }
        }
    }

    /// `rank`/`select` are inverse operations on present keys. Mirrors `rank_select?` and
    /// `select?_rank`.
    #[test]
    fn rank_select_are_inverse(xs in prop::collection::vec(-50..50i32, 0..50)) {
        let mut t = Bst::new();
        for x in &xs {
            t.insert(*x);
        }
        let unique: BTreeSet<i32> = xs.into_iter().collect();
        for a in &unique {
            let r = t.rank(a);
            prop_assert_eq!(t.select(r), Some(a));
            prop_assert_eq!(t.rank(t.select(r).unwrap()), r);
        }
    }

    /// `floor`/`ceiling` match a naive linear-scan reference implementation.
    #[test]
    fn floor_ceiling_match_naive_scan(
        xs in prop::collection::vec(-50..50i32, 0..50),
        a in -60..60i32,
    ) {
        let mut t = Bst::new();
        for x in &xs {
            t.insert(*x);
        }
        let keys: BTreeSet<i32> = xs.into_iter().collect();
        let naive_floor = keys.iter().filter(|&&k| k <= a).max().copied();
        let naive_ceiling = keys.iter().filter(|&&k| k >= a).min().copied();
        prop_assert_eq!(t.floor(&a).copied(), naive_floor);
        prop_assert_eq!(t.ceiling(&a).copied(), naive_ceiling);
    }

    /// [`Bst::delete`] and [`Bst::delete_hibbard`] build the same tree on every input, as
    /// `BST.deleteHibbard_eq_delete` proves for the Lean definitions.
    #[test]
    fn delete_and_delete_hibbard_agree_on_the_tree(
        xs in prop::collection::vec(-50..50i32, 0..50),
        target in -50..50i32,
    ) {
        let mut t1 = Bst::new();
        let mut t2 = Bst::new();
        for x in &xs {
            t1.insert(*x);
            t2.insert(*x);
        }
        t1.delete_hibbard(&target);
        t2.delete(&target);
        prop_assert_eq!(t1, t2);
    }
}

/// `check_valid` names the box invariant, then the layout check, each broken alone.
#[test]
fn check_valid_names_each_check() {
    assert_eq!(balanced(7).check_valid(), Ok(()));
    let t = Bst::node(Bst::node(Bst::new(), 2, leaf(7)), 5, Bst::new());
    assert_eq!(t.check_valid(), Err("invariant 1 (sorted)"));
    let mut u = balanced(7);
    root_mut(&mut u).size = 8;
    assert_eq!(u.check_valid(), Err("layout (sizes_add_up)"));
}
