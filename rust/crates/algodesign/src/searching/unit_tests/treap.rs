// SPDX-License-Identifier: Apache-2.0
use super::*;

/// `len` answers from the count the tree keeps, whatever that count says.
#[test]
fn len_reads_the_cached_count() {
    let mut t = Treap::new();
    for k in 0..7u64 {
        t.insert(k, k);
    }
    t.len = 1_000;
    assert_eq!(t.len(), 1_000);
}

/// `insert` rotates the new node up, one rotation per level it rises: the count
/// `insert_with_rotations` returns is the depth a plain BST insert would give the key minus the
/// depth it ends at.
#[test]
fn insert_rotates_up_one_level_per_rotation() {
    fn depth_of(t: &Tree<u64>, key: u64) -> usize {
        let (mut cur, mut d) = (t, 0);
        while let Some(n) = cur {
            match key.cmp(&n.key) {
                Ordering::Equal => return d,
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
            }
            d += 1;
        }
        panic!("key not found");
    }
    fn plain_depth(t: &Tree<u64>, key: u64) -> usize {
        let (mut cur, mut d) = (t, 0);
        while let Some(n) = cur {
            cur = if key < n.key { &n.left } else { &n.right };
            d += 1;
        }
        d
    }
    let mut state = 0x1234_5678_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut total = 0;
    for _ in 0..200 {
        let mut t: Treap<u64> = Treap::new();
        for _ in 0..30 {
            let key = next() % 64;
            if t.contains(&key) {
                continue;
            }
            let priority = next() % 8;
            let expected = plain_depth(&t.root, key);
            let (added, made) = t.insert_with_rotations(key, priority);
            assert!(added);
            assert_eq!(made, expected - depth_of(&t.root, key));
            total += made;
        }
    }
    assert!(total > 0, "the corpus must make rotations happen");
}

/// `delete` rotates the doomed node down, one rotation per level it sinks, until it is a
/// leaf. Each rotation takes one node off either the right spine of its left subtree or the
/// left spine of its right subtree, and it stops when both are empty, so the count is the sum
/// of those two spines' lengths. Priorities are drawn from `0..4`, so ties are common.
#[test]
fn delete_rotates_down_one_level_per_rotation() {
    fn spines(t: &Tree<u64>, key: u64) -> usize {
        let mut cur = t;
        while let Some(n) = cur {
            match key.cmp(&n.key) {
                Ordering::Less => cur = &n.left,
                Ordering::Greater => cur = &n.right,
                Ordering::Equal => {
                    let (mut count, mut side) = (0, &n.left);
                    while let Some(m) = side {
                        count += 1;
                        side = &m.right;
                    }
                    let mut side = &n.right;
                    while let Some(m) = side {
                        count += 1;
                        side = &m.left;
                    }
                    return count;
                }
            }
        }
        panic!("key not found");
    }
    let mut state = 0x9e37_79b9_7f4a_7c15_u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut total = 0;
    for _ in 0..200 {
        let mut t: Treap<u64> = Treap::new();
        for _ in 0..30 {
            let key = next() % 64;
            let priority = next() % 4;
            t.insert(key, priority);
        }
        let keys: Vec<u64> = t.iter().copied().collect();
        for key in keys {
            let expected = spines(&t.root, key);
            let (removed, made) = t.delete_with_rotations(&key);
            assert!(removed);
            assert_eq!(made, expected, "deleting {key}");
            total += made;
        }
        assert!(t.is_empty());
    }
    assert!(total > 0, "the corpus must make rotations happen");
}
use proptest::prelude::*;
use rand::seq::SliceRandom;
use std::collections::BTreeSet;

/// In-order traversal, collecting keys.
fn in_order<T: Clone>(t: &Tree<T>, out: &mut Vec<T>) {
    if let Some(node) = t {
        in_order(&node.left, out);
        out.push(node.key.clone());
        in_order(&node.right, out);
    }
}

/// `Treap.Sorted`: the in-order traversal is strictly increasing.
fn is_bst_sorted<T: Ord + Clone>(t: &Tree<T>) -> bool {
    let mut xs = Vec::new();
    in_order(t, &mut xs);
    xs.windows(2).all(|w| w[0] < w[1])
}

/// `Treap.HeapOrdered`: every node's priority is `>=` both of its children's.
fn is_heap_ordered<T>(t: &Tree<T>) -> bool {
    match t {
        None => true,
        Some(node) => {
            let left_ok = node
                .left
                .as_deref()
                .is_none_or(|l| l.priority <= node.priority);
            let right_ok = node
                .right
                .as_deref()
                .is_none_or(|r| r.priority <= node.priority);
            left_ok && right_ok && is_heap_ordered(&node.left) && is_heap_ordered(&node.right)
        }
    }
}

#[test]
fn empty_tree_has_no_members() {
    let t: Treap<i32> = Treap::new();
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
    assert!(!t.contains(&0));
    assert!(!t.contains(&42));
}

#[test]
fn single_insert_is_found() {
    let mut t = Treap::new();
    t.insert(5, 100);
    assert!(!t.is_empty());
    assert_eq!(t.len(), 1);
    assert!(t.contains(&5));
    assert!(!t.contains(&6));
}

#[test]
fn insert_then_delete_same_key_empties_again() {
    let mut t = Treap::new();
    t.insert("a", 10);
    assert!(t.contains(&"a"));
    t.delete(&"a");
    assert!(!t.contains(&"a"));
    assert!(t.is_empty());
}

#[test]
fn delete_on_empty_tree_is_a_no_op() {
    let mut t: Treap<i32> = Treap::new();
    t.delete(&5);
    assert!(t.is_empty());
}

#[test]
fn reinserting_an_existing_key_does_not_duplicate_it() {
    let mut t = Treap::new();
    t.insert(1, 5);
    t.insert(1, 99);
    assert_eq!(t.len(), 1);
    assert!(t.contains(&1));
}

#[test]
fn worked_example_matches_naive_sorted_reference() {
    let entries = [(5, 3), (2, 9), (8, 1), (1, 7), (9, 2), (4, 6), (7, 4)];
    let mut t = Treap::new();
    for &(k, p) in &entries {
        t.insert(k, p);
    }
    let mut got = Vec::new();
    in_order(&t.root, &mut got);

    let mut expected: Vec<i32> = entries.iter().map(|&(k, _)| k).collect();
    expected.sort_unstable();

    assert_eq!(got, expected);
    assert!(is_bst_sorted(&t.root));
    assert!(is_heap_ordered(&t.root));
}

#[test]
fn insert_random_convenience_wrapper_works() {
    let mut t = Treap::new();
    for k in 0..200i32 {
        t.insert_random(k);
    }
    assert_eq!(t.len(), 200);
    for k in 0..200i32 {
        assert!(t.contains(&k));
    }
    assert!(is_bst_sorted(&t.root));
    assert!(is_heap_ordered(&t.root));
}

/// Expected fewer than two rotations per insert under random priorities (Seidel–Aragon): the
/// average [`rotation_count`] stays under a loose bound of 10, which an `O(log n)` count at
/// `n = 4000` would trip.
#[test]
fn average_rotation_count_stays_well_under_generous_bound() {
    let n = 4000usize;
    let mut keys: Vec<i32> = (0..n as i32).collect();
    keys.shuffle(&mut rand::rng());

    let mut t: Treap<i32> = Treap::new();
    let mut total_rotations: u64 = 0;
    for &k in &keys {
        let priority = rand::random::<u64>();
        total_rotations += rotation_count(&k, priority, &t.root) as u64;
        t.insert(k, priority);
    }

    let average = total_rotations as f64 / n as f64;
    println!("average rotation_count over {n} random inserts: {average:.4}");
    assert!(
        average < 10.0,
        "average rotation_count {average} exceeded the generous sanity bound of 10 \
             (Theorem 8.8 expects an average around/under 2)"
    );
}

fn key_strategy() -> impl Strategy<Value = i32> {
    -30..30
}

fn priority_strategy() -> impl Strategy<Value = u64> {
    0u64..50
}

#[derive(Debug, Clone)]
enum Op {
    Insert(i32, u64),
    Delete(i32),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (key_strategy(), priority_strategy()).prop_map(|(k, p)| Op::Insert(k, p)),
        key_strategy().prop_map(Op::Delete),
    ]
}

proptest! {
    /// Drives a `Treap<i32>` through a random sequence of `insert`/`delete` operations, all
    /// with explicit priorities, checking after every step `Treap.Sorted`, `Treap.HeapOrdered`,
    /// the key set and reported `bool`s against a `BTreeSet`, and the cached `len`.
    #[test]
    fn treap_invariants_preserved_under_random_ops(ops in prop::collection::vec(op_strategy(), 0..200)) {
        let mut t: Treap<i32> = Treap::new();
        let mut reference: BTreeSet<i32> = BTreeSet::new();

        for op in ops {
            match op {
                Op::Insert(k, p) => {
                    prop_assert_eq!(t.insert(k, p), reference.insert(k));
                }
                Op::Delete(k) => {
                    prop_assert_eq!(t.delete(&k), reference.remove(&k));
                }
            }

            // The cached count, after every step.
            prop_assert_eq!(t.len(), reference.len(), "cached len diverged from the reference");
            prop_assert_eq!(t.is_empty(), reference.is_empty());
            prop_assert!(is_bst_sorted(&t.root), "BST ordering violated");
            prop_assert!(is_heap_ordered(&t.root), "max-heap property violated");

            let mut got = Vec::new();
            in_order(&t.root, &mut got);
            let expected: Vec<i32> = reference.iter().copied().collect();
            prop_assert_eq!(got, expected, "membership diverged from reference BTreeSet");
        }
    }
}

// The iterator and trait surface, against a `BTreeSet` model.
proptest! {
    #[test]
    fn iter_and_len_agree_with_a_set_model(
        ops in prop::collection::vec((0..30i32, 0..1000u64, prop::bool::ANY), 0..80),
    ) {
        use std::collections::BTreeSet;
        let mut t: Treap<i32> = Treap::new();
        let mut model: BTreeSet<i32> = BTreeSet::new();
        for (k, pr, insert) in &ops {
            if *insert {
                prop_assert_eq!(t.insert(*k, *pr), model.insert(*k));
            } else {
                prop_assert_eq!(t.delete(k), model.remove(k));
            }
        }
        let got: Vec<i32> = t.iter().copied().collect();
        prop_assert_eq!(got, model.iter().copied().collect::<Vec<_>>());
        prop_assert_eq!(t.len(), model.len());
        prop_assert_eq!(t.is_empty(), model.is_empty());
        prop_assert!(t.is_valid());
    }

    #[test]
    fn from_iter_holds_every_key(xs in prop::collection::vec(0..100i32, 0..60)) {
        use std::collections::BTreeSet;
        let t: Treap<i32> = xs.iter().copied().collect();
        let model: BTreeSet<i32> = xs.iter().copied().collect();
        prop_assert_eq!(t.iter().copied().collect::<Vec<_>>(),
                        model.iter().copied().collect::<Vec<_>>());
        prop_assert!(t.is_valid());
    }
}

/// `Treap::with_seed(7)` draws `SplitMix64`'s stream, one draw per call, the duplicate 3 included,
/// and builds the tree the Python's `Treap(seed=7)` builds (its test holds the same preorder).
#[test]
fn a_seed_builds_the_tree_the_python_builds() {
    fn preorder(t: &Tree<i32>, out: &mut Vec<(i32, u64)>) {
        if let Some(n) = t {
            out.push((n.key, n.priority));
            preorder(&n.left, out);
            preorder(&n.right, out);
        }
    }
    let mut t = Treap::with_seed(7);
    for k in [5, 3, 8, 3, 1, 9, 2] {
        t.insert_random(k);
    }
    let mut got = Vec::new();
    preorder(&t.root, &mut got);
    assert_eq!(
        got,
        vec![
            (8, 16_616_101_746_815_609_346),
            (2, 8_632_209_307_422_871_798),
            (1, 8_346_079_845_500_723_674),
            (5, 7_191_089_600_892_374_487),
            (3, 309_689_372_594_955_804),
            (9, 4_601_199_455_465_548_305),
        ]
    );
}

/// The chapter's claim, on 4 000 keys at seeded priorities: fewer than two rotations per insert
/// and per delete on average.
#[test]
fn random_updates_average_fewer_than_two_rotations() {
    let mut keys: Vec<u32> = (0..4000).collect();
    let mut order = crate::rng::SplitMix64::new(1);
    let mut shuffle = |keys: &mut Vec<u32>| {
        for i in (1..keys.len()).rev() {
            let j = usize::try_from(order.next_u64() % (i as u64 + 1)).expect("below len");
            keys.swap(i, j);
        }
    };
    let mut t = Treap::with_seed(1);
    shuffle(&mut keys);
    let inserted: usize = keys
        .iter()
        .map(|&k| t.insert_random_with_rotations(k).1)
        .sum();
    shuffle(&mut keys);
    let deleted: usize = keys.iter().map(|k| t.delete_with_rotations(k).1).sum();
    assert!(t.is_empty());
    assert!(inserted < 2 * keys.len() && deleted < 2 * keys.len());
    assert_eq!(t.delete_with_rotations(&0), (false, 0));
}

proptest! {
    /// The counted entry points build the trees the plain ones build.
    #[test]
    fn counting_changes_no_tree(ops in prop::collection::vec((any::<bool>(), 0..40u8, 0..6u64), 0..80)) {
        let (mut plain, mut counted) = (Treap::new(), Treap::new());
        for (insert, key, priority) in ops {
            if insert {
                prop_assert_eq!(plain.insert(key, priority), counted.insert_with_rotations(key, priority).0);
            } else {
                prop_assert_eq!(plain.delete(&key), counted.delete_with_rotations(&key).0);
            }
            prop_assert_eq!(&plain, &counted);
        }
    }
}
