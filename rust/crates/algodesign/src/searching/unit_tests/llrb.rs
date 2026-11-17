// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;
use std::collections::BTreeSet;

/// `len` answers from the root's cached count, so it answers whatever that count says; a
/// walk would find the real 7.
#[test]
fn len_reads_the_cached_count() {
    let mut t: Llrb<i32> = (0..7).collect();
    t.0.as_mut().expect("non-empty").size = 1_000;
    assert_eq!(t.len(), 1_000);
}

fn in_order<'a, T>(t: &'a Llrb<T>, out: &mut Vec<&'a T>) {
    if let Some(n) = t.as_node() {
        in_order(&n.left, out);
        out.push(&n.key);
        in_order(&n.right, out);
    }
}

fn assert_valid<T: Ord + std::fmt::Debug>(t: &Llrb<T>) {
    assert!(t.is_left_leaning(), "LeftLeaning violated: {t:?}");
    assert!(t.is_no_red_red(), "NoRedRed violated: {t:?}");
    assert!(t.black_height().is_some(), "black-balance violated: {t:?}");
    assert!(t.is_root_black(), "RootBlack violated: {t:?}");
    let mut out = Vec::new();
    in_order(t, &mut out);
    assert!(
        out.windows(2).all(|w| w[0] < w[1]),
        "Sorted violated: {t:?}"
    );
}

// --- unit tests: edge cases -------------------------------------------------------------

#[test]
fn empty_tree() {
    let t: Llrb<i32> = Llrb::new();
    assert!(t.is_leaf());
    assert!(!t.contains(&0));
    assert_eq!(t.min(), None);
    assert_valid(&t);
}

#[test]
fn single_insert() {
    let t = Llrb::from_iter([5]);
    assert!(t.contains(&5));
    assert!(!t.contains(&6));
    assert_eq!(t.min(), Some(&5));
    assert_valid(&t);
}

#[test]
fn duplicate_insert_is_noop() {
    let mut t = Llrb::new();
    for x in [5, 5, 5] {
        t.insert(x);
    }
    let mut out = Vec::new();
    in_order(&t, &mut out);
    assert_eq!(out, vec![&5]);
    assert_valid(&t);
}

#[test]
fn delete_only_key() {
    let mut t = Llrb::from_iter([42]);
    t.delete(&42);
    assert!(t.is_leaf());
    assert!(!t.contains(&42));
}

#[test]
fn delete_missing_key_is_noop() {
    let mut t = Llrb::new();
    for x in [3, 1, 4, 1, 5, 9] {
        t.insert(x);
    }
    let before: Vec<i32> = {
        let mut out = Vec::new();
        in_order(&t, &mut out);
        out.into_iter().copied().collect()
    };
    t.delete(&100);
    let after: Vec<i32> = {
        let mut out = Vec::new();
        in_order(&t, &mut out);
        out.into_iter().copied().collect()
    };
    assert_eq!(before, after);
    assert_valid(&t);
}

/// `delete` without its `contains` guard: the Lean `deleteTop` minus its `search`.
fn delete_unguarded<T: Ord>(t: &mut Llrb<T>, a: &T) {
    let root_is_2node = !t.left().is_some_and(Llrb::is_red) && !t.right().is_some_and(Llrb::is_red);
    if root_is_2node {
        t.set_color(Color::Red);
    }
    t.delete_inner(a, &mut ());
    t.set_color(Color::Black);
}

/// The "no right child" arm of `delete_inner`, reached directly by an absent key: returning
/// `left` without comparing would delete whichever key the walk ran out of right children at.
///
/// Traced: `{1, 2}` is root 2 with a red left 1. Deleting 3 rotates 1 up, walks right to 2,
/// finds no right child there, and must compare before splicing: 2 is not 3.
#[test]
fn delete_inner_on_an_absent_key_removes_nothing() {
    let mut t = Llrb::new();
    t.insert(2);
    t.insert(1);
    delete_unguarded(&mut t, &3);
    assert_eq!(t.iter().copied().collect::<Vec<_>>(), vec![1, 2]);
    assert_eq!(t.len(), 2);
    assert_valid(&t);
}

#[test]
fn delete_min_drains_in_sorted_order() {
    let input = [8, 3, 10, 1, 6, 14, 4, 7, 13, 2];
    let mut t = Llrb::new();
    for x in input {
        t.insert(x);
    }
    let mut drained = Vec::new();
    while !t.is_leaf() {
        drained.push(*t.min().unwrap());
        t.delete_min();
        assert_valid(&t);
    }
    let mut expected: Vec<i32> = input.to_vec();
    expected.sort_unstable();
    expected.dedup();
    assert_eq!(drained, expected);
}

/// Inserting 10, 20, 30, 15, 5 gives root 20 with 10 red below it, 10's two children black,
/// and 30 as the root's black right child.
#[test]
fn book_worked_example_shape() {
    let mut t = Llrb::new();
    for x in [10, 20, 30, 15, 5] {
        t.insert(x);
    }
    let black = |k| Llrb::node(Color::Black, Llrb::new(), k, Llrb::new());
    let expected = Llrb::node(
        Color::Black,
        Llrb::node(Color::Red, black(5), 10, black(15)),
        20,
        black(30),
    );
    assert_eq!(
        t, expected,
        "Sedgewick's worked example, Algorithms 4e §3.3"
    );
}

/// Pins the `move_red_right` trigger (`need_borrow` in `delete_inner`): guarding one level too
/// deep breaks black balance on this insert/delete sequence.
#[test]
fn regression_move_red_right_trigger() {
    let ops: [(bool, i32); 16] = [
        (true, 6),
        (true, 6),
        (true, -14),
        (true, 7),
        (true, -2),
        (true, -29),
        (true, 8),
        (true, 0),
        (true, 9),
        (true, -5),
        (false, -2),
        (true, 4),
        (false, -14),
        (true, 1),
        (true, -1),
        (false, 4),
    ];
    let mut t = Llrb::new();
    for (is_insert, x) in ops {
        if is_insert {
            t.insert(x);
        } else {
            t.delete(&x);
        }
        assert_valid(&t);
    }
}

// --- property tests ----------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1000))]

    /// Every node's cached `size` is the number of keys actually below it, after every step
    /// of an arbitrary insert/delete mix.
    #[test]
    fn cached_sizes_stay_consistent(
        ops in prop::collection::vec((any::<bool>(), -40..40i32), 0..200),
    ) {
        fn walked<T>(t: &Llrb<T>) -> Option<usize> {
            match t.as_node() {
                None => Some(0),
                Some(n) => {
                    let l = walked(&n.left)?;
                    let r = walked(&n.right)?;
                    (n.size == l + r + 1).then_some(n.size)
                }
            }
        }
        let mut t = Llrb::new();
        let mut model = std::collections::BTreeSet::new();
        for (is_insert, k) in ops {
            if is_insert {
                prop_assert_eq!(t.insert(k), model.insert(k));
            } else {
                prop_assert_eq!(t.delete(&k), model.remove(&k));
            }
            prop_assert!(walked(&t).is_some(), "a node's size field is wrong");
            prop_assert_eq!(t.len(), model.len());
        }
    }

    /// The property Lean actually proves (`valid_insert`): `insert` alone never violates
    /// `LeftLeaning`, `NoRedRed`, or black-balance.
    #[test]
    fn insert_only_preserves_invariants(xs in prop::collection::vec(-100..100i32, 0..300)) {
        let mut t = Llrb::new();
        for x in xs {
            t.insert(x);
            assert_valid(&t);
        }
    }

    /// `delete` preserves `LeftLeaning`, `NoRedRed` and black balance, sortedness, and exact
    /// `Mem` agreement with a `BTreeSet` model, across arbitrary interleavings with insert.
    #[test]
    fn insert_delete_preserves_invariants_and_matches_model(
        ops in prop::collection::vec(
            prop_oneof![
                (-30..30i32).prop_map(|x| (true, x)),
                (-30..30i32).prop_map(|x| (false, x)),
            ],
            0..300,
        )
    ) {
        let mut t = Llrb::new();
        let mut model: BTreeSet<i32> = BTreeSet::new();
        for (is_insert, x) in ops {
            if is_insert {
                t.insert(x);
                model.insert(x);
            } else {
                t.delete(&x);
                model.remove(&x);
            }
            assert_valid(&t);

            let mut out = Vec::new();
            in_order(&t, &mut out);
            let collected: Vec<i32> = out.into_iter().copied().collect();
            let expected: Vec<i32> = model.iter().copied().collect();
            prop_assert_eq!(&collected, &expected, "Mem/Sorted mismatch against BTreeSet model");

            for v in -30..30i32 {
                prop_assert_eq!(t.contains(&v), model.contains(&v), "contains({}) mismatch", v);
            }
        }
    }

    /// `delete_min` specifically, interleaved with inserts, checked the same way.
    #[test]
    fn insert_delete_min_preserves_invariants_and_matches_model(
        ops in prop::collection::vec(
            prop_oneof![
                2 => (-30..30i32).prop_map(Some),
                1 => Just(None),
            ],
            0..300,
        )
    ) {
        let mut t = Llrb::new();
        let mut model: BTreeSet<i32> = BTreeSet::new();
        for op in ops {
            match op {
                Some(x) => {
                    t.insert(x);
                    model.insert(x);
                }
                None => {
                    // The key comes back, and it is the minimum: on a non-empty tree
                    // `delete_min` never answers `None`, which is what the empty tree says.
                    let expected = model.iter().next().copied();
                    prop_assert_eq!(t.delete_min(), expected);
                    if let Some(m) = expected {
                        model.remove(&m);
                    }
                }
            }
            assert_valid(&t);
            let mut out = Vec::new();
            in_order(&t, &mut out);
            let collected: Vec<i32> = out.into_iter().copied().collect();
            let expected: Vec<i32> = model.iter().copied().collect();
            prop_assert_eq!(&collected, &expected);
            prop_assert_eq!(t.len(), model.len());
        }
    }

    /// Every absent key, straight into `delete_inner` with no `contains` in front: the tree
    /// keeps its keys, its count and its invariants.
    #[test]
    fn unguarded_delete_of_an_absent_key_removes_nothing(
        xs in prop::collection::btree_set(0..60i32, 0..80),
        probe in 0..60i32,
    ) {
        // Only even keys go in, so every odd probe is absent and falls between two present
        // keys or past either end.
        let mut t: Llrb<i32> = xs.iter().map(|x| x * 2).collect();
        delete_unguarded(&mut t, &(probe * 2 + 1));
        assert_valid(&t);
        let expected: Vec<i32> = xs.iter().map(|x| x * 2).collect();
        prop_assert_eq!(t.iter().copied().collect::<Vec<_>>(), expected);
        prop_assert_eq!(t.len(), xs.len());
    }
}

// ---------------------------------------------------------------------------------------
// `check_valid`: one tree per piece, breaking that piece alone.
// ---------------------------------------------------------------------------------------

fn red(l: Llrb<i32>, k: i32, r: Llrb<i32>) -> Llrb<i32> {
    Llrb::node(Color::Red, l, k, r)
}

fn black(l: Llrb<i32>, k: i32, r: Llrb<i32>) -> Llrb<i32> {
    Llrb::node(Color::Black, l, k, r)
}

#[test]
fn check_valid_names_each_piece() {
    let e = Llrb::new;
    assert_eq!((0..20).collect::<Llrb<i32>>().check_valid(), Ok(()));
    let cases = [
        // Keys out of order, colors legal.
        (black(red(e(), 2, e()), 1, e()), "invariant 1 (sorted)"),
        // A red root alone.
        (red(e(), 1, e()), "invariant 2 (root_black)"),
        // Equal black heights, but the red link leans right.
        (
            black(e(), 1, red(e(), 2, e())),
            "invariant 3 (left_leaning)",
        ),
        // Two reds in a row down the left; black height still 2 on every path.
        (
            black(red(red(e(), 1, e()), 2, e()), 3, e()),
            "invariant 4 (no_red_red)",
        ),
        // A black left child and nothing on the right.
        (
            black(black(e(), 1, e()), 2, e()),
            "invariant 5 (black_height_ok)",
        ),
    ];
    for (tree, label) in cases {
        assert_eq!(tree.check_valid(), Err(label));
        assert!(!tree.is_valid());
    }
}

proptest! {
    /// The counted entry points build the trees the plain ones build, and a no-op counts none.
    #[test]
    fn counting_changes_no_tree(ops in prop::collection::vec((any::<bool>(), 0..40u8), 0..80)) {
        let (mut plain, mut counted) = (Llrb::new(), Llrb::new());
        for (insert, key) in ops {
            if insert {
                let (added, made) = counted.insert_with_rotations(key);
                prop_assert_eq!(plain.insert(key), added);
                prop_assert!(added || made == 0);
            } else {
                let (removed, made) = counted.delete_with_rotations(&key);
                prop_assert_eq!(plain.delete(&key), removed);
                prop_assert!(removed || made == 0);
            }
            prop_assert_eq!(format!("{plain:?}"), format!("{counted:?}"));
        }
    }
}
