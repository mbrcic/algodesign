// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::collections::BTreeSet;

/// `len` answers from the root's cached count, so it answers whatever that count says; a
/// walk would find the real 7.
#[test]
fn len_reads_the_cached_count() {
    let mut t: RbTree<i32> = (0..7).collect();
    t.0.as_mut().expect("non-empty").size = 1_000;
    assert_eq!(t.len(), 1_000);
}

#[test]
fn empty_tree() {
    let t: RbTree<i32> = RbTree::new();
    assert!(t.is_empty());
    assert!(!t.contains(&0));
    assert_eq!(t.get(&0), None);
    assert!(t.check_valid().is_ok());
}

#[test]
fn single_insert() {
    let t = RbTree::from_iter([5]);
    assert!(t.contains(&5));
    assert!(!t.contains(&6));
    assert!(t.is_root_black());
    assert!(t.check_valid().is_ok());
}

#[test]
fn duplicate_insert_is_noop() {
    let t = RbTree::from_iter([5, 5, 5]);
    assert_eq!(t.in_order(), vec![&5]);
    assert!(t.check_valid().is_ok());
}

#[test]
fn delete_only_key() {
    let mut t = RbTree::from_iter([5]);
    t.delete(&5);
    assert!(!t.contains(&5));
    assert!(t.is_empty());
    assert!(t.check_valid().is_ok());
}

#[test]
fn delete_missing_key_is_noop() {
    let mut t = RbTree::from_iter([1, 2, 3]);
    let expected: Vec<i32> = t.in_order().into_iter().copied().collect();
    t.delete(&42);
    let actual: Vec<i32> = t.in_order().into_iter().copied().collect();
    assert_eq!(actual, expected);
    assert!(t.check_valid().is_ok());
}

#[test]
fn delete_empty_tree_is_noop() {
    let mut t: RbTree<i32> = RbTree::new();
    t.delete(&0);
    assert!(t.is_empty());
}

#[test]
fn delete_root_repeatedly() {
    let mut t = RbTree::new();
    for k in [10, 5, 15, 3, 7, 12, 20] {
        t.insert(k);
    }
    assert!(t.check_valid().is_ok());
    // Delete whatever key sits at the root, until empty: roots with zero, one and two children.
    while let Some(root_key) = t.as_node().map(|n| n.key) {
        t.delete(&root_key);
        assert!(!t.contains(&root_key));
        assert!(t.check_valid().is_ok(), "{:?}", t.check_valid());
    }
    assert!(t.is_empty());
}

#[test]
fn delete_leaf_node() {
    let mut t = RbTree::new();
    for k in [10, 5, 15] {
        t.insert(k);
    }
    t.delete(&5);
    assert!(!t.contains(&5));
    assert!(t.contains(&10));
    assert!(t.contains(&15));
    assert!(t.check_valid().is_ok());
}

#[test]
fn delete_two_child_node() {
    let mut t = RbTree::new();
    for k in [10, 5, 15, 3, 7, 12, 20] {
        t.insert(k);
    }
    t.delete(&10); // the root, which has two children in this shape
    assert!(!t.contains(&10));
    for k in [5, 15, 3, 7, 12, 20] {
        assert!(t.contains(&k));
    }
    assert!(t.check_valid().is_ok());
}

/// Tiny xorshift64 PRNG for a reproducible large stress sequence.
struct Xorshift(u64);

impl Xorshift {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn next_below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }
}

/// Insert/delete a large random sequence, checking all five CLRS color properties (via
/// `check_valid`, which is `Sorted` + `RootBlack` + `NoRedRed` + `BlackHeightOk`) and
/// `Mem`-preservation against a `BTreeSet` reference model after **every single operation**,
/// not just at the end. Also tracks the rotation count of every single insert/delete (via
/// `insert_with_rotations`/`delete_with_rotations`) and asserts CLRS's stated bounds (<=2 insert, <=3
/// delete) are never exceeded -- and, since a bound that's never *attained* would mean the
/// instrumentation itself might not be wired up correctly, also asserts both bounds are
/// actually reached at least once over the 5000-step sequence (a 500-key keyspace is small
/// enough, relative to 5000 ops, that both worst cases are expected to occur).
#[test]
fn stress_random_sequence_validated_after_every_op() {
    let mut rng = Xorshift(0x9E3779B97F4A7C15);
    let mut tree: RbTree<i32> = RbTree::new();
    let mut model: BTreeSet<i32> = BTreeSet::new();
    let mut max_insert_rotations = 0usize;
    let mut max_delete_rotations = 0usize;

    for step in 0..5_000 {
        let delete_known = !model.is_empty() && rng.next_below(3) == 0;
        if delete_known {
            let idx = rng.next_below(model.len() as u64) as usize;
            let key = *model.iter().nth(idx).unwrap();
            let (_, rotations) = tree.delete_with_rotations(&key);
            assert!(
                rotations <= 3,
                "step {step}: delete did {rotations} rotations (> 3)"
            );
            max_delete_rotations = max_delete_rotations.max(rotations);
            model.remove(&key);
        } else {
            let key = rng.next_below(500) as i32;
            if rng.next_below(3) == 0 {
                let (_, rotations) = tree.delete_with_rotations(&key);
                assert!(
                    rotations <= 3,
                    "step {step}: delete did {rotations} rotations (> 3)"
                );
                max_delete_rotations = max_delete_rotations.max(rotations);
                model.remove(&key);
            } else {
                let (_, rotations) = tree.insert_with_rotations(key);
                assert!(
                    rotations <= 2,
                    "step {step}: insert did {rotations} rotations (> 2)"
                );
                max_insert_rotations = max_insert_rotations.max(rotations);
                model.insert(key);
            }
        }

        assert!(
            tree.check_valid().is_ok(),
            "step {step}: {:?}",
            tree.check_valid()
        );
        let tree_keys: Vec<i32> = tree.in_order().into_iter().copied().collect();
        let model_keys: Vec<i32> = model.iter().copied().collect();
        assert_eq!(tree_keys, model_keys, "step {step}: Mem mismatch");
    }

    // CLRS's bounds are known to be tight: over 5000 ops on a 500-key space, both worst cases
    // should actually occur. If either is short of its bound, either the fixup logic is more
    // conservative than CLRS's worst case (unlikely, given the case-by-case derivation) or the
    // rotation-counting instrumentation itself isn't firing correctly -- either way, worth
    // knowing rather than silently passing on a vacuous "<=" check.
    assert_eq!(
        max_insert_rotations, 2,
        "expected an insert to attain CLRS's tight bound of 2 rotations somewhere in this run"
    );
    assert_eq!(
        max_delete_rotations, 3,
        "expected a delete to attain CLRS's tight bound of 3 rotations somewhere in this run"
    );
}

fn op_strategy() -> impl proptest::strategy::Strategy<Value = Op> {
    use proptest::prelude::*;
    prop_oneof![
        (0..64i32).prop_map(Op::Insert),
        (0..64i32).prop_map(Op::Delete),
    ]
}

#[derive(Debug, Clone, Copy)]
enum Op {
    Insert(i32),
    Delete(i32),
}

proptest::proptest! {
    /// Every node's cached `size` is the number of keys actually below it, after every step
    /// of an arbitrary insert/delete mix. `len()` cannot police the field it reads, so this is the
    /// check that can see the cache lie.
    #[test]
    fn cached_sizes_stay_consistent(
        ops in proptest::collection::vec((proptest::prelude::any::<bool>(), -40..40i32), 0..200),
    ) {
        fn walked<T>(t: &RbTree<T>) -> Option<usize> {
            match t.as_node() {
                None => Some(0),
                Some(n) => {
                    let l = walked(&n.left)?;
                    let r = walked(&n.right)?;
                    (n.size == l + r + 1).then_some(n.size)
                }
            }
        }
        let mut t = RbTree::new();
        let mut model = std::collections::BTreeSet::new();
        for (is_insert, k) in ops {
            if is_insert {
                proptest::prop_assert_eq!(t.insert(k), model.insert(k));
            } else {
                proptest::prop_assert_eq!(t.delete(&k), model.remove(&k));
            }
            proptest::prop_assert!(walked(&t).is_some(), "a node's size field is wrong");
            proptest::prop_assert_eq!(t.len(), model.len());
        }
    }

    /// CLRS's five color properties, `Mem`-preservation, and the ≤2 (insert) / ≤3 (delete)
    /// rotation-count bounds, all checked after every operation in a random insert/delete
    /// sequence -- not just at the end.
    #[test]
    fn five_properties_and_rotation_bounds_after_every_op(
        ops in proptest::collection::vec(op_strategy(), 0..200)
    ) {
        let mut tree: RbTree<i32> = RbTree::new();
        let mut model: BTreeSet<i32> = BTreeSet::new();

        for op in ops {
            match op {
                Op::Insert(x) => {
                    let (_, rotations) = tree.insert_with_rotations(x);
                    proptest::prop_assert!(
                        rotations <= 2,
                        "insert performed {} rotations (CLRS bound is <= 2)",
                        rotations
                    );
                    model.insert(x);
                }
                Op::Delete(x) => {
                    let (_, rotations) = tree.delete_with_rotations(&x);
                    proptest::prop_assert!(
                        rotations <= 3,
                        "delete performed {} rotations (CLRS bound is <= 3)",
                        rotations
                    );
                    model.remove(&x);
                }
            }

            proptest::prop_assert!(tree.check_valid().is_ok(), "{:?}", tree.check_valid());
            let tree_keys: Vec<i32> = tree.in_order().into_iter().copied().collect();
            let model_keys: Vec<i32> = model.iter().copied().collect();
            proptest::prop_assert_eq!(tree_keys, model_keys, "Mem mismatch");
        }
    }
}

proptest::proptest! {
    /// The counted entry points build the trees the plain ones build, and a no-op counts none.
    #[test]
    fn counting_changes_no_tree(
        ops in proptest::collection::vec((proptest::bool::ANY, 0..40u8), 0..80)
    ) {
        let (mut plain, mut counted) = (RbTree::new(), RbTree::new());
        for (insert, key) in ops {
            if insert {
                let (added, made) = counted.insert_with_rotations(key);
                proptest::prop_assert_eq!(plain.insert(key), added);
                proptest::prop_assert!(added || made == 0);
            } else {
                let (removed, made) = counted.delete_with_rotations(&key);
                proptest::prop_assert_eq!(plain.delete(&key), removed);
                proptest::prop_assert!(removed || made == 0);
            }
            proptest::prop_assert_eq!(format!("{plain:?}"), format!("{counted:?}"));
        }
    }
}
