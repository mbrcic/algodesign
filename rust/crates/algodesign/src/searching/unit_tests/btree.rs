// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;
use std::collections::BTreeSet as StdBTreeSet;

// ---------------------------------- Unit tests ----------------------------------

/// `len` answers from the count the tree keeps, whatever that count says.
#[test]
fn len_reads_the_cached_count() {
    let mut t: BTree<i32> = (0..7).collect();
    t.len = 1_000;
    assert_eq!(t.len(), 1_000);
}

/// `is_empty` answers from the same count, and a node answers from its own shape: neither
/// walks.
#[test]
fn is_empty_reads_the_count_and_the_shape() {
    let mut t: BTree<i32> = (0..7).collect();
    assert!(!t.is_empty());
    t.len = 0;
    assert!(t.is_empty());
    let keyless_internal: Node<i32> = Node::Internal(vec![], vec![Node::Leaf(vec![])]);
    assert!(!keyless_internal.is_empty());
}

/// Every node's key buffer holds `2t - 1` keys and every internal node's child buffer `2t`
/// children, from the moment the node exists. Checked after a build and part-way through
/// draining it, at three degrees.
#[test]
fn split_born_nodes_have_full_capacity() {
    fn check<T>(node: &Node<T>, t: usize) {
        match node {
            Node::Leaf(keys) => assert!(keys.capacity() >= 2 * t - 1, "leaf capacity"),
            Node::Internal(keys, children) => {
                assert!(keys.capacity() >= 2 * t - 1, "internal key capacity");
                assert!(children.capacity() >= 2 * t, "internal child capacity");
                for c in children {
                    check(c, t);
                }
            }
        }
    }
    for t in [2, 3, 6] {
        // A fixed permutation of 0..2000 (37 is coprime to 2000).
        let keys: Vec<u32> = (0..2000u32).map(|i| (i * 37 + 11) % 2000).collect();
        let mut tree = BTree::new(t);
        for &k in &keys {
            tree.insert(k);
        }
        assert!(
            tree.height() >= 3,
            "t = {t}: deep enough to split internal nodes"
        );
        check(tree.root(), t);
        // A clone keeps it: deleting from a clone must not regrow what the original does not.
        let copy = tree.clone();
        assert_eq!(copy, tree);
        check(copy.root(), t);
        for &k in &keys[..1500] {
            tree.delete(&k);
        }
        check(tree.root(), t);
    }
}

#[test]
fn empty_tree_has_no_keys() {
    let tree: Node<i32> = Node::default();
    assert!(tree.is_empty());
    assert_eq!(tree.len(), 0);
    assert!(!tree.search(&0));
    assert!(tree.is_valid(2));
}

/// The read-only view other crates get: a leaf has no children, an internal node one more
/// child than keys, and walking it in order gives the keys in order.
#[test]
fn keys_and_children_describe_the_tree() {
    let mut tree = BTree::new(2);
    tree.extend(0..20);
    let root = tree.root();
    assert_eq!(root.children().len(), root.keys().len() + 1);
    fn walk(n: &Node<i32>, out: &mut Vec<i32>) {
        if n.children().is_empty() {
            out.extend_from_slice(n.keys());
            return;
        }
        assert_eq!(n.children().len(), n.keys().len() + 1);
        for (i, child) in n.children().iter().enumerate() {
            walk(child, out);
            if let Some(k) = n.keys().get(i) {
                out.push(*k);
            }
        }
    }
    let mut seen = Vec::new();
    walk(root, &mut seen);
    assert_eq!(seen, (0..20).collect::<Vec<_>>());
}

#[test]
fn single_insert_is_found() {
    let mut tree = Node::default();
    tree.insert_at(2, 42);
    assert_eq!(tree.len(), 1);
    assert!(tree.search(&42));
    assert!(!tree.search(&41));
    assert!(tree.is_valid(2));
}

#[test]
fn insert_exactly_2t_minus_1_keys_then_one_more_forces_a_root_split() {
    // t = 2: 2t - 1 = 3. Inserting 1, 2, 3 fills the root leaf; inserting 4 must split it.
    let mut tree = Node::default();
    for k in [1, 2, 3] {
        tree.insert_at(2, k);
    }
    assert!(
        matches!(&tree, Node::Leaf(keys) if keys.len() == 3),
        "root not yet full: {tree:?}"
    );
    tree.insert_at(2, 4);
    assert_eq!(
        tree,
        Node::Internal(vec![2], vec![Node::Leaf(vec![1]), Node::Leaf(vec![3, 4])])
    );
    for k in [1, 2, 3, 4] {
        assert!(tree.search(&k));
    }
    assert!(tree.is_valid(2));
}

/// Deleting a key that sits in an internal node, where the *right* flanking child has a spare
/// key (and the left doesn't): replaced by the in-order successor (`take_min`).
#[test]
fn delete_internal_key_with_spare_right_child_uses_successor() {
    let mut tree = Node::default();
    for k in [1, 2, 3, 4] {
        tree.insert_at(2, k);
    }
    // tree = Node([2], [Leaf([1]), Leaf([3, 4])]) — left child is minimal (1 key), right has
    // a spare (2 keys), so deleting the root's own key 2 should pull up its successor, 3.
    let found = tree.delete_at(2, &2);
    assert!(found);
    assert_eq!(
        tree,
        Node::Internal(vec![3], vec![Node::Leaf(vec![1]), Node::Leaf(vec![4])])
    );
    assert!(!tree.search(&2));
    for k in [1, 3, 4] {
        assert!(tree.search(&k));
    }
    assert!(tree.is_valid(2));
}

/// Symmetric to `delete_internal_key_with_spare_right_child_uses_successor`: the *left*
/// flanking child has a spare key, so deleting the internal key pulls up its in-order
/// predecessor (`take_max`) instead.
#[test]
fn delete_internal_key_with_spare_left_child_uses_predecessor() {
    let mut tree = Node::default();
    for k in [1, 2, 3, 4] {
        tree.insert_at(2, k);
    }
    tree.insert_at(2, 0);
    // tree = Node([2], [Leaf([0, 1]), Leaf([3, 4])]) — left child has a spare (2 keys), so
    // deleting the root's own key 2 should pull up its predecessor, 1.
    let found = tree.delete_at(2, &2);
    assert!(found);
    assert_eq!(
        tree,
        Node::Internal(vec![1], vec![Node::Leaf(vec![0]), Node::Leaf(vec![3, 4])])
    );
    assert!(!tree.search(&2));
    for k in [0, 1, 3, 4] {
        assert!(tree.search(&k));
    }
    assert!(tree.is_valid(2));
}

/// Deleting a key that isn't in the root but whose target child is minimal, while its sibling
/// has a spare key: `top_up` should borrow rather than merge.
#[test]
fn delete_forces_a_sibling_borrow() {
    let mut tree = Node::default();
    for k in [1, 2, 3, 4] {
        tree.insert_at(2, k);
    }
    // tree = Node([2], [Leaf([1]), Leaf([3, 4])]) — deleting 1 targets the minimal left
    // child; its only sibling (right) has a spare key, so this should borrow from the right.
    let found = tree.delete_at(2, &1);
    assert!(found);
    assert_eq!(
        tree,
        Node::Internal(vec![3], vec![Node::Leaf(vec![2]), Node::Leaf(vec![4])])
    );
    assert!(!tree.search(&1));
    for k in [2, 3, 4] {
        assert!(tree.search(&k));
    }
    assert!(tree.is_valid(2));
}

/// Forces a merge on delete (both children of a found key are minimal, `t - 1` keys), and
/// that merge draining the root's last key forces a root collapse.
#[test]
fn delete_forces_a_merge_and_then_a_root_collapse() {
    let mut tree = Node::default();
    for k in [1, 2, 3, 4] {
        tree.insert_at(2, k);
    }
    // tree = Node([2], [Leaf([1]), Leaf([3, 4])]).
    let found4 = tree.delete_at(2, &4);
    assert!(found4);
    // Now Node([2], [Leaf([1]), Leaf([3])]) — both children minimal (1 key each).
    assert_eq!(
        tree,
        Node::Internal(vec![2], vec![Node::Leaf(vec![1]), Node::Leaf(vec![3])])
    );
    assert!(tree.is_valid(2));

    // Deleting the root's own key 2 now must merge both children (neither has a spare key),
    // which drains the root to zero keys / one child — a root collapse.
    let found2 = tree.delete_at(2, &2);
    assert!(found2);
    assert_eq!(tree, Node::Leaf(vec![1, 3]));
    assert!(!tree.search(&2));
    assert!(tree.search(&1));
    assert!(tree.search(&3));
    assert!(tree.is_valid(2));
}

#[test]
fn delete_missing_key_is_a_no_op() {
    let mut tree = Node::default();
    for k in [1, 2, 3] {
        tree.insert_at(2, k);
    }
    let before = tree.clone();
    let found = tree.delete_at(2, &99);
    assert!(!found);
    assert_eq!(tree, before);
}

// -------------------------------- Property tests ---------------------------------

#[derive(Debug, Clone, Copy)]
enum Op {
    Insert(i32),
    Delete(i32),
}

/// Keys from a small universe, so inserts collide and deletes land on present keys.
fn op_strategy() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0..40i32).prop_map(Op::Insert),
        (0..40i32).prop_map(Op::Delete),
    ]
}

/// Runs `ops` against both a `BTree` (minimum degree `t`) and a `std::collections::BTreeSet`
/// reference model, checking after *every* op that:
/// - each piece of the Lean `Valid` holds, checked one by one so a failure names it;
/// - the in-order traversal exactly matches the model's sorted contents — BST-style ordering,
///   and `Mem`-preservation (nothing lost, nothing invented) in one check;
/// - `search` agrees with the model on every key the model actually contains, and (after a
///   delete) directly on the just-deleted key;
/// - `delete`'s reported `found` flag agrees with whether the model actually had the key.
fn run_ops_and_check(t: usize, ops: &[Op]) {
    let mut tree: Node<i32> = Node::default();
    let mut model: StdBTreeSet<i32> = StdBTreeSet::new();
    for op in ops {
        match *op {
            Op::Insert(k) => {
                tree.insert_at(t, k);
                model.insert(k);
            }
            Op::Delete(k) => {
                let found = tree.delete_at(t, &k);
                let was_present = model.remove(&k);
                assert_eq!(
                    found, was_present,
                    "delete found-flag mismatch for key {k}, t={t}"
                );
                assert!(!tree.search(&k), "deleted key {k} still found, t={t}");
            }
        }
        assert!(
            tree.is_keys_in_order(),
            "KeysInOrder violated, t={t}, tree={tree:?}"
        );
        assert!(
            tree.is_one_more_child(),
            "OneMoreChild violated, t={t}, tree={tree:?}"
        );
        assert!(
            tree.is_half_full_to_full(t),
            "HalfFullToFull violated, t={t}, tree={tree:?}"
        );
        assert!(
            tree.is_root_branches(),
            "RootBranches violated, t={t}, tree={tree:?}"
        );
        assert!(
            tree.is_same_depth(),
            "SameDepth violated, t={t}, tree={tree:?}"
        );
        assert!(tree.is_valid(t), "Valid violated, t={t}, tree={tree:?}");

        let actual: Vec<i32> = tree.in_order().into_iter().copied().collect();
        let expected: Vec<i32> = model.iter().copied().collect();
        assert_eq!(
            actual, expected,
            "in-order/Mem-preservation mismatch, t={t}"
        );

        for k in &model {
            assert!(tree.search(k), "search missed present key {k}, t={t}");
        }
    }
}

/// The same random mix through the container ([`BTree::insert`], [`BTree::delete`]), so the
/// count `BTree` keeps is checked after every operation, as is each reported `bool`. Unlike
/// [`run_ops_and_check`], which drives a bare [`Node`].
fn run_container_ops_and_check(t: usize, ops: &[Op]) {
    let mut tree: BTree<i32> = BTree::new(t);
    let mut model: StdBTreeSet<i32> = StdBTreeSet::new();
    for op in ops {
        match *op {
            Op::Insert(k) => {
                assert_eq!(
                    tree.insert(k),
                    model.insert(k),
                    "insert({k}) reported wrong, t={t}"
                );
            }
            Op::Delete(k) => {
                assert_eq!(
                    tree.delete(&k),
                    model.remove(&k),
                    "delete({k}) reported wrong, t={t}"
                );
            }
        }
        assert_eq!(
            tree.len(),
            model.len(),
            "cached len diverged after {op:?}, t={t}"
        );
        assert_eq!(
            tree.is_empty(),
            model.is_empty(),
            "is_empty after {op:?}, t={t}"
        );
        assert!(tree.is_valid(), "invariants violated after {op:?}, t={t}");
        assert!(
            tree.iter().eq(model.iter()),
            "contents diverged after {op:?}, t={t}"
        );
    }
}

/// Inserts `0..n` (in an order permuted by `insert_priorities`, via a stable sort — see
/// below) into an empty tree, then deletes all of them (in a *different* order, permuted by
/// `delete_priorities`), checking `Valid` and `search`/`Mem`-agreement after every single
/// operation. This builds a deep tree and fully unwinds it, so every split, borrow, merge and
/// collapse path runs, including the internal-node arms of
/// [`take_max`]/[`take_min`]/[`merge_at`].
fn fill_then_drain_check(t: usize, n: usize, insert_priorities: &[u32], delete_priorities: &[u32]) {
    let mut insert_order: Vec<i32> = (0..n as i32).collect();
    insert_order.sort_by_key(|&k| insert_priorities[k as usize % insert_priorities.len()]);
    let mut delete_order: Vec<i32> = (0..n as i32).collect();
    delete_order.sort_by_key(|&k| delete_priorities[k as usize % delete_priorities.len()]);

    let mut tree: Node<i32> = Node::default();
    for &k in &insert_order {
        tree.insert_at(t, k);
        assert!(
            tree.is_valid(t),
            "Valid violated during fill, t={t}, key={k}"
        );
    }
    assert_eq!(tree.len(), n);
    for k in &insert_order {
        assert!(
            tree.search(k),
            "search missed key {k} right after fill, t={t}"
        );
    }

    for &k in &delete_order {
        let found = tree.delete_at(t, &k);
        assert!(found, "expected key {k} present during drain, t={t}");
        assert!(!tree.search(&k), "key {k} still found after delete, t={t}");
        assert!(
            tree.is_valid(t),
            "Valid violated during drain, t={t}, key={k}"
        );
    }
    assert!(
        tree.is_empty(),
        "tree not empty after draining all keys, t={t}"
    );
    assert_eq!(tree, Node::Leaf(Vec::new()));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    // One named test per minimum degree, so a failure names its `t`.

    #[test]
    fn invariants_hold_across_ops_degree_2(ops in prop::collection::vec(op_strategy(), 0..200)) {
        run_ops_and_check(2, &ops);
    }

    #[test]
    fn invariants_hold_across_ops_degree_3(ops in prop::collection::vec(op_strategy(), 0..200)) {
        run_ops_and_check(3, &ops);
    }

    #[test]
    fn invariants_hold_across_ops_degree_5(ops in prop::collection::vec(op_strategy(), 0..200)) {
        run_ops_and_check(5, &ops);
    }

    #[test]
    fn container_len_tracks_a_model_across_ops(
        t in 2usize..=5,
        ops in prop::collection::vec(op_strategy(), 0..200),
    ) {
        run_container_ops_and_check(t, &ops);
    }

    /// Insert-only sequences, across a wider range of degrees and a larger key universe.
    #[test]
    fn insert_only_preserves_invariants(
        t in 2usize..=8,
        keys in prop::collection::vec(any::<i32>(), 0..300),
    ) {
        let mut tree: Node<i32> = Node::default();
        for k in keys {
            tree.insert_at(t, k);
            prop_assert!(tree.is_valid(t), "Valid violated after insert, t={t}");
        }
    }

    // Fill-then-drain builds a deep tree; fewer cases, since each does `O(n)` operations.

    #[test]
    fn fill_then_drain_preserves_invariants_degree_2(
        n in 20usize..250,
        insert_priorities in prop::collection::vec(any::<u32>(), 1..64),
        delete_priorities in prop::collection::vec(any::<u32>(), 1..64),
    ) {
        fill_then_drain_check(2, n, &insert_priorities, &delete_priorities);
    }

    #[test]
    fn fill_then_drain_preserves_invariants_degree_3(
        n in 20usize..250,
        insert_priorities in prop::collection::vec(any::<u32>(), 1..64),
        delete_priorities in prop::collection::vec(any::<u32>(), 1..64),
    ) {
        fill_then_drain_check(3, n, &insert_priorities, &delete_priorities);
    }

    #[test]
    fn fill_then_drain_preserves_invariants_degree_5(
        n in 50usize..300,
        insert_priorities in prop::collection::vec(any::<u32>(), 1..64),
        delete_priorities in prop::collection::vec(any::<u32>(), 1..64),
    ) {
        fill_then_drain_check(5, n, &insert_priorities, &delete_priorities);
    }
}

// The container API: the degree belongs to the tree, and the standard traits work because of
// it.
#[test]
fn the_tree_remembers_its_own_degree() {
    let mut t = BTree::new(4);
    assert_eq!(t.degree(), 4);
    for k in 0..50 {
        assert!(t.insert(k));
    }
    assert!(!t.insert(7), "a duplicate is not new");
    assert_eq!(t.degree(), 4, "an insertion cannot change the degree");
    assert!(t.is_valid());
    assert!(t.delete(&7));
    assert!(!t.delete(&7));
    assert!(t.is_valid(), "still valid after a deletion");
    assert_eq!(t.len(), 49);
}

#[test]
fn collects_and_extends() {
    let built: BTree<i32> = (0..40).collect();
    assert_eq!(built.degree(), DEFAULT_DEGREE);
    assert_eq!(
        built.in_order().into_iter().copied().collect::<Vec<_>>(),
        (0..40).collect::<Vec<_>>()
    );
    assert!(built.is_valid());

    let mut wide = BTree::new(16);
    wide.extend(0..40);
    assert_eq!(
        wide.degree(),
        16,
        "extend preserves the degree it was built with"
    );
    assert!(wide.is_valid());
    assert_eq!(
        wide.iter().copied().collect::<Vec<_>>(),
        built.iter().copied().collect::<Vec<_>>()
    );
}

#[test]
fn an_empty_tree_is_empty_at_any_degree() {
    for t in 2..8 {
        let tree: BTree<i32> = BTree::new(t);
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.height(), 0);
        assert!(tree.iter().next().is_none());
    }
}

#[test]
#[should_panic(expected = "minimum degree t must be at least 2")]
fn degree_one_is_rejected_at_construction() {
    let _: BTree<i32> = BTree::new(1);
}

/// Each piece's verdict, in the Lean order, then the degree and `is_valid`.
fn verdicts(tree: &Node<i32>, t: usize) -> [bool; 7] {
    [
        tree.is_keys_in_order(),
        tree.is_one_more_child(),
        tree.is_half_full_to_full(t),
        tree.is_root_branches(),
        tree.is_same_depth(),
        t >= 2,
        tree.is_valid(t),
    ]
}

/// Every piece accepts a legal tree, and each hand-built tree below breaks exactly one piece: that
/// piece and `is_valid` reject it, every other piece accepts it, and none panics. A piece that
/// rejected everything, or a missing conjunct in `is_valid`, would fail here.
#[test]
fn each_piece_rejects_the_tree_that_breaks_it_and_only_that() {
    use Node::{Internal as N, Leaf as L};
    let built: BTree<i32> = (0..40).collect();
    let legal = [
        (L(vec![]), 2),
        (N(vec![5], vec![L(vec![1]), L(vec![7])]), 2),
        (N(vec![4], vec![L(vec![1, 2, 3]), L(vec![5, 6, 7])]), 2),
        (built.root().clone(), built.degree()),
    ];
    for (tree, t) in &legal {
        assert_eq!(verdicts(tree, *t), [true; 7], "{tree:?}");
    }
    // (the piece it breaks, in `verdicts` order, the tree, its degree)
    let broken = [
        (0, L(vec![2, 1]), 2),
        (0, L(vec![3, 3]), 2),
        // 12 is right of its parent's 5 but left of the root's 10.
        (
            0,
            N(
                vec![10],
                vec![
                    N(vec![5], vec![L(vec![1]), L(vec![12])]),
                    N(vec![15], vec![L(vec![11]), L(vec![20])]),
                ],
            ),
            2,
        ),
        (1, N(vec![5], vec![L(vec![1]), L(vec![7]), L(vec![9])]), 2),
        (1, N(vec![3, 5], vec![L(vec![1]), L(vec![4])]), 2),
        (2, L(vec![1, 2, 3, 4]), 2),
        (2, N(vec![5], vec![L(vec![1, 2]), L(vec![7])]), 3),
        (3, N(vec![], vec![L(vec![1])]), 2),
        (
            4,
            N(
                vec![5],
                vec![L(vec![1]), N(vec![7], vec![L(vec![6]), L(vec![8])])],
            ),
            2,
        ),
        (5, L(vec![1]), 1),
        (5, L(vec![]), 0),
    ];
    for (piece, tree, t) in &broken {
        let mut expected = [true; 7];
        expected[*piece] = false;
        expected[6] = false;
        assert_eq!(verdicts(tree, *t), expected, "{tree:?}, t={t}");
    }
}

// ---------------------------------------------------------------------------------------
// `check_valid`: one tree per piece, breaking that piece alone.
// ---------------------------------------------------------------------------------------

#[test]
fn check_valid_names_each_piece() {
    let leaf = |ks: &[i32]| Node::Leaf(ks.to_vec());
    let node = |ks: &[i32], cs: Vec<Node<i32>>| Node::Internal(ks.to_vec(), cs);
    assert_eq!((0..50).collect::<BTree<i32>>().check_valid(), Ok(()));
    let cases = [
        (leaf(&[2, 1]), 2, "invariant 1 (keys_in_order)"),
        (
            node(&[2], vec![leaf(&[1])]),
            2,
            "invariant 2 (one_more_child)",
        ),
        (leaf(&[1, 2, 3, 4]), 2, "invariant 3 (half_full_to_full)"),
        (
            node(&[], vec![leaf(&[1])]),
            2,
            "invariant 4 (root_branches)",
        ),
        (
            node(
                &[3],
                vec![node(&[1], vec![leaf(&[0]), leaf(&[2])]), leaf(&[4])],
            ),
            2,
            "invariant 5 (same_depth)",
        ),
        (leaf(&[]), 1, "not in the box (degree_at_least_two)"),
    ];
    for (tree, t, label) in cases {
        assert_eq!(tree.check_valid(t), Err(label));
        assert!(!tree.is_valid(t));
    }
}
