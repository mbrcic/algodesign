// SPDX-License-Identifier: Apache-2.0
use std::collections::BTreeMap;

use proptest::prelude::*;

use super::*;
use crate::strings::trie::Trie;

proptest! {
    /// Inserts (duplicates included) against `Trie` and `BTreeMap`, `is_valid` after every one.
    /// Lean: `valid_insertSorted`, `insertSpec`, `words_ofTrie`.
    #[test]
    fn matches_a_trie_and_a_btreemap_while_staying_valid(
        keys in prop::collection::vec(prop::collection::vec(0u8..3, 0..6), 0..30),
        probes in prop::collection::vec(prop::collection::vec(0u8..3, 0..7), 1..10),
    ) {
        let mut pat = Patricia::new();
        let mut trie = Trie::new();
        let mut map: BTreeMap<Vec<u8>, usize> = BTreeMap::new();
        for (i, k) in keys.iter().enumerate() {
            let old = map.insert(k.clone(), i);
            prop_assert_eq!(pat.insert(k, i), old);
            prop_assert_eq!(trie.insert(k, i), old);
            prop_assert!(pat.is_valid()); // Lean: valid_insertSorted
            prop_assert_eq!(pat.len(), map.len());
            prop_assert_eq!(pat.len(), trie.len());
        }

        for q in probes.iter().chain(keys.iter()) {
            prop_assert_eq!(pat.get(q), map.get(q.as_slice())); // Lean: insertSpec_insertSorted
            prop_assert_eq!(pat.get(q), trie.get(q));

            let longest = map
                .keys()
                .filter(|k| q.starts_with(k))
                .max_by_key(|k| k.len())
                .map(|k| &q[..k.len()]);
            // Lean: longestPrefix_eq_some_iff, longestPrefix_eq_none_iff.
            prop_assert_eq!(pat.longest_prefix(q), longest);
            prop_assert_eq!(pat.longest_prefix(q), trie.longest_prefix(q));

            for cut in 0..=q.len() {
                let p = &q[..cut];
                let mut mine = pat.keys_with_prefix(p);
                let mut theirs = trie.keys_with_prefix(p);
                let mut oracle: Vec<Vec<u8>> =
                    map.keys().filter(|k| k.starts_with(p)).cloned().collect();
                mine.sort();
                theirs.sort();
                oracle.sort();
                prop_assert_eq!(&mine, &oracle); // Lean: words_ofTrie
                prop_assert_eq!(&mine, &theirs);
                let pairs: Vec<(Vec<u8>, usize)> =
                    pat.iter_with_prefix(p).map(|(k, v)| (k, *v)).collect();
                let want: Vec<(Vec<u8>, usize)> = map
                    .iter()
                    .filter(|(k, _)| k.starts_with(p))
                    .map(|(k, v)| (k.clone(), *v))
                    .collect();
                // Lean: keysWithPrefix_sorted.
                prop_assert_eq!(pairs, want);
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Op {
    Insert(Vec<u8>, u32),
    Remove(Vec<u8>),
}

fn op() -> impl Strategy<Value = Op> {
    let key = || prop::collection::vec(0u8..3, 0..6);
    prop_oneof![
        3 => (key(), any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
        2 => key().prop_map(Op::Remove),
    ]
}

proptest! {
    /// Inserts and removes mixed, against a `BTreeMap`; answers, pairs, shape and node count
    /// (against a fresh rebuild) checked after every operation.
    #[test]
    fn insert_and_remove_keep_the_shape(ops in prop::collection::vec(op(), 0..60)) {
        let mut pat = Patricia::new();
        let mut map: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
        for op in &ops {
            match op {
                Op::Insert(k, v) => prop_assert_eq!(pat.insert(k, *v), map.insert(k.clone(), *v)),
                Op::Remove(k) => prop_assert_eq!(pat.remove(k), map.remove(k)),
            }
            prop_assert_eq!(pat.len(), map.len(), "cached len diverged after {:?}", op);
            prop_assert!(
                pat.is_branches_unless_word_ends() && pat.is_no_empty_branches(),
                "box lines 3 and 4 broken after {:?}",
                op
            );
            // Lean: `valid_insertSorted`, `valid_remove`, `sortedHeads_remove`.
            prop_assert!(pat.is_valid(), "invalid after {:?}", op);
            let pairs: Vec<(Vec<u8>, u32)> = pat.iter().map(|(k, v)| (k, *v)).collect();
            let model: Vec<(Vec<u8>, u32)> =
                map.iter().map(|(k, v)| (k.clone(), *v)).collect();
            // Lean: words_remove.
            prop_assert_eq!(pairs, model);
            let rebuilt: Patricia<u32> = map.iter().map(|(k, v)| (k.as_slice(), *v)).collect();
            prop_assert_eq!(pat.node_count(), rebuilt.node_count(), "shape after {:?}", op);
        }
        for op in &ops {
            let (Op::Insert(k, _) | Op::Remove(k)) = op;
            // Lean: insertSpec_insertSorted, get_remove, get_remove_other.
            prop_assert_eq!(pat.get(k), map.get(k));
        }
    }
}

/// Removing a leaf that leaves its parent valueless with one child merges the parent.
#[test]
fn removing_a_leaf_re_collapses_its_parent() {
    let mut p = Patricia::new();
    for (i, w) in [&b"analogy"[..], b"analysis", b"an"]
        .into_iter()
        .enumerate()
    {
        p.insert(w, i);
    }
    // root -> "an"(2) -> "al" -> {"ogy"(0), "ysis"(1)}
    assert_eq!(p.node_count(), 5);
    assert_eq!(p.remove(b"analysis"), Some(1));
    // root -> "an"(2) -> "alogy"(0): the "al" branch point is gone.
    assert_eq!(p.node_count(), 3);
    assert!(p.is_branches_unless_word_ends() && p.is_no_empty_branches());
    assert!(p.is_valid());
    assert_eq!(p.get(b"analogy"), Some(&0));
    assert_eq!(p.keys_with_prefix(b"anal"), vec![b"analogy".to_vec()]);
}

/// Removing a key at a node with one child merges that node into its child.
#[test]
fn removing_an_inner_key_merges_its_node_into_the_only_child() {
    let mut p = Patricia::new();
    p.insert(b"ab", 0);
    p.insert(b"abcd", 1);
    assert_eq!(p.node_count(), 3);
    assert_eq!(p.remove(b"ab"), Some(0));
    assert_eq!(p.node_count(), 2);
    assert!(p.is_branches_unless_word_ends() && p.is_no_empty_branches());
    assert!(p.is_valid());
    assert_eq!(p.get(b"abcd"), Some(&1));
    assert_eq!(p.remove(b"abc"), None); // inside a label: nothing changes
    assert_eq!(p.remove(b"abcd"), Some(1));
    assert_eq!((p.len(), p.node_count()), (0, 1));
}

/// The root stays, valueless with one child, when that is what is left.
#[test]
fn remove_leaves_the_root_alone() {
    let mut p = Patricia::new();
    p.insert(b"", 0);
    p.insert(b"xy", 1);
    assert_eq!(p.remove(b""), Some(0));
    assert_eq!(p.node_count(), 2);
    assert!(p.is_valid());
    assert_eq!(p.remove(b""), None);
}

/// `len` reads the kept count, not a walk.
#[test]
fn len_reads_the_cached_count() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    p.insert(b"shells", 1);
    p.insert(b"sea", 2);
    p.len = 1_000;
    assert_eq!(p.len(), 1_000);
    assert_eq!(p.iter().count(), 3);
    p.len = 0;
    assert!(p.is_empty());
}

/// `Eq`, `Extend` and `FromIterator`: a later pair overwrites.
#[test]
fn collect_and_extend_insert_in_turn() {
    let mut p: Patricia<i32> = [(&b"she"[..], 0), (b"sea", 1), (b"she", 2)]
        .into_iter()
        .collect();
    assert_eq!(p.len(), 2);
    assert_eq!(p.get(b"she"), Some(&2));
    p.extend(vec![(b"shells".to_vec(), 3)]);
    let mut by_hand = Patricia::new();
    by_hand.insert(b"sea", 1);
    by_hand.insert(b"she", 2);
    by_hand.insert(b"shells", 3);
    assert_eq!(p, by_hand);
    assert!(p.is_valid());
    fn is_eq<T: Eq>(_: &T) {}
    is_eq(&p);
}

#[test]
fn same_keys_fewer_nodes_than_the_trie() {
    let words: [&[u8]; 5] = [b"she", b"shells", b"sea", b"shore", b"seashore"];
    let mut trie = Trie::new();
    let mut pat = Patricia::new();
    for (i, w) in words.iter().enumerate() {
        trie.insert(w, i);
        pat.insert(w, i);
    }
    let mut a: Vec<Vec<u8>> = trie.keys_with_prefix(b"");
    let mut b: Vec<Vec<u8>> = pat.keys_with_prefix(b"");
    a.sort();
    b.sort();
    assert_eq!(a, b); // Lean: words_ofTrie
    assert!(pat.node_count() < trie.node_count()); // compression's measurement
}

#[test]
fn no_valueless_single_child_chain_survives() {
    let mut pat = Patricia::new();
    for w in [b"romane".as_slice(), b"romanus", b"romulus"] {
        pat.insert(w, 0);
    }
    assert!(pat.is_branches_unless_word_ends()); // Lean: branchesUnlessWordEnds_insert
}

#[test]
fn root_with_one_child_is_valid() {
    // A single key: a valueless root with one child, which box line 3 exempts.
    let mut pat = Patricia::new();
    pat.insert(b"abc", 0);
    assert_eq!(pat.node_count(), 2); // root + one leaf, no chain
    assert!(pat.is_valid());
}

#[test]
fn below_root_valueless_single_child_chain_breaks_branches_unless_word_ends() {
    let leaf = Node {
        label: b"b".to_vec().into_boxed_slice(),
        value: Some(1),
        children: Vec::new(),
    };
    let chain = Node {
        label: b"a".to_vec().into_boxed_slice(),
        value: None,
        children: vec![(b'b', Box::new(leaf))],
    };
    let root = Node {
        label: Box::new([]),
        value: None,
        children: vec![(b'a', Box::new(chain))],
    };
    let pat = Patricia { root, len: 1 };
    assert!(!pat.is_branches_unless_word_ends());
}

#[test]
fn an_empty_edge_label_below_the_root_breaks_no_empty_branches() {
    // Two children, so only the empty-label check can reject it.
    let leaf_x = Node {
        label: b"x".to_vec().into_boxed_slice(),
        value: Some(1),
        children: Vec::new(),
    };
    let leaf_y = Node {
        label: b"y".to_vec().into_boxed_slice(),
        value: Some(2),
        children: Vec::new(),
    };
    let bad = Node {
        label: Box::new([]), // empty: the invariant this test violates
        value: None,
        children: vec![(b'x', Box::new(leaf_x)), (b'y', Box::new(leaf_y))],
    };
    let root = Node {
        label: Box::new([]),
        value: None,
        // An empty label has no head byte; `b'a'` is an arbitrary tag.
        children: vec![(b'a', Box::new(bad))],
    };
    let pat = Patricia { root, len: 2 };
    assert!(!pat.is_no_empty_branches());
}

#[test]
fn stores_and_retrieves() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    p.insert(b"shells", 1);
    p.insert(b"sea", 2);
    assert_eq!(p.get(b"shells"), Some(&1));
    assert_eq!(p.get(b"shell"), None);
    assert_eq!(p.keys_with_prefix(b"sh").len(), 2);
    assert_eq!(p.longest_prefix(b"shellsort"), Some(&b"shells"[..]));
    assert!(p.is_valid());
}

#[test]
fn keys_with_prefix_can_land_inside_an_edge_label() {
    let mut p = Patricia::new();
    p.insert(b"romane", 0);
    p.insert(b"romanus", 1);
    p.insert(b"romulus", 2);
    // "rom" ends strictly inside the "rom" edge (shared by all three), not at a node.
    let mut got = p.keys_with_prefix(b"rom");
    got.sort();
    let mut want = vec![b"romane".to_vec(), b"romanus".to_vec(), b"romulus".to_vec()];
    want.sort();
    assert_eq!(got, want);
    // "roma" ends strictly inside the edge leading to the romane/romanus split.
    let mut got2 = p.keys_with_prefix(b"roma");
    got2.sort();
    let mut want2 = vec![b"romane".to_vec(), b"romanus".to_vec()];
    want2.sort();
    assert_eq!(got2, want2);
}

#[test]
fn inserting_a_proper_prefix_of_an_existing_key_splits_exactly_at_the_label_end() {
    // `insert`'s `common == rest.len()` arm: "shell" splits the "lls" leaf edge into a valued
    // "ll" node with an "s" leaf.
    let mut p = Patricia::new();
    for (i, w) in [b"she".as_slice(), b"shells", b"sea", b"shore", b"seashore"]
        .iter()
        .enumerate()
    {
        p.insert(w, i);
    }
    let before = p.node_count();
    p.insert(b"shell", 99);
    assert_eq!(p.get(b"shells"), Some(&1)); // untouched by the split
    assert_eq!(p.get(b"shell"), Some(&99)); // the new, shorter key
    assert!(p.is_valid()); // the arm's whole point: the split stays valid
    assert_eq!(p.node_count(), before + 1);
}

#[test]
fn empty_patricia_has_no_keys_and_a_root_only_node_count() {
    let p: Patricia<u8> = Patricia::new();
    assert!(p.is_empty());
    assert_eq!(p.len(), 0);
    assert_eq!(p.node_count(), 1);
    assert_eq!(p.get(b""), None);
    assert_eq!(p.get(b"x"), None);
    assert_eq!(p.longest_prefix(b"x"), None);
    assert!(p.keys_with_prefix(b"").is_empty());
    assert!(p.is_valid());
}

#[test]
fn insert_overwrite_returns_the_old_value_and_does_not_grow_len() {
    let mut p = Patricia::new();
    assert_eq!(p.insert(b"a", 1), None);
    assert_eq!(p.len(), 1);
    assert_eq!(p.insert(b"a", 2), Some(1));
    assert_eq!(p.len(), 1);
    assert_eq!(p.get(b"a"), Some(&2));
}

#[test]
fn empty_key_is_a_valid_key() {
    let mut p = Patricia::new();
    assert_eq!(p.insert(b"", 7), None);
    assert_eq!(p.get(b""), Some(&7));
    assert_eq!(p.longest_prefix(b"anything"), Some(&b""[..]));
}

#[test]
fn keys_with_prefix_of_an_absent_path_is_empty() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    assert!(p.keys_with_prefix(b"zz").is_empty());
    assert!(p.keys_with_prefix(b"sheer").is_empty());
}

#[test]
fn iter_yields_every_stored_pair_exactly_once() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    p.insert(b"shells", 1);
    p.insert(b"sea", 2);
    let mut got: Vec<(Vec<u8>, i32)> = p.iter().map(|(k, v)| (k, *v)).collect();
    got.sort();
    let mut want = vec![
        (b"she".to_vec(), 0),
        (b"shells".to_vec(), 1),
        (b"sea".to_vec(), 2),
    ];
    want.sort();
    assert_eq!(got, want);
    assert_eq!(p.iter().count(), p.len());
}

#[test]
fn node_count_is_bounded_by_twice_len() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    p.insert(b"shells", 1);
    p.insert(b"sea", 2);
    // At most `n` leaves, `n - 1` branching nodes and the root.
    assert!(p.node_count() <= 2 * p.len());
}

#[test]
fn clone_is_equal_and_independent() {
    let mut p = Patricia::new();
    p.insert(b"she", 0);
    p.insert(b"shells", 1);
    let mut copy = p.clone();
    assert_eq!(p, copy);
    copy.insert(b"sea", 2);
    assert_ne!(p, copy);
    assert_eq!(p.get(b"sea"), None);
}

#[test]
fn partial_eq_distinguishes_the_fork_from_the_chain_collision() {
    // Both `walk` to the values [None, Some(2), Some(1)], over different keys.
    let mut fork = Patricia::new();
    fork.insert(b"a", 1);
    fork.insert(b"b", 2);

    let mut chain = Patricia::new();
    chain.insert(b"y", 2);
    chain.insert(b"yz", 1);

    assert_ne!(fork, chain);
    assert_eq!(fork, fork.clone());
    assert_eq!(chain, chain.clone());
}

#[test]
fn debug_shows_the_stored_pairs() {
    let mut p = Patricia::new();
    p.insert(b"a", 1);
    let text = format!("{p:?}");
    assert!(text.contains('1'));
}

/// A chain of `depth` single-byte-label, valued nodes, built bottom-up in `O(n)` (through
/// `insert` it would be `O(n^2)`).
fn deep_chain(depth: usize) -> Patricia<u8> {
    let mut node = Node {
        label: b"a".to_vec().into_boxed_slice(),
        value: Some(0),
        children: Vec::new(),
    };
    for _ in 1..depth {
        node = Node {
            label: b"a".to_vec().into_boxed_slice(),
            value: Some(0),
            children: vec![(b'a', Box::new(node))],
        };
    }
    let root = Node {
        label: Box::new([]),
        value: None,
        children: vec![(b'a', Box::new(node))],
    };
    Patricia { root, len: depth }
}

#[test]
fn a_long_chain_does_not_abort_on_drop() {
    // A recursive `Drop` would overflow on this.
    drop(deep_chain(200_000));
}

#[test]
fn clone_partial_eq_and_debug_survive_a_deep_chain() {
    // Smaller: `Clone` reinserts every key, `O(n^2)` on a chain.
    let t = deep_chain(3_000);
    let c = t.clone();
    assert_eq!(c, t);
    assert_eq!(c.node_count(), t.node_count());
    assert!(c.is_branches_unless_word_ends() && c.is_no_empty_branches());
    let text = format!("{t:?}");
    assert!(text.contains('0'));
}

// `is_valid`'s checks, each shown false alone.

fn node(label: &[u8], value: Option<u32>, children: Vec<(u8, Node<u32>)>) -> Node<u32> {
    Node {
        label: label.to_vec().into_boxed_slice(),
        value,
        children: children
            .into_iter()
            .map(|(b, c)| (b, Box::new(c)))
            .collect(),
    }
}

fn tree(children: Vec<(u8, Node<u32>)>, len: usize) -> Patricia<u32> {
    Patricia {
        root: node(b"", None, children),
        len,
    }
}

/// Which of `is_valid`'s six checks hold, in its order: the three pieces, then the layout.
fn conjuncts(p: &Patricia<u32>) -> [bool; 6] {
    [
        p.is_distinct_first_letters(),
        p.is_branches_unless_word_ends(),
        p.is_no_empty_branches(),
        p.is_sorted_heads(),
        p.is_children_filed_by_head(),
        p.is_len_matches(),
    ]
}

#[test]
fn a_valueless_leaf_breaks_is_branches_unless_word_ends_alone() {
    // Box invariant 4 passes it; box invariant 3 does not, and `remove` must unlink such a node.
    let p = tree(
        vec![
            (b'a', node(b"a", None, vec![])),
            (b'b', node(b"b", Some(1), vec![])),
        ],
        1,
    );
    assert_eq!(conjuncts(&p), [true, false, true, true, true, true]);
    assert_eq!(
        p.check_valid(),
        Err("invariant 3 (branches_unless_word_ends)")
    );
}

#[test]
fn children_out_of_order_break_sorted_heads_alone() {
    // Each tag matches its label, but the labels' heads descend: binary search misses `a`.
    let p = tree(
        vec![
            (b'c', node(b"c", Some(1), vec![])),
            (b'b', node(b"b", Some(2), vec![])),
            (b'a', node(b"a", Some(3), vec![])),
        ],
        3,
    );
    assert_eq!(conjuncts(&p), [true, true, true, false, true, true]);
    assert_eq!(p.check_valid(), Err("layout (sorted_heads)"));
    assert_eq!(p.get(b"a"), None); // what the order is for
}

#[test]
fn a_tag_that_is_not_its_labels_head_breaks_children_filed_by_head_alone() {
    // Labels `a`, `c`: heads distinct and ascending. The second is filed under `b`.
    let p = tree(
        vec![
            (b'a', node(b"a", Some(1), vec![])),
            (b'b', node(b"c", Some(2), vec![])),
        ],
        2,
    );
    assert_eq!(conjuncts(&p), [true, true, true, true, false, true]);
    assert_eq!(p.check_valid(), Err("layout (children_filed_by_head)"));
    assert_eq!(p.get(b"c"), None); // filed under the wrong byte, so never found
}

#[test]
fn a_wrong_len_breaks_len_matches_alone() {
    let mut p = Patricia::new();
    p.insert(b"ab", 1);
    p.insert(b"ac", 2);
    p.len += 1;
    assert_eq!(conjuncts(&p), [true, true, true, true, true, false]);
    assert_eq!(p.check_valid(), Err("layout (len_matches)"));
}

#[test]
fn siblings_with_one_head_break_is_distinct_first_letters() {
    // `is_sorted_heads` fails with it.
    let inner = node(
        b"x",
        None,
        vec![
            (b'a', node(b"ab", Some(1), vec![])),
            (b'a', node(b"ac", Some(2), vec![])),
        ],
    );
    let p = tree(vec![(b'x', inner)], 2);
    assert_eq!(conjuncts(&p), [false, true, true, false, true, true]);
    assert_eq!(p.check_valid(), Err("invariant 2 (distinct_first_letters)"));
    assert!(!p.is_valid());
}

#[test]
fn an_empty_label_beside_a_zero_head_reads_as_the_lean_does() {
    // An empty label: head `None` for distinct letters (Lean `head?`), `0` for ascending
    // heads (Lean `headSym`).
    let p = tree(
        vec![
            (0, node(b"", Some(1), vec![])),
            (1, node(&[0, 7], Some(2), vec![])),
        ],
        2,
    );
    assert!(p.is_branches_unless_word_ends() && !p.is_no_empty_branches());
    assert!(p.is_distinct_first_letters());
    assert!(!p.is_sorted_heads());
    assert!(!p.is_children_filed_by_head());
    assert_eq!(p.check_valid(), Err("invariant 4 (no_empty_branches)"));
}

#[test]
fn the_root_is_exempt_from_is_branches_unless_word_ends_only() {
    // A valueless root with one child keeps box invariant 3.
    let mut p = Patricia::new();
    p.insert(b"abc", 0);
    assert!(p.is_valid());
    let q = tree(
        vec![
            (b'b', node(b"b", Some(1), vec![])),
            (b'a', node(b"a", Some(2), vec![])),
        ],
        2,
    );
    assert!(q.is_branches_unless_word_ends() && !q.is_sorted_heads());
}

#[cfg(feature = "unchecked")]
#[test]
fn parts_round_trip_in_stored_order() {
    let p: Patricia<u32> = [(&b"analogy"[..], 0), (b"analysis", 1), (b"an", 2), (b"", 3)]
        .into_iter()
        .collect();
    let parts = p.to_parts();
    assert!(parts.label.is_empty());
    assert_eq!(parts.value, Some(3));
    let back = Patricia::from_parts_unchecked(parts.clone(), p.len());
    assert_eq!(back, p);
    assert_eq!(back.to_parts(), parts);
    assert!(back.is_valid());
    assert_eq!(back.node_count(), p.node_count());
}

#[cfg(feature = "unchecked")]
#[test]
fn parts_keep_what_insert_cannot_build() {
    let leaf = |label: &[u8]| PatriciaParts {
        label: label.to_vec(),
        value: Some(1u32),
        children: Vec::new(),
    };
    // Unsorted, mismatched and repeated tags, and an empty label, all as given.
    let root = PatriciaParts {
        label: Vec::new(),
        value: None,
        children: vec![(b'b', leaf(b"b")), (b'z', leaf(b"a")), (b'z', leaf(b""))],
    };
    let p = Patricia::from_parts_unchecked(root.clone(), 7);
    assert_eq!(p.to_parts(), root);
    assert_eq!(conjuncts(&p), [true, true, false, false, false, false]);
}

#[cfg(feature = "unchecked")]
#[test]
#[should_panic(expected = "the root has no incoming edge")]
fn a_root_label_cannot_be_given() {
    let _ = Patricia::<u32>::from_parts_unchecked(
        PatriciaParts {
            label: b"a".to_vec(),
            value: None,
            children: Vec::new(),
        },
        0,
    );
}

#[cfg(feature = "unchecked")]
#[test]
fn the_conversions_do_not_recurse_on_a_deep_chain() {
    // The parts are consumed, so their recursive drop glue never runs.
    let p = deep_chain(100_000);
    let back = Patricia::from_parts_unchecked(p.to_parts(), p.len());
    assert!(back.is_valid());
    assert_eq!(back.node_count(), p.node_count());
}

/// A boxed child entry is 16 bytes; an inline node would be 48 or more.
#[test]
fn a_child_entry_is_a_tag_and_a_pointer() {
    use std::mem::size_of;
    assert_eq!(size_of::<(u8, Box<Node<u32>>)>(), 16);
    assert!(size_of::<Node<()>>() >= 48);
    assert!(size_of::<Node<u32>>() >= 48);
}

/// `Clone` copies the structure node for node, and `PartialEq` walks both in lockstep: two
/// built from the same pairs in different orders are equal, a changed value or a missing key is
/// not, and a clone is valid and equal.
#[test]
fn structural_clone_and_eq_agree_with_the_maps() {
    let keys: [&[u8]; 6] = [b"", b"a", b"ab", b"abc", b"b", b"abd"];
    let forward: Patricia<usize> = keys.iter().enumerate().map(|(i, k)| (*k, i)).collect();
    let backward: Patricia<usize> = keys
        .iter()
        .enumerate()
        .rev()
        .map(|(i, k)| (*k, i))
        .collect();
    assert_eq!(forward, backward);
    let copy = forward.clone();
    assert_eq!(copy.check_valid(), Ok(()));
    assert_eq!(copy, forward);
    assert!(copy.iter().eq(forward.iter()));

    let mut changed = forward.clone();
    changed.insert(b"abc", 99);
    assert_ne!(changed, forward);
    let mut fewer = forward.clone();
    fewer.remove(b"ab");
    assert_ne!(fewer, forward);
    assert_eq!(
        forward.len(),
        keys.len(),
        "the clones share nothing with the original"
    );
}
