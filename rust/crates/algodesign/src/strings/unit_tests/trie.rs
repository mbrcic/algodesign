// SPDX-License-Identifier: Apache-2.0
use std::collections::BTreeMap;

use proptest::prelude::*;

use super::*;

/// One call on the public surface: inserts (overwrites included) and removes (of absent keys
/// and bare prefixes included) interleaved with every query.
#[derive(Debug, Clone)]
enum Op {
    Insert(Vec<u8>, u32),
    Remove(Vec<u8>),
    Get(Vec<u8>),
    KeysWithPrefix(Vec<u8>),
    LongestPrefix(Vec<u8>),
}

/// Short keys over three bytes, so they share prefixes, nest and repeat.
fn key() -> impl Strategy<Value = Vec<u8>> {
    prop::collection::vec(0u8..3, 0..6)
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        3 => (key(), any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
        2 => key().prop_map(Op::Remove),
        1 => key().prop_map(Op::Get),
        1 => key().prop_map(Op::KeysWithPrefix),
        1 => key().prop_map(Op::LongestPrefix),
    ]
}

proptest! {
    /// A random mix against a `BTreeMap`; after every operation `len`, the contents in order
    /// and the node count (against a fresh rebuild) are checked.
    #[test]
    fn matches_a_btreemap_and_keeps_its_count(ops in prop::collection::vec(op(), 0..60)) {
        let mut t = Trie::new();
        let mut map: BTreeMap<Vec<u8>, u32> = BTreeMap::new();
        for op in &ops {
            match op {
                Op::Insert(k, v) => prop_assert_eq!(t.insert(k, *v), map.insert(k.clone(), *v)),
                Op::Remove(k) => prop_assert_eq!(t.remove(k), map.remove(k)),
                // Lean: get_insert, get_insert_other, get_remove, get_remove_other
                Op::Get(k) => prop_assert_eq!(t.get(k), map.get(k)),
                Op::KeysWithPrefix(p) => {
                    let mut got = t.keys_with_prefix(p);
                    got.sort();
                    let want: Vec<Vec<u8>> =
                        map.keys().filter(|k| k.starts_with(p)).cloned().collect();
                    prop_assert_eq!(got, want); // Lean: keysWithPrefix_perm
                    let pairs: Vec<(Vec<u8>, u32)> =
                        t.iter_with_prefix(p).map(|(k, v)| (k, *v)).collect();
                    let want: Vec<(Vec<u8>, u32)> = map
                        .iter()
                        .filter(|(k, _)| k.starts_with(p))
                        .map(|(k, v)| (k.clone(), *v))
                        .collect();
                    prop_assert_eq!(pairs, want); // Lean: keysWithPrefix_sorted
                }
                Op::LongestPrefix(q) => {
                    let want = map
                        .keys()
                        .filter(|k| q.starts_with(k))
                        .max_by_key(|k| k.len())
                        .map(|k| &q[..k.len()]);
                    // Lean: longestPrefix_eq_some_iff, longestPrefix_eq_none_iff
                    prop_assert_eq!(t.longest_prefix(q), want);
                }
            }
            prop_assert_eq!(t.len(), map.len(), "cached len diverged after {:?}", op);
            prop_assert_eq!(t.len(), t.iter().count(), "cached len disagrees with a walk");
            prop_assert_eq!(t.is_empty(), map.is_empty());
            let pairs: Vec<(Vec<u8>, u32)> = t.iter().map(|(k, v)| (k, *v)).collect();
            let model: Vec<(Vec<u8>, u32)> =
                map.iter().map(|(k, v)| (k.clone(), *v)).collect();
            prop_assert_eq!(pairs, model);
            let rebuilt: Trie<u32> = map.iter().map(|(k, v)| (k.as_slice(), *v)).collect();
            prop_assert_eq!(t.node_count(), rebuilt.node_count(), "shape after {:?}", op);
            // Lean: `valid_insert`, `valid_remove`.
            prop_assert!(t.is_valid(), "invalid after {:?}", op);
            prop_assert!(t.is_distinct_letters(), "a repeated child after {:?}", op);
        }
    }

    /// `FromIterator` is the pairs inserted in turn, the last value for a key winning.
    #[test]
    fn from_iter_is_insert_in_turn(
        pairs in prop::collection::vec((key(), any::<u32>()), 0..30),
    ) {
        let t: Trie<u32> = pairs.iter().map(|(k, v)| (k.as_slice(), *v)).collect();
        let map: BTreeMap<Vec<u8>, u32> = pairs.iter().cloned().collect();
        prop_assert_eq!(t.len(), map.len());
        for (k, v) in &map {
            prop_assert_eq!(t.get(k), Some(v));
        }
    }
}

/// `len` reads the kept count, not a walk.
#[test]
fn len_reads_the_cached_count() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    t.insert(b"sea", 2);
    t.len = 1_000;
    assert_eq!(t.len(), 1_000);
    assert_eq!(t.iter().count(), 3);
    t.len = 0;
    assert!(t.is_empty());
}

/// `Eq`, `Extend` and `FromIterator`: a later pair overwrites.
#[test]
fn collect_and_extend_insert_in_turn() {
    let mut t: Trie<i32> = [(&b"she"[..], 0), (b"sea", 1), (b"she", 2)]
        .into_iter()
        .collect();
    assert_eq!(t.len(), 2);
    assert_eq!(t.get(b"she"), Some(&2));
    t.extend(vec![(b"shells".to_vec(), 3)]);
    let mut by_hand = Trie::new();
    by_hand.insert(b"sea", 1);
    by_hand.insert(b"she", 2);
    by_hand.insert(b"shells", 3);
    assert_eq!(t, by_hand);
    fn is_eq<T: Eq>(_: &T) {}
    is_eq(&t);
}

#[test]
fn stores_and_retrieves() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    t.insert(b"sea", 2);
    assert_eq!(t.get(b"shells"), Some(&1));
    assert_eq!(t.get(b"shell"), None);
    assert_eq!(t.keys_with_prefix(b"sh").len(), 2);
    assert_eq!(t.longest_prefix(b"shellsort"), Some(&b"shells"[..]));
}

#[test]
fn a_long_thin_trie_does_not_abort() {
    // Depth is the key length: a recursive `Drop` would overflow here.
    let mut t = Trie::new();
    t.insert(&vec![b'a'; 200_000], 1);
    drop(t);
}

#[test]
fn removing_a_long_thin_key_does_not_abort() {
    // Removing the key detaches a 200 000-node chain and restores the empty shape.
    let mut t = Trie::new();
    t.insert(&vec![b'a'; 200_000], 1);
    assert_eq!(t.remove(&vec![b'a'; 200_000]), Some(1));
    assert_eq!(t.node_count(), 1);
    assert!(t.is_empty());
}

#[test]
fn remove_takes_only_the_unshared_suffix_of_the_path() {
    // Removing a key cuts back to the first node another key still needs.
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    t.insert(b"sea", 2);
    let before = t.node_count();
    assert_eq!(t.remove(b"shell"), None); // a bare prefix: nothing changes
    assert_eq!(t.remove(b"shellsort"), None); // absent
    assert_eq!(t.node_count(), before);
    assert_eq!(t.remove(b"shells"), Some(1)); // "lls" goes, "she" stays
    assert_eq!(t.node_count(), before - 3);
    assert_eq!(t.remove(b"she"), Some(0)); // "he" goes, "s" still leads to "sea"
    assert_eq!(t.node_count(), before - 5);
    assert_eq!(t.get(b"sea"), Some(&2));
    assert_eq!(t.remove(b"sea"), Some(2));
    assert_eq!((t.len(), t.node_count()), (0, 1));
}

#[test]
fn removing_a_key_that_others_extend_keeps_their_path() {
    let mut t = Trie::new();
    t.insert(b"", 0);
    t.insert(b"ab", 1);
    t.insert(b"abc", 2);
    let before = t.node_count();
    assert_eq!(t.remove(b"ab"), Some(1));
    assert_eq!(t.node_count(), before);
    assert_eq!(t.remove(b""), Some(0));
    assert_eq!(t.get(b"abc"), Some(&2));
    assert_eq!(t.longest_prefix(b"abcd"), Some(&b"abc"[..]));
}

#[test]
fn empty_trie_has_no_keys_and_a_root_only_node_count() {
    let t: Trie<u8> = Trie::new();
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
    assert_eq!(t.node_count(), 1);
    assert_eq!(t.get(b""), None);
    assert_eq!(t.get(b"x"), None);
    assert_eq!(t.longest_prefix(b"x"), None);
    assert!(t.keys_with_prefix(b"").is_empty());
}

#[test]
fn insert_overwrite_returns_the_old_value_and_does_not_grow_len() {
    let mut t = Trie::new();
    assert_eq!(t.insert(b"a", 1), None);
    assert_eq!(t.len(), 1);
    assert_eq!(t.insert(b"a", 2), Some(1));
    assert_eq!(t.len(), 1);
    assert_eq!(t.get(b"a"), Some(&2));
}

#[test]
fn empty_key_is_a_valid_key() {
    let mut t = Trie::new();
    assert_eq!(t.insert(b"", 7), None);
    assert_eq!(t.get(b""), Some(&7));
    assert_eq!(t.longest_prefix(b"anything"), Some(&b""[..]));
}

#[test]
fn keys_with_prefix_of_an_absent_path_is_empty() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    assert!(t.keys_with_prefix(b"zz").is_empty());
}

#[test]
fn iter_yields_every_stored_pair_exactly_once() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    t.insert(b"sea", 2);
    let mut got: Vec<(Vec<u8>, i32)> = t.iter().map(|(k, v)| (k, *v)).collect();
    got.sort();
    let mut want = vec![
        (b"she".to_vec(), 0),
        (b"shells".to_vec(), 1),
        (b"sea".to_vec(), 2),
    ];
    want.sort();
    assert_eq!(got, want);
    assert_eq!(t.iter().count(), t.len());
}

#[test]
fn node_count_exceeds_len_when_keys_share_prefixes() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    t.insert(b"sea", 2);
    // 3 keys, but "sh"/"s" are shared spine, so strictly more than 3 nodes plus the root.
    assert!(t.node_count() > t.len());
}

#[test]
fn clone_is_equal_and_independent() {
    let mut t = Trie::new();
    t.insert(b"she", 0);
    t.insert(b"shells", 1);
    let mut copy = t.clone();
    assert_eq!(t, copy);
    copy.insert(b"sea", 2);
    assert_ne!(t, copy);
    assert_eq!(t.get(b"sea"), None);
}

#[test]
fn partial_eq_distinguishes_the_fork_from_the_chain_collision() {
    // Both `walk` to the values [None, Some(2), Some(1)], over different keys.
    let mut fork = Trie::new();
    fork.insert(b"a", 1);
    fork.insert(b"b", 2);

    let mut chain = Trie::new();
    chain.insert(b"y", 2);
    chain.insert(b"yz", 1);

    assert_ne!(fork, chain);
    assert_eq!(fork, fork.clone());
    assert_eq!(chain, chain.clone());
}

#[test]
fn debug_shows_the_stored_pairs() {
    let mut t = Trie::new();
    t.insert(b"a", 1);
    let text = format!("{t:?}");
    assert!(text.contains('1'));
}

#[test]
fn clone_partial_eq_and_debug_survive_a_deep_chain() {
    // A deep key: `Clone`, `PartialEq` and `Debug` must not recurse.
    let mut t = Trie::new();
    t.insert(&vec![b'a'; 50_000], 1);
    let c = t.clone();
    assert_eq!(c, t);
    assert_eq!(c.node_count(), t.node_count());
    let text = format!("{t:?}");
    assert!(text.contains('1'));
}

// `is_valid`'s checks, each shown false alone.

#[test]
fn a_dead_branch_breaks_is_no_dead_branches_alone() {
    let mut t = Trie::new();
    t.insert(b"a", 1);
    // A valueless, childless node below the root: the branch `remove` would have cut.
    t.root.next[usize::from(b'b')] = Some(Box::new(Node::empty()));
    assert!(t.is_distinct_letters());
    assert!(!t.is_no_dead_branches());
    assert!(t.is_len_matches());
    assert_eq!(t.check_valid(), Err("invariant 3 (no_dead_branches)"));
}

#[test]
fn a_wrong_len_breaks_len_matches_alone() {
    let mut t = Trie::new();
    t.insert(b"a", 1);
    t.len = 2;
    assert!(t.is_distinct_letters() && t.is_no_dead_branches());
    assert!(!t.is_len_matches());
    assert_eq!(t.check_valid(), Err("layout (len_matches)"));
}

#[test]
fn the_root_is_exempt_from_is_no_dead_branches() {
    // The empty trie's root is valueless and childless, and valid.
    let t: Trie<u32> = Trie::new();
    assert!(t.is_no_dead_branches());
    assert!(t.is_valid());
}

#[cfg(feature = "unchecked")]
#[test]
fn parts_round_trip_in_byte_order() {
    let t: Trie<u32> = [(&b"ba"[..], 1), (b"a", 2), (b"", 3), (b"bb", 4)]
        .into_iter()
        .collect();
    let parts = t.to_parts();
    let bytes: Vec<u8> = parts.children.iter().map(|(b, _)| *b).collect();
    assert_eq!(bytes, vec![b'a', b'b']);
    assert_eq!(parts.value, Some(3));
    let back = Trie::from_parts_unchecked(parts.clone(), t.len());
    assert_eq!(back, t);
    assert_eq!(back.to_parts(), parts);
    assert!(back.is_valid());
}

#[cfg(feature = "unchecked")]
#[test]
fn parts_build_what_insert_cannot() {
    let dead = TrieParts {
        value: None,
        children: vec![(
            b'a',
            TrieParts {
                value: None,
                children: Vec::new(),
            },
        )],
    };
    let t: Trie<u32> = Trie::from_parts_unchecked(dead, 0);
    assert!(!t.is_no_dead_branches());
    assert!(t.is_len_matches());
}

#[cfg(feature = "unchecked")]
#[test]
#[should_panic(expected = "one slot per byte")]
fn a_repeated_byte_cannot_be_represented() {
    let leaf = || TrieParts {
        value: Some(1u32),
        children: Vec::new(),
    };
    let _ = Trie::from_parts_unchecked(
        TrieParts {
            value: None,
            children: vec![(b'a', leaf()), (b'a', leaf())],
        },
        2,
    );
}

#[cfg(feature = "unchecked")]
#[test]
fn the_conversions_do_not_recurse_on_a_deep_chain() {
    // The parts are consumed, so their recursive drop glue never runs.
    let key = vec![7u8; 100_000];
    let mut t = Trie::new();
    t.insert(&key, 1u32);
    let back = Trie::from_parts_unchecked(t.to_parts(), 1);
    assert!(back.is_valid());
    assert_eq!(back.get(&key), Some(&1));
}

/// `Clone` copies the structure node for node, and `PartialEq` walks both in lockstep: two
/// built from the same pairs in different orders are equal, a changed value or a missing key is
/// not, and a clone is valid and equal.
#[test]
fn structural_clone_and_eq_agree_with_the_maps() {
    let keys: [&[u8]; 6] = [b"", b"a", b"ab", b"abc", b"b", b"abd"];
    let forward: Trie<usize> = keys.iter().enumerate().map(|(i, k)| (*k, i)).collect();
    let backward: Trie<usize> = keys
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
