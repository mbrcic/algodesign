// SPDX-License-Identifier: Apache-2.0
//! Looking a key up must not require *owning* one.
//!
//! A lookup that took `&T` would make finding a key in a `Bst<String>` build a `String` first,
//! an allocation per lookup. The lookups take `&Q where T: Borrow<Q>`, which is what `std`'s
//! containers do and the reason `BTreeSet<String>::contains("x")` compiles.
//!
//! This file is the check that the bound is actually usable. A signature can carry
//! `T: Borrow<Q>` and still be impossible to call with anything but `&T` if a comparison inside
//! forgot to borrow, and the compiler will not say so — nothing in the crate's own tests uses a
//! key type where `T` and `Q` differ.

use algodesign::searching::bst::Bst;
use algodesign::searching::btree::BTree;
use algodesign::searching::llrb::Llrb;
use algodesign::searching::lsm::Lsm;
use algodesign::searching::red_black_standard::RbTree;
use algodesign::searching::treap::Treap;

const WORDS: [&str; 6] = ["delta", "alpha", "echo", "bravo", "foxtrot", "charlie"];

#[test]
fn bst_takes_a_str_for_a_string_key() {
    let mut t: Bst<String> = WORDS.iter().map(|s| (*s).to_string()).collect();

    // The point: `&str`, not `&String`. None of these allocates.
    assert!(t.contains("alpha"));
    assert!(t.search("echo"));
    assert!(!t.contains("zulu"));
    assert_eq!(t.floor("brb").map(String::as_str), Some("bravo"));
    assert_eq!(t.ceiling("brb").map(String::as_str), Some("charlie"));
    assert_eq!(t.rank("charlie"), 2);

    assert!(t.delete("alpha"));
    assert!(!t.delete("alpha"));
    assert!(t.delete_hibbard("bravo"));
    assert_eq!(
        t.iter().map(String::as_str).collect::<Vec<_>>(),
        ["charlie", "delta", "echo", "foxtrot"]
    );
}

#[test]
fn balanced_trees_take_a_str_too() {
    let mut l: Llrb<String> = Llrb::new();
    let mut r: RbTree<String> = RbTree::new();
    let mut p: Treap<String> = Treap::new();
    let mut b: BTree<String> = BTree::new(3);
    for w in WORDS {
        l.insert(w.to_string());
        r.insert(w.to_string());
        p.insert_random(w.to_string());
        b.insert(w.to_string());
    }

    assert!(l.contains("alpha") && l.search("alpha") && l.get("alpha").is_some());
    assert!(r.contains("alpha") && r.get("alpha").is_some());
    assert!(p.contains("alpha"));
    assert!(b.contains("alpha") && b.search("alpha"));

    assert!(!l.contains("zulu") && !r.contains("zulu") && !p.contains("zulu"));
    assert!(!b.contains("zulu"));

    assert!(l.delete("alpha"));
    assert!(r.delete("alpha"));
    assert!(p.delete("alpha"));
    assert!(b.delete("alpha"));
    assert!(!l.contains("alpha") && !r.contains("alpha"));
    assert!(!p.contains("alpha") && !b.contains("alpha"));
    assert!(l.is_valid() && r.is_valid() && p.is_valid());
}

/// The same lookups still accept an owned key, so nothing that compiled before stops compiling.
#[test]
fn an_owned_key_still_works() {
    let t: Bst<i64> = (0..10).collect();
    let k = 4i64;
    assert!(t.contains(&k));
    assert_eq!(t.rank(&k), 4);
}

#[test]
fn lsm_takes_a_str_for_a_string_key() {
    // A small memtable, so the lookups below reach the runs as well as the memtable.
    let mut s: Lsm<String, usize> = Lsm::with_shape(2, 2, 2);
    for (i, w) in WORDS.iter().enumerate() {
        s.write((*w).to_string(), i);
    }
    s.delete("echo".to_string());
    assert!(!s.levels().is_empty(), "the lookups must reach a run");

    assert_eq!(s.get("alpha"), Some(&1));
    assert!(s.contains("charlie") && !s.contains("zulu"));
    assert_eq!(s.lookup("echo"), Some(None));
    assert_eq!(s.lookup("zulu"), None);
}
