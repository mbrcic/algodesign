// SPDX-License-Identifier: Apache-2.0
//! The iterator refinements the containers claim.
//!
//! `ExactSizeIterator` is a promise `std` and every adaptor believe without checking: `collect`
//! into a `Vec` preallocates from `size_hint`, and a wrong hint there is a silently wrong
//! capacity rather than a panic. So the hint is checked at every step, not only at the start —
//! an off-by-one that only shows up midway through is exactly the shape this catches.
//!
//! `Lsm` is absent on purpose: its `len` is `O(n)`, so an exact hint would cost a walk to produce
//! and the claim is not worth the walk. It is `FusedIterator`, which costs nothing.
//!
//! `Llrb` and `RbTree` nodes carry a subtree count, which makes the hint free; without it
//! `collect()` would grow the result vector from zero.

use algodesign::searching::bst::Bst;
use algodesign::searching::btree::BTree;
use algodesign::searching::llrb::Llrb;
use algodesign::searching::red_black_standard::RbTree;
use algodesign::searching::treap::Treap;

fn keys(n: u64) -> Vec<u64> {
    let mut s = 0x243F_6A88_85A3_08D3u64;
    (0..n)
        .map(|_| {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            (z ^ (z >> 31)) % 4096
        })
        .collect()
}

/// Walk the iterator, requiring the hint to equal the number of items actually still to come.
fn hint_is_exact_at_every_step<'a, I>(it: I, expected: usize)
where
    I: ExactSizeIterator<Item = &'a u64> + Clone,
{
    assert_eq!(it.len(), expected, "the initial length is wrong");
    let mut probe = it.clone();
    for step in 0..=expected {
        let (lo, hi) = probe.size_hint();
        let left = expected - step;
        assert_eq!(lo, left, "lower bound wrong after {step} items");
        assert_eq!(hi, Some(left), "upper bound wrong after {step} items");
        assert_eq!(probe.len(), left, "len() wrong after {step} items");
        if probe.next().is_none() {
            assert_eq!(step, expected, "ran out after {step} of {expected} items");
        }
    }
    // Collecting must not have to grow: the promise is what `Vec` sizes itself from.
    let collected: Vec<_> = it.collect();
    assert_eq!(collected.len(), expected);
}

#[test]
fn bst_iteration_reports_its_exact_length() {
    for n in [0u64, 1, 2, 17, 500] {
        let mut t = Bst::new();
        for k in keys(n) {
            t.insert(k);
        }
        hint_is_exact_at_every_step(t.iter(), t.len());
    }
}

#[test]
fn treap_iteration_reports_its_exact_length() {
    for n in [0u64, 1, 2, 17, 500] {
        let mut t = Treap::new();
        for k in keys(n) {
            t.insert_random(k);
        }
        hint_is_exact_at_every_step(t.iter(), t.len());
    }
}

#[test]
fn btree_iteration_reports_its_exact_length() {
    for n in [0u64, 1, 2, 17, 500] {
        for degree in [2usize, 3, 6] {
            let mut t = BTree::new(degree);
            for k in keys(n) {
                t.insert(k);
            }
            hint_is_exact_at_every_step(t.iter(), t.len());
        }
    }
}

#[test]
fn llrb_iteration_reports_its_exact_length() {
    for n in [0u64, 1, 2, 17, 500] {
        let mut t = Llrb::new();
        for k in keys(n) {
            t.insert(k);
        }
        hint_is_exact_at_every_step(t.iter(), t.len());
    }
}

#[test]
fn rbtree_iteration_reports_its_exact_length() {
    for n in [0u64, 1, 2, 17, 500] {
        let mut t = RbTree::new();
        for k in keys(n) {
            t.insert(k);
        }
        hint_is_exact_at_every_step(t.iter(), t.len());
    }
}

/// Deletion is where a maintained count is most likely to drift from the tree.
#[test]
fn the_length_survives_deletions() {
    let ks = keys(500);
    let mut bst = Bst::new();
    let mut treap = Treap::new();
    let mut btree = BTree::new(3);
    let mut llrb = Llrb::new();
    let mut rb = RbTree::new();
    for k in &ks {
        bst.insert(*k);
        treap.insert_random(*k);
        btree.insert(*k);
        llrb.insert(*k);
        rb.insert(*k);
    }
    for k in ks.iter().take(300) {
        bst.delete(k);
        treap.delete(k);
        btree.delete(k);
        llrb.delete(k);
        rb.delete(k);
    }
    hint_is_exact_at_every_step(bst.iter(), bst.iter().count());
    hint_is_exact_at_every_step(treap.iter(), treap.iter().count());
    hint_is_exact_at_every_step(btree.iter(), btree.iter().count());
    hint_is_exact_at_every_step(llrb.iter(), llrb.iter().count());
    hint_is_exact_at_every_step(rb.iter(), rb.iter().count());
}
