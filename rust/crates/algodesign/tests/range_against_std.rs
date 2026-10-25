// SPDX-License-Identifier: Apache-2.0
//! `range` against `std::collections::BTreeSet::range`, which is the specification it is trying
//! to meet: same bounds, same order, same emptiness, same panics.
//!
//! Three kinds of check, because they fail differently:
//!
//! * **forward** and **reversed** collection catch a bound read the wrong way round, an
//!   off-by-one on `Excluded`, and a seed descent that turns down the wrong subtree;
//! * an **interleaving** of `next` and `next_back` against a `VecDeque` of the same keys catches
//!   the one bug the other two cannot see. The two ends of a double-ended range stop each other,
//!   and a wrong stopping rule still collects correctly from either end alone — it hands back a
//!   key twice, or drops the last one, only when both ends are walking.
//!
//! The bound pairs are *exhaustive* rather than sampled: every `(start, end)` in `0..=13` against
//! every one of the nine `Bound` combinations, over a key set with deliberate gaps, so
//! `Excluded` on a present key, bounds inside a gap, bounds outside the tree entirely, empty
//! ranges and single-key ranges are all reached by construction rather than by luck.

use std::collections::{BTreeSet, VecDeque};
use std::ops::Bound;

use algodesign::searching::bst::Bst;
use algodesign::searching::btree::BTree;
use algodesign::searching::llrb::Llrb;
use algodesign::searching::red_black_standard::RbTree;

/// Keys with gaps in them: every second number, so half the bounds tested fall between keys.
fn keys() -> Vec<u64> {
    (0..=6).map(|k| k * 2).collect()
}

/// A scattered, deterministic key set for the larger pass. Splitmix64, as elsewhere in this
/// crate's tests, so a failure is reproducible without a seed to record.
fn scattered(n: u64) -> Vec<u64> {
    let mut s = 0x2545_F491_4F6C_DD1Du64;
    (0..n)
        .map(|_| {
            s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            (z ^ (z >> 31)) % (4 * n)
        })
        .collect()
}

/// The nine bound pairs that are legal for a given `(lo, hi)`, skipping the two `std` panics on.
fn bound_pairs(lo: u64, hi: u64) -> Vec<(Bound<u64>, Bound<u64>)> {
    let starts = [Bound::Included(lo), Bound::Excluded(lo), Bound::Unbounded];
    let ends = [Bound::Included(hi), Bound::Excluded(hi), Bound::Unbounded];
    let mut out = Vec::new();
    for s in starts {
        for e in ends {
            let illegal = match (s, e) {
                (
                    Bound::Included(a) | Bound::Excluded(a),
                    Bound::Included(b) | Bound::Excluded(b),
                ) => {
                    a > b || (a == b && matches!((s, e), (Bound::Excluded(_), Bound::Excluded(_))))
                }
                _ => false,
            };
            if !illegal {
                out.push((s, e));
            }
        }
    }
    out
}

/// A deterministic bit stream for the interleaving: which end to take the next key from.
fn coin(state: &mut u64) -> bool {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1);
    (*state >> 33) & 1 == 1
}

/// Every check, for one structure. `$ctor` builds an empty one and `range` is called as an
/// inherent method on it, so each structure's own implementation is what runs — the macro exists
/// because the five containers share no trait, not to abstract over one.
macro_rules! suite {
    ($name:ident, $ty:ty, $ctor:expr) => {
        mod $name {
            use super::*;

            fn build(ks: &[u64]) -> $ty {
                let mut t = $ctor;
                for &k in ks {
                    t.insert(k);
                }
                t
            }

            fn model(ks: &[u64]) -> BTreeSet<u64> {
                ks.iter().copied().collect()
            }

            fn check(ks: &[u64], span: u64) {
                let t = build(ks);
                let m = model(ks);
                let mut rng = 0x7A11_5EEDu64;
                for lo in 0..=span {
                    for hi in 0..=span {
                        for b in bound_pairs(lo, hi) {
                            let want: Vec<u64> = m.range(b).copied().collect();

                            let got: Vec<u64> = t.range(b).copied().collect();
                            assert_eq!(got, want, "forward, bounds {b:?}");

                            let got_rev: Vec<u64> = t.range(b).rev().copied().collect();
                            let mut want_rev = want.clone();
                            want_rev.reverse();
                            assert_eq!(got_rev, want_rev, "reversed, bounds {b:?}");

                            // Both ends at once, against a deque of the same keys.
                            let mut deque: VecDeque<u64> = want.iter().copied().collect();
                            let mut it = t.range(b);
                            while !deque.is_empty() {
                                if coin(&mut rng) {
                                    assert_eq!(
                                        it.next().copied(),
                                        deque.pop_front(),
                                        "interleaved front, bounds {b:?}"
                                    );
                                } else {
                                    assert_eq!(
                                        it.next_back().copied(),
                                        deque.pop_back(),
                                        "interleaved back, bounds {b:?}"
                                    );
                                }
                            }
                            assert_eq!(it.next(), None, "past the end, bounds {b:?}");
                            assert_eq!(it.next_back(), None, "past the start, bounds {b:?}");
                            // Fused: still nothing, twice over.
                            assert_eq!(it.next(), None, "fused, bounds {b:?}");
                            assert_eq!(it.next_back(), None, "fused backwards, bounds {b:?}");
                        }
                    }
                }
            }

            #[test]
            fn every_bound_pair_over_a_gappy_key_set() {
                check(&keys(), 13);
            }

            #[test]
            fn the_empty_tree_answers_every_bound_pair_with_nothing() {
                check(&[], 3);
            }

            #[test]
            fn a_scattered_tree_agrees_too() {
                let ks = scattered(200);
                let t = build(&ks);
                let m = model(&ks);
                for lo in (0..800).step_by(37) {
                    for hi in (0..800).step_by(53) {
                        for b in bound_pairs(lo, hi) {
                            let want: Vec<u64> = m.range(b).copied().collect();
                            let got: Vec<u64> = t.range(b).copied().collect();
                            assert_eq!(got, want, "bounds {b:?}");
                        }
                    }
                }
            }

            #[test]
            fn floor_and_ceiling_are_spelled_through_range() {
                let ks = keys();
                let t = build(&ks);
                let m = model(&ks);
                for a in 0..=13u64 {
                    assert_eq!(
                        t.range(..=a).next_back().copied(),
                        m.range(..=a).next_back().copied(),
                        "floor({a})"
                    );
                    assert_eq!(
                        t.range(a..).next().copied(),
                        m.range(a..).next().copied(),
                        "ceiling({a})"
                    );
                }
            }

            #[test]
            fn the_hint_never_lies() {
                let ks = keys();
                let t = build(&ks);
                for b in bound_pairs(2, 10) {
                    let n = t.range(b).count();
                    let (lo, hi) = t.range(b).size_hint();
                    assert!(
                        lo <= n,
                        "the lower hint {lo} exceeds the {n} keys there are"
                    );
                    assert!(
                        hi.is_some_and(|h| h >= n),
                        "the upper hint {hi:?} is below the {n} keys there are"
                    );
                }
            }

            #[test]
            fn a_clone_walks_the_same_keys() {
                let ks = keys();
                let t = build(&ks);
                let mut it = t.range(2..=10);
                it.next();
                let rest: Vec<u64> = it.clone().copied().collect();
                let rest_again: Vec<u64> = it.copied().collect();
                assert_eq!(rest, rest_again);
            }

            #[test]
            #[should_panic(expected = "range start is greater than range end")]
            fn a_backwards_range_panics_as_std_does() {
                let t = build(&keys());
                let _ = t.range((Bound::Included(9), Bound::Included(4)));
            }

            #[test]
            #[should_panic(expected = "range start and end are equal and excluded")]
            fn a_doubly_excluded_point_panics_as_std_does() {
                let t = build(&keys());
                let _ = t.range((Bound::Excluded(4), Bound::Excluded(4)));
            }

            #[test]
            fn an_empty_range_is_legal() {
                let t = build(&keys());
                assert_eq!(t.range(4..4).count(), 0);
                assert_eq!(t.range((Bound::Included(4), Bound::Excluded(4))).count(), 0);
            }
        }
    };
}

suite!(bst, Bst<u64>, Bst::new());
suite!(llrb, Llrb<u64>, Llrb::new());
suite!(rbtree, RbTree<u64>, RbTree::new());
// Both fanouts the crate ships: the default, which is `std`'s own, and a wide one, where a node
// holds enough keys that the cursor's key positions matter more than its child positions.
suite!(btree_t3, BTree<u64>, BTree::new(3));
suite!(btree_t6, BTree<u64>, BTree::new(6));
suite!(btree_t2, BTree<u64>, BTree::new(2));
