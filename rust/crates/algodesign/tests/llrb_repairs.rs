// SPDX-License-Identifier: Apache-2.0
//! Exhaustive tests of the LLRB's repair steps, over small fixed trees.
//!
//! Each check is a plain function below: build a fixed tree by insertion, apply one operation
//! with one more key, and assert what the Lean states about the result -- `Valid` (all five
//! conjuncts, `is_valid()`), the key count, and which keys are in it. A `#[test]` runs it on
//! every key in a range.
//!
//! ## Why each check starts from a fixed tree
//!
//! `rotate_right` and `flip_colors` need at least three nodes, and `delete_min` borrows (runs
//! `move_red_left`) only on a tree of three or more. So the shape comes from a concrete prefix and
//! only the last key varies, which reaches every repair:
//!
//! | check | prefix | last key | fires |
//! |---|---|---|---|
//! | `insert_into` | `1, 3` (3 with a red left 1) | `0..=4` | `rotate_left` (2), `rotate_right` (0, 2), `flip_colors` (0, 2, 4) |
//! | `delete_min_after` | `1, 3` | `0..=4` | `move_red_left`'s flip (every three-key tree) |
//! | `delete_min_after` | `1, 3, 5` | `0..=6` | `move_red_left`'s rotations (4 lands red under 5) |
//!
//! One repair needs a bigger tree: `move_red_left` without its *last* `flip_colors` changes no
//! tree of up to eight keys, and `delete_min_needs_move_red_lefts_last_flip` below checks it on
//! ten.
//!
//! What this still is not: a proof for every tree. It is a few fixed shapes, each checked
//! against every key that can land in it, which is what makes the repair cases reachable at all.
//! The Lean theorems (`valid_insert`, `valid_deleteMinTop`) are the statement for all trees.

use algodesign::searching::llrb::Llrb;
use std::ops::RangeInclusive;

/// The tree the prefix builds, checked valid before the operation under test touches it.
fn build(prefix: &[i32]) -> Llrb<i32> {
    let mut t = Llrb::new();
    for &k in prefix {
        t.insert(k);
    }
    assert!(t.is_valid());
    t
}

/// Mirrors `LLRB.valid_insert` and `LLRB.mem_insert`: inserting `k` into the prefix's tree leaves
/// a valid tree holding the prefix's keys and `k`, and nothing else.
fn insert_into(prefix: &[i32], k: i32) {
    let mut t = build(prefix);
    let fresh = !prefix.contains(&k);
    assert!(t.insert(k) == fresh);
    assert!(t.is_valid());
    assert!(t.len() == prefix.len() + usize::from(fresh));
    assert!(t.contains(&k));
    for p in prefix {
        assert!(t.contains(p));
    }
}

/// Mirrors `LLRB.valid_deleteMinTop`: after inserting `k`, `delete_min` returns the least key,
/// removes it and nothing else, and leaves a valid tree.
fn delete_min_after(prefix: &[i32], k: i32) {
    let mut t = build(prefix);
    t.insert(k);
    let n = t.len();
    let mut least = k;
    for &p in prefix {
        if p < least {
            least = p;
        }
    }
    assert!(t.delete_min() == Some(least));
    assert!(t.is_valid());
    assert!(t.len() == n - 1);
    assert!(!t.contains(&least));
    if k != least {
        assert!(t.contains(&k));
    }
    for p in prefix {
        if *p != least {
            assert!(t.contains(p));
        }
    }
}

/// The fixed prefixes and the ranges their last key is drawn from.
const TWO: [i32; 2] = [1, 3];
const TWO_KEYS: RangeInclusive<i32> = 0..=4;
const THREE: [i32; 3] = [1, 3, 5];
const THREE_KEYS: RangeInclusive<i32> = 0..=6;

/// Mirrors `LLRB.search_correct` in the direction that matters here: a key that was inserted is
/// afterwards found.
fn insert_then_find(k: i32) {
    let mut t = Llrb::new();
    t.insert(k);
    assert!(t.contains(&k));
}

// The tests: every key in each range. (`insert_then_find` holds for any `i32`; the test takes a
// spread of them.)

#[test]
fn insert_then_contains() {
    for k in [i32::MIN, -1, 0, 1, i32::MAX] {
        insert_then_find(k);
    }
}

#[test]
fn insert_preserves_valid() {
    for k in TWO_KEYS {
        insert_into(&TWO, k);
    }
}

#[test]
fn delete_min_preserves_valid() {
    for k in TWO_KEYS {
        delete_min_after(&TWO, k);
    }
}

#[test]
fn delete_min_rotating_borrow_preserves_valid() {
    for k in THREE_KEYS {
        delete_min_after(&THREE, k);
    }
}

/// The one repair step the small trees above cannot see.
/// `move_red_left` ends with a `flip_colors` after its rotations, and dropping it changes nothing
/// on any tree of up to eight keys, by `delete_min` or by `delete` of any key, shapes and colors
/// included (checked exhaustively over every insertion order): the `fix_up` on the way back up
/// flips the same node. From ten keys on it does not. This prefix, the smallest found (no nine-key
/// tree in 500 000 random ones), is invalid after `delete_min` for most last keys from 26 up
/// without that flip. The test runs every last key in `0..=40`.
const NINE: [i32; 9] = [25, 2, 4, 22, 32, 8, 37, 19, 1];

#[test]
fn delete_min_needs_move_red_lefts_last_flip() {
    for k in 0..=40 {
        delete_min_after(&NINE, k);
    }
}
