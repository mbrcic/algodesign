// SPDX-License-Identifier: Apache-2.0
//! Heap allocations per operation, counted and held to the measured numbers.
//!
//! An update that rebuilt its path with fresh boxes would pass every lookup test, because a
//! rebuilt path holds the same keys in the same shape. Only a count sees it.
//!
//! Counted: allocations *and* reallocations, since a `Vec` that regrows by doubling reallocates
//! rather than allocates.
//!
//! `harness = false` (see `Cargo.toml`): the counter is global to the process, so this runs as a
//! plain `main` on one thread, and a failed check panics, which fails `cargo test`.

use std::alloc::System;
use std::hint::black_box;

use algodesign::searching::{
    bst::Bst, btree::BTree, llrb::Llrb, red_black_standard::RbTree, treap::Treap,
};
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

/// Run `f`, and return what it returned with the heap blocks it asked for, fresh or regrown.
fn counted<R>(f: impl FnOnce() -> R) -> (R, usize) {
    let region = Region::new(GLOBAL);
    let r = f();
    let s = region.change();
    (r, s.allocations + s.reallocations)
}

/// `n` distinct keys in a scrambled order (SplitMix64 is a bijection on `u64`).
fn keys(n: u64) -> Vec<u64> {
    (0..n).map(splitmix64).collect()
}

fn splitmix64(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The binary trees: exactly one allocation per new key (its node), none for a key already
/// there, none to look up, count or delete. `$t` is a tree, `$insert` its insert call.
macro_rules! binary_tree {
    ($name:literal, $t:expr, |$tree:ident, $k:ident| $insert:expr) => {{
        let ks = keys(2_000);
        let mut $tree = $t;
        for &$k in &ks {
            let (added, a) = counted(|| $insert);
            assert!(added);
            assert_eq!(
                a, 1,
                "{}: insert of a new key allocated {a}, not its one node",
                $name
            );
        }
        for &$k in &ks {
            let (added, a) = counted(|| $insert);
            assert!(!added);
            assert_eq!(a, 0, "{}: insert of a present key allocated {a}", $name);
        }
        for k in &ks {
            let (hit, a) = counted(|| $tree.contains(black_box(k)));
            assert!(hit);
            assert_eq!(a, 0, "{}: contains allocated {a}", $name);
        }
        let ((len, empty), a) = counted(|| (black_box(&$tree).len(), $tree.is_empty()));
        assert_eq!((len, empty), (ks.len(), false));
        assert_eq!(a, 0, "{}: len/is_empty allocated {a}", $name);
        $tree
    }};
}

/// Deleting frees; it never allocates. Every key, then every key again (now absent).
macro_rules! deletes_allocate_nothing {
    ($name:literal, $tree:ident) => {{
        let ks = keys(2_000);
        for pass in 0..2 {
            for k in &ks {
                let (removed, a) = counted(|| $tree.delete(black_box(k)));
                assert_eq!(removed, pass == 0);
                assert_eq!(a, 0, "{}: delete allocated {a}", $name);
            }
        }
        assert!($tree.is_empty());
    }};
}

fn main() {
    // Bst, and its order statistics: `rank`/`select` steer by the cached subtree counts and
    // allocate nothing (they once walked, which allocated, and cost O(n) per call).
    let mut bst = binary_tree!("Bst", Bst::new(), |t, k| t.insert(k));
    for (i, k) in keys(2_000).iter().enumerate().step_by(7) {
        let (r, a) = counted(|| bst.rank(black_box(k)));
        assert_eq!(a, 0, "Bst: rank allocated {a}");
        let (s, b) = counted(|| bst.select(black_box(r)).copied());
        assert_eq!(s, Some(*k), "select(rank(k)) = k, at key {i}");
        assert_eq!(b, 0, "Bst: select allocated {b}");
    }
    deletes_allocate_nothing!("Bst", bst);
    let mut bst = binary_tree!("Bst", Bst::new(), |t, k| t.insert(k));
    for k in &keys(2_000) {
        let (_, a) = counted(|| bst.delete_hibbard(black_box(k)));
        assert_eq!(a, 0, "Bst: delete_hibbard allocated {a}");
    }

    let mut llrb = binary_tree!("Llrb", Llrb::new(), |t, k| t.insert(k));
    deletes_allocate_nothing!("Llrb", llrb);
    let mut llrb = binary_tree!("Llrb", Llrb::new(), |t, k| t.insert(k));
    while !llrb.is_empty() {
        let (_, a) = counted(|| llrb.delete_min());
        assert_eq!(a, 0, "Llrb: delete_min allocated {a}");
    }

    let mut rb = binary_tree!("RbTree", RbTree::new(), |t, k| t.insert(k));
    deletes_allocate_nothing!("RbTree", rb);

    // Treap: the new node, plus the rotate-up insert's path stack, which keeps eight levels
    // inline and spills to a `Vec` on a deeper path, now and then. Measured on these keys:
    // 2055 blocks for 2000 inserts (1949 took one, 47 two, 4 three). A path rebuilt with fresh
    // boxes would cost one more block for every level the insert passes.
    {
        let ks = keys(2_000);
        let mut treap = Treap::new();
        let mut total = 0;
        for &k in &ks {
            let (added, a) = counted(|| treap.insert(k, splitmix64(k ^ 0x5EED)));
            assert!(added);
            assert!(
                a >= 1,
                "Treap: an insert that adds a key allocates its node"
            );
            total += a;
        }
        assert!(
            total * 100 <= ks.len() * 105,
            "Treap: {total} allocations for {} inserts, more than 1.05 per key",
            ks.len()
        );
        for k in &ks {
            let (_, a) = counted(|| treap.contains(black_box(k)));
            assert_eq!(a, 0, "Treap: contains allocated {a}");
        }
        let ((len, empty), a) = counted(|| (black_box(&treap).len(), treap.is_empty()));
        assert_eq!((len, empty), (ks.len(), false));
        assert_eq!(a, 0, "Treap: len/is_empty allocated {a}");
        deletes_allocate_nothing!("Treap", treap);
    }

    // BTree: a split allocates the new node's buffers, at full capacity, so the node never
    // regrows; nothing else allocates. At n = 100 000 it is 0.152 blocks per key at `t = 6` and
    // 0.011 at `t = 64`; these 20 000 keys measure 0.151 and 0.012.
    for (t, per_mille) in [(6, 160), (64, 15)] {
        let ks = keys(20_000);
        let mut tree = BTree::new(t);
        let (_, build) = counted(|| {
            for &k in &ks {
                tree.insert(k);
            }
        });
        assert!(
            build * 1000 <= ks.len() * per_mille,
            "BTree t={t}: {build} allocations for {} keys, above {per_mille} per thousand",
            ks.len()
        );
        for k in &ks {
            let (_, a) = counted(|| tree.contains(black_box(k)));
            assert_eq!(a, 0, "BTree: contains allocated {a}");
        }
        let ((len, empty), a) = counted(|| (black_box(&tree).len(), tree.is_empty()));
        assert_eq!((len, empty), (ks.len(), false));
        assert_eq!(a, 0, "BTree: len/is_empty allocated {a}");
        // A clone deletes as cheaply as the original: its nodes are cloned at full capacity too.
        let mut copy = tree.clone();
        for k in &ks {
            let (_, a) = counted(|| copy.delete(black_box(k)));
            assert_eq!(a, 0, "BTree t={t}: delete from a clone allocated {a}");
        }
        for k in &ks {
            let (_, a) = counted(|| tree.delete(black_box(k)));
            assert_eq!(a, 0, "BTree t={t}: delete allocated {a}");
        }
    }
}
