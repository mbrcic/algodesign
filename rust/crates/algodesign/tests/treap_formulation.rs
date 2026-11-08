// SPDX-License-Identifier: Apache-2.0
//! `Treap`'s two formulations must build the same trees, node for node.
//!
//! The module implements the textbook insert -- descend as an ordinary BST insert, then rotate the
//! new node up while it outranks its parent -- with an explicit stack in place of the recursion.
//! Deletion sinks the doomed node iteratively. Those are equality claims about *shape*, not just about which keys survive, and shape is what the
//! unit tests in `src/searching/treap.rs` do not pin: every one of them would pass against a formulation
//! that balanced differently, so long as it stayed a valid treap over the same keys.
//!
//! This walks a deterministic corpus and folds every intermediate tree into two hashes. `SHAPES`
//! takes the structure after each of 15360 updates, spelled out by `Treap`'s own `Debug`
//! (parenthesised, priorities included), plus each operation's return value, `len`, `is_valid`
//! and key sequence; `KEYS` takes the same run with the renderings left out. Two hashes because
//! only one of them survives a change to how a tree prints, and a reader who sees a red build
//! needs to know at a glance which kind of change caused it.
//!
//! `KEYS` is the same for the recursive formulation and the iterative one. `SHAPES` pins the tie
//! and duplicate rules of the textbooks (the right root lifted on a delete tie; a present key left
//! unchanged).
//!
//! The hash is spelled out here rather than taken from `DefaultHasher`, whose algorithm std
//! explicitly declines to keep stable across releases -- a golden constant hashed with it would
//! turn a toolchain upgrade into a red build with a misleading message.

use algodesign::searching::treap::Treap;

/// Every intermediate tree, `Debug`-rendered: shape, keys and priorities.
const SHAPES: u64 = 0xdbb4_b318_1446_b189;
/// The same run with the renderings left out: keys, counts and verdicts only.
const KEYS: u64 = 0x063d_43aa_6281_58de;
const UPDATES: u64 = 15360;

/// FNV-1a, 64-bit. Fixed here so the constants above outlive any toolchain.
#[derive(Clone, Copy)]
struct Fnv(u64);

impl Fnv {
    fn new() -> Self {
        Fnv(0xcbf2_9ce4_8422_2325)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0 ^ u64::from(*b)).wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    fn u64(&mut self, v: u64) {
        self.write(&v.to_le_bytes());
    }
    fn flag(&mut self, v: bool) {
        self.write(&[u8::from(v)]);
    }
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Fold one tree state into both hashes: the rendering into `shapes`, everything else into both.
fn record(shapes: &mut Fnv, keys: &mut Fnv, t: &Treap<u64>, answer: bool) {
    shapes.write(format!("{t:?}").as_bytes());
    for h in [&mut *shapes, &mut *keys] {
        h.flag(answer);
        h.u64(t.len() as u64);
        h.flag(t.is_valid());
        for k in t {
            h.u64(*k);
        }
    }
}

#[test]
fn every_intermediate_tree_matches_the_recursive_formulation() {
    let mut shapes = Fnv::new();
    let mut keys = Fnv::new();
    let mut updates: u64 = 0;

    for seed in 0..40u64 {
        for n in [1usize, 2, 3, 5, 8, 13, 40, 120] {
            let mut rng = 0x_5BE7_C0DE_0000_0000 ^ (seed << 8) ^ (n as u64);
            let mut t: Treap<u64> = Treap::new();
            for _ in 0..n {
                // Keys drawn from twice the range, so re-inserts are common; a quarter of the
                // priorities are drawn from a tiny range instead, so ties and the
                // already-present-and-outranked path are both reached often.
                let k = splitmix64(&mut rng) % (2 * n as u64);
                let pr = splitmix64(&mut rng);
                let pr = if pr % 4 == 0 { pr % 16 } else { pr };
                let added = t.insert(k, pr);
                record(&mut shapes, &mut keys, &t, added);
                updates += 1;
            }
            for _ in 0..n {
                let k = splitmix64(&mut rng) % (2 * n as u64);
                let hit = t.delete(&k);
                record(&mut shapes, &mut keys, &t, hit);
                updates += 1;
            }
            // A clone must be the same tree under the hand-written `PartialEq`, which compares
            // priorities as well as keys, on an explicit stack.
            let copy = t.clone();
            assert!(copy == t, "clone differs from its source");
            assert_eq!(format!("{copy:?}"), format!("{t:?}"));
        }
    }

    assert_eq!(updates, UPDATES, "the corpus changed size");
    // Keys first: if both fail, the algorithm changed; if only the second does, the rendering did.
    assert_eq!(keys.0, KEYS, "the corpus no longer holds the same keys");
    assert_eq!(
        shapes.0, SHAPES,
        "some tree in the corpus is a different shape, or prints differently"
    );
}
