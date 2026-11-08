// SPDX-License-Identifier: Apache-2.0
//! Deep-shape regression: the two structures here whose depth the caller controls must survive a
//! degenerate one on a small stack.
//!
//! `Bst` and `Treap` are the only two. The three balanced trees (`Llrb`, `RbTree`, `BTree`) bound
//! their own height, so their recursive drop glue and derived traits are bounded with it; `Lsm` is
//! flat. `Bst` degenerates on sorted input, which is the case the Search chapter is *about*. `Treap`
//! degenerates only under caller-chosen priorities -- `insert_random` makes it vanishingly
//! unlikely -- but `Treap::insert` takes an explicit priority, so a hash-as-priority scheme under
//! adversarial keys reaches this shape, and the API must not abort when it does.
//!
//! A stack overflow is a SIGABRT, not a panic: it cannot be caught, so a regression here fails by
//! killing the test binary with "fatal runtime error: stack overflow" rather than by an assertion
//! message. That is the whole reason this file exists: an operation below that recursed once per
//! level would abort here, and nothing else in the suite would notice.
//!
//! The stack is deliberately 256 KiB, an eighth of the 2 MiB a spawned thread gets by default and
//! a thirty-second of the main thread's 8 MiB, so the margin is real rather than incidental. Each
//! body runs in its own thread for that reason and no other.

use algodesign::searching::bst::Bst;
use algodesign::searching::treap::Treap;

/// Enough levels that any per-level frame overflows 256 KiB.
const N: u64 = 10_000;
const SMALL_STACK: usize = 256 * 1024;

fn on_a_small_stack<F: FnOnce() + Send + 'static>(body: F) {
    std::thread::Builder::new()
        .stack_size(SMALL_STACK)
        .spawn(body)
        .expect("spawning a thread")
        .join()
        .expect("the body panicked");
}

#[test]
fn bst_survives_a_sorted_spine() {
    on_a_small_stack(|| {
        let mut t: Bst<u64> = Bst::new();
        for i in 0..N {
            assert!(t.insert(i));
        }
        assert_eq!(t.len(), N as usize);
        // The checker walks every node of the spine against the interval its ancestors allow.
        assert!(t.is_valid());
        assert!(t.contains(&(N - 1)));
        assert_eq!(t.min(), Some(&0));
        assert_eq!(t.max(), Some(&(N - 1)));
        assert_eq!(t.iter().count(), N as usize);

        // `range` descends twice and walks with two stacks; on a spine both descents are N deep,
        // which is exactly the shape a recursive seed would abort on. The bounds are inside the
        // spine on both sides so neither descent stops early.
        assert_eq!(t.range(1..N - 1).count(), N as usize - 2);
        assert_eq!(t.range(1..N - 1).next(), Some(&1));
        assert_eq!(t.range(1..N - 1).next_back(), Some(&(N - 2)));
        assert_eq!(t.range(..).rev().count(), N as usize);

        let copy = t.clone();
        assert!(copy == t);
        assert_eq!(format!("{t:?}").len(), format!("{copy:?}").len());

        assert!(t.delete(&(N - 1)));
        assert!(t.is_valid());
        drop(copy);
        drop(t);
    });
}

#[test]
fn treap_survives_caller_chosen_priorities() {
    on_a_small_stack(|| {
        // Decreasing priority against increasing key: every node is forced under the previous
        // one, so the treap is a right spine of N nodes and still perfectly valid.
        let mut t: Treap<u64> = Treap::new();
        for i in 0..N {
            assert!(t.insert(i, N - i));
        }
        assert_eq!(t.len(), N as usize);
        assert!(t.is_valid());
        assert!(t.contains(&(N - 1)));
        assert_eq!(t.iter().count(), N as usize);

        let copy = t.clone();
        assert!(copy == t);
        assert_eq!(format!("{t:?}").len(), format!("{copy:?}").len());

        // Deleting the spine's deepest key sinks a node the whole way down.
        assert!(t.delete(&(N - 1)));
        assert!(t.is_valid());
        // Inserting at the top priority rotates the new node up past the entire spine.
        assert!(t.insert(N, u64::MAX));
        assert!(t.is_valid());
        assert_eq!(t.len(), N as usize);

        drop(copy);
        drop(t);
    });
}
