// SPDX-License-Identifier: Apache-2.0
//! Implementations for the Search chapter of *Modern Algorithm Design*.
//!
//! One implementation per structure: the algorithm the book teaches, written to be fast. `BTree`'s
//! default degree is 6, std's own fanout. `Bst`, `Llrb`, `RbTree` and `Treap` write through `&mut`: `Bst`, `Llrb` and `RbTree` allocate only the new node on an insertion, `Treap` 1.03
//! allocations per key on average (its rotate-up path spills past eight levels), and a deletion
//! allocates nothing (`tests/allocations.rs`). `benches/structures.rs` times each structure
//! against `BTreeSet`.
//!
//! No input aborts the process: `Bst` and `Treap`, whose depth a caller can drive to `n`, run
//! every operation (drop, `Clone`, `PartialEq` and `Debug` included) on an explicit stack
//! (`tests/deep_trees.rs`). There is no `unsafe` (`unsafe_code = "forbid"`).
//!
//! Each module mirrors one file of `lean/AlgoDesign/Searching/`. No Lean proof transfers to
//! this code; the proptests beside each module hold it to the Lean's invariants. The invariant
//! predicates (`is_valid`, `check_valid` and their pieces), the `unchecked` feature's unchecked
//! constructors and a few `#[cfg(test)]` counters are the only checking aids in `src/`.
//!
//! # Conventions
//!
//! - **Lookups borrow:** every lookup takes `&Q where K: Borrow<Q>`, as `std`'s containers do, so
//!   finding a `String` key takes a `&str` (`tests/borrowed_lookup.rs`).
//! - **Panic on a broken contract, documented under `# Panics`:** a B-tree degree below two or
//!   past `usize::MAX / 2` ([`btree::BTree::new`]), an unusable LSM shape
//!   ([`lsm::Lsm::with_shape`]), and the two bound pairs `BTreeSet::range` rejects, in its words,
//!   on every `range`. Nothing here reads input from outside the program, so nothing returns a
//!   `Result` but the `check_valid` checkers.
//! - **`check_valid`** returns `Result<(), &'static str>` naming the first failed piece of the
//!   Lean `Valid`, in its order.
//! - **The chapter's counts are public:** a sequential search's checks
//!   ([`sequential_search::contains_with_checks`]), a binary search's glances
//!   ([`binary_search::search_with_glances`]), and the rotations of an LLRB, red-black or treap
//!   update (`insert_with_rotations`, `delete_with_rotations`). Each is a second entry point
//!   into the same code, made generic over what receives the count; the plain entry point gives
//!   it nothing to receive, so it pays nothing for the count.

#![warn(clippy::must_use_candidate)]
// Narrowing casts would be refused or explained, as in the Strings modules; these modules have
// none. Not in the test build: the unit tests' inputs are small by construction.
#![cfg_attr(not(test), warn(clippy::cast_possible_truncation))]
// `allow_attributes_without_reason` asks every `allow` to say, in its `reason`, why it is safe.
#![warn(
    clippy::checked_conversions,
    clippy::doc_markdown,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::allow_attributes_without_reason,
    missing_debug_implementations
)]

use std::ops::{Bound, RangeBounds};

pub mod binary_search;
pub mod bst;
pub mod btree;
pub mod llrb;
pub mod lsm;
pub mod red_black_standard;
pub mod sequential_search;
pub mod treap;

pub use bst::Bst;
pub use btree::BTree;
pub use llrb::Llrb;
pub use lsm::Lsm;
pub use red_black_standard::RbTree;
pub use treap::Treap;

/// Rejects the two bound combinations [`std::collections::BTreeSet::range`] rejects, in the same
/// words, naming `who`. An empty range such as `5..5` is legal.
pub(crate) fn check_bounds<'r, Q, R>(range: &'r R, who: &str) -> (Bound<&'r Q>, Bound<&'r Q>)
where
    Q: Ord + ?Sized,
    R: RangeBounds<Q>,
{
    let (start, end) = (range.start_bound(), range.end_bound());
    match (start, end) {
        (Bound::Excluded(s), Bound::Excluded(e)) if s == e => {
            panic!("range start and end are equal and excluded in {who}")
        }
        (Bound::Included(s) | Bound::Excluded(s), Bound::Included(e) | Bound::Excluded(e))
            if s > e =>
        {
            panic!("range start is greater than range end in {who}")
        }
        _ => {}
    }
    (start, end)
}

/// Where an operation reports the steps the chapter counts (a check, a glance, a rotation). The
/// plain entry points pass `()`, whose `add_one` is empty, so once the generic code is compiled
/// for `()` no count is left in it; the `*_with_*` entry points pass a `usize` and return it.
pub(crate) trait Count {
    /// One more step.
    fn add_one(&mut self);
}

impl Count for () {
    #[inline(always)]
    fn add_one(&mut self) {}
}

impl Count for usize {
    #[inline(always)]
    fn add_one(&mut self) {
        *self += 1;
    }
}

/// A stack capacity no root-to-leaf path of a red-black tree of `n` keys exceeds: the proved
/// height bound `2·lg(n + 1)`, plus one. Zero for the empty tree, which then allocates nothing.
pub(crate) fn height_bound(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        2 * (usize::BITS - n.leading_zeros()) as usize + 1
    }
}

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "searching/unit_tests/unchecked.rs"]
mod unchecked_doctests;
