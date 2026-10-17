// SPDX-License-Identifier: Apache-2.0
//! Implementations for the textbook *Modern Algorithm Design*, one module per book topic.
//!
//! - [`searching`]: the Search chapter -- sequential and binary search, the
//!   binary search tree, the left-leaning and the standard red-black tree, the treap, the B-tree
//!   and the LSM-tree.
//! - [`strings`]: the Strings chapter -- Rabin-Karp, the trie and Patricia
//!   tree, the suffix array and LCP array, the Burrows-Wheeler transform, rank/select directories
//!   and the FM-index.
//! - [`geometry`]: the geometry chapter -- the scan, the k-d tree and the range tree, the
//!   orientation test, random projection, LSH, HNSW and RaBitQ.
//!
//! Each topic module re-exports its main types, so `algodesign::searching::Bst` names the same
//! type as `algodesign::searching::bst::Bst`. Most modules mirror a Lean file under
//! `lean/AlgoDesign/`, where the structure's properties are proved; each topic module says which.
//!
//! Unit tests that need private internals are in `src/<topic>/unit_tests/`; tests of the public
//! API are in `tests/`.

pub mod geometry;
pub(crate) mod rng;
pub mod searching;
pub mod strings;
