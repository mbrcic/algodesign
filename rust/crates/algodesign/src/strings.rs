// SPDX-License-Identifier: Apache-2.0
//! Implementations for the Strings chapter of *Modern Algorithm Design*.
//!
//! One implementation per algorithm: the variant the book teaches, written to be fast. Positions
//! are `u32`, so one index covers at most `u32::MAX` characters; larger corpora shard at a record
//! boundary. There is no `unsafe` (`unsafe_code = "forbid"`).
//!
//! Each module mirrors one file of `lean/AlgoDesign/Strings/`, except [`naive`] (the plain scan,
//! and the tests' slow references) and the compressed-`occ` modules ([`rrr`], [`wavelet_tree`],
//! [`chunked_wavelet`], [`occ`]), which have no Lean model. No Lean proof transfers to this code;
//! the property tests, `tests/third_party_oracles.rs` and differential tests against the Lean
//! definitions hold it to the Lean. A test that mirrors a Lean theorem says so in a
//! `// Lean: <name>` comment. Step counts cited from Lean's `TimeM` are costs of the `List Nat`
//! models, not measurements of this crate.
//!
//! # Conventions
//!
//! **`#[must_use]`** is on every pure public method that returns a value, except the two
//! `insert`s: a method that returns the value it displaced ([`trie::Trie::insert`],
//! [`patricia::Patricia::insert`]) does not carry it, as `HashMap::insert` does not.
//! `clippy::must_use_candidate` enforces most of them (below).
//!
//! **Errors.**
//!
//! - **`Result` for input from outside the program:** [`bwt::try_encode`] and
//!   [`fm_index::FmIndex::try_build`] return [`bwt::EncodeError`] naming the misplaced sentinel or
//!   the length past `u32::MAX`; [`bwt::try_decode`] returns [`bwt::DecodeError`] naming the
//!   sentinel count of a last column read back, or its length; and [`records::Corpus::try_build`]
//!   returns [`records::BuildError`] naming the record, the position and the reserved byte, or the
//!   length of a concatenation past `u32::MAX`. [`bwt::encode`], [`bwt::decode`],
//!   [`fm_index::FmIndex::build`] and [`records::Corpus::build`] are the panicking conveniences.
//! - **Panic on a broken contract, documented under `# Panics`:** a sampling rate of zero
//!   ([`fm_index::FmIndex::build`]), record starts not beginning at 0
//!   ([`records::Records::new`]), a `len` past the bits supplied ([`count_index::BitIndex::new`]),
//!   a text longer than `u32::MAX` ([`suffix_array::suffix_array`], [`rabin_karp::search`]), a
//!   suffix array of the wrong length or with an entry past the text ([`lcp::lcp`]).
//! - **The empty answer for a query that cannot match:** [`records::Corpus::find`] and
//!   [`records::Corpus::count`] return nothing for a fragment carrying [`bwt::SENTINEL`] or
//!   [`records::SEPARATOR`].
//! - **The empty pattern occurs at every shift**, as CLRS's definition of a valid shift gives
//!   (shifts `0..=n`):
//!   [`naive::search`], [`rabin_karp::search`] and [`suffix_array::search`] answer so;
//!   [`fm_index::FmIndex::count`] answers [`fm_index::FmIndex::text_len`], one per row; and
//!   [`records::Corpus::find`] answers every quote.

#![warn(clippy::must_use_candidate)]
// Held here rather than workspace-wide: each was met with few or no fixes in these modules.
// `allow_attributes_without_reason` asks every `allow` to say, in its `reason`, why it is safe.
#![warn(
    clippy::checked_conversions,
    clippy::doc_markdown,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::allow_attributes_without_reason,
    missing_debug_implementations
)]
// Positions are created here (the suffix array, LCP, the samples, the directories), and one that
// does not fit its integer must be refused, never wrapped. Every narrowing `as` in these modules
// is therefore either a `try_from` that fails loudly or carries an `allow` naming the bound that
// makes it exact. Not in the test build: the unit tests' inputs are small by construction.
#![cfg_attr(not(test), warn(clippy::cast_possible_truncation))]

pub mod backward_search;
mod bits;
pub mod bwt;
pub mod chunked_wavelet;
pub mod count_index;
pub mod fm_index;
pub mod lcp;
pub mod naive;
pub mod occ;
pub mod patricia;
pub mod rabin_karp;
pub mod records;
pub mod rrr;
pub mod suffix_array;
pub mod trie;
pub mod wavelet_tree;

pub use chunked_wavelet::ChunkedWavelet;
pub use count_index::{Alphabet, BitIndex, ByteIndex};
pub use fm_index::FmIndex;
pub use occ::Occ;
pub use patricia::Patricia;
pub use records::{Corpus, Quote, Records};
pub use rrr::Rrr;
pub use trie::Trie;
pub use wavelet_tree::WaveletTree;

/// What this module keeps out of reach, as doctests: `cargo test --doc` collects them.
#[cfg(doctest)]
#[path = "strings/unit_tests/unchecked.rs"]
mod unchecked_doctests;
