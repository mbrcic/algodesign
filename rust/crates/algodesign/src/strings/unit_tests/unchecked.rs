// SPDX-License-Identifier: Apache-2.0
//! What the strings module keeps out of reach, as doctests. Each example compiles only with the
//! `unchecked` feature, or not at all, and checks the error code it fails with; with the feature
//! on, the feature-gated ones run. Compiled only when rustdoc collects doctests, so no page of the
//! documentation shows them.

/// `FmIndex::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::strings::fm_index::FmIndex;
///
/// let mut parts = FmIndex::build(b"banana\0", 2).to_parts();
/// parts.c[1] += 1;
/// let lying = FmIndex::from_parts_unchecked(parts);
/// assert_eq!(lying.check_valid(), Err("not in the box (smaller_letters_counted)")); // a `C` no column has
/// ```
pub struct FmIndexFromParts;

/// `Patricia::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::strings::patricia::Patricia;
///
/// let mut p = Patricia::new();
/// p.insert(b"ab", 1);
/// let lying = Patricia::from_parts_unchecked(p.to_parts(), 2);
/// assert!(!lying.is_valid()); // `len` says two keys: the tree `insert` could never build
/// ```
pub struct PatriciaFromParts;

/// `Records::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::strings::records::Records;
///
/// let late = Records::from_parts_unchecked(&[false, false, true], 1);
/// assert!(!late.is_valid()); // positions 0 and 1 lie in no record: `new` refuses this
/// ```
pub struct RecordsFromParts;

/// `Corpus::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::strings::fm_index::FmIndex;
/// use algodesign::strings::records::{Corpus, Records};
///
/// // The records `ab` and `c`, but the second said to start one byte early.
/// let index = FmIndex::build(b"ab\x01c\0", 32);
/// let records = Records::from_parts_unchecked(&[true, false, true, false, false], 2);
/// let lying = Corpus::from_parts_unchecked(index, records);
/// assert!(!lying.is_valid()); // the separator is not where the starts put it
/// ```
pub struct CorpusFromParts;

/// `Trie::from_parts_unchecked` needs the `unchecked` feature.
///
#[cfg_attr(not(feature = "unchecked"), doc = "```compile_fail,E0599")]
#[cfg_attr(feature = "unchecked", doc = "```")]
/// use algodesign::strings::trie::Trie;
///
/// let mut t = Trie::new();
/// t.insert(b"ab", 1);
/// let lying = Trie::from_parts_unchecked(t.to_parts(), 2);
/// assert!(!lying.is_valid()); // `len` says two keys: the trie `insert` could never build
/// ```
pub struct TrieFromParts;
