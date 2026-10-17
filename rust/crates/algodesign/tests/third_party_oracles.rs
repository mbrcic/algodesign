// SPDX-License-Identifier: Apache-2.0
//! Differential tests against two independent crates: `suffix` (SA-IS) for
//! `algodesign::strings::suffix_array::suffix_array`, and `bio`'s suffix array (also SA-IS) plus its
//! `bwt` routine for `algodesign::strings::bwt::encode`. Both are dev-dependencies, used only here --
//! neither is a dependency of the library itself.

use proptest::prelude::*;

// Both crates build the suffix array by SA-IS, not by prefix doubling, so agreement is evidence
// rather than a tautology. `occ` has no third-party oracle; `count_index` checks it against
// `naive::rank`.
proptest! {
    #[test]
    fn suffix_array_agrees_with_the_suffix_crate(text in "[a-d]{1,400}") {
        // `suffix::SuffixTable` takes a `&str` but its entries are byte indices into the text,
        // as ours are. The small alphabet `[a-d]` gives the ties and shared prefixes that stress
        // a suffix-array construction.
        let ours = algodesign::strings::suffix_array::suffix_array(text.as_bytes());
        let theirs = suffix::SuffixTable::new(text.as_str());
        prop_assert_eq!(ours.as_slice(), theirs.table());
    }

    #[test]
    fn bwt_agrees_with_rust_bio(text in "[a-d]{1,400}") {
        // One `0` byte at the end, this crate's `bwt::SENTINEL` convention, also meets bio's
        // (a smallest sentinel at the end, several allowed). Both read the last column as
        // `text[(p + n - 1) % n]`, so what is compared is bio's SA-IS suffix array against this
        // crate's prefix doubling.
        let mut t = text.into_bytes();
        t.push(0);
        let ours = algodesign::strings::bwt::encode(&t);
        let sa = bio::data_structures::suffix_array::suffix_array(&t);
        let theirs = bio::data_structures::bwt::bwt(&t, &sa);
        prop_assert_eq!(ours, theirs);
    }
}
