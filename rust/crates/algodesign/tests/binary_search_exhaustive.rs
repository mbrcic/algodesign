// SPDX-License-Identifier: Apache-2.0
//! `binary_search::search` against an independent linear scan, on every small input.
//!
//! The proptest in `src/searching/binary_search.rs` samples large arrays at random. This test is the
//! exhaustive complement: every non-decreasing array of length 0 to 4 over the values `0..=4`
//! (duplicates included, 126 arrays), searched for every target in `-1..=5` (below, between and
//! above the values). That is every shape the closed stretch `[lo, hi]` can take on up to four
//! elements, with every comparison outcome at every probe.

use algodesign::searching::binary_search::search;

const MAX_LEN: usize = 4;
const VALUES: std::ops::RangeInclusive<i32> = 0..=4;
const TARGETS: std::ops::RangeInclusive<i32> = -1..=5;

/// Every non-decreasing array of exactly `len` elements drawn from `VALUES`.
fn sorted_arrays(len: usize) -> Vec<Vec<i32>> {
    let mut out = vec![Vec::new()];
    for _ in 0..len {
        let mut next = Vec::new();
        for xs in &out {
            let lo = xs.last().copied().unwrap_or(*VALUES.start());
            for v in lo..=*VALUES.end() {
                let mut ys = xs.clone();
                ys.push(v);
                next.push(ys);
            }
        }
        out = next;
    }
    out
}

/// `search` returns an index holding the target exactly when the target is present. Membership
/// is recomputed by a linear scan, so the check assumes nothing about `search`'s own logic.
#[test]
fn search_agrees_with_presence_on_every_small_sorted_array() {
    let mut arrays = 0;
    for len in 0..=MAX_LEN {
        for xs in sorted_arrays(len) {
            arrays += 1;
            for target in TARGETS {
                let present = xs.contains(&target);
                match search(&xs, &target) {
                    Some(idx) => {
                        assert!(idx < xs.len(), "{xs:?}, {target}: index {idx} out of range");
                        assert_eq!(xs[idx], target, "{xs:?}, {target}: wrong index {idx}");
                    }
                    None => assert!(!present, "{xs:?}, {target}: present but not found"),
                }
            }
        }
    }
    // C(5 + len - 1, len) for len = 0..=4: 1 + 5 + 15 + 35 + 70.
    assert_eq!(arrays, 126);
}
