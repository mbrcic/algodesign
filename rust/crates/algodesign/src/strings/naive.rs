// SPDX-License-Identifier: Apache-2.0
//! The plain scan: every start of a pattern, tried one shift at a time, the search the Strings
//! chapter starts from and the one every faster search is measured against.
//!
//! The other functions here are slow references that are correct by inspection, for the tests to
//! compare the real structures against. They are built only for the tests and behind the
//! `unchecked` feature, so they are not part of the library's interface.

/// Every start of `pat` in `text`, checked one shift at a time (CLRS §32.1). `O(n·m)`.
///
/// # Panics
///
/// If a match starts past `u32::MAX`.
#[must_use]
pub fn search(text: &[u8], pat: &[u8]) -> Vec<u32> {
    if pat.len() > text.len() {
        return Vec::new();
    }
    (0..=text.len() - pat.len())
        .filter(|&i| &text[i..i + pat.len()] == pat)
        .map(|i| u32::try_from(i).expect("positions are u32"))
        .collect()
}

/// Suffix array by sorting slices. `O(n² log n)`.
///
/// # Panics
///
/// If `text` is longer than `u32::MAX`.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn suffix_array(text: &[u8]) -> Vec<u32> {
    let n = u32::try_from(text.len()).expect("positions are u32");
    let mut sa: Vec<u32> = (0..n).collect();
    sa.sort_by(|&a, &b| text[a as usize..].cmp(&text[b as usize..]));
    sa
}

/// BWT by sorting the rotation matrix.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn bwt_rotations(text: &[u8]) -> Vec<u8> {
    let n = text.len();
    let mut rots: Vec<Vec<u8>> = (0..n)
        .map(|i| text[i..].iter().chain(&text[..i]).copied().collect())
        .collect();
    rots.sort();
    rots.iter().map(|r| r[n - 1]).collect()
}

/// Set bits strictly before `i`, counted one by one.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[must_use]
pub fn rank(words: &[u64], i: usize) -> usize {
    (0..i)
        .filter(|&b| words[b / 64] >> (b % 64) & 1 == 1)
        .count()
}

#[cfg(test)]
#[path = "unit_tests/naive.rs"]
mod tests;
