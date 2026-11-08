// SPDX-License-Identifier: Apache-2.0
//! The LCP array by Kasai's algorithm (CLRS 4th ed. §32.5, `COMPUTE-LCP`): `lcp[i]` is the
//! common-prefix length of the suffixes at `sa[i - 1]` and `sa[i]`, and `lcp[0]` is `0`.
//!
//! Lean: `SuffixArray/LCP.lean`, `kasai_eq`.

/// The LCP array of `text`, given its suffix array `sa`, by Kasai's algorithm.
///
/// `O(n)`: `h` drops by at most one per position. `sa` must be `suffix_array(text)`. Lean:
/// `kasai_eq`.
///
/// # Panics
///
/// If `sa.len() != text.len()`, or an entry of `sa` is out of range:
///
/// ```should_panic
/// algodesign::strings::lcp::lcp(b"banana", &[0, 1, 2, 3, 4, 99]);
/// ```
#[must_use]
pub fn lcp(text: &[u8], sa: &[u32]) -> Vec<u32> {
    let n = text.len();
    assert_eq!(sa.len(), n, "sa must be the suffix array of text");
    if n == 0 {
        return Vec::new();
    }

    // row is sa's inverse, the row where each suffix sits; the casts below are of values below `n`.
    let mut row = vec![0u32; n];
    #[allow(
        clippy::cast_possible_truncation,
        reason = "i < n <= u32::MAX, the suffix array being of a text that long"
    )]
    for (i, &p) in sa.iter().enumerate() {
        row[p as usize] = i as u32;
    }

    let mut out = vec![0u32; n];
    let mut h: usize = 0;
    for p in 0..n {
        let r = row[p] as usize;
        #[allow(clippy::cast_possible_truncation, reason = "h < n <= u32::MAX")]
        if r > 0 {
            let q = sa[r - 1] as usize;
            while p + h < n && q + h < n && text[p + h] == text[q + h] {
                h += 1;
                #[cfg(test)]
                MATCHED.with(|m| m.set(m.get() + 1));
            }
            out[r] = h as u32;
        }
        // The next suffix shares at least `h - 1` with its predecessor.
        h = h.saturating_sub(1);
    }
    out
}

#[cfg(test)]
thread_local! {
    /// Successful byte comparisons [`lcp`] has made on this thread.
    static MATCHED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The longest substring occurring at least twice (possibly overlapping), the smallest in byte
/// order on ties; empty if no byte repeats. `O(n log n)`. Lean: `longestRepeat`.
#[must_use]
pub fn longest_repeat(text: &[u8]) -> &[u8] {
    let sa = crate::strings::suffix_array::suffix_array(text);
    let (mut best_row, mut best_len) = (0usize, 0u32);
    for (row, &len) in lcp(text, &sa).iter().enumerate() {
        if len > best_len {
            (best_row, best_len) = (row, len);
        }
    }
    if best_len == 0 {
        return &[];
    }
    let start = sa[best_row] as usize;
    &text[start..start + best_len as usize]
}

#[cfg(test)]
#[path = "unit_tests/lcp.rs"]
mod tests;
