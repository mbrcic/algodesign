// SPDX-License-Identifier: Apache-2.0
//! Backward search's running state as a check on any interval `[lo, hi)` of suffix-array rows
//! after reading `read`, the pattern's last symbols. Reads the text and its suffix array, so it
//! is for tests. Lean: `BackwardSearch.Valid` (`FMIndex/Spec.lean`).

/// Suffix `p` of `text`, empty past the end.
fn suffix(text: &[u8], p: usize) -> &[u8] {
    text.get(p..).unwrap_or(&[])
}

/// Box invariant 1: the rows kept so far are exactly the suffixes that start with the part of the
/// pattern read so far. Lean: `StretchHoldsMatches`.
#[must_use]
pub fn is_stretch_holds_matches(
    text: &[u8],
    sa: &[u32],
    read: &[u8],
    lo: usize,
    hi: usize,
) -> bool {
    (0..hi + sa.len()).all(|r| {
        let inside = lo <= r && r < hi;
        let matches = sa
            .get(r)
            .is_some_and(|&p| suffix(text, p as usize).starts_with(read));
        inside == matches
    })
}

/// Not in the box: `lo` counts the suffixes sorting below `read`. Lean:
/// `StretchStartsRight`.
#[must_use]
pub fn is_stretch_starts_right(text: &[u8], read: &[u8], lo: usize) -> bool {
    lo == (0..text.len()).filter(|&i| suffix(text, i) < read).count()
}

/// Not in the box: `hi - lo` is the number of occurrences of `read`. Lean:
/// `StretchAsWideAsMatches`.
#[must_use]
pub fn is_stretch_as_wide_as_matches(text: &[u8], read: &[u8], lo: usize, hi: usize) -> bool {
    let occurrences = (0..text.len())
        .filter(|&i| suffix(text, i).starts_with(read))
        .count();
    hi == lo + occurrences
}

/// All three pieces. Lean: `BackwardSearch.Valid`.
#[must_use]
pub fn is_valid(text: &[u8], sa: &[u32], read: &[u8], lo: usize, hi: usize) -> bool {
    check_valid(text, sa, read, lo, hi).is_ok()
}

/// [`is_valid`], naming the first piece that fails.
///
/// # Errors
///
/// `"invariant 1 (stretch_holds_matches)"`, `"not in the box (stretch_starts_right)"` or
/// `"not in the box (stretch_as_wide_as_matches)"`.
pub fn check_valid(
    text: &[u8],
    sa: &[u32],
    read: &[u8],
    lo: usize,
    hi: usize,
) -> Result<(), &'static str> {
    if !is_stretch_holds_matches(text, sa, read, lo, hi) {
        return Err("invariant 1 (stretch_holds_matches)");
    }
    if !is_stretch_starts_right(text, read, lo) {
        return Err("not in the box (stretch_starts_right)");
    }
    if !is_stretch_as_wide_as_matches(text, read, lo, hi) {
        return Err("not in the box (stretch_as_wide_as_matches)");
    }
    Ok(())
}

#[cfg(test)]
#[path = "unit_tests/backward_search.rs"]
mod tests;
