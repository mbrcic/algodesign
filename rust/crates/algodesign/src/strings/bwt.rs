// SPDX-License-Identifier: Apache-2.0
//! The Burrows–Wheeler transform, computed through the suffix array as
//! `bwt[i] = text[(sa[i] + n - 1) % n]`, which is the sorted rotations' last column on a text
//! ending in one smallest sentinel. Lean: `lean/AlgoDesign/Strings/BWT/`.
//!
//! **Against the Python, and how fast.** The same procedure line for line, `block_start` and `seen`
//! named as in the chapter's listing; its time is the suffix-array build it calls. Not measured on
//! its own; `STRINGS_STRUCTURES_ONLY=1 cargo bench -p algodesign --bench strings` times that build
//! (`suffix_array/build`).

use crate::strings::suffix_array::suffix_array;

/// The byte that terminates every text [`encode`] accepts: `0`, below every other byte.
pub const SENTINEL: u8 = 0;

/// Why [`try_encode`] rejected a text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EncodeError {
    /// The text was empty, so it has no last byte to be the sentinel.
    Empty,
    /// The text's last byte was not [`SENTINEL`].
    MissingSentinel,
    /// The text is longer than `u32::MAX` bytes, the most `u32` positions can name.
    TooLong {
        /// The text's length.
        len: usize,
    },
    /// [`SENTINEL`] appeared at this position before the last one.
    SentinelBeforeEnd(usize),
}

impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(
                f,
                "bwt::encode: text is empty, so it cannot end with SENTINEL"
            ),
            Self::MissingSentinel => {
                write!(f, "bwt::encode: text must end with SENTINEL (0)")
            }
            Self::TooLong { len } => write!(
                f,
                "bwt::encode: {len} bytes, but positions are u32, so one text holds at most \
                 u32::MAX bytes; shard instead"
            ),
            Self::SentinelBeforeEnd(pos) => write!(
                f,
                "bwt::encode: SENTINEL (0) appeared at position {pos}, before the text's end; \
                 it may appear only as the last byte"
            ),
        }
    }
}

impl std::error::Error for EncodeError {}

/// Why [`try_decode`] rejected a last column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum DecodeError {
    /// The column was nonempty but held this many [`SENTINEL`] bytes, not exactly one.
    SentinelCount(usize),
    /// The column is longer than `u32::MAX` bytes, the most the `u32` counts and rows hold.
    TooLong {
        /// The column's length.
        len: usize,
    },
}

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SentinelCount(count) => write!(
                f,
                "bwt::decode: input must contain exactly one SENTINEL byte, found {count}"
            ),
            Self::TooLong { len } => write!(
                f,
                "bwt::decode: {len} bytes, but counts and rows are u32 and hold at most \
                 u32::MAX; shard instead"
            ),
        }
    }
}

impl std::error::Error for DecodeError {}

/// The Burrows–Wheeler transform of a sentinel-terminated `text`. `O(n log n)`. Lean:
/// `bwt_eq_rotations`.
///
/// # Errors
///
/// [`EncodeError`] unless `text` ends with its only [`SENTINEL`] and is at most `u32::MAX` bytes
/// long.
pub fn try_encode(text: &[u8]) -> Result<Vec<u8>, EncodeError> {
    try_encode_with_sa(text).map(|(last, _)| last)
}

/// [`try_encode`], also handing back the suffix array it was computed through.
pub(crate) fn try_encode_with_sa(text: &[u8]) -> Result<(Vec<u8>, Vec<u32>), EncodeError> {
    let n = text.len();
    match text.last() {
        None => return Err(EncodeError::Empty),
        Some(&b) if b != SENTINEL => return Err(EncodeError::MissingSentinel),
        Some(_) => {}
    }
    if u32::try_from(n).is_err() {
        return Err(EncodeError::TooLong { len: n });
    }
    if let Some(pos) = text[..n - 1].iter().position(|&b| b == SENTINEL) {
        return Err(EncodeError::SentinelBeforeEnd(pos));
    }

    let sa = suffix_array(text);
    let last = sa.iter().map(|&i| text[(i as usize + n - 1) % n]).collect();
    Ok((last, sa))
}

/// [`try_encode`], panicking instead of returning an error.
///
/// # Panics
///
/// Where [`try_encode`] errs.
#[must_use]
pub fn encode(text: &[u8]) -> Vec<u8> {
    try_encode(text).unwrap_or_else(|e| panic!("{e}"))
}

/// Inverts [`encode`] by the LF-mapping walk. `O(n)`. Lean: `invertBwt_bwt`. The empty column
/// decodes to the empty text.
///
/// # Errors
///
/// [`DecodeError`] if `last` is nonempty and does not contain exactly one [`SENTINEL`] byte, or
/// is longer than `u32::MAX`.
pub fn try_decode(last: &[u8]) -> Result<Vec<u8>, DecodeError> {
    try_decode_at_most(last, u32::MAX as usize)
}

/// [`try_decode`], panicking instead of returning an error.
///
/// # Panics
///
/// Where [`try_decode`] errs.
#[must_use]
pub fn decode(last: &[u8]) -> Vec<u8> {
    try_decode(last).unwrap_or_else(|e| panic!("{e}"))
}

fn try_decode_at_most(last: &[u8], max_len: usize) -> Result<Vec<u8>, DecodeError> {
    let n = last.len();
    if n > max_len {
        return Err(DecodeError::TooLong { len: n });
    }
    if n == 0 {
        return Ok(Vec::new());
    }

    let mut counts = [0u32; 256];
    for &b in last {
        counts[b as usize] += 1;
    }
    if counts[SENTINEL as usize] != 1 {
        return Err(DecodeError::SentinelCount(
            counts[SENTINEL as usize] as usize,
        ));
    }

    // block_start[b]: the row where byte b's block starts in the first column, the chapter's C.
    let mut block_start = [0u32; 256];
    let mut running = 0u32;
    for (b, &count) in counts.iter().enumerate() {
        block_start[b] = running;
        running += count;
    }

    // lf[i]: the row whose rotation starts one position earlier than row i's. seen[b]: how many
    // b's sit above row i in the last column.
    let mut seen = [0u32; 256];
    let mut lf = vec![0u32; n];
    for (i, &b) in last.iter().enumerate() {
        lf[i] = block_start[b as usize] + seen[b as usize];
        seen[b as usize] += 1;
    }

    // The sentinel's row is the rotation starting at 0; walking `lf` emits the text backwards.
    let start = last
        .iter()
        .position(|&b| b == SENTINEL)
        .expect("checked above: exactly one SENTINEL byte");

    let mut reversed = Vec::with_capacity(n);
    let mut row = u32::try_from(start).expect("start < n <= u32::MAX, asserted above");
    for _ in 0..n {
        reversed.push(last[row as usize]);
        row = lf[row as usize];
    }
    reversed.reverse();
    Ok(reversed)
}

/// Box invariant 1: it is a permutation of the text (Lean `BWT.SameLetters`). `O(n)`.
#[must_use]
pub fn is_same_letters(text: &[u8], last: &[u8]) -> bool {
    let mut balance = [0isize; 256];
    for &c in text {
        balance[usize::from(c)] += 1;
    }
    for &c in last {
        balance[usize::from(c)] -= 1;
    }
    text.len() == last.len() && balance.iter().all(|&d| d == 0)
}

/// Box invariant 2: for each suffix, in sorted order, the letter just before it (Lean
/// `BWT.LetterBeforeEachSuffix`). `O(n log n)`.
///
/// # Panics
///
/// If `text` is longer than `u32::MAX`.
#[must_use]
pub fn is_letter_before_each_suffix(text: &[u8], last: &[u8]) -> bool {
    let n = text.len();
    last.len() == n
        && suffix_array(text)
            .iter()
            .zip(last)
            .all(|(&p, &c)| text[(p as usize + n - 1) % n] == c)
}

/// The box's assumption read on the letters: the sentinel stands among them exactly once (Lean
/// `BWT.SentinelOnce`). `O(n)`.
#[must_use]
pub fn is_sentinel_once(last: &[u8]) -> bool {
    last.iter().filter(|&&c| c == SENTINEL).count() == 1
}

/// The two box invariants and the box's assumption on the letters, the Lean `BWT.Valid` and
/// `BWT.WellFormed`.
///
/// # Panics
///
/// If `text` is longer than `u32::MAX`.
#[must_use]
pub fn is_valid(text: &[u8], last: &[u8]) -> bool {
    check_valid(text, last).is_ok()
}

/// [`is_valid`], naming the first piece that fails, in the Lean's order: `Valid`'s pieces, then
/// `WellFormed`'s.
///
/// # Errors
///
/// The first failed piece's name, e.g. `"invariant 1 (same_letters)"`.
///
/// # Panics
///
/// If `text` is longer than `u32::MAX`.
pub fn check_valid(text: &[u8], last: &[u8]) -> Result<(), &'static str> {
    if !is_same_letters(text, last) {
        return Err("invariant 1 (same_letters)");
    }
    if !is_letter_before_each_suffix(text, last) {
        return Err("invariant 2 (letter_before_each_suffix)");
    }
    if !is_sentinel_once(last) {
        return Err("assumption (sentinel_once)");
    }
    Ok(())
}

#[cfg(test)]
#[path = "unit_tests/bwt.rs"]
mod tests;
