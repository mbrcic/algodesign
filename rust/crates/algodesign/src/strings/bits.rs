// SPDX-License-Identifier: Apache-2.0
//! Bit helpers the compressed containers share: fixed-width fields packed into `u64` words, a
//! binary search over a predicate, and select inside one word.

/// The `width`-bit field starting at bit `pos` of `words` (bit `k` is bit `k % 64` of word
/// `k / 64`). `width ≤ 64`; a field may straddle two words.
#[inline]
pub(crate) fn read_bits(words: &[u64], pos: usize, width: u32) -> u64 {
    if width == 0 {
        return 0;
    }
    let (word, shift) = (pos / 64, pos % 64);
    let mut value = words[word] >> shift;
    if shift + width as usize > 64 {
        value |= words[word + 1] << (64 - shift);
    }
    if width == 64 {
        value
    } else {
        value & ((1u64 << width) - 1)
    }
}

/// Append the low `width` bits of `value` at bit `pos`, growing `words` as needed.
pub(crate) fn write_bits(words: &mut Vec<u64>, pos: usize, width: u32, value: u64) {
    if width == 0 {
        return;
    }
    let end = pos + width as usize;
    if words.len() < end.div_ceil(64) {
        words.resize(end.div_ceil(64), 0);
    }
    let (word, shift) = (pos / 64, pos % 64);
    words[word] |= value << shift;
    if shift + width as usize > 64 {
        words[word + 1] |= value >> (64 - shift);
    }
}

/// The first `k` in `0..n` where `pred(k)` is false, given `pred` true on a prefix and false
/// after it; `n` when it never turns false. Binary search.
pub(crate) fn partition_point(n: usize, pred: impl Fn(usize) -> bool) -> usize {
    let (mut lo, mut hi) = (0, n);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if pred(mid) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Position of the `j`-th set bit (zero-based) in `x`, by six halving steps.
#[inline]
pub(crate) fn select_in_word(x: u64, j: u32) -> u32 {
    debug_assert!(j < x.count_ones(), "no {j}-th set bit in {x:#x}");
    let (mut rest, mut j, mut pos) = (x, j, 0u32);
    let mut width = 32;
    while width > 0 {
        let low = (rest & ((1u64 << width) - 1)).count_ones();
        if j >= low {
            j -= low;
            pos += width;
            rest >>= width;
        }
        width /= 2;
    }
    pos
}
