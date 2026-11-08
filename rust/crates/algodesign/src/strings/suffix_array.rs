// SPDX-License-Identifier: Apache-2.0
//! Suffix array by **prefix doubling** (CLRS §32.5; Manber–Myers 1993), with a counting sort per
//! round and a plain binary search over the finished array.
//!
//! No sentinel: a proper prefix sorts before its extension. Lean:
//! `lean/AlgoDesign/Strings/SuffixArray/`.
//!
//! **Against the Python, and how fast.** The same doubling, with other tag values: a tag here is
//! one plus the index where its group starts, not the Python's dense `1..=top`, so a tag's bucket
//! start is the tag minus one and the second counting sort needs no count pass and no prefix sum.
//! On `banana` the tags differ from the chapter's figure (`b` = 5, `n` = 6 against 3 and 4); the
//! order they give is the same. Not measured on its own;
//! `STRINGS_STRUCTURES_ONLY=1 cargo bench -p algodesign --bench strings` times the build
//! (`suffix_array/build`) on the first MiB of the corpus.

use std::cmp::Ordering;

/// The suffix array of `text`: the start positions of its suffixes, in lexicographic order.
///
/// `O(n log n)` time, `O(n)` extra space. Lean: `valid_suffixArray`, `suffixArrayEarly_eq`.
///
/// # Panics
///
/// If `text.len()` exceeds `u32::MAX`.
#[must_use]
pub fn suffix_array(text: &[u8]) -> Vec<u32> {
    doubling(text).0
}

/// [`suffix_array`] and the number of doubling rounds it ran after the byte sort (the Lean's
/// `earlyRounds`). Behind the `unchecked` feature.
///
/// # Panics
///
/// As [`suffix_array`].
#[cfg(feature = "unchecked")]
#[must_use]
pub fn suffix_array_with_rounds(text: &[u8]) -> (Vec<u32>, usize) {
    doubling(text)
}

fn doubling(text: &[u8]) -> (Vec<u32>, usize) {
    #[cfg(test)]
    SA_BUILDS.with(|b| b.set(b.get() + 1));
    let n = text.len();
    if n == 0 {
        return (Vec::new(), 0);
    }
    assert!(
        u32::try_from(n).is_ok(),
        "positions are u32: one suffix array indexes at most u32::MAX characters; shard instead"
    );

    let mut sa = vec![0u32; n];
    let mut scratch = vec![0u32; n];
    let mut tag = vec![0u32; n];
    let mut next = vec![0u32; n];

    // Narrowing casts below are of values below `n <= u32::MAX`.

    // Round 0: one 256-bucket counting sort over the bytes themselves.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "i < n <= u32::MAX, asserted above"
    )]
    for (i, s) in scratch.iter_mut().enumerate() {
        *s = i as u32;
    }
    let mut bytes = [0u32; 256];
    counting_sort_by(&scratch, &mut sa, &mut bytes, |p| {
        usize::from(text[p as usize])
    });
    // `Doubling.Valid t tag 0` (`Doubling.valid_initial`).
    let mut top = retag(&sa, &mut tag, |a, b| text[a as usize] == text[b as usize]);

    // Invariant: `Doubling.Valid text tag k` with `h == 2^k`; all tags distinct exits early.
    let mut h = 1usize;
    let mut rounds = 0usize;
    let mut buckets = vec![0u32; n + 1];
    let n32 = u32::try_from(n).expect("n <= u32::MAX, asserted above");
    while top < n32 && h < n {
        rounds += 1;
        // The pair's second component; `0` when the suffix `h` along is empty (no-sentinel rule).
        let second = |p: u32| -> u32 {
            let q = p as usize + h;
            if q < n {
                tag[q]
            } else {
                0
            }
        };

        // Order by the second component without sorting: first the `h` positions whose second
        // half ran out, then `q - h` for each `q >= h` in `sa`, which is already in tag order.
        let (tail, rest) = scratch.split_at_mut(h);
        #[allow(
            clippy::cast_possible_truncation,
            reason = "p < n <= u32::MAX, asserted above"
        )]
        for (slot, p) in tail.iter_mut().zip(n - h..n) {
            *slot = p as u32;
        }
        #[allow(
            clippy::cast_possible_truncation,
            reason = "h < n <= u32::MAX, asserted above"
        )]
        for (slot, &q) in rest.iter_mut().zip(sa.iter().filter(|&&q| q as usize >= h)) {
            *slot = q - h as u32;
        }
        // Then one stable pass by the first component: tag `r`'s bucket starts at `r - 1`, so
        // no count or prefix sum is needed.
        #[allow(
            clippy::cast_possible_truncation,
            reason = "r < n <= u32::MAX, asserted above"
        )]
        for (r, start) in buckets.iter_mut().enumerate() {
            *start = r.saturating_sub(1) as u32;
        }
        // Gather the keys first so the random `tag` loads overlap.
        for (key, &p) in next.iter_mut().zip(&scratch) {
            *key = tag[p as usize];
        }
        for (&p, &r) in scratch.iter().zip(&next) {
            let slot = &mut buckets[r as usize];
            sa[*slot as usize] = p;
            *slot += 1;
        }

        // Equal pairs must take equal tags: `Doubling.Valid` is an iff.
        top = retag(&sa, &mut next, |a, b| {
            tag[a as usize] == tag[b as usize] && second(a) == second(b)
        });

        std::mem::swap(&mut tag, &mut next);
        h *= 2;
    }

    (sa, rounds)
}

#[cfg(test)]
thread_local! {
    /// Suffix arrays built on this thread.
    pub(crate) static SA_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Calls to [`counting_sort_by`] on this thread.
    static SORTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Stable counting sort of `input` into `out` by `key`, using `starts` as the bucket table.
/// `starts` must cover the key range; `out` must be as long as `input`.
fn counting_sort_by<F>(input: &[u32], out: &mut [u32], starts: &mut [u32], key: F)
where
    F: Fn(u32) -> usize,
{
    #[cfg(test)]
    SORTS.with(|c| c.set(c.get() + 1));
    starts.fill(0);
    for &p in input {
        starts[key(p)] += 1;
    }
    let mut running = 0u32;
    for slot in starts.iter_mut() {
        let count = *slot;
        *slot = running;
        running += count;
    }
    for &p in input {
        let b = key(p);
        out[starts[b] as usize] = p;
        starts[b] += 1;
    }
}

/// Tag each position of the sorted `sa` as one plus the index where its group (per `same`)
/// starts; returns the number of groups. `sa` must be non-empty.
fn retag<F>(sa: &[u32], tag: &mut [u32], same: F) -> u32
where
    F: Fn(u32, u32) -> bool,
{
    let mut head = 1u32;
    let mut groups = 1u32;
    tag[sa[0] as usize] = head;
    // `i + 2 <= n`, and every caller's `sa` indexes a text of at most `u32::MAX` bytes.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "i + 2 <= n, and the suffix array indexes a text of at most u32::MAX bytes"
    )]
    for (i, pair) in sa.windows(2).enumerate() {
        if !same(pair[0], pair[1]) {
            head = i as u32 + 2;
            groups += 1;
        }
        tag[pair[1] as usize] = head;
    }
    groups
}

/// Box invariant 1: every position of the text appears once (Lean `EachPositionOnce`). `O(n)`.
#[must_use]
pub fn is_each_position_once(text: &[u8], sa: &[u32]) -> bool {
    let n = text.len();
    if sa.len() != n {
        return false;
    }
    let mut seen = vec![false; n];
    sa.iter().all(|&p| match seen.get_mut(p as usize) {
        Some(s) if !*s => {
            *s = true;
            true
        }
        _ => false,
    })
}

/// Box invariant 2: the suffixes are kept in sorted order (Lean `SuffixesSorted`), a position
/// past the end naming the empty suffix. `O(n²)` byte comparisons in the worst case.
#[must_use]
pub fn is_suffixes_sorted(text: &[u8], sa: &[u32]) -> bool {
    let suffix = |p: u32| text.get(p as usize..).unwrap_or(&[]);
    sa.windows(2).all(|w| suffix(w[0]) <= suffix(w[1]))
}

/// Both box invariants, the Lean `SuffixArray.Valid`. Lean: `valid_unique`, `valid_suffixArray`.
#[must_use]
pub fn is_valid(text: &[u8], sa: &[u32]) -> bool {
    check_valid(text, sa).is_ok()
}

/// [`is_valid`], naming the first piece that fails, in the Lean `Valid`'s order.
///
/// # Errors
///
/// The first failed piece's name, e.g. `"invariant 2 (suffixes_sorted)"`.
pub fn check_valid(text: &[u8], sa: &[u32]) -> Result<(), &'static str> {
    if !is_each_position_once(text, sa) {
        return Err("invariant 1 (each_position_once)");
    }
    if !is_suffixes_sorted(text, sa) {
        return Err("invariant 2 (suffixes_sorted)");
    }
    Ok(())
}

/// Every start position of `pat` in `text`, in suffix order, by two binary searches over
/// `sa = suffix_array(text)`. `O(m log n)`. The empty `pat` answers `n` followed by all of `sa`.
///
/// # Panics
///
/// If `pat` is empty and `text.len()` exceeds `u32::MAX`.
#[must_use]
pub fn search(text: &[u8], sa: &[u32], pat: &[u8]) -> Vec<u32> {
    if pat.is_empty() {
        let n = u32::try_from(text.len()).expect("positions are u32");
        return std::iter::once(n).chain(sa.iter().copied()).collect();
    }
    let lower = sa.partition_point(|&p| cmp_prefix(text, p, pat) == Ordering::Less);
    let upper = sa.partition_point(|&p| cmp_prefix(text, p, pat) != Ordering::Greater);
    sa[lower..upper].to_vec()
}

/// Compare the suffix at `p` against `pat` as a prefix: `Equal` means a match.
fn cmp_prefix(text: &[u8], p: u32, pat: &[u8]) -> Ordering {
    let suffix = &text[p as usize..];
    let k = suffix.len().min(pat.len());
    suffix[..k]
        .cmp(&pat[..k])
        .then(if suffix.len() < pat.len() {
            Ordering::Less
        } else {
            Ordering::Equal
        })
}

#[cfg(test)]
#[path = "unit_tests/suffix_array.rs"]
mod tests;
