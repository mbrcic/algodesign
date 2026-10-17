# SPDX-License-Identifier: Apache-2.0
"""The LCP array, by Kasai's algorithm (Kasai et al. 2001; CLRS §32.5).

`lcp[i]` is the length of the longest common prefix of the suffixes at `sa[i - 1]` and `sa[i]`;
`lcp[0]` is `0`.

Computing each entry from scratch restarts every comparison at offset 0 and can take O(n^2) time.
Kasai visits the suffixes in *text* order instead, carrying an offset `h` from one position to the
next. Why that is safe: say suffix `p - 1` shares `h` characters with its predecessor `s` in suffix
order. Dropping the first character from each, suffixes `s + 1` and `p` share at least `h - 1`.
Suffix `s + 1` sorts somewhere before `p`, and neighbours in the suffix array share at least as long
a prefix as suffixes further apart, so `p`'s own predecessor shares at least `h - 1` with it too.
The comparison can resume at `h - 1` instead of `0`.

`h` never exceeds n and drops by at most one per position, so it rises at most 2n times in total:
O(n) time, and O(n) extra space for the inverse of `sa`.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/SuffixArray/LCP.lean`:
`kasai_eq`.
"""

from __future__ import annotations

from .suffix_array import suffix_array


def lcp(text: bytes, sa: list[int]) -> list[int]:
    """The LCP array of `text`, given its suffix array `sa`, by Kasai's algorithm.

    Invert `sa` so that each position can find its predecessor in suffix order, then make one pass
    over the text positions, carrying the comparison offset `h` from one position to the next.

    Raises:
        ValueError: if `len(sa) != len(text)`.
    """
    n = len(text)
    if len(sa) != n:
        raise ValueError("lcp.lcp: sa must be the suffix array of text")
    if n == 0:
        return []

    # `row[p]` is the row of the suffix array where suffix `p` sits: `sa`'s inverse.
    row = [0] * n
    for i, p in enumerate(sa):
        row[p] = i

    out = [0] * n
    h = 0
    for p in range(n):
        r = row[p]
        if r > 0:
            q = sa[r - 1]
            while p + h < n and q + h < n and text[p + h] == text[q + h]:
                h += 1
            out[r] = h
        # The next position loses at most one matched character.
        h = max(h - 1, 0)
    return out


def longest_repeat(text: bytes) -> bytes:
    """The longest substring of `text` that occurs at least twice (possibly overlapping), the
    smallest in byte order among ties; `b""` if no byte repeats.

    Two occurrences of a substring start two suffixes sharing it as a prefix, and such suffixes sit
    together in the suffix array, so the largest `lcp` entry is the length of the longest repeat.
    O(n log n), the suffix array's cost.
    """
    sa = suffix_array(text)
    best_row, best_len = 0, 0
    for row, length in enumerate(lcp(text, sa)):
        if length > best_len:  # strictly: the first row to reach the maximum keeps it
            best_row, best_len = row, length
    start = sa[best_row] if best_len else 0
    return text[start : start + best_len]
