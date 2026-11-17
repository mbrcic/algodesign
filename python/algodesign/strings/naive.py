# SPDX-License-Identifier: Apache-2.0
"""The plain scan, and slow versions that are correct by inspection.

`search` is the scan the Strings chapter starts from. Each of the others solves its problem the
way the chapter first states it, before the idea that makes it fast, so the tests can compare the
real structures against something that cannot share their bug.
"""

from __future__ import annotations

from collections.abc import Sequence

from ._constants import SENTINEL


def search(text: bytes, pattern: bytes) -> list[int]:
    """Every start position at which `pattern` occurs in `text`, in increasing order.

    O(n*m): compare the pattern against the window at each position. The empty pattern occurs at
    every shift `0..n` (CLRS's valid shifts). A pattern longer than the text has no matches.
    """
    m = len(pattern)
    if m > len(text):
        return []
    return [i for i in range(len(text) - m + 1) if text[i : i + m] == pattern]


def suffix_array(text: bytes) -> list[int]:
    """The suffix array of `text`, by sorting the suffixes as whole slices: O(n^2 log n) time and
    O(n^2) memory."""
    return sorted(range(len(text)), key=lambda i: text[i:])


def bwt_rotations(text: bytes) -> bytes:
    """The Burrows-Wheeler transform of `text`, by sorting the full rotation matrix.

    Write out all n rotations, sort them, read down the last column. O(n^2 log n) time and O(n^2)
    space.
    """
    n = len(text)
    rotations = sorted(text[i:] + text[:i] for i in range(n))
    return bytes(rotation[n - 1] for rotation in rotations)


def bwt_inverse(last: bytes) -> bytes:
    """The text a last column is the transform of, by repeated prepend-and-sort.

    `n` times, write the last column in front of the rows and sort them. After round `k` the rows
    are the sorted rotations cut to `k` characters; the text is the full row ending with the
    sentinel. O(n^2 log n) time and O(n^2) space.
    """
    n = len(last)
    rows = [b""] * n
    for _ in range(n):
        rows = sorted(bytes([last[i]]) + rows[i] for i in range(n))
    return next((row for row in rows if row.endswith(bytes([SENTINEL]))), b"")


def rank(bits: Sequence[int], i: int) -> int:
    """The number of set bits strictly before position `i`, counted one at a time."""
    return sum(1 for bit in bits[:i] if bit)
