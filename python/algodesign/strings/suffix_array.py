# SPDX-License-Identifier: Apache-2.0
"""The suffix array by prefix doubling (Manber-Myers; CLRS §32.5).

The suffix array of a text lists the start positions of its suffixes in sorted order. Sorting the
suffixes directly compares long strings; prefix doubling never compares more than two numbers.

The key idea is an invariant on tags: after round `k`, `tag[i]` orders the suffixes by their first
`2^k` characters, with equal prefixes getting equal tags. Round `k + 1` then needs no characters at
all -- it keys position `i` by the pair `(tag[i], tag[i + 2^k])`, two numbers standing in for
`2^(k+1)` characters. Once `2^k` covers the text, or every tag is already distinct, tag order is
suffix order.

Each round is two O(n) steps and there are at most O(log n) rounds: O(n log n) time, O(n) extra
space. No sentinel is appended, so a proper prefix sorts before its extension.

The Rust differs here: a tag is one plus where its group starts, not dense, so the second counting
sort needs no count pass.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/SuffixArray/` (specification:
`SuffixArray/Spec.lean`): `valid_of_doubling` (the invariant this loop keeps) and
`valid_suffixArray` (the Lean's own rounds, which hand out tags by insertion, not by counting).
"""

from __future__ import annotations

from bisect import bisect_left, bisect_right
from collections.abc import Sequence
from itertools import pairwise

from ._constants import BYTE_VALUES  # round 0's buckets: one per possible byte


def _counting_sort_by(positions: list[int], key: Sequence[int], key_count: int) -> list[int]:
    """`positions`, rearranged into non-decreasing order of `key[p]`, **stably**.

    `key[p]` must lie in `range(key_count)`. Count into a table, turn the table into *exclusive*
    prefix sums, then walk `positions` forward handing out each bucket's slots front to back, so
    equal keys leave in the order they arrived. Key-indexed counting, Sedgewick-Wayne §5.1.
    """
    counts = [0] * key_count
    for p in positions:
        counts[key[p]] += 1

    starts = [0] * key_count
    running = 0
    for bucket in range(key_count):
        starts[bucket] = running
        running += counts[bucket]

    out = [0] * len(positions)
    for p in positions:
        bucket = key[p]
        out[starts[bucket]] = p
        starts[bucket] += 1
    return out


def _dense_tags(sa: list[int], key: Sequence[object]) -> tuple[list[int], int]:
    """Tags `1..=top` for every position, and `top`, from `sa` already sorted by `key`.

    Step the tag only where two adjacent positions carry different keys. `top == len(sa)` means
    every tag is distinct. `sa` must be non-empty.
    """
    tag = [0] * len(sa)
    top = 1
    tag[sa[0]] = top
    for previous, current in pairwise(sa):
        if key[previous] != key[current]:
            top += 1
        tag[current] = top
    return tag, top


def suffix_array(text: bytes) -> list[int]:
    """The suffix array of `text`: the start positions of its suffixes, in lexicographic order.

    O(n log n) time, by prefix doubling. Round 0 tags each position by its own byte through a
    256-bucket counting sort. Round `k` keys position `i` by the pair `(tag[i], tag[i + 2^k])`,
    orders the positions by that pair -- least significant component first, as a radix sort does --
    and re-tags. The second component costs no sort: `sa` is already in tag order, so the
    positions in order of `tag[i + 2^k]` are read off it in one scan (Manber-Myers). The first
    component takes one stable counting sort.

    **Tags run `1..=n`, and `0` is reserved** for a suffix that has run out, so it sorts before
    one that continues.
    """
    n = len(text)
    if n == 0:
        return []

    # Round 0: one 256-bucket counting sort over the bytes themselves.
    sa = _counting_sort_by(list(range(n)), text, BYTE_VALUES)
    tag, top = _dense_tags(sa, text)

    # Invariant at the head of every turn: `tag` orders the suffixes by their first `covered`
    # characters, the prefix each tag covers. One turn re-establishes it for twice as many.
    covered = 1
    while top < n and covered < n:
        # The tag of the suffix `covered` along, or `0` when that suffix is empty.
        second = [tag[p + covered] if p + covered < n else 0 for p in range(n)]
        pairs = list(zip(tag, second, strict=True))

        # The positions in order of the second component, read off `sa`: first those whose
        # second half has run out, then `q - covered` for each `q` in `sa`.
        by_second = list(range(n - covered, n)) + [q - covered for q in sa if q >= covered]
        # Then one stable counting sort by the first component (tags reach `n`).
        sa = _counting_sort_by(by_second, tag, n + 1)

        tag, top = _dense_tags(sa, pairs)
        covered *= 2

    return sa


def is_each_position_once(text: bytes, sa: list[int]) -> bool:
    """Box invariant 1: every position of the text appears once, so no occurrence can be missed.
    The Lean `EachPositionOnce`, `sa.Perm (List.range n)`."""
    n = len(text)
    if len(sa) != n:
        return False
    seen = [False] * n
    for p in sa:
        if not 0 <= p < n or seen[p]:
            return False
        seen[p] = True
    return True


def is_suffixes_sorted(text: bytes, sa: list[int]) -> bool:
    """Box invariant 2: the suffixes are kept in sorted order, so the occurrences of any fragment
    lie side by side.

    The Lean `SuffixesSorted`. Checking neighbours is enough: the order is transitive.
    """
    return all(text[p:] <= text[q:] for p, q in pairwise(sa))


def check_valid(text: bytes, sa: list[int]) -> str | None:
    """The first piece of the Lean `SuffixArray.Valid` that `sa` breaks, or `None`."""
    if not is_each_position_once(text, sa):
        return "invariant 1 (each_position_once)"
    if not is_suffixes_sorted(text, sa):
        return "invariant 2 (suffixes_sorted)"
    return None


def is_valid(text: bytes, sa: list[int]) -> bool:
    """Whether `sa` is the suffix array of `text`: the Lean `SuffixArray.Valid`, both pieces.
    Lean: `valid_unique` says at most one array passes."""
    return check_valid(text, sa) is None


def search(text: bytes, sa: list[int], pattern: bytes) -> list[int]:
    """The stretch of `sa` holding every start position of `pattern` in `text`, in suffix order
    rather than text order.

    The suffixes that begin with `pattern` sit next to each other in `sa`, so two binary searches
    on the suffixes cut to `m` characters bracket them. Each probe compares at most `m`
    characters: O(m log n).

    The empty pattern occurs at every shift: `[n]` (the empty suffix) and then all of `sa`.
    """
    if not pattern:
        return [len(text), *sa]
    m = len(pattern)
    first_m = lambda p: text[p:p + m]
    lo = bisect_left(sa, pattern, key=first_m)
    hi = bisect_right(sa, pattern, key=first_m)
    return sa[lo:hi]
