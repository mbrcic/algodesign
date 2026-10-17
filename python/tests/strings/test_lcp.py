# SPDX-License-Identifier: Apache-2.0
"""Kasai, checked the way `rust/crates/algodesign/src/strings/lcp.rs` checks it.

The property test mirrors that module's `kasai_matches_the_definition` and the fixed cases mirror
the ones it pins. `lcp_naive` lives here rather than in `naive.py` for the reason the Rust keeps
its copy in a test module: it is the other side of one differential, not an oracle the chapter
ships.

The Rust's `comparison_count_is_linear_on_a_concrete_input` has a counterpart here,
`test_the_carried_offset_keeps_the_character_reads_linear`, for a different reason: not as a
performance claim, which this package does not make, but because Kasai *is* the carried offset.
An LCP array computed from offset 0 every time gives the same answers and is a different
algorithm.
"""

import random

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.strings import naive
from algodesign.strings.lcp import lcp, longest_repeat
from algodesign.strings.suffix_array import suffix_array

from .cost_probes import CountingBytes

# Alphabet `{0, 1, 2, 3}`, the Rust proptest's `0u8..4`, non-empty as there too. A small alphabet
# is what makes adjacent suffixes actually share prefixes, so the carried offset is exercised.
SYMBOLS = st.integers(min_value=0, max_value=3)
texts = st.lists(SYMBOLS, min_size=1, max_size=300).map(bytes)


def lcp_naive(text: bytes, sa: list[int]) -> list[int]:
    """The LCP array by its definition: for each `i >= 1`, compare the suffixes at `sa[i - 1]`
    and `sa[i]` from offset `0`. This is `lcpEntry`, and restarting every comparison is exactly
    what Kasai's carried offset removes."""
    out = [0] * len(sa)
    for i in range(1, len(sa)):
        a, b = text[sa[i - 1] :], text[sa[i] :]
        shared = 0
        while shared < len(a) and shared < len(b) and a[shared] == b[shared]:
            shared += 1
        out[i] = shared
    return out


@given(texts)
def test_kasai_matches_the_definition(text: bytes) -> None:
    """Mirrors `kasai_matches_the_definition`.

    Lean: `kasai_eq` -- for `sa` satisfying `SuffixArray.Valid ⟨text, sa⟩`, which `suffix_array(text)`
    supplies here, the scan equals the array `lcpEntry` defines.
    """
    sa = suffix_array(text)
    assert lcp(text, sa) == lcp_naive(text, sa)


def test_banana() -> None:
    """Suffix order: a, ana, anana, banana, na, nana."""
    sa = suffix_array(b"banana")
    assert sa == [5, 3, 1, 0, 4, 2]
    assert lcp(b"banana", sa) == [0, 1, 3, 0, 0, 2]


def test_empty_and_single_byte_texts() -> None:
    """The property test's length range starts at 1, so these fall outside it -- an off-by-one at
    either boundary (empty rank table, or the `r > 0` guard on the only position) shows up here
    first."""
    assert lcp(b"", []) == []
    assert lcp(b"a", [0]) == [0]


def test_all_equal_bytes_give_the_staircase() -> None:
    """One repeated byte sorts the suffixes shortest first, so each shares its whole self with
    its successor: the LCP array is 0, 1, 2, .... This is the input where restarting every
    comparison costs the most, and where the carried offset shows most clearly."""
    text = bytes([7]) * 32
    sa = suffix_array(text)
    assert lcp(text, sa) == list(range(32))
    assert lcp(text, sa) == lcp_naive(text, sa)


def test_a_proper_prefix_and_its_extension_are_adjacent() -> None:
    """The no-sentinel witness again, read through the LCP array: with `suffix_array(b"abaa") ==
    [3, 2, 0, 1]`, "a" and "aa" share one character and "aa" and "abaa" share one."""
    sa = suffix_array(b"abaa")
    assert sa == naive.suffix_array(b"abaa")
    assert lcp(b"abaa", sa) == [0, 1, 1, 0]


def test_the_carried_offset_keeps_the_character_reads_linear() -> None:
    """Every character comparison reads two bytes. A comparison that matches raises `h`, which
    never exceeds `n` and drops by at most one per position, so at most `2n` of them match; at
    most one per position fails. That is at most `6n` reads. Restarting each comparison at offset
    0 reads about `n^2` on `b"a" * n`, where every neighbour shares all it can."""
    rng = random.Random(3)
    cases = [bytes(rng.choice(b"ab") for _ in range(n)) for n in (1, 2, 5, 50, 400)]
    for text in cases + [b"a" * 300, b"ab" * 150, b"abaababaabaab" * 20]:
        sa = suffix_array(text)
        counted = CountingBytes(text)
        assert lcp(counted, sa) == lcp_naive(text, sa)
        assert counted.reads <= 6 * len(text), (len(text), counted.reads)


def test_mismatched_lengths_raise() -> None:
    """Where the Rust asserts, the Python raises."""
    with pytest.raises(ValueError, match="lcp.lcp: sa must be the suffix array of text"):
        lcp(b"banana", [0, 1])


def longest_repeat_naive(text: bytes) -> bytes:
    """Every substring, counted where it starts: the longest that starts in two places, the
    smallest of those in byte order, `b""` if none. O(n^3), which is the point of an oracle."""
    best = b""
    for length in range(1, len(text)):
        starts: dict[bytes, int] = {}
        repeats = []
        for i in range(len(text) - length + 1):
            piece = text[i : i + length]
            starts[piece] = starts.get(piece, 0) + 1
            if starts[piece] == 2:
                repeats.append(piece)
        if not repeats:
            break  # no repeat of this length means none longer either
        best = min(repeats)
    return best


@given(st.lists(SYMBOLS, max_size=60).map(bytes))
def test_longest_repeat_matches_the_definition(text: bytes) -> None:
    """The LCP array's maximum, read off at its first row, is the longest repeated substring and
    the smallest of that length. Stated in words, not proved: `SuffixArray/LCP.lean` defines `longestRepeat`
    and checks examples, and this is the evidence that the row rule picks the right one."""
    assert longest_repeat(text) == longest_repeat_naive(text)


def test_longest_repeat_on_the_textbook_examples() -> None:
    assert longest_repeat(b"banana") == b"ana"  # the two occurrences overlap
    assert longest_repeat(b"mississippi") == b"issi"
    assert longest_repeat(b"abcd") == b""  # nothing repeats
    assert longest_repeat(b"") == b""
    assert longest_repeat(b"abab") == b"ab"
    assert longest_repeat(b"xaybxa") == b"xa"  # ties with nothing; "a" and "x" are shorter
    assert longest_repeat(b"abxba") == b"a"  # "a" and "b" tie at length 1: the smaller wins
