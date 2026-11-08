# SPDX-License-Identifier: Apache-2.0
"""Backward search's running state, `BackwardSearch.Valid`: mirrors the Rust's
`unit_tests/backward_search.rs`."""

from __future__ import annotations

from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings._constants import SENTINEL
from algodesign.strings.backward_search import check_valid
from algodesign.strings.suffix_array import suffix_array


def _steps(text: bytes, sa: list[int], pattern: bytes) -> list[tuple[bytes, int, int]]:
    """The interval after each symbol read, right to left, computed from the suffix array itself:
    the state backward search must be in."""
    out = []
    for j in range(1, len(pattern) + 1):
        read = pattern[len(pattern) - j :]
        lo = sum(1 for i in range(len(text)) if text[i:] < read)
        hi = lo + sum(1 for i in range(len(text)) if text[i:].startswith(read))
        out.append((read, lo, hi))
    return out


def test_banana_after_every_symbol() -> None:
    text = b"banana" + bytes([SENTINEL])
    sa = suffix_array(text)
    for read, lo, hi in _steps(text, sa, b"ana"):
        assert check_valid(text, sa, read, lo, hi) is None, read


def test_each_piece_fails_where_it_should() -> None:
    text = b"banana" + bytes([SENTINEL])
    sa = suffix_array(text)
    assert check_valid(text, sa, b"ana", 2, 5) == "invariant 1 (stretch_holds_matches)"
    assert check_valid(text, sa, b"x", 7, 7) is None
    assert check_valid(text, sa, b"x", 6, 6) == "not in the box (stretch_starts_right)"
    assert check_valid(text, sa, b"x", 7, 6) == "not in the box (stretch_as_wide_as_matches)"


@given(st.binary(max_size=40).map(lambda b: bytes(c % 3 + 1 for c in b)),
       st.binary(min_size=1, max_size=4).map(lambda b: bytes(c % 3 + 1 for c in b)))
@settings(deadline=None)
def test_the_index_interval_is_valid_after_every_symbol(body: bytes, pattern: bytes) -> None:
    """Lean: `BackwardSearch.valid_backwardSearch`, on `FMIndex`'s own interval after the whole
    pattern."""
    from algodesign.strings.fm_index import FMIndex

    text = body + bytes([SENTINEL])
    sa = suffix_array(text)
    interval = FMIndex(text, 3)._interval(pattern)
    if interval is not None:
        lo, hi = interval
        assert check_valid(text, sa, pattern, lo, hi) is None
