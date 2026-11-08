# SPDX-License-Identifier: Apache-2.0
"""Smoke tests for the slow reference versions, matching `naive.rs`'s own: each does the obvious
thing on the obvious case. `bwt_inverse` is checked against `bwt_rotations` in `test_bwt.py`.
"""

from algodesign.strings import naive


def test_search_finds_every_occurrence() -> None:
    assert naive.search(b"banana", b"ana") == [1, 3]
    assert naive.search(b"banana", b"xyz") == []
    assert naive.search(b"banana", b"") == [0, 1, 2, 3, 4, 5, 6]
    assert naive.search(b"", b"") == [0]
    assert naive.search(b"ab", b"abc") == []


def test_suffix_array_orders_suffixes_lexicographically() -> None:
    assert naive.suffix_array(b"banana") == [5, 3, 1, 0, 4, 2]
    # The chapter's pinned witness that rotation order and suffix order differ without a
    # sentinel; `suffix_array.py` is held to the same fact.
    assert naive.suffix_array(b"abaa") == [3, 2, 0, 1]
    assert naive.suffix_array(b"") == []


def test_bwt_rotations_matches_the_textbook_example() -> None:
    assert naive.bwt_rotations(b"banana") == b"nnbaaa"


def test_rank_counts_set_bits_strictly_before_i() -> None:
    bits = [1, 1, 0, 1]
    assert [naive.rank(bits, i) for i in range(5)] == [0, 1, 2, 2, 3]
