# SPDX-License-Identifier: Apache-2.0
"""`rrr.RRR` against counting bits one at a time, and the class/offset code against Navarro's
worked examples."""

from __future__ import annotations

from math import comb

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings.rrr import BLOCK_BITS, RRR, SUPERBLOCK_BLOCKS, decode, encode

SUPERBLOCK_BITS = BLOCK_BITS * SUPERBLOCK_BLOCKS


@st.composite
def _bitvectors(draw: st.DrawFn) -> list[int]:
    """Bitvectors up to four superblocks long, the length drawn first so that long ones are drawn as
    often as short ones, at a drawn density so that sparse, even and dense blocks all occur."""
    length = draw(st.integers(min_value=0, max_value=4 * SUPERBLOCK_BITS + 7))
    ones_in_eight = draw(st.integers(min_value=0, max_value=8))
    return [
        1 if draw(st.integers(min_value=0, max_value=7)) < ones_in_eight else 0
        for _ in range(length)
    ]


def _check(bits: list[int]) -> None:
    rrr = RRR(bits)
    assert len(rrr) == len(bits)
    ones = 0
    for i in range(len(bits) + 2):
        assert rrr.rank(i) == ones
        if i < len(bits):
            assert rrr.access(i) == bits[i]
            ones += bits[i]


@given(_bitvectors())
@settings(deadline=None)
def test_rank_and_access_match_counting(bits: list[int]) -> None:
    _check(bits)


@given(st.lists(st.integers(min_value=0, max_value=1), min_size=BLOCK_BITS, max_size=BLOCK_BITS))
def test_decode_inverts_encode(block: list[int]) -> None:
    c, offset = encode(block)
    assert c == sum(block)
    assert 0 <= offset < comb(BLOCK_BITS, c)
    assert decode(c, offset) == block


def test_offsets_count_blocks_in_numeric_order() -> None:
    """Navarro's Example 4.2, read at this block length: among blocks with one 1, the one whose 1
    is last is offset 0, and the one whose 1 is first is the last offset."""
    last = [0] * (BLOCK_BITS - 1) + [1]
    first = [1] + [0] * (BLOCK_BITS - 1)
    assert encode(last) == (1, 0)
    assert encode(first) == (1, BLOCK_BITS - 1)
    assert encode([0] * BLOCK_BITS) == (0, 0)
    assert encode([1] * BLOCK_BITS) == (BLOCK_BITS, 0)


def test_block_and_superblock_boundaries() -> None:
    """Lengths either side of one block and of one superblock, at every position."""
    for length in (0, 1, BLOCK_BITS - 1, BLOCK_BITS, BLOCK_BITS + 1, SUPERBLOCK_BITS - 1,
                   SUPERBLOCK_BITS, SUPERBLOCK_BITS + 1, 3 * SUPERBLOCK_BITS + 2):
        _check([0] * length)
        _check([1] * length)
        _check([1 if (i * 7 + i // BLOCK_BITS) % 5 < 2 else 0 for i in range(length)])


def test_positions_outside_the_vector_are_refused() -> None:
    """`rank(-1)` raises `ValueError`, as `BitIndex.rank` does, instead of an `IndexError` from
    inside the block walk; `access` refuses a position that is not a bit of the vector."""
    vector = RRR([1, 0, 1])
    with pytest.raises(ValueError, match="position"):
        vector.rank(-1)
    for i in (-1, 3):
        with pytest.raises(ValueError, match="position"):
            vector.access(i)
    assert vector.rank(99) == 2
