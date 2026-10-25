# SPDX-License-Identifier: Apache-2.0
"""`wavelet_tree.WaveletTree` and `chunked_wavelet.ChunkedWavelet` against counting, and the
Huffman tie-break the Rust shares."""

from __future__ import annotations

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings.chunked_wavelet import ChunkedWavelet, default_chunk
from algodesign.strings.wavelet_tree import WaveletTree

PROBES = (0, 1, 2, 3, 4, 9)


@st.composite
def _strings(draw: st.DrawFn) -> bytes:
    """Byte strings over five symbols, up to 300 long, the length drawn first."""
    length = draw(st.integers(min_value=0, max_value=300))
    return bytes(
        draw(st.lists(st.integers(min_value=0, max_value=4), min_size=length, max_size=length))
    )


@given(_strings())
@settings(deadline=None)
def test_rank_and_access_match_counting(text: bytes) -> None:
    tree = WaveletTree(text)
    seen = [0] * 256
    for i in range(len(text) + 2):
        for c in PROBES:
            assert tree.rank(c, i) == seen[c]
        if i < len(text):
            assert tree.access_rank(i) == (text[i], seen[text[i]])
            seen[text[i]] += 1


@given(_strings(), st.sampled_from([1, 2, 7, 63, 64, 1000]))
@settings(deadline=None)
def test_chunks_answer_as_counting(text: bytes, chunk: int) -> None:
    """Chunk lengths that put positions on exact multiples of the chunk, make `n` a multiple of it,
    and leave symbols absent from a chunk but present in the whole."""
    chunked = ChunkedWavelet(text, chunk)
    assert chunked.chunks() == -(-len(text) // chunk)
    seen = [0] * 256
    for i in range(len(text) + 2):
        for c in PROBES:
            assert chunked.occ(c, i) == seen[c]
        if i < len(text):
            assert chunked.access_occ(i) == (text[i], seen[text[i]])
            seen[text[i]] += 1


def test_huffman_shape_on_abracadabra() -> None:
    """The same codes the Rust pins: a `0`, c `100`, d `101`, b `110`, r `111`."""
    tree = WaveletTree(b"abracadabra")
    codes = {chr(c): tree.code(c) for c in b"abcdr"}
    assert codes == {"a": "0", "c": "100", "d": "101", "b": "110", "r": "111"}
    assert tree.code(ord("z")) is None
    assert tree.stored_bits() == 23


def test_one_symbol_has_no_internal_node() -> None:
    tree = WaveletTree(bytes(10))
    assert tree.code(0) == ""
    assert tree.rank(0, 4) == 4
    assert tree.rank(0, 99) == 10
    assert tree.rank(1, 4) == 0
    assert tree.access_rank(7) == (0, 7)


def test_the_default_chunk_is_sigma_times_bit_length_squared() -> None:
    text = b"banana" * 200
    assert default_chunk(text) == 3 * 11 * 11
    assert ChunkedWavelet(text).chunks() == 4
    assert default_chunk(b"") == 1


def test_a_zero_chunk_is_rejected() -> None:
    with pytest.raises(ValueError, match="must be positive"):
        ChunkedWavelet(b"ab", 0)


def test_positions_outside_the_string_are_refused() -> None:
    """The package's rule: invalid input raises `ValueError`, so `occ(c, -1)` and `access_occ` at a
    position that does not exist are refused. A position past the end still saturates in
    `occ`/`rank`."""
    chunked, tree = ChunkedWavelet(b"abcab", 2), WaveletTree(b"abcab")
    for bad in (
        lambda: chunked.occ(ord("b"), -1),
        lambda: chunked.access_occ(-1),
        lambda: chunked.access_occ(5),
        lambda: tree.rank(ord("b"), -1),
        lambda: tree.access_rank(-1),
        lambda: tree.access_rank(5),
    ):
        with pytest.raises(ValueError, match="position"):
            bad()
    assert chunked.occ(ord("b"), 99) == tree.rank(ord("b"), 99) == 2
