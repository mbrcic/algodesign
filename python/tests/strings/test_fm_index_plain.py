# SPDX-License-Identifier: Apache-2.0
"""`fm_index_plain.PlainFMIndex`, the uncompressed teaching form, against `fm_index.FMIndex`: the
same `count`, the same `locate` list in the same order, the same `extract`, on every input drawn --
and both against `naive.search`. The plain index is Python-only; this file is what holds it to
the library's index."""

from __future__ import annotations

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings import naive
from algodesign.strings._constants import SENTINEL
from algodesign.strings.fm_index import SAMPLE, FMIndex
from algodesign.strings.fm_index_plain import PlainFMIndex

from .assembly import assemble_fm as _assemble
from .assembly import fm_conjuncts as _conjuncts
from .assembly import fm_pieces as _pieces


@st.composite
def _texts(draw: st.DrawFn) -> bytes:
    """Sentinel-terminated texts of up to 300 bytes over `1..4`, the length drawn first, as
    `test_fm_index._texts` draws them (its docstring has the measurement of why)."""
    length = draw(st.integers(min_value=1, max_value=299))
    body = draw(st.lists(st.integers(min_value=1, max_value=4), min_size=length, max_size=length))
    return bytes(body) + bytes([SENTINEL])


patterns = st.lists(st.integers(min_value=1, max_value=4), min_size=0, max_size=5).map(bytes)
"""Patterns over the texts' alphabet, the empty one included: both indexes answer it alike."""


@given(
    _texts(),
    st.lists(patterns, min_size=1, max_size=6),
    st.integers(min_value=2, max_value=40),
    st.one_of(st.none(), st.integers(min_value=1, max_value=40)),
)
@settings(deadline=None)
def test_the_plain_index_answers_as_the_library_s_does(
    text: bytes, pats: list[bytes], sample: int, chunk: int | None
) -> None:
    """At `FMIndex`'s default chunk length (one chunk at these sizes) and at short ones, so its
    backward search and LF cross chunk boundaries."""
    plain = PlainFMIndex(text, sample)
    library = FMIndex(text, sample, chunk)
    assert plain.text_len() == library.text_len()
    for pattern in pats:
        assert plain.count(pattern) == library.count(pattern)
        assert plain.locate(pattern) == library.locate(pattern)
    n = len(text)
    for start, length in ((0, n), (n // 3, n // 2), (n - 1, 1), (n, 0)):
        assert plain.extract(start, length) == library.extract(start, length)


@given(_texts(), patterns.filter(bool))
@settings(deadline=None)
def test_count_and_locate_match_naive(text: bytes, pattern: bytes) -> None:
    index = PlainFMIndex(text, SAMPLE)
    expected = naive.search(text, pattern)
    assert index.count(pattern) == len(expected)
    assert sorted(index.locate(pattern)) == expected
    assert index.extract(0, len(text)) == text


def test_banana() -> None:
    text = b"banana\x00"
    index = PlainFMIndex(text, 2)
    assert index.count(b"ana") == 2
    assert index.locate(b"ana") == [3, 1]
    assert index.extract(1, 3) == b"ana"
    assert index.extract(0, 7) == text



def test_the_rate_defaults_to_sample() -> None:
    """`PlainFMIndex(text)` samples at `SAMPLE`, as `FMIndex(text)` does."""
    text = b"mississippi banana " * 20 + bytes([SENTINEL])
    default, explicit = PlainFMIndex(text), PlainFMIndex(text, SAMPLE)
    assert default._sample == SAMPLE
    assert default._sa_samples == explicit._sa_samples
    assert default._isa_samples == explicit._isa_samples


def test_the_conventions_are_fm_index_s() -> None:
    index = PlainFMIndex(b"banana\x00", SAMPLE)
    assert index.count(b"") == 7
    assert sorted(index.locate(b"")) == list(range(7))
    assert index.count(b"xyz") == 0
    assert index.count(b"bananabanana") == 0
    assert index.locate(b"na\x00") == []
    wrapping = PlainFMIndex(b"ab\x00", SAMPLE)
    assert wrapping.count(b"\x00a") == 0
    assert wrapping.count(b"b\x00") == 0


def test_a_lone_sentinel_is_a_legal_text() -> None:
    index = PlainFMIndex(b"\x00", SAMPLE)
    assert index.count(b"\x00") == 0
    assert index.locate(b"\x00") == []
    assert index.count(b"") == 1
    assert index.extract(0, 1) == b"\x00"


def test_bad_input_raises() -> None:
    with pytest.raises(ValueError, match="sampling rate must be at least 2"):
        PlainFMIndex(b"a\x00", 0)
    with pytest.raises(ValueError, match="sampling rate must be at least 2"):
        PlainFMIndex(b"a\x00", 1)
    with pytest.raises(ValueError, match="must end with SENTINEL"):
        PlainFMIndex(b"banana", SAMPLE)
    with pytest.raises(ValueError, match="runs past the text's 7 bytes"):
        PlainFMIndex(b"banana\x00", SAMPLE).extract(5, 5)
    with pytest.raises(ValueError, match="start -1 is negative"):
        PlainFMIndex(b"banana\x00", SAMPLE).extract(-1, 2)


@given(
    _texts(),
    st.integers(min_value=2, max_value=8),
    st.sampled_from(["c", "last", "marks", "sa", "isa"]),
    st.integers(min_value=0, max_value=1000),
    st.integers(min_value=-3, max_value=310),
)
@settings(deadline=None)
def test_the_checks_agree_with_the_library_s_on_a_corrupted_index(
    text: bytes, sample: int, piece: str, where: int, value: int
) -> None:
    """The seven checks of `is_valid`, on both indexes holding the same pieces after one entry of
    one piece is overwritten (a value in `C`, a column byte, a mark, a stored position or row):
    the plain index must give `FMIndex`'s verdict on every check, valid or not. This pins
    Python-against-Python agreement only: the two classes and their backends."""
    last, c, marks, sa, isa = _pieces(text, sample)
    if piece == "c":
        c[sorted(c)[where % len(c)]] = value
    elif piece == "last":
        column = bytearray(last)
        column[where % len(column)] = value % 6
        last = bytes(column)
    elif piece == "marks":
        marks[where % len(marks)] ^= 1
    elif piece == "sa":
        sa[where % len(sa)] = value
    else:
        isa[where % len(isa)] = value
    pieces = (last, c, marks, sa, isa, sample)
    assert _conjuncts(_assemble(PlainFMIndex, *pieces)) == _conjuncts(
        _assemble(FMIndex, *pieces)
    )
