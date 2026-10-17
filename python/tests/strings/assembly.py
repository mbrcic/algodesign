# SPDX-License-Identifier: Apache-2.0
"""String structures assembled from plain pieces, every private field written directly.

The library has no unchecked constructor, by design: its code is the code the book prints, and
a constructor that skips the invariants would be API no reader of the chapter ever sees. So an
index, a records vector or a corpus that no constructor would build -- a corrupted one, which is
what `is_valid` exists to be handed -- is assembled here, by writing its slots.

Two readers share this module, so that "an index holding these pieces" means one thing to both:

- the FM-index and records tests in this directory (`test_fm_index.py`,
  `test_fm_index_plain.py`, `test_records.py`);
- the cross-language checks, which load this file by its path, so that they read the same
  assembly the tests do.

It is a helper, not a test module: it holds no test, and it imports nothing but the library.
"""

from __future__ import annotations

from collections.abc import Sequence

from algodesign.strings.chunked_wavelet import ChunkedWavelet
from algodesign.strings.count_index import BitIndex, ByteIndex
from algodesign.strings.fm_index import FMIndex
from algodesign.strings.fm_index_plain import PlainFMIndex
from algodesign.strings.records import Corpus, Records
from algodesign.strings.rrr import RRR

Index = FMIndex | PlainFMIndex

Pieces = tuple[bytes, dict[int, int], list[int], list[int], list[int]]


def assemble_fm(
    cls: type[Index],
    last: bytes,
    c: dict[int, int],
    marks: Sequence[int],
    sa: list[int],
    isa: list[int],
    sample: int,
) -> Index:
    """An index of class `cls` holding exactly these pieces, nothing checked: the column in the
    class's own structure (`ChunkedWavelet` or `ByteIndex`), the marks in its own bit vector (`RRR`
    or `BitIndex`, given as 0/1 values), and `C`, both sample lists and the rate as given."""
    if cls is FMIndex:
        wavelet = FMIndex.__new__(FMIndex)
        wavelet._occ = ChunkedWavelet(last)
        wavelet._marks = RRR(marks)
        idx: Index = wavelet
    else:
        plain = PlainFMIndex.__new__(PlainFMIndex)
        plain._occ = ByteIndex(last)
        plain._marks = BitIndex(marks)
        idx = plain
    idx._c = c
    idx._sa_samples = sa
    idx._isa_samples = isa
    idx._sample = sample
    return idx


def fm_pieces(text: bytes, sample: int) -> Pieces:
    """The column, `C`, the marks and both sample lists of the index built over `text`, as plain
    data, read back out of an `FMIndex`."""
    idx = FMIndex(text, sample)
    n = idx.text_len()
    column = bytes(idx._occ.access_occ(row)[0] for row in range(n))
    marks = [idx._marks.access(row) for row in range(n)]
    return column, dict(idx._c), marks, list(idx._sa_samples), list(idx._isa_samples)


def fm_conjuncts(idx: Index) -> list[bool]:
    """Which of the seven pieces hold, in `is_valid`'s order (the Lean `FMIndex.Valid`'s)."""
    return [
        idx.is_positions_kept(),
        idx.is_sentinel_once(),
        idx.is_smaller_letters_counted(),
        idx.is_walk_visits_every_row(),
        idx.is_kept_rows_listed(),
        idx.is_letters_are_bytes(),
        idx.is_rate_at_least_one(),
    ]


def fm_kept_parts(idx: Index) -> list[bool]:
    """Which of invariant 2's three parts hold, in `is_positions_kept`'s order."""
    return [idx._kept_evenly(), idx._kept_rows_flagged(), idx._kept_positions_correct()]


def c_from_dense(last: bytes, dense: Sequence[int]) -> dict[int, int]:
    """The Rust's dense `C` (one entry per symbol of the column, ascending) as the Python's `dict`
    from symbol to block start.

    The entries are paired with the column's symbols in ascending order. A surplus entry gets a
    key past every byte (256, 257, ...) and a missing one leaves its symbol without a key, so the
    `dict` equals the one `is_smaller_letters_counted` computes exactly when the dense list equals the
    Rust's: the Rust's length check and pointwise check in one comparison. A pairing that
    truncated to the shorter of the two would turn a wrong `C` into a right one."""
    symbols = sorted(set(last))
    keys = symbols + list(range(256, 256 + max(0, len(dense) - len(symbols))))
    return {key: value for key, value in zip(keys[: len(dense)], dense, strict=True)}


def assemble_records(bits: Sequence[int], count: int) -> Records:
    """Records holding exactly these start bits (0/1) and this count, nothing checked; the text
    length is the number of bits, as the Rust's `from_parts_unchecked` takes it."""
    records = Records.__new__(Records)
    records._starts = BitIndex(bits)
    records._text_len = len(bits)
    records._count = count
    return records


def assemble_corpus(index: FMIndex, records: Records) -> Corpus:
    """The corpus `index` and `records` make, as given."""
    corpus = Corpus.__new__(Corpus)
    corpus._index = index
    corpus._records = records
    return corpus
