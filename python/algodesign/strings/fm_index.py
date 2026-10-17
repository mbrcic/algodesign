# SPDX-License-Identifier: Apache-2.0
"""The FM-index (Ferragina-Manzini 2000; Navarro §11): count, locate and extract without keeping
the text, in less space than the text.

It is built from the last column `L` of the BWT (`bwt`) and the array `C`, where `C[c]` counts the
text's bytes smaller than `c`. `L` is held compressed, in a `ChunkedWavelet` (Navarro §11.3.3):
it answers `occ(c, i)`, the number of `c`s in `L[0:i]`, and reads `L[i]` together with
`occ(L[i], i)`. `fm_index_plain.PlainFMIndex` is the same index with `L` stored as plain bytes.

**Backward search.** Hold the stretch `[lo, hi)` of suffix-array rows whose suffix begins with the
part of the pattern read so far, and extend the pattern one character `c` to the **left**. The rows
that keep matching are those in `[lo, hi)` whose last-column character is `c`, and in the sorted
first column they land inside `c`'s block, in the same relative order. So the new stretch is `C[c]
+ occ(c, lo)` to `C[c] + occ(c, hi)`. Two `occ` lookups per pattern character: `count` is O(m) in
the pattern length, independent of the text length.

**Sampling** (Navarro §11.1.4). `locate` holds a row and wants its text position; `extract` holds a
text position and wants its row. Both use one rate, `sample`: every text position that is a
multiple of it is sampled. A bitvector `B` (an `RRR`) marks the rows of those positions, and a list
holds their positions in row order, found by `rank(B, row)`; a second list holds the row of each
sampled position, found by division. Each LF step moves one position earlier in the text. Text
position 0 is sampled, so a `locate` walk takes fewer than `sample` steps.

**The sentinel in a pattern.** The index answers about the text without its `SENTINEL`, which a
pattern holding one cannot occur in, so such a pattern answers nothing. (Backward search matches
*rotations* of the stored text, and a rotation that wraps past the sentinel is not a substring.)
The empty pattern occurs at every position of that text, its end included: `n` of them for a
stored text of `n` bytes.

The Rust differs here: the structure is the same; it packs both kept-position arrays at `ceil(log2
n)` bits.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/FMIndex/` (specification:
`FMIndex/Spec.lean`): `count_of_valid`, `locate_perm_of_valid`, `fmCount_eq`, `fmLocate_perm`.
"""

from __future__ import annotations

from ._constants import SENTINEL
from ._fm_valid import ValidPieces
from .bwt import encode_with_sa as bwt_encode_with_sa
from .chunked_wavelet import ChunkedWavelet
from .rrr import RRR

SAMPLE = 32
"""The default sampling rate: one sampled text position in 32. `FMIndex(text)` and
`records.Corpus` build at it."""


class FMIndex(ValidPieces):
    """An index over one sentinel-terminated text: counts, locates and extracts without it."""

    __slots__ = ("_c", "_isa_samples", "_marks", "_occ", "_sa_samples", "_sample")

    _marks: RRR
    _occ: ChunkedWavelet

    def __init__(self, text: bytes, sample: int = SAMPLE, chunk: int | None = None) -> None:
        """Build the index over the sentinel-terminated `text`, sampling every `sample`-th text
        position (`SAMPLE` if not given), with `L` in chunks of `chunk` symbols
        (`ChunkedWavelet`'s default if `None`).

        Both samples are read off the suffix array `bwt.encode_with_sa` returns with `L`.

        Raises:
            ValueError: if `sample` is not positive, or if `text` is empty, does not end with
                `SENTINEL`, or carries `SENTINEL` before its last position.
        """
        if sample <= 0:
            raise ValueError(f"fm_index.FMIndex: the sampling rate must be positive, got {sample}")
        last, sa = bwt_encode_with_sa(text)
        n = len(last)
        self._sample = sample
        self._occ = ChunkedWavelet(last, chunk)

        # C, by prefix sum over the symbols in ascending order: where each symbol's block begins
        # in the sorted first column.
        self._c: dict[int, int] = {}
        below = 0
        for symbol in self._occ.symbols():
            self._c[symbol] = below
            below += self._occ.occ(symbol, n)

        # Both samples, in one pass over the rows.
        marks = [0] * n
        self._sa_samples: list[int] = []
        self._isa_samples = [0] * ((n + sample - 1) // sample)
        for row, position in enumerate(sa):
            if position % sample == 0:
                marks[row] = 1
                self._sa_samples.append(position)
                self._isa_samples[position // sample] = row
        self._marks = RRR(marks)

    def text_len(self) -> int:
        """Length of the indexed text, sentinel included."""
        return len(self._occ)

    def count(self, pattern: bytes) -> int:
        """Occurrences of `pattern` in the text without its sentinel, without decoding any of it.
        `O(m)`."""
        if SENTINEL in pattern:  # the text without its sentinel holds no such pattern
            return 0
        stretch = self._interval(pattern)
        if stretch is None:
            return 0
        lo, hi = stretch
        return hi - lo

    def locate(self, pattern: bytes) -> list[int]:
        """Start positions of every occurrence of `pattern`, in suffix order, not text order. One
        LF walk per hit."""
        if SENTINEL in pattern:
            return []
        stretch = self._interval(pattern)
        if stretch is None:
            return []
        lo, hi = stretch
        return [self._position_of(row) for row in range(lo, hi)]

    def extract(self, start: int, length: int) -> bytes:
        """`text[start : start + length]`, sentinel included if the range reaches it.

        Navarro's Algorithm 11.7: start at the first sampled text position past the range, walk
        LF backwards from its row emitting `L[row]`, and reverse. Past the end, start from position
        `n`, which is position 0 read cyclically.

        Raises:
            ValueError: if `start` or `length` is negative, or `start + length` runs past the
                text.
        """
        n = self.text_len()
        if start < 0:
            raise ValueError(
                f"fm_index.FMIndex.extract: start {start} is negative; positions count from 0"
            )
        if length < 0:
            raise ValueError(f"fm_index.FMIndex.extract: length {length} is negative")
        if start + length > n:
            raise ValueError(
                f"fm_index.FMIndex.extract: range {start}..{start + length} runs past the "
                f"text's {n} bytes"
            )
        if length == 0:
            return b""
        k = (start + length + self._sample - 1) // self._sample
        if k * self._sample >= n:
            position, row = n, self._isa_samples[0]
        else:
            position, row = k * self._sample, self._isa_samples[k]
        out = bytearray()
        for _ in range(position - start):
            symbol, row = self._lf(row)
            out.append(symbol)
        out.reverse()
        return bytes(out[:length])

    def _lf(self, row: int) -> tuple[int, int]:
        """`L[row]`, and the row one text position earlier: `C[L[row]] + occ(L[row], row)`."""
        symbol, occ = self._occ.access_occ(row)
        return symbol, self._c[symbol] + occ

    def _interval(self, pattern: bytes) -> tuple[int, int] | None:
        """The rows `[lo, hi)` whose suffix begins with `pattern`, or `None` when there are none.

        Backward search, right to left; the empty pattern keeps every row.
        """
        n = self.text_len()
        if len(pattern) > n or SENTINEL in pattern[:-1]:
            return None
        lo, hi = 0, n
        for symbol in reversed(pattern):
            base = self._c.get(symbol)
            if base is None:
                return None
            lo = base + self._occ.occ(symbol, lo)
            hi = base + self._occ.occ(symbol, hi)
            if lo >= hi:
                return None
        return lo, hi

    def _position_of(self, row: int) -> int:
        """Text position of `row` (Navarro's Algorithm 11.6): walk LF to a marked row, read its
        sample, and add back the steps.

        Each step moves one text position earlier, and position 0 is sampled, so on a valid index
        the walk meets a mark in fewer than `min(sample, n)` steps.

        Raises:
            RuntimeError: if no marked row is met within that bound (the index is corrupt).
        """
        limit = min(self._sample, self.text_len())
        for steps in range(limit):
            if self._marks.access(row):
                return self._sa_samples[self._marks.rank(row)] + steps
            _, row = self._lf(row)
        raise RuntimeError(
            f"fm_index.FMIndex: an LF walk met no sampled row in {limit} steps; the index is "
            f"corrupt (every walk reaches text position 0, which is always sampled)"
        )

    # -- Checking the stored pieces ------------------------------------------------------------
    # What `ValidPieces`' seven checks read, each stored piece against the column; they answer on
    # any index, however corrupted.

    def _column_and_lf(self) -> tuple[list[int], list[int]]:
        """The column, and LF over it with `C` rebuilt from the column itself rather than read
        from `_c`: the Lean's `lf`."""
        reads = [self._occ.access_occ(row) for row in range(self.text_len())]
        count: dict[int, int] = {}
        for symbol, _ in reads:
            count[symbol] = count.get(symbol, 0) + 1
        below: dict[int, int] = {}
        running = 0
        for symbol in sorted(count):
            below[symbol] = running
            running += count[symbol]
        column = [symbol for symbol, _ in reads]
        lf = [below[symbol] + occ for symbol, occ in reads]
        return column, lf

    def _is_marked(self, row: int) -> bool:
        """Whether `row` is a row of the marks and marked; `False` outside them."""
        return 0 <= row < len(self._marks) and self._marks.access(row) == 1
