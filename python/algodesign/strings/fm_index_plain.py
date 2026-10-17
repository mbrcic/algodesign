# SPDX-License-Identifier: Apache-2.0
"""The FM-index uncompressed: the plain version the tests hold `fm_index.FMIndex` to.

The same index with the last column `L` stored as plain bytes and `occ` answered by
`count_index.ByteIndex`, and the sampled-row marker a plain `count_index.BitIndex`, so every `occ`
is a count you can check by hand. Run side by side with `FMIndex`, it isolates the compressed
containers (`chunked_wavelet`, `rrr`): the two agree everywhere exactly when those containers
answer as the plain ones do. It is several times larger than the text; see `fm_index` for
backward search and sampling.
"""

from __future__ import annotations

from ._constants import SENTINEL
from ._fm_valid import ValidPieces
from .bwt import encode_with_sa as bwt_encode_with_sa
from .count_index import BitIndex, ByteIndex
from .fm_index import SAMPLE


class PlainFMIndex(ValidPieces):
    """`fm_index.FMIndex` with the last column stored as plain bytes."""

    __slots__ = ("_c", "_isa_samples", "_marks", "_occ", "_sa_samples", "_sample")

    _marks: BitIndex
    _occ: ByteIndex

    def __init__(self, text: bytes, sample: int = SAMPLE) -> None:
        """Build the index over the sentinel-terminated `text`, sampling every `sample`-th text
        position (`SAMPLE` if not given).

        Raises:
            ValueError: if `sample` is not positive, or if `text` is empty, does not end with
                `SENTINEL`, or carries `SENTINEL` before its last position.
        """
        if sample <= 0:
            raise ValueError(
                f"fm_index_plain.PlainFMIndex: the sampling rate must be positive, got {sample}"
            )
        last, sa = bwt_encode_with_sa(text)
        n = len(last)
        self._sample = sample
        self._occ = ByteIndex(last)  # also stores L itself, as `text()`

        # C[c]: how many characters sort below c, where c's block of the first column begins.
        self._c: dict[int, int] = {}
        below = 0
        for symbol in self._occ.symbols():
            self._c[symbol] = below
            below += self._occ.occ(symbol, n)

        # Both samples, in one pass over the suffix array: row r is suffix sa[r].
        marks = [0] * n
        self._sa_samples: list[int] = []
        self._isa_samples = [0] * ((n + sample - 1) // sample)
        for row, position in enumerate(sa):
            if position % sample == 0:
                marks[row] = 1
                self._sa_samples.append(position)
                self._isa_samples[position // sample] = row
        self._marks = BitIndex(marks)

    def text_len(self) -> int:
        """Length of the indexed text, sentinel included."""
        return len(self._occ)

    def count(self, pattern: bytes) -> int:
        """Occurrences of `pattern`, as `FMIndex.count` answers them."""
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
        """`text[start : start + length]`, as `FMIndex.extract` rebuilds it.

        Raises:
            ValueError: if `start` or `length` is negative, or `start + length` runs past the
                text.
        """
        n = self.text_len()
        if start < 0:
            raise ValueError(
                f"fm_index_plain.PlainFMIndex.extract: start {start} is negative; positions count "
                f"from 0"
            )
        if length < 0:
            raise ValueError(f"fm_index_plain.PlainFMIndex.extract: length {length} is negative")
        if start + length > n:
            raise ValueError(
                f"fm_index_plain.PlainFMIndex.extract: range {start}..{start + length} runs past "
                f"the text's {n} bytes"
            )
        if length == 0:
            return b""
        # Start at the first sampled position past the range (position n is 0, cyclically).
        k = (start + length + self._sample - 1) // self._sample
        if k * self._sample >= n:
            position, row = n, self._isa_samples[0]
        else:
            position, row = k * self._sample, self._isa_samples[k]
        column = self._occ.text()
        out = bytearray()
        for _ in range(position - start):
            out.append(column[row])  # L[row] is the character just before row's position
            row = self._lf(row)
        out.reverse()
        return bytes(out[:length])

    def _lf(self, row: int) -> int:
        """The row one text position earlier: `C[L[row]] + occ(L[row], row)`."""
        symbol = self._occ.text()[row]
        return self._c[symbol] + self._occ.occ(symbol, row)

    def _interval(self, pattern: bytes) -> tuple[int, int] | None:
        """The rows `[lo, hi)` whose suffix begins with `pattern`, or `None`: backward search."""
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
        """Text position of `row`: walk LF to a marked row, read its sample, add back the steps.
        Fewer than `min(sample, n)` steps on a valid index; past that it raises `RuntimeError`."""
        limit = min(self._sample, self.text_len())
        for steps in range(limit):
            if self._marks.access(row):
                return self._sa_samples[self._marks.rank(row)] + steps
            row = self._lf(row)
        raise RuntimeError(
            f"fm_index_plain.PlainFMIndex: an LF walk met no sampled row in {limit} steps; the "
            f"index is corrupt (every walk reaches text position 0, which is always sampled)"
        )

    # -- Checking the stored pieces: `FMIndex`'s seven checks, over the plain column ---------------

    def _column_and_lf(self) -> tuple[bytes, list[int]]:
        """The column, and LF over it with `C` rebuilt from the column, as `FMIndex` reads them."""
        column = self._occ.text()
        count: dict[int, int] = {}
        for symbol in column:
            count[symbol] = count.get(symbol, 0) + 1
        below: dict[int, int] = {}
        running = 0
        for symbol in sorted(count):
            below[symbol] = running
            running += count[symbol]
        lf = [below[symbol] + self._occ.occ(symbol, row) for row, symbol in enumerate(column)]
        return column, lf

    def _is_marked(self, row: int) -> bool:
        """Whether `row` is a row of the marks and marked; `False` outside them."""
        return 0 <= row < len(self._marks) and self._marks.access(row) == 1
