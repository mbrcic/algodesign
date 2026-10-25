# SPDX-License-Identifier: Apache-2.0
"""The seven checks of the Lean `FMIndex.Valid` and `FMIndex.WellFormed`, shared by
`fm_index.FMIndex` and `fm_index_plain.PlainFMIndex`, which store the same parts in different
containers.

A class using this one stores `_c`, `_isa_samples`, `_marks`, `_occ`, `_sa_samples` and `_sample`
as its index does, and supplies `text_len`, `_column_and_lf` (the last column and LF over it) and
`_is_marked`; the checks read the parts through nothing else.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Protocol

from ._constants import BYTE_VALUES, SENTINEL


class _Marks(Protocol):
    def __len__(self) -> int: ...
    def rank(self, i: int) -> int: ...


class _Occ(Protocol):
    def symbols(self) -> list[int]: ...
    def occ(self, symbol: int, i: int) -> int: ...


class ValidPieces:
    """`is_valid`, `check_valid` and the seven `is_<piece>` checks, over the parts a subclass
    stores."""

    __slots__ = ()

    _c: dict[int, int]
    _isa_samples: list[int]
    _marks: _Marks
    _occ: _Occ
    _sa_samples: list[int]
    _sample: int

    def text_len(self) -> int:
        """The length of the indexed text, sentinel included."""
        raise NotImplementedError

    def _column_and_lf(self) -> tuple[Sequence[int], list[int]]:
        """The last column, and LF over it with `C` rebuilt from the column itself."""
        raise NotImplementedError

    def _is_marked(self, row: int) -> bool:
        """Whether `row` is a row of the marks and marked; `False` outside them."""
        raise NotImplementedError

    def _kept_count(self) -> int:
        """How many text positions the rate keeps, `ceil(n / k)`; `0` for a non-positive rate."""
        if self._sample <= 0:
            return 0
        return (self.text_len() + self._sample - 1) // self._sample

    def is_positions_kept(self) -> bool:
        """Box invariant 2: at fixed intervals along the text, a row keeps its own position, so
        every match is a short walk from one. The Lean `PositionsKept`, its three parts in order:
        the positions kept are `0, k, 2k, ...` below `n`; one mark per row and one stored position
        per mark; each marked row holds its own position."""
        return self._kept_evenly() and self._kept_rows_flagged() and self._kept_positions_correct()

    def _kept_evenly(self) -> bool:
        """Invariant 2's first part: the stored positions are exactly `0, k, 2k, ...` below `n`,
        each once, in any order (none at a non-positive rate)."""
        m = self._kept_count()
        if len(self._sa_samples) != m:
            return False
        k = self._sample
        seen = [False] * m
        for position in self._sa_samples:
            if position < 0 or position % k != 0:
                return False
            j = position // k
            if j >= m or seen[j]:
                return False
            seen[j] = True
        return True

    def _kept_rows_flagged(self) -> bool:
        """Invariant 2's second part: one mark per row, and one stored position per mark."""
        n = self.text_len()
        return len(self._marks) == n and self._marks.rank(n) == len(self._sa_samples)

    def _kept_positions_correct(self) -> bool:
        """Invariant 2's third part, the Lean `KeptPositionsCorrect`: each marked row holds its own
        text position.

        Walking LF from the row of text position 0, the row reached after `j` steps holds position
        `(n - j) % n`: it is marked exactly when that position is a multiple of `k`, and then its
        stored position is that one.
        """
        column, lf = self._column_and_lf()
        n = len(column)
        if SENTINEL not in column:
            return True
        row = list(column).index(SENTINEL)
        k = self._sample
        for j in range(n):
            position = (n - j) % n
            kept = (position % k if k != 0 else position) == 0
            if row >= len(self._marks) or self._is_marked(row) != kept:
                return False
            if kept:
                rank = self._marks.rank(row)
                if rank >= len(self._sa_samples) or self._sa_samples[rank] != position:
                    return False
            row = lf[row]
        return True

    def is_smaller_letters_counted(self) -> bool:
        """Not in the box: `C` gives each symbol of the column the number of column symbols
        below it. The Lean `SmallerLettersCounted`."""
        n = self.text_len()
        want: dict[int, int] = {}
        below = 0
        for symbol in self._occ.symbols():
            want[symbol] = below
            below += self._occ.occ(symbol, n)
        return self._c == want

    def is_sentinel_once(self) -> bool:
        """The transform's box assumption, one `$`: `SENTINEL` stands in the column exactly once.
        The Lean `SentinelOnce`."""
        column, _ = self._column_and_lf()
        return list(column).count(SENTINEL) == 1

    def is_walk_visits_every_row(self) -> bool:
        """Not in the box: `n` LF steps from row 0 visit every row once and come back to
        row 0. The Lean `WalkVisitsEveryRow`."""
        _, lf = self._column_and_lf()
        n = len(lf)
        if n == 0:
            return True
        seen = [False] * n
        row = 0
        for _ in range(n):
            if seen[row]:
                return False
            seen[row] = True
            row = lf[row]
        return row == 0

    def is_kept_rows_listed(self) -> bool:
        """Not in the box: the row of each kept position is listed, in position order, for
        `extract` to start from. The Lean `KeptRowsListed`."""
        if len(self._isa_samples) != self._kept_count():
            return False
        n, k = self.text_len(), self._sample
        for j, row in enumerate(self._isa_samples):
            if not 0 <= row < n or row >= len(self._marks) or not self._is_marked(row):
                return False
            rank = self._marks.rank(row)
            if rank >= len(self._sa_samples) or self._sa_samples[rank] != j * k:
                return False
        return True

    def is_letters_are_bytes(self) -> bool:
        """Not in the box: every letter of the column is a byte. The Lean
        `LettersAreBytes`. Held by construction (both containers are built from `bytes`), so
        always `True`."""
        column, _ = self._column_and_lf()
        return all(letter < BYTE_VALUES for letter in column)

    def is_rate_at_least_two(self) -> bool:
        """Not in the box: the interval between kept positions is at least 2; smaller intervals
        are refused at build. The Lean `RateAtLeastTwo`."""
        return self._sample >= 2

    def check_valid(self) -> str | None:
        """The first piece of the Lean `FMIndex.Valid` or `FMIndex.WellFormed` the stored index
        breaks, in their order, or `None`: box invariant 2, the transform's assumption of one `$`,
        then the pieces not in the box."""
        # Box invariant 1 holds of backward search's running stretch, not of the stored index:
        # `backward_search.check_valid` checks it on each step's state.
        pieces = [
            (self.is_positions_kept, "invariant 2 (positions_kept)"),
            (self.is_sentinel_once, "assumption (sentinel_once)"),
            (self.is_smaller_letters_counted, "not in the box (smaller_letters_counted)"),
            (self.is_walk_visits_every_row, "not in the box (walk_visits_every_row)"),
            (self.is_kept_rows_listed, "not in the box (kept_rows_listed)"),
            (self.is_letters_are_bytes, "not in the box (letters_are_bytes)"),
            (self.is_rate_at_least_two, "not in the box (rate_at_least_two)"),
        ]
        for holds, name in pieces:
            if not holds():
                return name
        return None

    def is_valid(self) -> bool:
        """The Lean `FMIndex.Valid` and `FMIndex.WellFormed`, their seven pieces in order. Answers
        `False`, never raises, on a corrupted index."""
        return self.check_valid() is None
