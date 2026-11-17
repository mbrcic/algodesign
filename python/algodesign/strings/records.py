# SPDX-License-Identifier: Apache-2.0
"""Where the Strings chapter's search ends up: **from a hit to the whole quote**.

A fragment of a quote may be its opening words, its middle or its end, and all three cost the same.
A corpus is one text: the records joined by `SEPARATOR` and closed by `SENTINEL`, indexed by an
FM-index. A hit position is used **exactly once**, for a `rank` (`Records.record_of`) naming its
record; `Records.bounds` turns that number into an interval with two `select`s, and `Corpus.quote`
extracts its bytes.

Two guards keep every match inside one record: a record carrying a reserved byte is refused when
the corpus is built, and a query fragment carrying one is refused before the search runs.

A query costs O(m) for backward search on a fragment of length m, plus one bounded LF walk per hit.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/Records/` (specification:
`Records/Spec.lean`): `recordBounds_contains`, `recordOf_eq_of_no_start_between`. Over a model of
`Corpus.find` and `Corpus.quote` on the joined text, `Records/Corpus.lean` proves
`Corpus.findObligation` and `Corpus.quoteObligation`.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from itertools import pairwise

from ._constants import SENTINEL, SEPARATOR
from .count_index import BitIndex
from .fm_index import SAMPLE, FMIndex


class Records:
    """A bitvector of record starts over one text: `rank` names the record a position falls in,
    `select` bounds it.

    The last record ends at the end of the text rather than at another start.
    """

    __slots__ = ("_count", "_starts", "_text_len")

    def __init__(self, starts: Sequence[int], text_len: int) -> None:
        """Index `starts` -- strictly increasing positions, the first of them `0` -- over a text of
        `text_len` bytes.

        Raises:
            ValueError: if `text_len` is negative, if the first start is not `0`, if the starts are
                not strictly increasing, or if the last start is not inside the text.
        """
        if text_len < 0:
            raise ValueError(f"records.Records: text length {text_len} is negative")
        if starts:
            if starts[0] != 0:
                raise ValueError(
                    f"records.Records: the first record must start at position 0, not "
                    f"{starts[0]}; a position before the first start lies in no record"
                )
            for earlier, later in pairwise(starts):
                if earlier >= later:
                    raise ValueError(
                        f"records.Records: record starts must be strictly increasing, but "
                        f"{earlier} is followed by {later}"
                    )
            if starts[-1] >= text_len:
                raise ValueError(
                    f"records.Records: record start {starts[-1]} is not inside a "
                    f"{text_len}-byte text"
                )

        bits = [0] * text_len
        for start in starts:
            bits[start] = 1
        self._starts = BitIndex(bits)
        self._text_len = text_len
        self._count = len(starts)

    def __len__(self) -> int:
        """Records indexed."""
        return self._count

    def text_len(self) -> int:
        """Bytes of text the starts cover, and the end of the last record."""
        return self._text_len

    def record_of(self, pos: int) -> int:
        """The record `pos` falls in: one less than the number of starts at or before `pos`, since
        records are numbered from zero.

        **One `rank`, and the only use a hit position gets.**

        Raises:
            ValueError: if `pos` is negative, or if there are no records.
        """
        if pos < 0:
            raise ValueError(f"records.record_of: position {pos} is negative")
        at_or_before = self._starts.rank(pos + 1)
        if at_or_before == 0:
            raise ValueError(
                f"records.record_of: no record starts at or before position {pos}; "
                f"this corpus holds no records"
            )
        return at_or_before - 1

    def bounds(self, record_id: int) -> tuple[int, int]:
        """The half-open bounds `[start, end)` of record `record_id`: the `record_id`-th start, and
        the next one -- or the end of the text, for the last record, which has no next start.

        **Two `select`s**, and neither of them looks at a hit. In a `Corpus` each interval ends
        with a reserved byte, so a record's own bytes are `start .. end - 1`.

        Raises:
            ValueError: if `record_id` is not a record of this index.
        """
        start = None if record_id < 0 else self._starts.select(record_id)
        if start is None:
            raise ValueError(
                f"records.bounds: no record {record_id}; the records are numbered "
                f"0 to {self._count - 1}"
            )
        end = self._starts.select(record_id + 1)
        return start, self._text_len if end is None else end

    def starts(self) -> BitIndex:
        """The start bits: bit `p` is set when a record starts at position `p`."""
        return self._starts

    def starts_at_zero(self) -> bool:
        """Whether, if any record starts, one starts at position 0: the Lean `FirstRecordAtStart`.
        Lean: `recordBounds_contains_of_firstRecordAtStart`."""
        nothing_starts = self._starts.rank(len(self._starts)) == 0
        return nothing_starts or self._starts.rank(1) == 1

    def count_matches(self) -> bool:
        """Layout check: `len` is the number of starts."""
        return self._text_len >= 0 and self._count == self._starts.rank(self._text_len)

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, in its order, or `None`:
        `"not in the box (starts_at_zero)"` or `"layout (count_matches)"`."""
        if not self.starts_at_zero():
            return "not in the box (starts_at_zero)"
        if not self.count_matches():
            return "layout (count_matches)"
        return None

    def is_valid(self) -> bool:
        """`starts_at_zero` and `count_matches`; a bitvector cannot list starts out of order."""
        return self.check_valid() is None


@dataclass(frozen=True)
class Quote:
    """One whole record, recovered from a hit inside it."""

    record_id: int
    """Which record of the `Corpus` this is, in build order."""

    bounds: tuple[int, int]
    """Where it sits in the concatenation, as `Records.bounds` reports it -- reserved byte
    included, so `text` is one byte shorter than `bounds[1] - bounds[0]`."""

    text: bytes
    """The record's bytes: the whole quote, whichever fragment of it was remembered."""


def _is_unsearchable(fragment: bytes) -> bool:
    """Whether `fragment` carries a reserved byte, so no record can contain it."""
    return any(byte in (SENTINEL, SEPARATOR) for byte in fragment)


class Corpus:
    """A corpus of records under one search, queried by fragment and answering with whole records.

    The records are concatenated with a `SEPARATOR` between them and a `SENTINEL` at the end, one
    `FMIndex` is built over the whole, and their starts are marked in a `Records` bitvector. The
    index is the only copy of the text.
    """

    __slots__ = ("_index", "_records")

    def __init__(self, records: Sequence[bytes]) -> None:
        """Build the corpus over `records`, in the order given.

        Raises:
            ValueError: if any record contains `SENTINEL` or `SEPARATOR`.
        """
        text = bytearray()
        starts: list[int] = []
        for record_id, record in enumerate(records):
            for at, byte in enumerate(record):
                if byte in (SENTINEL, SEPARATOR):
                    raise ValueError(
                        f"records.Corpus: record {record_id} carries the reserved byte {byte} "
                        f"at position {at}; SENTINEL ({SENTINEL}) terminates the concatenation "
                        f"and SEPARATOR ({SEPARATOR}) divides it, so no record may hold either"
                    )
            starts.append(len(text))
            text += record
            text.append(SEPARATOR)
        # The last separator closes the concatenation, so it becomes the sentinel.
        if text:
            text[-1] = SENTINEL
        else:
            text.append(SENTINEL)

        self._index = FMIndex(bytes(text), SAMPLE)
        self._records = Records(starts, len(text))

    def __len__(self) -> int:
        """Records in the corpus."""
        return len(self._records)

    def records(self) -> Records:
        """The record starts, for a caller that wants the `rank`/`select` pair directly."""
        return self._records

    def count(self, fragment: bytes) -> int:
        """How many times `fragment` occurs in the corpus, before `find`'s per-record
        deduplication: one `FMIndex.count`, with no position located. Lean: `matchCount`.

        The empty fragment is at every position of every record, its end included, as the
        chapter has it: `count(b"")` is the sum of `len(record) + 1`, while `find(b"")` returns
        each record once. Each byte between records stands for one record's end."""
        if not self._records or _is_unsearchable(fragment):
            return 0
        return self._index.count(fragment)

    def quote(self, record_id: int) -> Quote:
        """The whole of record `record_id`.

        `Records.bounds` is two `select`s; `FMIndex.extract` decodes the interval out of the index;
        the `- 1` drops the reserved byte that closes it. Lean: `Corpus.quoteObligation`.

        Raises:
            ValueError: if `record_id` is not a record of this corpus.
        """
        start, end = self._records.bounds(record_id)
        return Quote(record_id, (start, end), self._index.extract(start, end - start - 1))

    def find(self, fragment: bytes) -> list[Quote]:
        """Every quote containing `fragment`, once each, in corpus order.

        `FMIndex.locate` finds the hits; each hit position is spent on one `Records.record_of` -- a
        `rank` -- and then discarded; the record numbers are deduplicated, and each is turned back
        into bytes by `quote`, which never reads the hit. Lean: `Corpus.findObligation`.
        """
        if not fragment:
            return [self.quote(record_id) for record_id in range(len(self._records))]
        if _is_unsearchable(fragment):
            return []
        numbers = {self._records.record_of(hit) for hit in self._index.locate(fragment)}
        return [self.quote(record_id) for record_id in sorted(numbers)]

    def lengths_agree(self) -> bool:
        """Layout check: the starts cover exactly the text the index holds."""
        return self._records.text_len() == self._index.text_len()

    def reserved_bytes_placed(self) -> bool:
        """Whether the separators sit exactly where the starts say: a `SEPARATOR` just before
        every start `s > 0`, at `s - 1`, and nowhere else. Asked of the index with `locate`, and
        only once the index's own `is_valid` holds, which already ends the text with its one
        `SENTINEL`.
        """
        if not self._index.is_valid():
            return False
        starts = self._records.starts()
        want = [s - 1 for s in range(1, len(starts)) if starts.access(s)]
        separators = sorted(self._index.locate(bytes([SEPARATOR])))
        return separators == want

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, in its order, or `None`: the index's own
        `check_valid` label, then the records', then `"layout (lengths_agree)"` or
        `"not in the box (reserved_bytes_placed)"`."""
        broken = self._index.check_valid() or self._records.check_valid()
        if broken is not None:
            return broken
        if not self.lengths_agree():
            return "layout (lengths_agree)"
        if not self.reserved_bytes_placed():
            return "not in the box (reserved_bytes_placed)"
        return None

    def is_valid(self) -> bool:
        """The index's `is_valid`, the records' `is_valid`, `lengths_agree` and
        `reserved_bytes_placed`."""
        return self.check_valid() is None
