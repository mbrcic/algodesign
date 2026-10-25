# SPDX-License-Identifier: Apache-2.0
"""Rank, select and occ with a two-level directory (Jacobson 1989; Navarro §4.2).

`BitIndex` answers two questions about a bitvector: `rank(i)`, the number of 1s before position `i`,
and `select(j)`, the position of the `j`-th 1. `ByteIndex` answers `occ(c, i)`, the number of
occurrences of byte `c` before position `i` of a text. Over the two symbols `0` and `1`, `occ` of
symbol `1` *is* `rank`, so both classes are built on one structure, `_TwoLevel`, and differ only in
how they count inside a single block.

A query at position `i` adds three numbers:

1. the **superblock** count -- set positions before `i`'s superblock, stored as an absolute count;
2. the **block** count -- set positions from that superblock's start to `i`'s block, stored relative
   to the superblock, so it stays small;
3. the **tail** -- counted directly, one position at a time, from the start of `i`'s block to `i`.

Steps 1 and 2 are table lookups and step 3 scans fewer than `BLOCK` positions, so `rank` and `occ`
take constant time. `select` binary-searches the same tables in O(log n). The small `BLOCK` and
`SUPERBLOCK` make the directory visible on examples short enough to trace by hand.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/RankSelect/` (specification:
`RankSelect/Spec.lean`): `occ_eq_rank`, `rank_select`.
"""

from __future__ import annotations

from bisect import bisect_right
from collections.abc import Sequence

BLOCK = 8
"""Positions in one block: the most the tail scan ever has to count."""

SUPERBLOCK = 64
"""Positions in one superblock, and a whole number of `BLOCK`s (eight of them).

A superblock that was not a whole number of blocks would give its last block a relative count taken
against the wrong base.
"""

BLOCKS_PER_SUPERBLOCK = SUPERBLOCK // BLOCK
"""Blocks inside one superblock. `SUPERBLOCK % BLOCK == 0` is what makes this the whole story."""


class _TwoLevel:
    """The shared directory behind both `BitIndex` and `ByteIndex`, built from one count per
    block."""

    __slots__ = ("blocks", "superblocks", "total")

    def __init__(self, block_counts: Sequence[int]) -> None:
        """`superblocks[s]` is the absolute count before superblock `s`; `blocks[b]` is the count
        before block `b` *relative to its superblock*."""
        superblocks: list[int] = []
        blocks: list[int] = []
        total = 0
        for block, count in enumerate(block_counts):
            if block % BLOCKS_PER_SUPERBLOCK == 0:
                superblocks.append(total)
            blocks.append(total - superblocks[block // BLOCKS_PER_SUPERBLOCK])
            total += count
        self.superblocks = superblocks
        self.blocks = blocks
        self.total = total

    def count_before_block(self, block: int) -> int:
        """Set positions strictly before the start of `block`: levels 1 and 2, added."""
        return self.superblocks[block // BLOCKS_PER_SUPERBLOCK] + self.blocks[block]

    def locate(self, j: int) -> int | None:
        """The block holding set position number `j`, or `None` when there is none.

        Both levels are binary-searched: prefix counts never decrease, so both lists are sorted.
        """
        if j < 0 or j >= self.total:
            return None
        superblock = bisect_right(self.superblocks, j) - 1
        base = self.superblocks[superblock]
        first = superblock * BLOCKS_PER_SUPERBLOCK
        last = min(first + BLOCKS_PER_SUPERBLOCK, len(self.blocks))
        return bisect_right(self.blocks, j - base, first, last) - 1


class BitIndex:
    """`rank` and `select` over a bitvector: `_TwoLevel` plus a tail that adds up bits."""

    __slots__ = ("_bits", "_index")

    def __init__(self, bits: Sequence[int]) -> None:
        """Index `bits`, one entry per bit.

        Raises:
            ValueError: if any entry is neither `0` nor `1`.
        """
        for position, bit in enumerate(bits):
            if bit not in (0, 1):
                raise ValueError(
                    f"count_index.BitIndex: entry {bit} at position {position} is neither 0 "
                    f"nor 1; a bitvector takes one 0-or-1 entry per bit"
                )
        self._bits = list(bits)
        block_counts = [
            sum(self._bits[start : start + BLOCK])
            for start in range(0, len(self._bits), BLOCK)
        ]
        self._index = _TwoLevel(block_counts)

    def __len__(self) -> int:
        """Bits indexed."""
        return len(self._bits)

    def rank(self, i: int) -> int:
        """Set bits strictly before position `i`. A position past the end counts the whole vector.

        Constant time: one superblock read, one block read, and a scan of fewer than `BLOCK`
        positions.

        Raises:
            ValueError: if `i` is negative.
        """
        if i < 0:
            raise ValueError(f"count_index.BitIndex.rank: position {i} is negative")
        if i >= len(self._bits):
            return self._index.total
        block = i // BLOCK
        tail = 0
        for bit in self._bits[block * BLOCK : i]:
            tail += bit
        return self._index.count_before_block(block) + tail

    def access(self, i: int) -> int:
        """Bit `i`.

        Raises:
            ValueError: if `i` is not a position of the vector.
        """
        if not 0 <= i < len(self._bits):
            raise ValueError(
                f"count_index.BitIndex.access: position {i} is not one of the "
                f"{len(self._bits)} positions"
            )
        return self._bits[i]

    def select(self, j: int) -> int | None:
        """Position of the `j`-th set bit, zero-based, or `None` when there is no such bit: binary
        search over the directory, then a walk of that block, `O(log n)`."""
        block = self._index.locate(j)
        if block is None:
            return None
        rest = j - self._index.count_before_block(block)
        for offset, bit in enumerate(self._bits[block * BLOCK : (block + 1) * BLOCK]):
            if bit:
                if rest == 0:
                    return block * BLOCK + offset
                rest -= 1
        return None


class ByteIndex:
    """`occ` over a text: the same `_TwoLevel` as `BitIndex`, one per symbol present, plus a scan of
    at most `BLOCK` bytes instead of a sum of bits.

    Only the byte values actually present get a directory.
    """

    __slots__ = ("_index", "_text")

    def __init__(self, text: bytes) -> None:
        """Index `text`. `O(n + sigma * n / BLOCK)`: one pass tallying every symbol's per-block
        count, then one directory built per symbol from those counts.

        The symbols are stored in **ascending byte order**, so an FM-index's `C` array can be
        built by walking `symbols()` left to right.
        """
        self._text = bytes(text)
        nblocks = (len(self._text) + BLOCK - 1) // BLOCK
        counts: dict[int, list[int]] = {byte: [0] * nblocks for byte in set(self._text)}
        for position, byte in enumerate(self._text):
            counts[byte][position // BLOCK] += 1
        self._index = {byte: _TwoLevel(counts[byte]) for byte in sorted(counts)}

    def __len__(self) -> int:
        """Positions indexed."""
        return len(self._text)

    def text(self) -> bytes:
        """The indexed text. The tail scan reads it, and so does `PlainFMIndex`."""
        return self._text

    def symbols(self) -> list[int]:
        """The byte values occurring in the text, ascending -- the effective alphabet."""
        return list(self._index)

    def occ(self, symbol: int, i: int) -> int:
        """Occurrences of `symbol` strictly before position `i`. Saturates at the end of the text.

        The same three levels as `BitIndex.rank`; the tail counts matches of one byte.

        Raises:
            ValueError: if `i` is negative.
        """
        if i < 0:
            raise ValueError(f"count_index.ByteIndex.occ: position {i} is negative")
        index = self._index.get(symbol)
        if index is None:
            return 0
        if i >= len(self._text):
            return index.total
        block = i // BLOCK
        start = block * BLOCK
        return index.count_before_block(block) + self._text.count(symbol, start, i)
