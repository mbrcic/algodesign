# SPDX-License-Identifier: Apache-2.0
"""An RRR compressed bitvector (Raman, Raman and Rao 2002; Navarro §4.1.1 and §4.2.3).

Cut the bits into blocks of `BLOCK_BITS`. A block with `c` ones is stored as a pair:

- its **class** `c`;
- its **offset** `o`: which of the `comb(BLOCK_BITS, c)` blocks with `c` ones it is, counting them
  in increasing order as numbers read first bit first. The offset takes exactly
  `ceil(log2(comb(BLOCK_BITS, c)))` bits, so an all-zero or all-one block takes none.

A block of few ones has few possible offsets and a short one, which is where the compression comes
from: the offsets add up to about `n * H0` bits.

The offsets have different widths, so they are written one after another into a single stream of
bits, and nobody can jump to block `t`'s offset without adding up the widths before it. So every
`SUPERBLOCK_BLOCKS` blocks we store a **sample**: the rank before the superblock and where its first
offset starts in the stream. `rank(i)` starts at the sample, adds the classes of the blocks before
`i`'s -- each class also says how far to move in the stream -- and decodes only `i`'s block.

The compressed FM-index uses this for its sampled-row marker (Navarro §11.1.4): one set bit per
`sample` rows is very compressible. The small blocks here let short examples cross several
superblocks.

No Lean statement models it: the tests hold its answers to plain counting, and the FM-index that
marks its sampled rows with it to the plain `fm_index_plain.PlainFMIndex`.
"""

from __future__ import annotations

from collections.abc import Sequence
from math import comb

BLOCK_BITS = 15
"""Bits per block."""

SUPERBLOCK_BLOCKS = 4
"""Blocks per superblock: one rank sample and one stream pointer each."""


def offset_width(c: int) -> int:
    """Bits an offset of class `c` takes: enough to count `comb(BLOCK_BITS, c)` blocks."""
    return (comb(BLOCK_BITS, c) - 1).bit_length()


def encode(block: Sequence[int]) -> tuple[int, int]:
    """The `(class, offset)` of a block of `BLOCK_BITS` bits (Navarro, Algorithm 4.1).

    Walk the bits left to right with `c` ones still to place among `left` positions. A 1 here means
    every block with a 0 here -- and the same ones still to come -- sorts before this one, and there
    are `comb(left - 1, c)` of those, so the offset skips over them.
    """
    c = sum(block)
    offset, ones = 0, c
    for position, bit in enumerate(block):
        left = BLOCK_BITS - position
        if bit:
            offset += comb(left - 1, ones)
            ones -= 1
    return c, offset


def decode(c: int, offset: int) -> list[int]:
    """The block of class `c` and offset `offset`: `encode` run backwards."""
    block = []
    ones = c
    for position in range(BLOCK_BITS):
        left = BLOCK_BITS - position
        skip = comb(left - 1, ones)
        if ones > 0 and offset >= skip:
            block.append(1)
            offset -= skip
            ones -= 1
        else:
            block.append(0)
    return block


class RRR:
    """`rank` and `access` over a bitvector stored as RRR classes and offsets."""

    __slots__ = ("_classes", "_length", "_sample_pointers", "_sample_ranks", "_stream")

    def __init__(self, bits: Sequence[int]) -> None:
        """Compress `bits`, one 0-or-1 entry per bit. The last block is padded with zeros.

        Raises:
            ValueError: if any entry is neither `0` nor `1`.
        """
        for position, bit in enumerate(bits):
            if bit not in (0, 1):
                raise ValueError(
                    f"rrr.RRR: entry {bit} at position {position} is neither 0 nor 1; a "
                    f"bitvector takes one 0-or-1 entry per bit"
                )
        self._length = len(bits)
        self._classes: list[int] = []
        self._stream: list[int] = []  # the offsets' bits, one after another
        self._sample_ranks: list[int] = []
        self._sample_pointers: list[int] = []
        ones = 0
        for t, start in enumerate(range(0, len(bits), BLOCK_BITS)):
            if t % SUPERBLOCK_BLOCKS == 0:
                self._sample_ranks.append(ones)
                self._sample_pointers.append(len(self._stream))
            block = list(bits[start : start + BLOCK_BITS])
            block += [0] * (BLOCK_BITS - len(block))
            c, offset = encode(block)
            self._classes.append(c)
            width = offset_width(c)
            self._stream += [(offset >> (width - 1 - k)) & 1 for k in range(width)]
            ones += c
        self._sample_ranks.append(ones)  # the total, for `rank` at the very end

    def __len__(self) -> int:
        """Bits indexed."""
        return self._length

    def _block(self, t: int) -> tuple[int, list[int]]:
        """The rank before block `t`, and block `t`'s bits: from the sample, skip whole blocks by
        their classes alone, then read and decode one offset (Navarro, Algorithm 4.5)."""
        superblock = t // SUPERBLOCK_BLOCKS
        rank = self._sample_ranks[superblock]
        pointer = self._sample_pointers[superblock]
        for before in range(superblock * SUPERBLOCK_BLOCKS, t):
            rank += self._classes[before]
            pointer += offset_width(self._classes[before])
        c = self._classes[t]
        offset = 0
        for bit in self._stream[pointer : pointer + offset_width(c)]:
            offset = 2 * offset + bit
        return rank, decode(c, offset)

    def rank(self, i: int) -> int:
        """Set bits strictly before position `i`. A position past the end counts every set bit.

        Raises:
            ValueError: if `i` is negative.
        """
        if i < 0:
            raise ValueError(f"rrr.rank: position {i} is negative")
        if i >= self._length:
            return self._sample_ranks[-1]
        rank, block = self._block(i // BLOCK_BITS)
        return rank + sum(block[: i % BLOCK_BITS])

    def access(self, i: int) -> int:
        """Bit `i`.

        Raises:
            ValueError: if `i` is not a position of the vector.
        """
        if not 0 <= i < self._length:
            raise ValueError(f"rrr.access: position {i} is not one of the {self._length} positions")
        _, block = self._block(i // BLOCK_BITS)
        return block[i % BLOCK_BITS]
