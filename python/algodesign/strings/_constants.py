# SPDX-License-Identifier: Apache-2.0
"""The two reserved bytes of the Strings chapter, and the number of byte values."""

from __future__ import annotations

SENTINEL = 0
"""The byte that terminates every text the BWT accepts.

`0`, so that it sorts below every other byte value: that is what makes the rotation matrix of
`text + SENTINEL` and the suffix array of `text + SENTINEL` list their rows in the same order,
which is what lets the transform be computed from a suffix array instead of from n rotations.
"""

SEPARATOR = 1
"""The byte that divides one record from the next inside a corpus's concatenation.

`1`, the lowest byte that is not `SENTINEL`. A corpus is one text, so its records need a divider
that sorts below ordinary content; the sentinel cannot serve, because it has to appear exactly
once, at the very end. No record may contain this byte, and no query fragment may either.
"""

BYTE_VALUES = 256
"""How many values a byte takes: the buckets of the suffix array's first counting sort, the
counters of the BWT's LF tables, and the R of an R-way trie over bytes (`trie.ALPHABET`)."""


def show(data: bytes) -> str:
    """`data` as a reader would write it: `SENTINEL` as `$`, `SEPARATOR` as `|`, and every other
    byte as its Latin-1 character. For reading output only -- `show(bwt.encode(parse("banana$")))`
    is `"annb$aa"`, where the raw bytes print as `b'annb\\x00aa'`."""
    readable = data.replace(bytes([SENTINEL]), b"$").replace(bytes([SEPARATOR]), b"|")
    return readable.decode("latin-1")


def parse(written: str) -> bytes:
    """The text a reader writes, as the bytes the chapter's functions take: `$` becomes
    `SENTINEL`, `|` becomes `SEPARATOR`, and every other character its Latin-1 byte. So the
    chapter's `banana$` can be run: `bwt.encode(parse("banana$"))`. A text that needs a literal
    `$` or `|` byte cannot be written this way; build its `bytes` directly."""
    raw = written.encode("latin-1")
    return raw.replace(b"$", bytes([SENTINEL])).replace(b"|", bytes([SEPARATOR]))
