# SPDX-License-Identifier: Apache-2.0
"""Test-only instrumentation for the Strings tests: what an algorithm reads, and how often it runs a step.

A test that compares answers cannot tell the chapter's algorithm from a slower one that gives the
same answers: `sorted()` in place of prefix doubling, Kasai restarting every comparison at offset 0,
Rabin-Karp hashing every window from scratch, `select` scanning every bit. Each of those is a
different algorithm, and the book picks the algorithm. The tests bind it by its cost instead --
characters read, bits read, steps run -- with the probes below, which wrap the input or a step
from the outside. They live here, not in the library, for the reason `treap_rotations.py` does:
the printed code is the algorithm, and this is a measurement of it.
"""

from __future__ import annotations

from collections.abc import Iterator
from typing import SupportsIndex, overload


class CountingBytes(bytes):
    """`bytes` that count the characters read through them: one per integer index, and the
    length of every slice taken. `reads` is per instance and starts at `0`."""

    reads: int

    def __new__(cls, data: bytes) -> CountingBytes:
        self = super().__new__(cls, data)
        self.reads = 0
        return self

    @overload
    def __getitem__(self, index: SupportsIndex) -> int: ...
    @overload
    def __getitem__(self, index: slice) -> bytes: ...
    def __getitem__(self, index: SupportsIndex | slice) -> int | bytes:
        value = super().__getitem__(index)
        self.reads += len(value) if isinstance(value, bytes) else 1
        return value

    def __iter__(self) -> Iterator[int]:
        for character in super().__iter__():
            self.reads += 1
            yield character


class CountingBits(list[int]):
    """A list of bits that counts the entries read through it: one per integer index, the length
    of every slice taken, and one per entry iterated over. `reads` starts at `0`."""

    reads: int

    def __init__(self, bits: list[int]) -> None:
        super().__init__(bits)
        self.reads = 0

    @overload
    def __getitem__(self, index: SupportsIndex) -> int: ...
    @overload
    def __getitem__(self, index: slice) -> list[int]: ...
    def __getitem__(self, index: SupportsIndex | slice) -> int | list[int]:
        value = super().__getitem__(index)
        self.reads += len(value) if isinstance(value, list) else 1
        return value

    def __iter__(self) -> Iterator[int]:
        for bit in super().__iter__():
            self.reads += 1
            yield bit


class RecordingBytes(bytes):
    """`bytes` that record *which* positions are read through them: every integer index, every
    position of a slice, and every position inside the `[start, end)` window of a `count` -- the
    C-level scan `ByteIndex.occ` uses, which `CountingBytes` cannot see. `positions` is per
    instance and starts empty."""

    positions: list[int]

    def __new__(cls, data: bytes) -> RecordingBytes:
        self = super().__new__(cls, data)
        self.positions = []
        return self

    @overload
    def __getitem__(self, index: SupportsIndex) -> int: ...
    @overload
    def __getitem__(self, index: slice) -> bytes: ...
    def __getitem__(self, index: SupportsIndex | slice) -> int | bytes:
        if isinstance(index, slice):
            self.positions.extend(range(*index.indices(len(self))))
        else:
            self.positions.append(range(len(self))[index])
        return super().__getitem__(index)

    def count(  # type: ignore[override]
        self, sub: int | bytes, start: SupportsIndex | None = None, end: SupportsIndex | None = None
    ) -> int:
        self.positions.extend(range(*slice(start, end).indices(len(self))))
        return super().count(sub, start, end)
