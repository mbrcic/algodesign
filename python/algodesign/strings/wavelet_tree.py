# SPDX-License-Identifier: Apache-2.0
"""A Huffman-shaped wavelet tree (Navarro §6.2): `rank` and `access_rank` over a byte string.

The Strings chapter uses it as a black box: `chunked_wavelet` asks it `occ` and an LF step's two
reads, and it answers them. In one line: each internal node keeps one bit per symbol passing
through it, and `rank` follows the symbol's Huffman code down, turning `i` into a `rank` of the
node's bits at every level.

Equal counts in the Huffman merge are broken by `(count, id)`: leaves numbered in byte order,
merged nodes numbered next, the first taken the `0` child.

No Lean statement models it: the tests hold its answers to plain counting.
"""

from __future__ import annotations

import heapq

from .count_index import BitIndex

type Shape = int | tuple[Shape, Shape]
"""A code tree: a leaf is its symbol, an internal node the pair of its `0` and `1` subtrees."""


def huffman_shape(text: bytes) -> Shape:
    """The Huffman code tree of the symbol counts of the non-empty `text`, ties broken as above."""
    counts: dict[int, int] = {}
    for symbol in text:
        counts[symbol] = counts.get(symbol, 0) + 1
    heap: list[tuple[int, int, Shape]] = [
        (count, number, symbol) for number, (symbol, count) in enumerate(sorted(counts.items()))
    ]
    heapq.heapify(heap)
    next_number = len(heap)
    while len(heap) > 1:
        count0, _, zero = heapq.heappop(heap)
        count1, _, one = heapq.heappop(heap)
        heapq.heappush(heap, (count0 + count1, next_number, (zero, one)))
        next_number += 1
    return heap[0][2]


def codes_of(shape: Shape, prefix: str = "") -> dict[int, str]:
    """Each leaf's code, as a string of `0`s and `1`s."""
    if isinstance(shape, int):
        return {shape: prefix}
    zero, one = shape
    return codes_of(zero, prefix + "0") | codes_of(one, prefix + "1")


class _Node:
    """An internal node: its bitvector and its two subtrees (a leaf is just its symbol)."""

    __slots__ = ("bits", "children")

    def __init__(self, bits: BitIndex, children: tuple[_Node | int, _Node | int]) -> None:
        self.bits = bits
        self.children = children


def _build(text: bytes, shape: Shape) -> _Node | int:
    """The tree for `text`, all of whose symbols lie under `shape`."""
    if isinstance(shape, int):
        return shape
    zero, one = shape
    goes_right = set(codes_of(one))
    bits = [1 if symbol in goes_right else 0 for symbol in text]
    left = bytes(s for s in text if s not in goes_right)
    right = bytes(s for s in text if s in goes_right)
    return _Node(BitIndex(bits), (_build(left, zero), _build(right, one)))


class WaveletTree:
    """`rank` and `access_rank` over a byte string, in a Huffman-shaped wavelet tree."""

    __slots__ = ("_codes", "_length", "_root", "_stored_bits")

    def __init__(self, text: bytes) -> None:
        """Build the tree over `text`."""
        self._length = len(text)
        self._codes: dict[int, str] = {}
        self._root: _Node | int = 0
        if text:
            shape = huffman_shape(text)
            self._codes = codes_of(shape)
            self._root = _build(text, shape)
        self._stored_bits = sum(len(self._codes[s]) for s in text)

    def __len__(self) -> int:
        """Length of the string."""
        return self._length

    def code(self, symbol: int) -> str | None:
        """`symbol`'s Huffman code, or `None` if it does not occur."""
        return self._codes.get(symbol)

    def stored_bits(self) -> int:
        """Bits in all the node bitvectors: the length of the Huffman encoding of the string."""
        return self._stored_bits

    def rank(self, symbol: int, i: int) -> int:
        """Occurrences of `symbol` before position `i` (all of them, if `i` is past the end).

        Raises:
            ValueError: if `i` is negative.
        """
        if i < 0:
            raise ValueError(f"wavelet_tree.rank: position {i} is negative")
        code = self._codes.get(symbol)
        if code is None:
            return 0
        i = min(i, self._length)
        node, depth = self._root, 0
        while isinstance(node, _Node):  # the leaf is reached exactly when the code runs out
            ones = node.bits.rank(i)
            if code[depth] == "1":
                i, node = ones, node.children[1]
            else:
                i, node = i - ones, node.children[0]
            depth += 1
        return i

    def access_rank(self, i: int) -> tuple[int, int]:
        """The symbol at position `i`, and how many of it come before `i`.

        Raises:
            ValueError: if `i` is not a position of the string.
        """
        if not 0 <= i < self._length:
            raise ValueError(
                f"wavelet_tree.access_rank: position {i} is not one of the {self._length} positions"
            )
        node = self._root
        while isinstance(node, _Node):
            ones = node.bits.rank(i)
            if node.bits.access(i):
                i, node = ones, node.children[1]
            else:
                i, node = i - ones, node.children[0]
        return node, i
