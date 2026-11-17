# SPDX-License-Identifier: Apache-2.0
"""The last column in fixed-length chunks, a Huffman-shaped wavelet tree per chunk (Navarro §11.3.3;
Kärkkäinen and Puglisi 2011).

Cut the string `L` into chunks of `chunk` symbols and build a separate `WaveletTree` for each. Keep
a table `R`, where `R[r][c]` is the number of `c`s before chunk `r` starts. Then

    occ(c, i) = R[i // chunk][c] + (c's in chunk i // chunk before its position i % chunk).

Over a BWT, a chunk tends to hold the symbols that precede a few similar contexts, so each chunk's
own Huffman code is short. Kärkkäinen and Puglisi bound the total at `n * H_k + chunk * sigma ** k`
bits for every `k` at once (`H_k` the `k`-th order entropy), where one tree for the whole string
costs `n * H0`.

The default chunk length is Kärkkäinen and Puglisi's `sigma * (bit length of n) ** 2`.

No Lean statement models it: the tests hold its answers to plain counting, and the FM-index built
on it to the plain `fm_index_plain.PlainFMIndex`.
"""

from __future__ import annotations

from .wavelet_tree import WaveletTree


def default_chunk(text: bytes) -> int:
    """`sigma * (bit length of n) ** 2`, at least 1."""
    return max(1, len(set(text)) * len(text).bit_length() ** 2)


class ChunkedWavelet:
    """`occ` and one LF step's reads over a string cut into chunks, one wavelet tree each."""

    __slots__ = ("_chunk", "_length", "_ranks", "_trees")

    def __init__(self, text: bytes, chunk: int | None = None) -> None:
        """Cut `text` into chunks of `chunk` symbols (the default length if `None`).

        Raises:
            ValueError: if `chunk` is not positive.
        """
        if chunk is None:
            chunk = default_chunk(text)
        if chunk <= 0:
            raise ValueError(f"chunked_wavelet: the chunk length must be positive, got {chunk}")
        self._chunk = chunk
        self._length = len(text)
        self._trees: list[WaveletTree] = []
        self._ranks: list[dict[int, int]] = []  # R[r][c]; one extra row holds the totals
        running: dict[int, int] = {}
        for start in range(0, len(text), chunk):
            piece = text[start : start + chunk]
            self._ranks.append(dict(running))
            for symbol in piece:
                running[symbol] = running.get(symbol, 0) + 1
            self._trees.append(WaveletTree(piece))
        self._ranks.append(running)

    def __len__(self) -> int:
        """Length of the string."""
        return self._length

    def symbols(self) -> list[int]:
        """The distinct symbols, ascending."""
        return sorted(self._ranks[-1])

    def chunks(self) -> int:
        """Number of chunks."""
        return len(self._trees)

    def occ(self, symbol: int, i: int) -> int:
        """Occurrences of `symbol` before position `i` (all of them, if `i` is past the end).

        Raises:
            ValueError: if `i` is negative.
        """
        if i < 0:
            raise ValueError(f"chunked_wavelet.occ: position {i} is negative")
        i = min(i, self._length)
        r, within = divmod(i, self._chunk)
        before = self._ranks[r].get(symbol, 0)
        if within == 0:
            return before
        return before + self._trees[r].rank(symbol, within)

    def access_occ(self, i: int) -> tuple[int, int]:
        """The symbol `c` at position `i` and `occ(c, i)`: one descent in `i`'s chunk.

        Raises:
            ValueError: if `i` is not a position of the string.
        """
        if not 0 <= i < self._length:
            raise ValueError(
                f"chunked_wavelet.access_occ: position {i} is not one of the "
                f"{self._length} positions"
            )
        r, within = divmod(i, self._chunk)
        symbol, rank = self._trees[r].access_rank(within)
        return symbol, self._ranks[r].get(symbol, 0) + rank

    def stored_bits(self) -> int:
        """Bits in all the chunks' trees: the sum of their Huffman encodings."""
        return sum(tree.stored_bits() for tree in self._trees)
