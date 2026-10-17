# SPDX-License-Identifier: Apache-2.0
"""The Burrows-Wheeler transform (Burrows-Wheeler 1994; Navarro §11), and the walk that undoes it.

Sort all n rotations of the text and read down the last column: **the transform permutes, it does
not compress**, but characters preceding similar contexts end up next to each other in long runs.

`encode` builds no rotation matrix. Row `i` of the sorted matrix is the rotation starting at suffix
`sa[i]`, so its last character is the byte just before that suffix: `text[(sa[i] + n - 1) % n]`. One
suffix array and one scan: O(n log n).

**The sentinel makes this shortcut correct.** Rotation order and suffix order agree only if the text
ends with a unique byte smaller than every other, so `encode` requires `text` to end with `SENTINEL`
and to contain it nowhere else.

`decode` recovers the text from the last column alone, by the LF mapping: if row `i`'s last byte is
`c`, then `LF(i) = C[c] + (number of c's in the last column above row i)`, where `C[c]` counts the
bytes smaller than `c`; the code calls `C` `block_start`, the count above row i `seen`, and the
last column `last`. `LF(i)` is the row whose rotation starts one position earlier in the text,
so following LF reads the text backwards. O(n) time and space.

The Rust differs here: nowhere in the procedure; its names are these.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/BWT/` (specification:
`BWT/Spec.lean`): `invertBwt_bwt` and `bwt_eq_rotations`, both for a sentinel-terminated text.
"""

from __future__ import annotations

from ._constants import BYTE_VALUES, SENTINEL  # the LF tables: one counter per possible byte
from .suffix_array import suffix_array


def encode(text: bytes) -> bytes:
    """The Burrows-Wheeler transform of the sentinel-terminated `text`."""
    return encode_with_sa(text)[0]


def encode_with_sa(text: bytes) -> tuple[bytes, list[int]]:
    """The Burrows-Wheeler transform of the sentinel-terminated `text`, and the suffix array it was
    computed through, which `fm_index.FMIndex` samples.

    Raises:
        ValueError: if `text` is empty, does not end with `SENTINEL`, or holds `SENTINEL` anywhere
            before its last position.
    """
    n = len(text)
    if n == 0:
        raise ValueError("bwt.encode: text is empty, so it cannot end with SENTINEL")
    if text[n - 1] != SENTINEL:
        raise ValueError("bwt.encode: text must end with SENTINEL (0)")
    for position in range(n - 1):
        if text[position] == SENTINEL:
            raise ValueError(
                f"bwt.encode: SENTINEL (0) appeared at position {position}, before the text's "
                "end; it may appear only as the last byte"
            )

    sa = suffix_array(text)
    last = bytearray(n)
    for row, start in enumerate(sa):
        last[row] = text[(start + n - 1) % n]
    return bytes(last), sa


def decode(last: bytes) -> bytes:
    """The text `last` is the transform of, recovered by the LF walk.

    Count the bytes to find where each one's block of rows begins, then in one forward pass give
    every row its `lf`: the row whose rotation starts one position earlier in the text.

    The walk starts at the row whose **last** character is the sentinel -- the rotation starting
    at text position 0 -- and reads the text back to front, so it is reversed at the end.

    Raises:
        ValueError: if `last` does not hold exactly one `SENTINEL` byte.
    """
    n = len(last)
    if n == 0:
        return b""

    counts = [0] * BYTE_VALUES
    for byte in last:
        counts[byte] += 1
    if counts[SENTINEL] != 1:
        raise ValueError(
            "bwt.decode: input must contain exactly one SENTINEL byte, found "
            f"{counts[SENTINEL]}"
        )

    # `block_start[c]` is the row at which byte `c`'s block begins once the rows are sorted:
    # every byte strictly below `c` stands above it in the first column.
    block_start = [0] * BYTE_VALUES
    running = 0
    for byte, count in enumerate(counts):
        block_start[byte] = running
        running += count

    # `lf[row]`: that row's block start, offset by how many equal bytes the column has already
    # shown; equal bytes keep their order between the two columns.
    seen = [0] * BYTE_VALUES
    lf = [0] * n
    for row, byte in enumerate(last):
        lf[row] = block_start[byte] + seen[byte]
        seen[byte] += 1

    row = last.index(SENTINEL)
    backwards = bytearray(n)
    for step in range(n):
        backwards[step] = last[row]
        row = lf[row]
    backwards.reverse()
    return bytes(backwards)


def is_same_letters(text: bytes, last: bytes) -> bool:
    """Box invariant 1: it is a permutation of the text, the same letters, each as often, `n` in
    all. The Lean `BWT.SameLetters`, `b.Perm t`."""
    return sorted(text) == sorted(last)


def is_letter_before_each_suffix(text: bytes, last: bytes) -> bool:
    """Box invariant 2: it follows the sorted suffixes, for each suffix, in their sorted order, the
    letter just before it. The Lean `BWT.LetterBeforeEachSuffix`,
    `b = bwtOfSa t (suffixArray t)`."""
    n = len(text)
    if len(last) != n:
        return False
    return all(
        text[(p + n - 1) % n] == c for p, c in zip(suffix_array(text), last, strict=True)
    )


def is_sentinel_once(last: bytes) -> bool:
    """The box's assumption read on the letters: the sentinel stands among them exactly once. The
    Lean `BWT.SentinelOnce`."""
    return last.count(SENTINEL) == 1


def check_valid(text: bytes, last: bytes) -> str | None:
    """The first piece of the Lean `BWT.Valid` that `last` breaks as the transform of
    `text`, in the box's order, or `None`."""
    if not is_same_letters(text, last):
        return "invariant 1 (same_letters)"
    if not is_letter_before_each_suffix(text, last):
        return "invariant 2 (letter_before_each_suffix)"
    if not is_sentinel_once(last):
        return "assumption (sentinel_once)"
    return None


def is_valid(text: bytes, last: bytes) -> bool:
    """The Lean `BWT.Valid`: the box's two invariants and its assumption on the letters. Lean:
    `valid_bwtOfSa` says `encode`'s output meets it on every terminated text."""
    return check_valid(text, last) is None
