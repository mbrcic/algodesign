# SPDX-License-Identifier: Apache-2.0
"""Backward search's running state, the Lean `BackwardSearch.Valid` (`FMIndex/Spec.lean`), as a
check on any interval.

These pieces read the text and its suffix array, which the index does not keep, so they are for
tests. The state is the stretch `[lo, hi)` of rows of `sa` after reading `read`, the pattern's last
`len(read)` bytes.
"""

from __future__ import annotations


def is_stretch_holds_matches(text: bytes, sa: list[int], read: bytes, lo: int, hi: int) -> bool:
    """Box invariant 1: the rows kept so far are exactly the suffixes that start with the part of
    the pattern read so far. The Lean `StretchHoldsMatches`: every row `r` below `hi + len(sa)` lies
    in `[lo, hi)` exactly when it is a row of `sa` whose suffix begins with `read`."""
    for r in range(hi + len(sa)):
        inside = lo <= r < hi
        matches = r < len(sa) and text[sa[r]:].startswith(read)
        if inside != matches:
            return False
    return True


def is_stretch_starts_right(text: bytes, read: bytes, lo: int) -> bool:
    """Not in the box: the stretch starts where the suffixes sorting below the part read so
    far end. The Lean `StretchStartsRight`, `lo = lexBelow t q`."""
    return lo == sum(1 for i in range(len(text)) if text[i:] < read)


def is_stretch_as_wide_as_matches(text: bytes, read: bytes, lo: int, hi: int) -> bool:
    """Not in the box: the stretch is as wide as the part read so far occurs. The Lean
    `StretchAsWideAsMatches`, `hi = lo + matchCount t q`."""
    return hi == lo + sum(1 for i in range(len(text)) if text[i:].startswith(read))


def check_valid(text: bytes, sa: list[int], read: bytes, lo: int, hi: int) -> str | None:
    """The first piece of the Lean `BackwardSearch.Valid` the state breaks, or `None`."""
    if not is_stretch_holds_matches(text, sa, read, lo, hi):
        return "invariant 1 (stretch_holds_matches)"
    if not is_stretch_starts_right(text, read, lo):
        return "not in the box (stretch_starts_right)"
    if not is_stretch_as_wide_as_matches(text, read, lo, hi):
        return "not in the box (stretch_as_wide_as_matches)"
    return None


def is_valid(text: bytes, sa: list[int], read: bytes, lo: int, hi: int) -> bool:
    """The Lean `BackwardSearch.Valid`: its three pieces. Lean: `BackwardSearch.valid_step` keeps
    it through one symbol."""
    return check_valid(text, sa, read, lo, hi) is None
