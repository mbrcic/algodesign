# SPDX-License-Identifier: Apache-2.0
"""Binary search on a sorted list.

Keep a stretch of positions that must contain the target if it is there at all, and halve it with
every look at its middle element. Among `n` elements the loop runs at most `floor(log2 n) + 1`
times, so a search costs `O(log n)`. `search_with_glances` is `search` with a count of the middle
elements it looked at, the chapter's glances: at most `ceil(log2(n + 1))`.

Source: Sedgewick §3.1, Algorithm 3.2 (`rank`), with its closed stretch `[lo, hi]`.

The Lean statements behind this module, in `lean/AlgoDesign/Searching/BinarySearch.lean`:
`search_isSome_iff`, `search_complete`, `searchProbes_le`.
"""

from __future__ import annotations

from ._ordering import SupportsLT


def search[T: SupportsLT](sorted_items: list[T], target: T) -> int | None:
    """Return the index of `target` in `sorted_items`, or `None` if it isn't there.

    `sorted_items` must be in ascending order. The loop invariant: `target`, if present, lies in
    `[lo, hi]`, both ends included. Comparing with the middle element either finds it or rules
    out one half, together with the middle itself; when `lo > hi` nothing is left. The midpoint
    `lo + (hi - lo) // 2` avoids the overflow `lo + hi` risks with fixed-width integers.
    """
    lo, hi = 0, len(sorted_items) - 1
    while lo <= hi:
        mid = lo + (hi - lo) // 2
        candidate = sorted_items[mid]
        if candidate == target:
            return mid
        elif candidate < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def search_with_glances[T: SupportsLT](sorted_items: list[T], target: T) -> tuple[int | None, int]:
    """`search`, and how many glances it took: one for each middle element compared."""
    glances = 0
    lo, hi = 0, len(sorted_items) - 1
    while lo <= hi:
        mid = lo + (hi - lo) // 2
        glances += 1
        candidate = sorted_items[mid]
        if candidate == target:
            return mid, glances
        elif candidate < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return None, glances
