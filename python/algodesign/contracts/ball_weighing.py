# SPDX-License-Identifier: Apache-2.0
"""Ball weighing: find the one heavier ball with a balance scale, in as few weighings as possible.

You have `n` balls, exactly one of them heavier, and a balance scale that says which pan is
heavier or that the two are equal. Each weighing has three outcomes, so `w` weighings can tell
apart at most `3**w` cases. Finding one odd ball among `n` therefore needs at least
`ceil(log3 n)` weighings, whatever the strategy, and splitting the candidates into three groups
reaches that bound.

It is binary search with a three-way answer instead of a yes-or-no one.
"""

from __future__ import annotations


def min_weighings(n: int) -> int:
    """The lower bound: the fewest weighings that can find one odd ball among `n`.

    The smallest `w` with `3**w >= n`, computed with integers, so no rounding can move it.
    """
    w, reach = 0, 1
    while reach < n:
        w, reach = w + 1, reach * 3
    return w


def find_heavier(n: int, odd_index: int) -> tuple[int, int]:
    """Find the heavier ball among `n` by splitting the candidates into three groups.

    Balls weigh 1 except `odd_index`, which weighs 2. Returns `(found_index, weighings_used)`.
    """
    if not 0 <= odd_index < n:
        raise ValueError("odd_index out of range")
    weighings = 0

    def weigh(left: list[int], right: list[int]) -> int:
        nonlocal weighings
        weighings += 1
        wl = sum(2 if i == odd_index else 1 for i in left)
        wr = sum(2 if i == odd_index else 1 for i in right)
        return (wl > wr) - (wl < wr)

    candidates = list(range(n))
    while len(candidates) > 1:
        # Each pan gets ceil(m/3) balls and the rest stay off the scale, so the largest of the
        # three groups is ceil(m/3) and the number of weighings is the optimal ceil(log3 m).
        pan = (len(candidates) + 2) // 3
        left = candidates[:pan]
        right = candidates[pan : 2 * pan]
        rest = candidates[2 * pan :]
        result = weigh(left, right)
        if result > 0:
            candidates = left
        elif result < 0:
            candidates = right
        else:
            candidates = rest
    return candidates[0], weighings
