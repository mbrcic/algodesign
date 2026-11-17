# SPDX-License-Identifier: Apache-2.0
"""Sequential (linear) search, and building a duplicate-free list with it.

With no order to exploit, the only way to find a key is to look at every element in turn -- so
the keys need only `==`. A hit costs at most `n` comparisons, and a miss costs exactly `n`.
Building a list of `n` distinct keys this way costs `0 + 1 + ... + (n - 1) = n(n - 1)/2`
comparisons.

`contains_with_checks` is `contains` with a count of the checks, the number the chapter states:
`n` on a miss.

Source: Sedgewick §3.1, Algorithm 3.1 (this list appends each new key; Sedgewick's prepends).

The Lean statements behind this module, in `lean/AlgoDesign/Searching/SequentialSearch.lean`:
`mem_buildM`, `nodup_buildM`, `time_containsM_tickEq_eq_length_of_not_mem`, `time_buildM_eq`.
"""

from __future__ import annotations

from collections.abc import Iterable


def contains[T](items: list[T], target: T) -> bool:
    """Whether `target` occurs in `items`: check each element, front to back, stopping at the
    first match."""
    for item in items:
        if item == target:
            return True
    return False


def contains_with_checks[T](items: list[T], target: T) -> tuple[bool, int]:
    """`contains`, and how many elements it checked: all of them on a miss, the first match's
    position plus one on a hit."""
    checks = 0
    for item in items:
        checks += 1
        if item == target:
            return True, checks
    return False, checks


def build[T](keys: Iterable[T]) -> list[T]:
    """The distinct keys of `keys`, in first-seen order. Each key is appended only if a linear
    search of the list so far misses it, which makes the whole build quadratic."""
    result: list[T] = []
    for key in keys:
        if not contains(result, key):
            result.append(key)
    return result
