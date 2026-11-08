# SPDX-License-Identifier: Apache-2.0
"""Union-find over the items `0 .. n-1`: are these two joined yet, while links keep arriving.

Each group is a tree whose root stands for it. `find` is CLRS's `FIND-SET` with full path
compression (CLRS 4th ed., §19.3, p. 530), recursive as printed: find the parent's root, point
the item straight at it, return it. `union` is Weiss's `unionSets` (Weiss, *Data Structures and
Algorithm Analysis in C++*, 4th ed., §8.5, Fig. 8.14): find `x`'s root first, then `y`'s; if they
are the same, merge nothing; otherwise the root of lower rank goes under the other, and on equal
ranks the second root goes under the first, whose rank rises by one. The lookup order is part of
the method: compression makes the links depend on it.

The recursion goes as deep as the path it walks, and no path is longer than log2 n, so Python's
recursion limit is never near. An item outside `0 .. n-1` raises `IndexError`, and a negative
number of items `ValueError`.

`is_upward_ends_at_root`, `is_ranks_rise_upward`, `is_root_rank_bounds_size` and
`is_count_is_roots` are the four pieces of the Lean `Valid` and `WellFormed`; each answers on any
stored state, broken or not, without trusting another. That shortening only points an item at
another higher up its own tree is about a step, not one of the box's invariants and not a state,
so no piece checks it: the Lean states it of `find` (`FindSpec.points_higher`).

Costs: `find`, `union` and `joined` walk at most log2 n links up; a long run of operations costs
nearly a constant per operation (argued: CLRS 4th ed., §19.4, Theorem 19.14).

The Lean statements behind this module, in `lean/AlgoDesign/Graphs/UnionFind/`: `find_spec`,
`union_spec`, `valid_union`.
"""

from __future__ import annotations


class UnionFind:
    """A union-find over the items `0 .. n-1`, fixed at construction."""

    def __init__(self, n: int) -> None:
        """Every item alone: each its own root, of rank 0, so `n` groups."""
        if n < 0:
            raise ValueError(f"the number of items must be nonnegative, not {n}")
        self.parent = list(range(n))  # a root is its own parent
        self.rank = [0] * n
        self._count = n  # the number of groups

    def find(self, x: int) -> int:
        """The root of `x`'s group; every item on the walk now points straight at it."""
        if not 0 <= x < len(self.parent):
            raise IndexError(f"item {x} out of range 0..{len(self.parent)}")
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, x: int, y: int) -> bool:
        """Merge the groups of `x` and `y`; True if two groups became one."""
        rx = self.find(x)
        ry = self.find(y)
        if rx == ry:
            return False
        if self.rank[rx] < self.rank[ry]:
            self.parent[rx] = ry
        elif self.rank[ry] < self.rank[rx]:
            self.parent[ry] = rx
        else:
            self.parent[ry] = rx
            self.rank[rx] += 1
        self._count -= 1
        return True

    def joined(self, x: int, y: int) -> bool:
        """Are `x` and `y` in one group? Looks up `x`, then `y`."""
        rx = self.find(x)
        ry = self.find(y)
        return rx == ry

    def count(self) -> int:
        """The number of groups."""
        return self._count

    # The checks below read a stored state as it is. An item outside the link array links to
    # itself and has rank 0 outside the rank array, so no check leaves the arrays, whatever is
    # stored.

    def _up(self, i: int) -> int:
        return self.parent[i] if 0 <= i < len(self.parent) else i

    def _rank_of(self, i: int) -> int:
        return self.rank[i] if 0 <= i < len(self.rank) else 0

    def _root_of(self, i: int) -> int:
        """Where `n` steps up from `i` lead, compressing nothing (Lean `root`)."""
        for _ in range(len(self.parent)):
            i = self._up(i)
        return i

    def is_upward_ends_at_root(self) -> bool:
        """Box invariant 1: every link stays among the items, and `n` steps up from any item
        reach an item that is its own parent (Lean `UpwardEndsAtRoot`)."""
        n = len(self.parent)
        return all(0 <= self._up(i) < n and self._up(self._root_of(i)) == self._root_of(i)
                   for i in range(n))

    def is_ranks_rise_upward(self) -> bool:
        """Box invariant 2, first half: an item that is not a root has a smaller rank than its
        parent (Lean `RanksRiseUpward`)."""
        return all(self._up(i) == i or self._rank_of(i) < self._rank_of(self._up(i))
                   for i in range(len(self.parent)))

    def is_root_rank_bounds_size(self) -> bool:
        """Box invariant 2, second half: a root of rank r has at least 2^r items, those in its tree
        (Lean `RootRankBoundsSize`)."""
        roots = [self._root_of(i) for i in range(len(self.parent))]
        # 2 ** rank <= size, asked as rank < size.bit_length(), so no rank builds a huge number.
        return all(self._up(r) != r or self._rank_of(r) < roots.count(r).bit_length()
                   for r in range(len(self.parent)))

    def is_count_is_roots(self) -> bool:
        """Not in the box: the group count is the number of roots (Lean `CountIsRoots`)."""
        return self._count == sum(1 for r in range(len(self.parent)) if self._up(r) == r)

    def one_rank_per_item(self) -> bool:
        """Layout: one rank per item; the Lean's ranks are a function on the items."""
        return len(self.rank) == len(self.parent)

    def check_valid(self) -> str | None:
        """The first piece of the Lean `Valid` the stored state breaks, or `None`."""
        if not self.is_upward_ends_at_root():
            return "invariant 1 (upward_ends_at_root)"
        if not self.is_ranks_rise_upward():
            return "invariant 2 (ranks_rise_upward)"
        if not self.is_root_rank_bounds_size():
            return "invariant 2 (root_rank_bounds_size)"
        if not self.is_count_is_roots():
            return "not in the box (count_is_roots)"
        return None

    def is_valid(self) -> bool:
        """The Lean `Valid`: its four pieces."""
        return self.check_valid() is None
