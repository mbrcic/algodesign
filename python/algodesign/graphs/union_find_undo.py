# SPDX-License-Identifier: Apache-2.0
"""Union-find that can take back its merges, last first.

Westbrook and Tarjan (*SIAM J. Comput.* 18(1), 1989, p. 3, crediting Mannila and Ukkonen): union
by rank without path compression, so a merge writes one link and perhaps one rank, and a log of
those writes undoes it. `find` walks up to the root and changes nothing. `union` has the same
guard and tie rule as `UnionFind`: find `x`'s root, then `y`'s; if they are the same, merge
nothing; otherwise the root of lower rank goes under the other, and on equal ranks the second root
goes under the first, whose rank rises by one.

The log has one entry per `union` call: the root that stopped being a root and whether the other
root's rank rose, or `None` when nothing merged, so a call that merged nothing still takes one
`undo`. `undo` takes back the last entry, restoring the links, the ranks and the group count, and
answers True; on an empty log it does nothing and answers False.

Costs: `find`, `union` and `joined` walk at most log2 n links up; `undo` and `count` are constant
time. There is no `check_valid`: the invariant, the union-find's together with every state the log
rolls back to being legal, is the Lean `Valid` (`RollbacksLegal`), and the tests check full and
partial rollbacks against a plain search instead.

No path is longer than log2 n, so the recursion in `find` stays shallow. An item outside
`0 .. n-1` raises `IndexError`, and a negative number of items `ValueError`.
"""

from __future__ import annotations


class UndoUnionFind:
    """A union-find over the items `0 .. n-1` with a log of its merges."""

    def __init__(self, n: int) -> None:
        """Every item alone: each its own root, of rank 0, so `n` groups; the log empty."""
        if n < 0:
            raise ValueError(f"the number of items must be nonnegative, not {n}")
        self.parent = list(range(n))  # a root is its own parent
        self.rank = [0] * n
        self._count = n  # the number of groups
        self.log: list[tuple[int, bool] | None] = []  # (root put under, other rank rose)

    def find(self, x: int) -> int:
        """The root of `x`'s group, found by walking up; nothing changes."""
        if not 0 <= x < len(self.parent):
            raise IndexError(f"item {x} out of range 0..{len(self.parent)}")
        if self.parent[x] == x:
            return x
        return self.find(self.parent[x])

    def union(self, x: int, y: int) -> bool:
        """Merge the groups of `x` and `y`, logging it; True if two groups became one."""
        rx = self.find(x)
        ry = self.find(y)
        if rx == ry:
            self.log.append(None)
            return False
        if self.rank[rx] < self.rank[ry]:
            self.parent[rx] = ry
            self.log.append((rx, False))
        elif self.rank[ry] < self.rank[rx]:
            self.parent[ry] = rx
            self.log.append((ry, False))
        else:
            self.parent[ry] = rx
            self.rank[rx] += 1
            self.log.append((ry, True))
        self._count -= 1
        return True

    def undo(self) -> bool:
        """Take back the last `union` call; False if there is none."""
        if not self.log:
            return False
        last = self.log.pop()
        if last is not None:
            child, rose = last
            if rose:  # read the old parent before the link is reset
                self.rank[self.parent[child]] -= 1
            self.parent[child] = child
            self._count += 1
        return True

    def joined(self, x: int, y: int) -> bool:
        """Are `x` and `y` in one group? Looks up `x`, then `y`."""
        rx = self.find(x)
        ry = self.find(y)
        return rx == ry

    def count(self) -> int:
        """The number of groups."""
        return self._count
