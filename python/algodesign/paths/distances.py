# SPDX-License-Identifier: Apache-2.0
"""The answer of a search from one start: each vertex's cost and the vertex it was reached from.

`cost[v]` is what the search found for `v`, or `None` when it never reached `v`. `previous[v]` is
the vertex `v` was last reached from, and `None` for the start and for every vertex not reached.
Following `previous` back from a reached vertex ends at the start, so `path_to(v)` reads the path
off it, start first. A vertex outside the graph raises `IndexError`.

A path names its vertices, not its arrows. Where several arrows join two consecutive vertices, its
cost is that of the cheapest of them: a cost is recorded only when it strictly drops, so the arrow
that set it last is the cheapest from that previous vertex.

The Lean definition behind this module, in `lean/AlgoDesign/Paths/Dijkstra/Spec.lean`: `Answer`.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass
class Distances:
    """Each vertex's cost from the start (`None` if not reached) and its previous vertex."""

    cost: list[int | None]
    previous: list[int | None]

    def path_to(self, v: int) -> list[int] | None:
        """The vertices from the start to `v`, following each previous vertex back; `None` if `v`
        was not reached."""
        if not 0 <= v < len(self.cost):
            raise IndexError(f"vertex {v} out of range 0..{len(self.cost)}")
        if self.cost[v] is None:
            return None
        path = [v]
        while (u := self.previous[path[-1]]) is not None:
            path.append(u)
        path.reverse()
        return path
