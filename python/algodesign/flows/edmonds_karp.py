# SPDX-License-Identifier: Apache-2.0
"""Edmonds–Karp's path rule: each round sends along one augmenting path with the fewest arrows.

A round is one first-in first-out search from the source over the residual arrows with residual
capacity, each row in input order, stopped as soon as the sink is labeled. A vertex keeps the arrow
that labeled it first. The path those arrows lead back along from the sink gets its bottleneck, the
smallest residual capacity on it. A round whose search misses the sink sends nothing (Edmonds and
Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", 1972; the
queue "labeled first, scanned first" of Ford and Fulkerson, 1957; "first vertex labeled wins",
Ahuja, Magnanti and Orlin, *Network Flows*, p. 216).

`shortest_path(residual, at_least)` is that search over the arrows with residual capacity at least
`at_least`; capacity scaling runs it too.

Each round is one search, linear in vertices plus arrows, and there are at most `n m` rounds for
`n` vertices and `m` arrows.

The Rust differs here: its labels and queue are arrays kept from round to round, and it sends
along the labels without building the path.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/MaxFlow/EdmondsKarp.lean`: the
rule's promise, `edmondsKarp_promise`; at most n·m added paths, `edmondsKarp_augmentations`.
"""

from __future__ import annotations

from collections import deque

from .residual import Augmentation, Residual


def shortest_path(residual: Residual, at_least: int) -> list[int] | None:
    """The path of fewest arrows with residual capacity at least `at_least` from the source to the
    sink, as the first-in first-out search finds it; `None` if there is none."""
    came_by: dict[int, int | None] = {residual.source: None}  # the arrow that labeled each
    queue = deque([residual.source])
    while queue:
        u = queue.popleft()
        for e in residual.out[u]:
            v = residual.head[e]
            if (residual.residual_capacity[e] >= at_least
                    and v not in came_by):
                came_by[v] = e
                if v == residual.sink:
                    return path_back(residual, came_by)
                queue.append(v)
    return None


def path_back(residual: Residual, came_by: dict[int, int | None]) -> list[int]:
    """The arrows that labeled the vertices from the source to the sink, source first."""
    path: list[int] = []
    v = residual.sink
    while (e := came_by[v]) is not None:
        path.append(e)
        v = residual.tail(e)
    path.reverse()
    return path


class EdmondsKarp:
    """One round, one path with the fewest arrows."""

    def start(self, residual: Residual) -> None:
        """Nothing to keep between rounds."""

    def round(self, residual: Residual) -> list[Augmentation]:
        """Send along the path of fewest arrows, or nothing if the sink is out of reach."""
        path = shortest_path(residual, 1)
        if path is None:
            return []
        return [(path, residual.augment(path))]
