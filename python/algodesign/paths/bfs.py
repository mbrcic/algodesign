# SPDX-License-Identifier: Apache-2.0
"""Breadth-first search: the fewest arrows from one start to every vertex.

Every arrow costs one. The search keeps a first-in first-out queue of vertices found but not yet
looked out from, and marks a vertex the moment it is found, by giving it a cost; a marked vertex
is never queued again. Taking the front vertex `u`, it walks `u`'s row in order (the Graphs
chapter's order: by neighbor, then id), and each unmarked neighbor gets cost `cost[u] + 1`, `u` as
its previous vertex, and a place at the back of the queue. Since the queue holds vertices in order
of cost, the first time a vertex is found is along a path of the fewest arrows (CLRS 4th ed., §20.2,
`BFS`).

Each vertex is queued at most once and each arrow walked at most once: linear in vertices plus
arrows. A start outside the graph raises `IndexError`.

The Rust differs here: its queue is the vector of vertices in the order found, read from a front
index, where this one is a `deque` of (vertex, cost) pairs.

No `check_valid`; the Lean `Valid` is `Bfs.Valid`. The Lean statements behind this module, in
`lean/AlgoDesign/Paths/Bfs.lean`: `valid_start`, `valid_step`, `bfs_reached`, `bfs_previous`,
`bfs_unreached`.
"""

from __future__ import annotations

from collections import deque

from algodesign.graphs import Digraph

from .distances import Distances


def bfs(g: Digraph, start: int) -> Distances:
    """The fewest arrows from `start` to each vertex, and the vertex each was found from."""
    if not 0 <= start < g.n:
        raise IndexError(f"start {start} out of range 0..{g.n}")
    cost: list[int | None] = [None] * g.n
    previous: list[int | None] = [None] * g.n
    cost[start] = 0
    queue = deque([(start, 0)])  # (vertex, its cost)
    while queue:
        u, du = queue.popleft()
        for w, _ in g.out[u]:
            if cost[w] is None:
                cost[w] = du + 1
                previous[w] = u
                queue.append((w, du + 1))
    return Distances(cost, previous)
