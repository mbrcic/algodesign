# SPDX-License-Identifier: Apache-2.0
"""Prim's method: the cheapest spanning forest, grown one tree at a time; Dijkstra's walk with the
key the link alone.

The skeleton is Dijkstra's: a binary heap (`heapq`) of entries, the smallest taken first, a vertex
already in a tree skipped when it comes off, a link pushed only when it is cheaper, by (cost, id),
than every link pushed so far towards its vertex, as Dijkstra pushes only a lower cost, and the row
of each vertex added walked in the Graphs chapter's order, by neighbor, then id. Only the key
changes: Dijkstra's is the cost so far plus the arrow, Prim's is the link's cost alone. An entry is
(link cost, link id, vertex), and Python compares the triples in that order, so equal costs go by
link id, the order Kruskal takes the links in. Then the two methods keep the same set of links.

The walk starts at vertex 0; when the heap runs empty it starts again from the lowest-numbered
vertex not yet in a tree, so a graph in several pieces gets one tree per piece. Any costs are
allowed. Jarník (1930) and Prim (1957); the method as Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, 4th ed., §21.2, `MST-PRIM`, p. 596, which lowers a key in place where
this walk pushes a new entry and skips the old one later.

Each link pushes at most one entry, so the work grows with the links times the logarithm of the
heap's size. A supporting method: it has no `check_valid`, and the Lean has no model of it.

The Rust differs here: it counts the entries it pushes in test builds, for the tests that hold the
push rule, where the tests here count them by wrapping `heapq.heappush`.
"""

from __future__ import annotations

import heapq

from .link_network import LinkNetwork


def prim(network: LinkNetwork) -> list[int]:
    """The link ids of a cheapest spanning forest, in the order added, each tree started at its
    lowest-numbered vertex and grown by the cheapest link that leaves the tree."""
    g, cost = network.g, network.cost
    in_tree = [False] * g.n
    best: list[tuple[int, int] | None] = [None] * g.n  # per vertex, the cheapest (cost, id) pushed
    added: list[int] = []
    queue: list[tuple[int, int, int]] = []

    def join(v: int) -> None:
        in_tree[v] = True
        for w, j in g.adj[v]:
            if in_tree[w]:
                continue
            old = best[w]
            if old is None or (cost[j], j) < old:
                best[w] = (cost[j], j)
                heapq.heappush(queue, (cost[j], j, w))

    for root in range(g.n):
        if in_tree[root]:
            continue
        join(root)
        while queue:
            _, i, v = heapq.heappop(queue)
            # an old entry: v joined a tree by a cheaper link
            if in_tree[v]:
                continue
            added.append(i)
            join(v)
    return added
