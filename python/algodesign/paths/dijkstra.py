# SPDX-License-Identifier: Apache-2.0
"""Dijkstra's method: the cheapest path from one start to every vertex, when no arrow costs less
than nothing.

The walk settles one vertex at a time, always the unsettled vertex of smallest known cost, and
then tries every arrow out of it (Weiss, *Data Structures and Algorithm Analysis in C++*, 4th ed.,
§9.3.2, Fig. 9.31, p. 399; Kleinberg and Tardos, *Algorithm Design*, §4.4, p. 180). The queue is
a binary heap (`heapq`) of entries `(cost, vertex)`; Python compares the pairs by cost, then by
vertex id, which is the tie rule (Goldberg and Harrelson, SODA 2005: "break ties based on vertex
IDs"). An entry is never taken out when a vertex's cost drops: a new one is pushed, and the old
one stays until it comes off the queue and is skipped, because its vertex is settled by then.

A settled vertex is frozen: it is skipped as it comes off the queue again, and no arrow into it is
tried. With a negative arrow that is exactly what goes wrong: on the three-vertex map where
0 -> 1 costs 1, 0 -> 2 costs 2 and 2 -> 1 costs -2, vertex 1 is settled at cost 1 before the
cheaper path through 2 (cost 0) is seen. Nothing checks the costs; the box assumes them.

A previous vertex changes only when a known cost strictly drops. Each arrow is tried at most once
and each try pushes at most one entry, so the work grows with the arrows times the logarithm of
the queue's size.

`dijkstra` is the walk; `dijkstra_to` is the same walk stopped the moment the goal comes off the
queue (Hart, Nilsson and Raphael, 1968, p. 102), before the goal's own arrows are tried, so only
the costs of settled vertices are final in its answer. `dijkstra_with_settled` also gives the
vertices in the order they were settled.

`State` is the walk's state, as the Lean's `State`: the settled vertices in order, each vertex's
known cost and previous vertex, the queue as a list kept in order (the Lean's queue, where the
heap above keeps only its smallest entry in front), and how many entries it has received. Its
`step` is the Lean's `step`, and `dijkstra_with_settled` runs it. Its `is_settled_are_cheapest`
and `is_known_is_cheapest_through_settled` are the box's two invariants and need the true cheapest
costs, which only a slow search knows: the tests pass them in from `naive`. The other four pieces
are not in the box. Each piece answers on any state, broken or not.

The Rust differs here: it asserts in debug builds that no arrow is negative, and one
keyed walk serves its `dijkstra`, `dijkstra_to`, `dijkstra_with_settled` and A*, where the Python
writes the loop in each; its `dijkstra_with_settled` runs that heap walk, where the Python's runs
`State`.

The Lean statements behind this module, in `lean/AlgoDesign/Paths/Dijkstra/`: `contract`,
`valid_start`, `valid_step`, `dijkstra_reached`, `dijkstra_previous`, `dijkstra_unreached`,
`dijkstra_cost`, `pushed_final_le`.
"""

from __future__ import annotations

import heapq
from bisect import insort
from dataclasses import dataclass
from itertools import pairwise

from .distances import Distances
from .network import Network


def dijkstra(network: Network, start: int) -> Distances:
    """The cheapest cost from `start` to each vertex, and the vertex each was last reached from;
    correct when no arrow is negative."""
    g, cost = network.g, network.cost
    if not 0 <= start < g.n:
        raise IndexError(f"start {start} out of range 0..{g.n}")
    known: list[int | None] = [None] * g.n
    previous: list[int | None] = [None] * g.n
    settled = [False] * g.n
    known[start] = 0
    queue = [(0, start)]
    while queue:
        du, u = heapq.heappop(queue)
        # an old entry: u was settled at a smaller cost
        if settled[u]:
            continue
        settled[u] = True
        for w, i in g.out[u]:
            if settled[w]:
                continue
            dw = du + cost[i]
            if (kw := known[w]) is None or dw < kw:
                known[w] = dw
                previous[w] = u
                heapq.heappush(queue, (dw, w))
    return Distances(known, previous)


def dijkstra_to(network: Network, start: int, goal: int) -> Distances:
    """The walk of `dijkstra`, stopped as soon as `goal` is settled: its cost is final, and so is
    every vertex settled before it; the others' costs are only what the walk had found."""
    g, cost = network.g, network.cost
    if not 0 <= start < g.n:
        raise IndexError(f"start {start} out of range 0..{g.n}")
    if not 0 <= goal < g.n:
        raise IndexError(f"goal {goal} out of range 0..{g.n}")
    known: list[int | None] = [None] * g.n
    previous: list[int | None] = [None] * g.n
    settled = [False] * g.n
    known[start] = 0
    queue = [(0, start)]
    while queue:
        du, u = heapq.heappop(queue)
        if settled[u]:
            continue
        settled[u] = True
        if u == goal:
            break
        for w, i in g.out[u]:
            if settled[w]:
                continue
            dw = du + cost[i]
            if (kw := known[w]) is None or dw < kw:
                known[w] = dw
                previous[w] = u
                heapq.heappush(queue, (dw, w))
    return Distances(known, previous)


def dijkstra_with_settled(network: Network, start: int) -> tuple[Distances, list[int]]:
    """The answer of `dijkstra`, and the vertices in the order they were settled; run through
    `State`, whose list queue and settled list make each step cost up to the number of vertices."""
    state = State.start(network, start)
    while state.queue:
        state.step(network)
    return Distances(state.known, state.previous), state.settled


@dataclass
class State:
    """A state of Dijkstra's walk: the settled vertices, in the order they were settled; each
    vertex's known cost (`None` while no arrow has reached it) and previous vertex; the queue's
    entries (cost, vertex), smallest first; and how many entries the queue has received. A vertex
    past the lists has no known cost and no previous vertex.

    The checks are for tests on small networks."""

    settled: list[int]
    known: list[int | None]
    previous: list[int | None]
    queue: list[tuple[int, int]]
    pushed: int

    @staticmethod
    def start(network: Network, start: int) -> State:
        """Nothing settled; only the start known, at cost 0, and queued."""
        n = network.g.n
        if not 0 <= start < n:
            raise IndexError(f"start {start} out of range 0..{n}")
        known: list[int | None] = [None] * n
        known[start] = 0
        return State([], known, [None] * n, [(0, start)], 1)

    def step(self, network: Network) -> None:
        """Take the smallest entry off the queue; skip its vertex if it is settled, else settle it
        and try every arrow out of it, in its row's order. An empty queue is left as it is."""
        if not self.queue:
            return
        du, u = self.queue.pop(0)
        if u in self.settled:
            return
        self.settled.append(u)
        for w, i in network.g.out[u]:
            if w in self.settled:
                continue
            dw = du + network.cost[i]
            if (kw := self.known[w]) is None or dw < kw:
                self.known[w] = dw
                self.previous[w] = u
                insort(self.queue, (dw, w))
                self.pushed += 1

    def _known(self, v: int) -> int | None:
        return self.known[v] if 0 <= v < len(self.known) else None

    def _previous(self, v: int) -> int | None:
        return self.previous[v] if 0 <= v < len(self.previous) else None

    def is_settled_are_cheapest(self, cheapest: list[int | None]) -> bool:
        """Box invariant 1: every settled vertex's cost is its cheapest, and a settled vertex is
        never settled again. `cheapest[v]` is the true cheapest cost from the start to `v`
        (Lean `SettledAreCheapest`)."""
        return len(set(self.settled)) == len(self.settled) and all(
            0 <= v < len(cheapest) and self._known(v) is not None and self._known(v) == cheapest[v]
            for v in self.settled)

    def is_known_is_cheapest_through_settled(self, network: Network,
                                             through: list[int | None]) -> bool:
        """Box invariant 2: every unsettled vertex's known cost is the cheapest over paths on which
        every earlier vertex is settled. `through[v]` is that cheapest cost, `None` when no such
        path reaches `v` (Lean `KnownIsCheapestThroughSettled`)."""
        return all(v < len(through) and self._known(v) == through[v]
                   for v in range(network.g.n) if v not in self.settled)

    def is_start_settled_first(self, start: int) -> bool:
        """Not in the box: once a vertex is settled, the start is the first (Lean
        `StartSettledFirst`)."""
        return not self.settled or self.settled[0] == start

    def is_settled_rows_tried(self, network: Network) -> bool:
        """Not in the box: every arrow from a settled vertex to an unsettled one has been tried, so
        the unsettled vertex's known cost is at most the settled one's plus the arrow's (Lean
        `SettledRowsTried`)."""
        g, cost = network.g, network.cost
        for x in self.settled:
            dx = self._known(x)
            if not 0 <= x < g.n or dx is None:
                continue
            for w, i in g.out[x]:
                if w not in self.settled and ((kw := self._known(w)) is None or kw > dx + cost[i]):
                    return False
        return True

    def is_queue_holds_known(self, network: Network) -> bool:
        """Not in the box: the queue is in order, holds each unsettled vertex's known cost, and each
        entry is a vertex of the graph, not below its known cost (Lean `QueueHoldsKnown`)."""
        return (self.queue == sorted(self.queue)
                and all((d, v) in self.queue for v in range(network.g.n)
                        if v not in self.settled and (d := self._known(v)) is not None)
                and all(0 <= v < network.g.n and (kv := self._known(v)) is not None and kv <= d
                        for d, v in self.queue))

    def _back(self, start: int, v: int, n: int) -> list[int] | None:
        """The vertices from `start` to `v` that following the previous vertices back from `v`
        gives, start first; `None` if the walk back leaves the graph, stops short of the start, or
        passes a vertex twice."""
        path = [v]
        while path[-1] != start:
            u = self._previous(path[-1])
            if u is None or not 0 <= u < n or u in path:
                return None
            path.append(u)
        path.reverse()
        return path

    def is_previous_leads_back(self, network: Network, start: int) -> bool:
        """Not in the box: following the previous vertices back from a vertex with a known cost
        gives a path from the start of exactly that cost, every earlier vertex of it settled; the
        start has no previous vertex (Lean `PreviousLeadsBack`)."""
        g, cost = network.g, network.cost
        if self._previous(start) is not None:
            return False
        for v in range(g.n):
            d = self._known(v)
            if d is None:
                continue
            path = self._back(start, v, g.n)
            if path is None or not all(x in self.settled for x in path[:-1]):
                return False
            # Two arrows between the same vertices may cost differently: some choice of arrow at
            # each step must give `d`.
            sums = {0}
            for a, b in pairwise(path):
                sums = {c + cost[i] for c in sums for w, i in g.out[a] if w == b}
            if d not in sums:
                return False
        return True

    def check_valid(self, network: Network, start: int, cheapest: list[int | None],
                    through: list[int | None]) -> str | None:
        """The first piece of the Lean `Valid` and `WellFormed` the state breaks, or `None`.
        `cheapest` and `through` are the true cheapest costs, over all paths and over paths
        through settled vertices."""
        if not self.is_settled_are_cheapest(cheapest):
            return "invariant 1 (settled_are_cheapest)"
        if not self.is_known_is_cheapest_through_settled(network, through):
            return "invariant 2 (known_is_cheapest_through_settled)"
        if not self.is_start_settled_first(start):
            return "not in the box (start_settled_first)"
        if not self.is_settled_rows_tried(network):
            return "not in the box (settled_rows_tried)"
        if not self.is_queue_holds_known(network):
            return "not in the box (queue_holds_known)"
        if not self.is_previous_leads_back(network, start):
            return "not in the box (previous_leads_back)"
        return None

    def is_valid(self, network: Network, start: int, cheapest: list[int | None],
                 through: list[int | None]) -> bool:
        """The Lean `Valid` and `WellFormed`: their six pieces."""
        return self.check_valid(network, start, cheapest, through) is None
