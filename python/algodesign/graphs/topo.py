# SPDX-License-Identifier: Apache-2.0
"""Topological order: put the vertices of a directed graph in a line with every arrow pointing
forward, or say why that cannot be done.

`topological_order` is Kahn's method with a first-in first-out queue, as Weiss prints it (*Data
Structures and Algorithm Analysis in C++*, 4th ed., §9.2, Fig. 9.7): count the arrows entering
each vertex, queue every vertex whose count is 0 (scanning vertices 0 upward), then repeatedly take
the front vertex, append it to the order, and walk its row, lowering each neighbour's count and
queueing the neighbour when its count reaches 0. A doubled arrow counts twice and a loop once on
its own vertex, so a vertex with a loop waits on itself. When vertices are left over, the answer is
`Stuck`: every vertex not placed, in increasing order (Ahuja, Magnanti and Orlin, *Network Flows*,
pp. 77-78). Each of them has an arrow into it from one of them, possibly itself, so no order exists.

`dfs_order` is the depth-first order (CLRS 4th ed., §20.4): the vertices in reverse finishing
order. The walk keeps its path as explicit frames `[vertex, next position in its row]`, as in
Tarjan and Zwick's Implementation V (2024, §6.1); a vertex is marked when its frame is pushed, and
the top frame advances one arrow at a time. An arrow to a vertex not yet entered pushes that vertex;
an arrow to a vertex on the path closes a cycle, and the answer is `Cycle`: the vertices w, ..., v,
w from the path, w being the arrow's target and v the vertex it leaves (a loop at v gives v, v); an
arrow to a finished vertex is skipped.

Both methods return their answer rather than raise it: a graph with a cycle is an input like any
other.

`KahnState` is a state of Kahn's walk: what is placed, each vertex's count, and the queue. Its
`is_placed_after_waits`, `is_counts_unplaced_waits` and `is_ready_is_zero` are the Lean `Valid`'s
three pieces (`TopoOrder.Valid`); each answers on any state, broken or not.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .digraph import Digraph


@dataclass(frozen=True)
class Stuck:
    """The vertices Kahn's method could not place, in increasing order."""

    vertices: list[int]


@dataclass(frozen=True)
class Cycle:
    """A cycle w, ..., v, w: each vertex has an arrow to the next."""

    vertices: list[int]


def topological_order(g: Digraph) -> list[int] | Stuck:
    """Kahn's order of the vertices, or the vertices that can never be placed. Linear in vertices
    plus arrows: each vertex is queued once and each arrow walked once."""
    waiting = [len(g.into[v]) for v in range(g.n)]  # arrows entering v from vertices not yet placed
    ready = deque(v for v in range(g.n) if waiting[v] == 0)
    order: list[int] = []
    while ready:
        v = ready.popleft()
        order.append(v)
        for w, _ in g.out[v]:
            waiting[w] -= 1
            if waiting[w] == 0:
                ready.append(w)
    if len(order) == g.n:
        return order
    placed = set(order)
    return Stuck([v for v in range(g.n) if v not in placed])


@dataclass
class KahnState:
    """A state of Kahn's walk: the vertices placed so far, in order; for each vertex, how many
    arrows into it come from vertices not yet placed; and the ready vertices, front first. A vertex
    past the counts has count 0.

    The checks are for tests on small graphs: each costs about vertices times arrows."""

    placed: list[int]
    count: list[int]
    queue: list[int]

    def _count(self, v: int) -> int:
        return self.count[v] if v < len(self.count) else 0

    def is_placed_after_waits(self, g: Digraph) -> bool:
        """Box invariant 1: each placed vertex comes after everything it waits for. Each placed
        vertex is a vertex of the graph, placed once, and every arrow into it comes from a vertex
        placed earlier (Lean `PlacedAfterWaits`)."""
        placed = self.placed
        return (len(set(placed)) == len(placed) and all(0 <= v < g.n for v in placed)
                and all(u in placed[:placed.index(v)] for u, v in g.arrows if v in placed))

    def is_counts_unplaced_waits(self, g: Digraph) -> bool:
        """Box invariant 2: each unplaced vertex counts the unplaced vertices it still waits for,
        counting arrows, so a doubled arrow counts twice (Lean `CountsUnplacedWaits`)."""
        return all(self._count(v) == sum(1 for u, w in g.arrows if w == v and u not in self.placed)
                   for v in range(g.n) if v not in self.placed)

    def is_ready_is_zero(self, g: Digraph) -> bool:
        """Box invariant 3: the ready list holds exactly the unplaced vertices whose count is zero,
        each queued once (Lean `ReadyIsZero`)."""
        ready = [v for v in range(g.n) if v not in self.placed and self._count(v) == 0]
        return len(set(self.queue)) == len(self.queue) and sorted(self.queue) == ready

    def check_valid(self, g: Digraph) -> str | None:
        """The first piece of the Lean `Valid` the state breaks, or `None`."""
        if not self.is_placed_after_waits(g):
            return "invariant 1 (placed_after_waits)"
        if not self.is_counts_unplaced_waits(g):
            return "invariant 2 (counts_unplaced_waits)"
        if not self.is_ready_is_zero(g):
            return "invariant 3 (ready_is_zero)"
        return None

    def is_valid(self, g: Digraph) -> bool:
        """The Lean `Valid`: its three pieces."""
        return self.check_valid(g) is None


NEW, ON_PATH, DONE = 0, 1, 2


def dfs_order(g: Digraph) -> list[int] | Cycle:
    """The vertices in reverse finishing order of a depth-first walk, or the first cycle it meets.
    Linear in vertices plus arrows."""
    state = [NEW] * g.n
    finished: list[int] = []
    for root in range(g.n):
        if state[root] != NEW:
            continue
        state[root] = ON_PATH
        path = [[root, 0]]  # frames [vertex, next position in its row]
        while path:
            frame = path[-1]
            v, i = frame
            if i == len(g.out[v]):  # every arrow of v walked: v finishes
                path.pop()
                state[v] = DONE
                finished.append(v)
                continue
            frame[1] = i + 1
            w, _ = g.out[v][i]
            if state[w] == NEW:
                state[w] = ON_PATH
                path.append([w, 0])
            elif state[w] == ON_PATH:  # v -> w closes a cycle along the path
                vertices = [vertex for vertex, _ in path]
                return Cycle(vertices[vertices.index(w):] + [w])
    finished.reverse()
    return finished
