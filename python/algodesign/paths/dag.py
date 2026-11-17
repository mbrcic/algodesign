# SPDX-License-Identifier: Apache-2.0
"""Cheapest paths in a graph with no cycle: each vertex's row tried once, in a topological order.

The order is the Graphs chapter's Kahn order (`topological_order`); on a graph with a cycle there is
none, and the answer is Kahn's `Stuck` set. The walk takes the vertices in that order. A vertex with
no known cost is passed without trying its row; for one with a known cost, every arrow out of it is
tried in its row's order: when the arrow's end has no known cost, or the arrow gives less, the end
gets the new cost and this vertex as its previous one. Every arrow into a vertex comes from one
taken before it, so its cost is final by the time it is taken (Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, 4th ed., §22.2, DAG-SHORTEST-PATHS, p. 617). Arrows may cost less than
nothing. Kahn's order and the walk each look at every vertex and every arrow once.

`State` is the walk's state, as the Lean's `State`: the vertices taken, in the order taken; the
vertices still to take; each vertex's known cost and previous vertex. Its `step` is the Lean's
`step`.

The Rust differs here: it has no `State`, and its walk is `dag_paths` alone.

The Lean statements behind this module, in `lean/AlgoDesign/Paths/DagOrder/`: `valid_start`,
`valid_step`, `dagPaths_reached`, `dagPaths_previous`, `dagPaths_unreached`, `dagPaths_stuck`,
`dagPaths_cost`.
"""

from __future__ import annotations

from dataclasses import dataclass

from algodesign.graphs import Stuck, topological_order

from .distances import Distances
from .network import Network


def dag_paths(network: Network, start: int) -> Distances | Stuck:
    """The cheapest cost from `start` to each vertex of a graph with no cycle, and the vertex each
    was last reached from; arrows may be negative. On a graph with a cycle, Kahn's set
    of the vertices that could not be placed."""
    g, cost = network.g, network.cost
    if not 0 <= start < g.n:
        raise IndexError(f"start {start} out of range 0..{g.n}")
    order = topological_order(g)
    if isinstance(order, Stuck):
        return order
    known: list[int | None] = [None] * g.n
    previous: list[int | None] = [None] * g.n
    known[start] = 0
    for u in order:
        du = known[u]
        # never reached: its arrows are not tried
        if du is None:
            continue
        for w, i in g.out[u]:
            if (kw := known[w]) is None or du + cost[i] < kw:
                known[w] = du + cost[i]
                previous[w] = u
    return Distances(known, previous)


@dataclass
class State:
    """A state of the walk: the vertices taken, in the order taken; the vertices still to take, in
    the order they will be taken; each vertex's known cost (`None` while no arrow has reached it)
    and previous vertex."""

    done: list[int]
    todo: list[int]
    known: list[int | None]
    previous: list[int | None]

    @staticmethod
    def start(network: Network, start: int, order: list[int]) -> State:
        """Nothing taken, `order` still to take; only the start known, at cost 0."""
        n = network.g.n
        if not 0 <= start < n:
            raise IndexError(f"start {start} out of range 0..{n}")
        known: list[int | None] = [None] * n
        known[start] = 0
        return State([], list(order), known, [None] * n)

    def step(self, network: Network) -> None:
        """Take the next vertex of the order and, if its cost is known, try every arrow out of it,
        in its row's order. With nothing left to take, the state is left as it is."""
        if not self.todo:
            return
        u = self.todo.pop(0)
        self.done.append(u)
        du = self.known[u]
        if du is None:
            return
        for w, i in network.g.out[u]:
            if (kw := self.known[w]) is None or du + network.cost[i] < kw:
                self.known[w] = du + network.cost[i]
                self.previous[w] = u
