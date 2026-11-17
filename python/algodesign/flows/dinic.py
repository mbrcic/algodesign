# SPDX-License-Identifier: Apache-2.0
"""Dinic's path rule in the Even–Itai form, the library's default: each round sends a blocking
flow through the layers of one search.

A first-in first-out search from the source over the arrows with residual capacity, each
row in input order and stopped as soon as the sink is labeled, gives each vertex it labels a layer,
its distance from the source. The round keeps the unsaturated arrows that go exactly one layer
deeper. Then one depth-first walk over the kept arrows, each vertex with a pointer to its current
arrow, starting at the first of its row. Standing at a vertex, the walk looks at its current arrow:
kept, it moves along it; not, it moves the pointer on. A vertex whose pointer has run past
its row, or a vertex on the sink's layer other than the sink, is a dead end: the walk steps back
along the last arrow and moves that arrow's tail's pointer past it. At the sink it sends the path's
bottleneck and starts again from the source, the pointers kept. The round ends when the source is
a dead end; a round whose search misses the sink sends nothing (Dinic, 1970, in the form of Even
and Itai: Even, *Graph Algorithms*, 1979; Dinitz, "Dinitz' algorithm: the original version and
Even's version", 2006; Ahuja, Magnanti and Orlin, *Network Flows*, pp. 216 and 222).

`sweep_steps` holds, for each round that sent something, how many steps its walk took: one per
move along an arrow, per pointer moved on, per dead end, and per path sent, and one more for the
last step, which finds the source a dead end and ends the round. Starting again from the source is
no step; its moves along arrows are counted again.

There are at most `n` rounds for `n` vertices, since the sink's layer grows every round, and each
walk takes `O(n m)` for `m` arrows.

The Rust differs here: its walk keeps its pointers, layers and path in arrays from round to round,
and counts its steps only in test builds.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/MaxFlow/Dinic.lean`: the rule's
promise, `dinic_promise`; at most n rounds, `dinic_rounds`; at most 2m paths a round,
`dinic_paths_per_round`. The walk-step count is the Lean's dinicSweepSteps.
"""

from __future__ import annotations

from collections import deque

from .residual import Augmentation, Residual


def layers(residual: Residual, at_least: int = 1) -> dict[int, int]:
    """Each labeled vertex's distance from the source over arrows with residual capacity at least
    `at_least`, by a first-in first-out search stopped as soon as the sink is labeled."""
    layer = {residual.source: 0}
    queue = deque([residual.source])
    while queue:
        u = queue.popleft()
        for e in residual.out[u]:
            v = residual.head[e]
            if residual.residual_capacity[e] >= at_least and v not in layer:
                layer[v] = layer[u] + 1
                if v == residual.sink:
                    return layer
                queue.append(v)
    return layer


class Dinic:
    """One round: the layers, then a blocking flow through them, by one walk."""

    def __init__(self) -> None:
        """No round run yet."""
        self.sweep_steps: list[int] = []

    def start(self, residual: Residual) -> None:
        """Forget the rounds of an earlier network."""
        self.sweep_steps = []

    def round(self, residual: Residual, at_least: int = 1) -> list[Augmentation]:
        """One round: the layers, then one walk sending every path it finds, over the arrows with
        residual capacity at least `at_least` (any residual capacity, by default)."""
        layer = layers(residual, at_least)
        s, t = residual.source, residual.sink
        if t not in layer:
            return []
        current = [0] * residual.n  # each vertex's current arrow, as a place in its row
        sent: list[Augmentation] = []
        steps = 0
        path: list[int] = []
        u = s
        while True:
            if u == t:
                sent.append((path, residual.augment(path)))
                path, u = [], s  # start again from the source
            elif layer[u] < layer[t] and current[u] < len(residual.out[u]):
                e = residual.out[u][current[u]]
                v = residual.head[e]
                if residual.residual_capacity[e] >= at_least and layer.get(v) == layer[u] + 1:
                    path.append(e)  # move along a kept arrow
                    u = v
                else:
                    current[u] += 1  # move the pointer on
            elif path:
                e = path.pop()  # a dead end: step back, past the arrow into it
                u = residual.tail(e)
                current[u] += 1
            else:
                steps += 1  # the source is a dead end: this last step ends the round
                break
            steps += 1
        self.sweep_steps.append(steps)
        return sent
