# SPDX-License-Identifier: Apache-2.0
"""A network: vertices `0 .. n-1`, arrows by id with a capacity each, a source and a sink.

Arrow `i` is `arrows[i] = (tail, head)` and may carry up to `capacity[i]`, an integer, zero or
more. Two arrows between the same two vertices, in the same or opposite directions, stay two
arrows, so a flow is told by arrow id. A loop is allowed and never carries anything: no augmenting
path passes a vertex twice.

A network that breaks one of these raises `ValueError` naming what broke: an arrow with an end
outside the vertices, a capacity list of the wrong length, a capacity below zero, a source or sink
outside the vertices, or the source equal to the sink.

The Rust differs here: its network wraps the Graphs chapter's `Digraph`, its capacities are
unsigned 64-bit (or 32-bit) integers, and it also refuses more than 2^31 - 1 arrows and capacities
leaving the source that add up past a 64-bit integer.

The Lean definitions behind this module, in `lean/AlgoDesign/Flows/MaxFlow/Spec.lean`: `Network`,
`Network.WellFormed`.
"""

from __future__ import annotations


class Network:
    """Vertices `0 .. n-1`, arrows `(tail, head)` by id, a capacity each, a source and a sink."""

    def __init__(
        self, n: int, arrows: list[tuple[int, int]], capacity: list[int], source: int, sink: int
    ) -> None:
        """Keep the network; raise `ValueError` if it is not one."""
        for i, (a, b) in enumerate(arrows):
            if not (0 <= a < n and 0 <= b < n):
                raise ValueError(f"arrow {i} = ({a}, {b}) has an end outside 0..{n}")
        if len(capacity) != len(arrows):
            raise ValueError(f"{len(capacity)} capacities for {len(arrows)} arrows")
        for i, c in enumerate(capacity):
            if c < 0:
                raise ValueError(f"arrow {i} has capacity {c}, below zero")
        for name, v in (("source", source), ("sink", sink)):
            if not 0 <= v < n:
                raise ValueError(f"the {name} {v} is outside 0..{n}")
        if source == sink:
            raise ValueError(f"vertex {source} is both the source and the sink")
        self.n = n
        self.arrows = list(arrows)  # by id
        self.capacity = list(capacity)  # by id
        self.source = source
        self.sink = sink
