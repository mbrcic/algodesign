# SPDX-License-Identifier: Apache-2.0
"""The residual graph of a flow: every arrow paired with its reverse arrow.

Arrow `i` gives two arrows of the residual graph, side by side: `2i`, along the arrow from its tail
to its head, with its residual capacity, what it has left, and `2i + 1`, the reverse arrow from its
head to its tail, with the amount it carries, which can be taken back. So `e ^ 1` is the reverse
arrow of `e`, and the two residual capacities of a pair always add up to the arrow's capacity. Only
the residual capacities are kept; the flow on arrow `i` is the residual capacity of `2i + 1` (Ahuja,
Magnanti and Orlin, *Network Flows*, §2.4).

`out[v]` lists the arrows of the residual graph leaving `v` in input order: for each arrow id
in turn, `2i` at its tail and `2i + 1` at its head. Every search of the topic reads a row in this
order, and the first vertex labeled keeps its label, so the Python and the Rust choose the same
paths.

`augment(path)` sends a path's bottleneck, the smallest residual capacity on it, along every arrow
of it. `reached()` is the set of vertices arrows with residual capacity lead to from the source: the
source's side of the cut.

The Rust differs here: its rows are one packed array, and a rule there sends one arrow at a time
(`Residual::send`), where `augment` here sends a whole path.

The Lean definitions behind this module, in `lean/AlgoDesign/Flows/`: `ResidualArrow` (`2i` is
`along i`, `2i + 1` is `back i`), `ResidualArrow.residualCapacity`, `sendOne`, `Augmentation.apply`,
`reached`.
"""

from __future__ import annotations

from collections import deque

from .network import Network

# One added path: its residual arrows from the source, and the amount sent along it.
Augmentation = tuple[list[int], int]


class Residual:
    """The residual graph of a flow: each residual arrow's head and residual capacity, each vertex's
    row."""

    def __init__(self, network: Network) -> None:
        """The residual graph of the zero flow: each arrow's residual capacity is its capacity,
        nothing back."""
        self.n = network.n
        self.source = network.source
        self.sink = network.sink
        self.head: list[int] = []
        self.residual_capacity: list[int] = []
        self.out: list[list[int]] = [[] for _ in range(network.n)]
        for i, (tail, head) in enumerate(network.arrows):
            self.head += [head, tail]
            self.residual_capacity += [network.capacity[i], 0]
            self.out[tail].append(2 * i)
            self.out[head].append(2 * i + 1)

    def tail(self, e: int) -> int:
        """The vertex residual arrow `e` leaves: where its reverse arrow points."""
        return self.head[e ^ 1]

    def send(self, e: int, amount: int) -> None:
        """Send `amount` along residual arrow `e`: its residual capacity shrinks, its reverse
        arrow's grows."""
        assert amount <= self.residual_capacity[e], (
            f"sending {amount} along arrow {e} with residual capacity {self.residual_capacity[e]}")
        self.residual_capacity[e] -= amount
        self.residual_capacity[e ^ 1] += amount

    def augment(self, path: list[int]) -> int:
        """Send the path's bottleneck along every arrow of it; return the amount sent."""
        amount = min(self.residual_capacity[e] for e in path)
        for e in path:
            self.send(e, amount)
        return amount

    def flow(self) -> list[int]:
        """The amount on each arrow of the network, by id: the residual capacity of its reverse
        arrow."""
        return self.residual_capacity[1::2]

    def reached(self) -> list[bool]:
        """For each vertex, whether arrows with residual capacity lead to it from the source."""
        seen = [False] * self.n
        seen[self.source] = True
        queue = deque([self.source])
        while queue:
            u = queue.popleft()
            for e in self.out[u]:
                v = self.head[e]
                if self.residual_capacity[e] > 0 and not seen[v]:
                    seen[v] = True
                    queue.append(v)
        return seen
