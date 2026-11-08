# SPDX-License-Identifier: Apache-2.0
"""A network: a directed graph of the Graphs chapter and one integer cost per arrow.

The graph is a plain `Digraph`, unchanged; the costs sit beside it, listed by arrow id, so
`cost[i]` is what arrow `i` costs. Two arrows between the same two vertices keep their own ids
and may cost differently. A cost may be any integer, negative too: a method that needs every
arrow to cost at least zero says so, and does not check it.

A cost list whose length is not the number of arrows raises `ValueError`.

The Lean definitions behind this module, in `lean/AlgoDesign/Paths/Network.lean`: `Network`,
`Network.WellFormed`, `Network.NoArrowBelowZero`.
"""

from __future__ import annotations

from algodesign.graphs import Digraph


class Network:
    """A directed graph and the cost of each of its arrows, by arrow id."""

    def __init__(self, g: Digraph, cost: list[int]) -> None:
        """Keep the graph and the costs; one cost per arrow."""
        if len(cost) != len(g.arrows):
            raise ValueError(f"{len(cost)} costs for {len(g.arrows)} arrows")
        self.g = g
        self.cost = list(cost)  # by arrow id
