# SPDX-License-Identifier: Apache-2.0
"""A link network: an undirected graph of the Graphs chapter and one integer cost per link.

The graph is a plain `Graph`, unchanged; the costs sit beside it, listed by link id, so `cost[i]`
is what link `i` costs. Two links between the same two vertices keep their own ids and may cost
differently, so a set of links is a list of link ids, not of vertex pairs. A cost may be any
integer, zero and negative too.

A set of links joins two vertices when a chain of its links leads from one to the other, each link
read either way. It closes no cycle when none of its links joins two vertices that the others
already join, so a loop, or a link listed twice, closes a cycle. A spanning forest is a set of the
graph's links that joins every two vertices the graph joins and closes no cycle. Whether links
join two vertices is asked of the Graphs chapter's union-find, with the links merged into it.

The checks read any list of ids, as the Lean does: an id past the links has the ends (0, 0) and
costs 0. A cost list whose length is not the number of links raises `ValueError`.

The Lean definitions behind this module, in `lean/AlgoDesign/Paths/LinkNetwork.lean`:
`LinkNetwork`, `LinkNetwork.Joins`, `LinkNetwork.total`, `LinkNetwork.ClosesNoCycle`,
`LinkNetwork.IsSpanningForest`.
"""

from __future__ import annotations

from algodesign.graphs import Graph, UnionFind


class LinkNetwork:
    """An undirected graph and the cost of each of its links, by link id."""

    def __init__(self, g: Graph, cost: list[int]) -> None:
        """Keep the graph and the costs; one cost per link."""
        if len(cost) != len(g.links):
            raise ValueError(f"{len(cost)} costs for {len(g.links)} links")
        self.g = g
        self.cost = list(cost)  # by link id

    def ends(self, i: int) -> tuple[int, int]:
        """The two ends of link `i`; (0, 0) past the links."""
        return self.g.links[i] if 0 <= i < len(self.g.links) else (0, 0)

    def link_cost(self, i: int) -> int:
        """The cost of link `i`; 0 past the links."""
        return self.cost[i] if 0 <= i < len(self.cost) else 0

    def groups(self, links: list[int]) -> UnionFind:
        """A union-find over the vertices with every one of `links` merged."""
        groups = UnionFind(self.g.n)
        for i in links:
            if 0 <= i < len(self.g.links):
                groups.union(*self.g.links[i])
        return groups

    def joins(self, links: list[int], u: int, v: int) -> bool:
        """Whether a chain of `links` leads from `u` to `v`; every vertex is joined to itself."""
        n = self.g.n
        return u == v or (0 <= u < n and 0 <= v < n and self.groups(links).joined(u, v))

    def total(self, links: list[int]) -> int:
        """The total cost of `links`, a link listed twice counted twice."""
        return sum(self.link_cost(i) for i in links)

    def joins_what_graph_joins(self, links: list[int]) -> bool:
        """Whether `links` join every two vertices the graph joins: the ends of every link."""
        groups = self.groups(links)
        return all(groups.joined(a, b) for a, b in self.g.links)

    def closes_no_cycle(self, links: list[int]) -> bool:
        """Whether no link of `links` joins two vertices the others already join."""
        return not any(self.joins(links[:k] + links[k + 1:], *self.ends(i))
                       for k, i in enumerate(links))

    def is_spanning_forest(self, links: list[int]) -> bool:
        """Whether `links` are links of the graph that join every two vertices the graph joins and
        close no cycle."""
        return (all(0 <= i < len(self.g.links) for i in links)
                and self.joins_what_graph_joins(links) and self.closes_no_cycle(links))
