# SPDX-License-Identifier: Apache-2.0
"""Kruskal's method: the cheapest spanning forest, taking the links cheapest first and keeping a
link unless it closes a cycle.

The link ids are sorted by cost; Python's `sorted` is stable, so equal costs go by id. The walk
takes the next link and gives its two ends to the Graphs chapter's `UnionFind.union`: the merge
answers yes when the ends were in two groups, and the link is kept; it answers no when they were
already in one, and the link would close a cycle. A loop is never kept, and of two links between the
same vertices the first in the order is. The walk stops once one group is left, since every later
link has both ends in it; on a graph in several pieces it goes through every link and gives one tree
per piece. Any costs are allowed, zero and negative too (Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, 4th ed., §21.2, `MST-KRUSKAL`, p. 594; that the kept links stay part
of some cheapest forest is the cut property with ties allowed, their Theorem 21.1, p. 587).

The sort costs m log m for m links; after it, each link given to the union-find costs nearly a
constant over the run.

`State` is the walk's state, as the Lean's `State`: the link ids still to take, the kept ones, the
ones given to the union-find, and the union-find. Its `step` is the Lean's `step`, and
`kruskal_with_tried` runs it. Its `is_part_of_cheapest` and `is_groups_are_kept_joins` are the
box's two invariants; the first needs the network's cheapest spanning forests, which only a slow
search knows, so the tests pass them in from `naive`. The other four pieces are not in the box.
Each piece answers on any state, broken or not: the groups are read off the stored links without
compressing them.

The Rust differs here: one walk serves both entry points, keeping a position in the sorted ids
instead of a list of the rest, and recording the links tried only when asked.

The Lean statements behind this module, in `lean/AlgoDesign/Paths/Kruskal/`: `contract`,
`valid_start`, `valid_step`, `kruskal_cheapestForest`, `run_cheapestForest`, `kruskal_cost`.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import pairwise

from algodesign.graphs import UnionFind

from .link_network import LinkNetwork

LABELS = (
    "invariant 1 (part_of_cheapest)",
    "invariant 2 (groups_are_kept_joins)",
    "not in the box (union_find_ready)",
    "not in the box (kept_closes_no_cycle)",
    "not in the box (rest_cheapest_first)",
    "not in the box (passed_are_joined)",
)


def kruskal(network: LinkNetwork) -> list[int]:
    """The link ids of a cheapest spanning forest, in the order kept: by cost, equal costs by
    id."""
    g, cost = network.g, network.cost
    groups = UnionFind(g.n)
    kept = []
    order = sorted(range(len(g.links)), key=lambda i: cost[i])
    for i in order:
        # one group left: every later link has both ends in it
        if groups.count() == 1:
            break
        if groups.union(*g.links[i]):
            kept.append(i)
    return kept


def kruskal_with_tried(network: LinkNetwork) -> tuple[list[int], list[int]]:
    """The kept link ids, and the link ids given to the union-find, in order; run through `State`,
    whose list of the links still to take makes each step cost up to the number of links."""
    state = State.start(network)
    while not state.done():
        state.step(network)
    return state.kept, state.tried


def _root(uf: UnionFind, i: int) -> int:
    """Where n steps up from `i` lead in the stored links, compressing nothing; an item past the
    links links to itself (Lean `root`)."""
    for _ in range(len(uf.parent)):
        i = uf.parent[i] if 0 <= i < len(uf.parent) else i
    return i


@dataclass
class State:
    """A state of Kruskal's walk: the link ids still to take, in order; the kept link ids, in the
    order kept; the link ids given to the union-find, in order; and the union-find.

    The checks are for tests on small networks."""

    rest: list[int]
    kept: list[int]
    tried: list[int]
    uf: UnionFind

    @staticmethod
    def start(network: LinkNetwork) -> State:
        """Nothing kept or tried, every vertex a group of its own, the links by cost."""
        order = sorted(range(len(network.g.links)), key=lambda i: network.cost[i])
        return State(order, [], [], UnionFind(network.g.n))

    def done(self) -> bool:
        """No link left to take, or one group left."""
        return not self.rest or self.uf.count() == 1

    def step(self, network: LinkNetwork) -> None:
        """Take the next link and merge its ends; keep it when the merge answers yes. With no link
        left, nothing changes."""
        if not self.rest:
            return
        i = self.rest.pop(0)
        if self.uf.union(*network.ends(i)):
            self.kept.append(i)
        self.tried.append(i)

    def is_part_of_cheapest(self, cheapest: list[list[int]]) -> bool:
        """Box invariant 1: the links kept so far are part of some minimum such set. `cheapest`
        holds the network's cheapest spanning forests (Lean `PartOfCheapest`)."""
        return any(all(i in forest for i in self.kept) for forest in cheapest)

    def is_groups_are_kept_joins(self, network: LinkNetwork) -> bool:
        """Box invariant 2: two vertices are in one union-find group exactly when the kept links
        join them (Lean `GroupsAreKeptJoins`)."""
        joined = network.groups(self.kept)
        n = network.g.n
        return all((_root(self.uf, u) == _root(self.uf, v)) == joined.joined(u, v)
                   for u in range(n) for v in range(n))

    def is_union_find_ready(self, network: LinkNetwork) -> bool:
        """Not in the box: the union-find is legal and well formed, over the graph's vertices
        (Lean `UnionFindReady`)."""
        return self.uf.is_valid() and len(self.uf.parent) == network.g.n

    def is_kept_closes_no_cycle(self, network: LinkNetwork) -> bool:
        """Not in the box: the kept links are links of the graph and close no cycle (Lean
        `KeptClosesNoCycle`)."""
        return (all(0 <= i < len(network.g.links) for i in self.kept)
                and network.closes_no_cycle(self.kept))

    def is_rest_cheapest_first(self, network: LinkNetwork) -> bool:
        """Not in the box: the links still to take are links of the graph, cheapest first (Lean
        `RestCheapestFirst`)."""
        return (all(0 <= i < len(network.g.links) for i in self.rest)
                and all(network.link_cost(i) <= network.link_cost(j)
                        for i, j in pairwise(self.rest)))

    def is_passed_are_joined(self, network: LinkNetwork) -> bool:
        """Not in the box: the kept links join the two ends of every link already taken, every link
        not among those still to take (Lean `PassedAreJoined`)."""
        joined = network.groups(self.kept)
        return all(i in self.rest or joined.joined(a, b)
                   for i, (a, b) in enumerate(network.g.links))

    def check_valid(self, network: LinkNetwork, cheapest: list[list[int]]) -> str | None:
        """The first piece of the Lean `Valid` and `WellFormed` the state breaks, or `None`.
        `cheapest` holds the network's cheapest spanning forests."""
        pieces = [
            self.is_part_of_cheapest(cheapest),
            self.is_groups_are_kept_joins(network),
            self.is_union_find_ready(network),
            self.is_kept_closes_no_cycle(network),
            self.is_rest_cheapest_first(network),
            self.is_passed_are_joined(network),
        ]
        return next((label for label, ok in zip(LABELS, pieces) if not ok), None)

    def is_valid(self, network: LinkNetwork, cheapest: list[list[int]]) -> bool:
        """The Lean `Valid` and `WellFormed`: their six pieces."""
        return self.check_valid(network, cheapest) is None
