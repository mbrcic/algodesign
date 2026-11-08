# SPDX-License-Identifier: Apache-2.0
"""Slow references that are correct by inspection, for the tests to compare the real methods
against: the cheapest cost to every vertex, found by trying every path, and the best packing of a
box, found by trying every set of items. The checks of `dijkstra.State` take their true answers
from here; the methods themselves never do.

A path passes no vertex twice, and two arrows between the same vertices are two different paths.
The number of paths grows exponentially, so these are for networks of a handful of vertices.

For link networks, every cheapest spanning forest, found by trying every set of links: the first
check of `kruskal.State` takes them from here. A dozen links make 4096 sets.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from itertools import combinations, pairwise

from .link_network import LinkNetwork
from .network import Network


def paths_from(network: Network, start: int) -> Iterator[tuple[list[int], int]]:
    """Every path from `start`, as the vertices it passes and its cost; the empty path first."""

    def extend(vertices: list[int], cost: int) -> Iterator[tuple[list[int], int]]:
        yield vertices, cost
        for w, i in network.g.out[vertices[-1]]:
            if w not in vertices:
                yield from extend(vertices + [w], cost + network.cost[i])

    yield from extend([start], 0)


def cheapest_through(network: Network, start: int, settled: Iterable[int]) -> list[int | None]:
    """For each vertex, the cheapest cost over the paths from `start` to it on which every vertex
    but the last is in `settled`; `None` when there is no such path."""
    allowed = set(settled)
    best: list[int | None] = [None] * network.g.n
    for vertices, cost in paths_from(network, start):
        v = vertices[-1]
        if all(x in allowed for x in vertices[:-1]) and ((b := best[v]) is None or cost < b):
            best[v] = cost
    return best


def cheapest(network: Network, start: int) -> list[int | None]:
    """For each vertex, the cost of the cheapest path from `start` to it; `None` when no path
    leads there."""
    return cheapest_through(network, start, range(network.g.n))


def cheapest_to(network: Network, goal: int) -> list[int | None]:
    """For each vertex, the cost of the cheapest path from it to `goal`; `None` when no path leads
    there."""
    return [cheapest(network, v)[goal] for v in range(network.g.n)]


# For Bellman-Ford: the cheapest over paths of at most so many arrows, by a plain count over the
# number of arrows; every cost of such a path; and the negative cycles, by trying every cycle.


def cheapest_walks(network: Network, start: int, k: int) -> list[list[int | None]]:
    """For each number of arrows `j` from 0 to `k`, the cheapest cost from `start` to each vertex
    over the paths of at most `j` arrows; `None` when no such path leads there. A path may pass a
    vertex more than once: a path of at most `j + 1` arrows is one of at most `j`, or one of at
    most `j` and one arrow more."""
    first: list[int | None] = [None] * network.g.n
    first[start] = 0
    rows = [first]
    for _ in range(k):
        last = rows[-1]
        row = list(last)
        for i, (u, w) in enumerate(network.g.arrows):
            if (du := last[u]) is not None and ((b := row[w]) is None or du + network.cost[i] < b):
                row[w] = du + network.cost[i]
        rows.append(row)
    return rows


def walk_costs(network: Network, start: int, k: int) -> list[set[int]]:
    """For each vertex, every cost of a path from `start` to it of at most `k` arrows."""
    exactly: list[set[int]] = [set() for _ in range(network.g.n)]
    exactly[start].add(0)
    every = [set(costs) for costs in exactly]
    for _ in range(k):
        longer: list[set[int]] = [set() for _ in range(network.g.n)]
        for i, (u, w) in enumerate(network.g.arrows):
            longer[w] |= {c + network.cost[i] for c in exactly[u]}
        for v, costs in enumerate(longer):
            every[v] |= costs
        exactly = longer
    return every


def walk_arrows_after(network: Network, tried: int) -> int:
    """How many arrows the paths `walk_costs` takes must have room for, for a state that has
    tried `tried` arrows: each try grows a path by at most one arrow, so `tried`; and `n` more,
    so that every path counts too."""
    return tried + network.g.n


def reached_from(network: Network, start: int) -> set[int]:
    """The vertices `start` reaches, itself included."""
    return {vertices[-1] for vertices, _ in paths_from(network, start)}


def reaches_cycle_below_zero(network: Network, start: int) -> bool:
    """Whether `start` reaches a negative cycle, by trying every cycle: from
    each vertex the start reaches, every path and an arrow back to its first vertex. A loop is a
    cycle of one arrow."""
    return any(w == v and cost + network.cost[i] < 0
               for v in reached_from(network, start)
               for vertices, cost in paths_from(network, v)
               for w, i in network.g.out[vertices[-1]])


def is_cycle_below_zero(network: Network, start: int, vertices: list[int]) -> bool:
    """Whether `vertices` is a negative cycle that `start` reaches: at least one arrow, the
    first vertex again last and no other vertex twice, an arrow from each vertex to the next, the
    cheapest such arrows with a negative total, and the first vertex reached from `start`."""
    g = network.g
    if (len(vertices) < 2 or vertices[0] != vertices[-1]
            or len(set(vertices[:-1])) != len(vertices) - 1
            or not all(0 <= v < g.n for v in vertices)):
        return False
    total = 0
    for a, b in pairwise(vertices):
        arrows = [network.cost[i] for w, i in g.out[a] if w == b]
        if not arrows:
            return False
        total += min(arrows)
    return total < 0 and vertices[0] in reached_from(network, start)

def cheapest_forests(network: LinkNetwork) -> list[list[int]]:
    """Every cheapest spanning forest, by trying every set of links: each a list of link ids in
    increasing order. A spanning forest always exists, so the list is never empty."""
    ids = range(len(network.g.links))
    forests = [list(links) for k in range(len(ids) + 1) for links in combinations(ids, k)
               if network.is_spanning_forest(list(links))]
    least = min(network.total(forest) for forest in forests)
    return [forest for forest in forests if network.total(forest) == least]

def best_value(weights: list[int], values: list[int], capacity: int) -> int:
    """The largest value of a set of items that fits in a box of `capacity`, by trying every set;
    the empty set fits and is worth 0."""
    n = len(weights)
    return max(sum(values[k] for k in items)
               for size in range(n + 1) for items in combinations(range(n), size)
               if sum(weights[k] for k in items) <= capacity)


def longest_gains(weights: list[int], values: list[int], capacity: int) -> list[list[int | None]]:
    """For each state `(i, w)` of the knapsack's graph, `i <= n` and `w <= capacity`, the largest
    gain of a path into it from `(0, 0)`: the most value of a set of the first `i` items weighing
    exactly `w`, by trying every set; `None` where no set weighs `w`."""
    table: list[list[int | None]] = []
    for i in range(len(weights) + 1):
        layer: list[int | None] = [None] * (capacity + 1)
        for size in range(i + 1):
            for items in combinations(range(i), size):
                w = sum(weights[k] for k in items)
                value = sum(values[k] for k in items)
                if w <= capacity and ((b := layer[w]) is None or b < value):
                    layer[w] = value
        table.append(layer)
    return table
