# SPDX-License-Identifier: Apache-2.0
"""HNSW, the hierarchical navigable small world graph (Malkov and Yashunin 2020, Algorithms 1, 2, 4
and 5).

Every point is a node with a random **level**, `floor(-ln(u) * m_L)` with `m_L = 1/ln M`, its top
layer, so few nodes reach the upper layers. On every layer up to its level, a node keeps a few
neighbors: at most `M` above layer 0 and `M0 = 2M` on layer 0. A search walks greedily down the
upper layers, runs a beam of width `ef` on layer 0, and ends with `finish`: the beam sorted by
exact distance, `k` kept.

Neighbors are picked by Algorithm 4's heuristic, with both its options off: scan the candidates
nearest first, and skip one if a neighbor already picked is *strictly* nearer to it than the base
is; a tie keeps it, as hnswlib does. The graph keeps the Lean `HNSW.Valid`, box invariant 1,
`is_degree_bounded`, and box invariant 3, `is_nested_layers`, and `HNSW.WellFormed`, not in the
box, `is_no_self_links`, `is_no_repeated_links`, `is_entry_on_top` and `is_one_node_per_point`.
Every
picking keeps box invariant 2, `is_picks_diverse`.

**The flat graph** is this code with every node at level 0 (`flat=True`), entered at node 0.
Distances tie-break by id, and levels come from the shared generator, so a seed draws the same
levels as the Rust; the links match it too unless two distances differ only in their last bits
(the Rust sums distances in a different order). No search guarantee is claimed: recall is measured
instead.

The Rust differs here: `u32` ids and one flat coordinate vector, and distances summed in another
order.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/GraphIndex/` (specification:
`GraphIndex/Spec.lean`): `picksDiverse_selectNeighbors`, `selectNeighbors_diverse`,
`selectNeighbors_length_le`, `selectNeighbors_subset`, `selectNeighbors_head`, `greedyStep_le`,
`promise_finish`, `valid_insert`, `valid_build`.
"""

from __future__ import annotations

import heapq
import math
from collections.abc import Callable, Sequence

from ._rng import SplitMix64
from .point import check_query, copy_points, sq_dist

Found = list[tuple[float, int]]
"""Nodes as `(squared distance, id)`, nearest first."""


def select_neighbors(
    points: Sequence[Sequence[float]], base: Sequence[float], candidates: Found, m: int
) -> list[int]:
    """Algorithm 4, with its two options (extendCandidates, keepPrunedConnections) off, as
    hnswlib runs it: up to `m` of the `candidates` (nearest first), each kept unless a neighbor
    already kept is strictly nearer to it than `base` is."""
    kept: list[int] = []
    for _, c in candidates:
        if len(kept) >= m:
            break
        to_base = sq_dist(points[c], base)
        if all(to_base <= sq_dist(points[c], points[k]) for k in kept):
            kept.append(c)
    return kept


def is_picks_diverse(
    points: Sequence[Sequence[float]],
    base: Sequence[float],
    candidates: Sequence[int],
    picked: Sequence[int],
    m: int,
) -> bool:
    """Box invariant 2: a point picks its neighbors nearest first, skipping any candidate that is
    closer to one already picked than to the place. The candidates come nearest to `base` first, and
    `picked` is what that rule keeps, at most `m`, a tie keeping the candidate. Picks are compared
    as points, as the Lean compares them. The Lean `PicksDiverse`."""
    if points and len(base) != len(points[0]):
        return False
    if any(not 0 <= i < len(points) for i in [*candidates, *picked]):
        return False
    distances = [sq_dist(points[c], base) for c in candidates]
    if distances != sorted(distances):
        return False
    so_far: list[int] = []
    for c in candidates:
        to_base = sq_dist(points[c], base)
        if len(so_far) < m and all(to_base <= sq_dist(points[k], points[c]) for k in so_far):
            if len(so_far) >= len(picked) or points[picked[len(so_far)]] != points[c]:
                return False
            so_far.append(c)
    return len(so_far) == len(picked)


def check_picking_valid(
    points: Sequence[Sequence[float]],
    base: Sequence[float],
    candidates: Sequence[int],
    picked: Sequence[int],
    m: int,
) -> str | None:
    """The Lean `HNSW.Picking.Valid` at one picking: the piece that fails, or `None`."""
    if not is_picks_diverse(points, base, candidates, picked, m):
        return "invariant 2 (picks_diverse)"
    return None


def is_picking_valid(
    points: Sequence[Sequence[float]],
    base: Sequence[float],
    candidates: Sequence[int],
    picked: Sequence[int],
    m: int,
) -> bool:
    """The Lean `HNSW.Picking.Valid`: `is_picks_diverse`."""
    return check_picking_valid(points, base, candidates, picked, m) is None


def finish(beam: Found, k: int) -> Found:
    """The search's last step: the beam sorted by squared distance, then id, and `k` kept. The
    Lean `HNSW.finish`."""
    return sorted(beam)[:k]


def greedy_step(
    points: Sequence[Sequence[float]], q: Sequence[float], cur: int, neighbors: Sequence[int]
) -> int:
    """One greedy move: the neighbor nearest `q`, if it is nearer than `cur`; else stay.

    The Lean `greedyStep`, kept to state the greedy walk one step at a time: `search` does not
    call it, since the walk it runs is `search_layer` with a beam of 1, which takes the same
    steps. The tests hold the two to each other."""
    best = cur
    for x in neighbors:
        if sq_dist(points[x], q) < sq_dist(points[best], q):
            best = x
    return best


class HNSW:
    """A hierarchical navigable small world graph over points of one dimension."""

    def __init__(
        self,
        points: Sequence[Sequence[float]],
        m: int,
        ef_construction: int = 200,
        seed: int = 0,
        flat: bool = False,
    ) -> None:
        if m < 2:
            raise ValueError(f"HNSW needs M >= 2 (m_L = 1/ln M), got M = {m}")
        if ef_construction < 1:
            raise ValueError(f"HNSW needs ef_construction >= 1, got {ef_construction}")
        self.points = copy_points(points)
        self.m = m
        self.m0 = 2 * m
        self.ml = 1.0 / math.log(m)
        self.ef_construction = ef_construction
        self.links: list[list[list[int]]] = []  # links[v][lc]: v's neighbors on layer lc
        self.entry: int | None = None
        self.max_level = 0
        rng = SplitMix64(seed)
        for v in range(len(self.points)):
            level = 0 if flat else math.floor(-math.log(1.0 - rng.next_f64()) * self.ml)
            self.insert(v, level)

    def level(self, v: int) -> int:
        """Node `v`'s level: the top layer it is on."""
        return len(self.links[v]) - 1

    def insert(self, v: int, level: int) -> None:
        """Algorithm 1."""
        self.links.append([[] for _ in range(level + 1)])
        if self.entry is None:
            self.entry, self.max_level = v, level
            return
        q = self.points[v]

        def dist(i: int) -> float:
            return sq_dist(self.points[i], q)

        entry_points: Found = [(dist(self.entry), self.entry)]
        for lc in range(self.max_level, level, -1):
            entry_points = self.search_layer(dist, entry_points, 1, lc)[:1]
        for lc in range(min(level, self.max_level), -1, -1):
            found = self.search_layer(dist, entry_points, self.ef_construction, lc)
            neighbors = select_neighbors(self.points, q, found, self.m)
            most = self.m0 if lc == 0 else self.m
            for e in neighbors:
                self.links[e][lc].append(v)
                if len(self.links[e][lc]) > most:
                    base = self.points[e]
                    links = self.links[e][lc]
                    by_distance = sorted((sq_dist(self.points[c], base), c) for c in links)
                    self.links[e][lc] = select_neighbors(self.points, base, by_distance, most)
            self.links[v][lc] = neighbors
            entry_points = found
        if level > self.max_level:
            self.entry, self.max_level = v, level

    def is_degree_bounded(self) -> bool:
        """Box invariant 1: every point has at most a fixed number of neighbors. Every list on
        layer 0 holds at most `M0` neighbors, every list above it at most `M`. The Lean
        `DegreeBounded`."""
        return all(
            len(ns) <= (self.m0 if lc == 0 else self.m)
            for node in self.links
            for lc, ns in enumerate(node)
        )

    def is_nested_layers(self) -> bool:
        """Box invariant 3: with layers: every place on a layer is on every layer below it, and
        each layer up keeps a random few of the one below. A node is on layers
        `0 .. len(links[v]) - 1`, so the first half holds by how the graph is stored; this checks
        what can fail: every node is on layer 0, and every link on a layer reaches a node on that
        layer. The random few is the level draw's, not a property of one graph. The Lean
        `NestedLayers`."""
        n = len(self.links)

        def on(u: int, lc: int) -> bool:
            return 0 <= u < n and lc < len(self.links[u])

        return all(len(node) > 0 for node in self.links) and all(
            on(u, lc) for node in self.links for lc, ns in enumerate(node) for u in ns
        )

    def is_no_self_links(self) -> bool:
        """Not in the box: no node is its own neighbor. The Lean `NoSelfLinks`."""
        return all(v not in ns for v, node in enumerate(self.links) for ns in node)

    def is_no_repeated_links(self) -> bool:
        """Not in the box: no list names a neighbor twice. The Lean `NoRepeatedLinks`."""
        return all(len(set(ns)) == len(ns) for node in self.links for ns in node)

    def is_entry_on_top(self) -> bool:
        """Not in the box: the entry point is a node on the top layer, so no node is on
        more layers than it is; `None` exactly when there are no nodes. The Lean `EntryOnTop`."""
        if self.entry is None:
            return len(self.links) == 0
        return 0 <= self.entry < len(self.links) and all(
            len(node) <= len(self.links[self.entry]) for node in self.links
        )

    def is_one_node_per_point(self) -> bool:
        """Not in the box: the graph carries its points, one node per stored point. The
        Lean `OneNodePerPoint`."""
        return len(self.links) == len(self.points)

    def check_valid(self) -> str | None:
        """The first piece of the Lean `HNSW.Valid` or `HNSW.WellFormed` the graph breaks, or
        `None`."""
        if not self.is_degree_bounded():
            return "invariant 1 (degree_bounded)"
        if not self.is_nested_layers():
            return "invariant 3 (nested_layers)"
        if not self.is_no_self_links():
            return "not in the box (no_self_links)"
        if not self.is_no_repeated_links():
            return "not in the box (no_repeated_links)"
        if not self.is_entry_on_top():
            return "not in the box (entry_on_top)"
        if not self.is_one_node_per_point():
            return "not in the box (one_node_per_point)"
        return None

    def is_valid(self) -> bool:
        """The Lean `HNSW.Valid` and `HNSW.WellFormed`: `is_degree_bounded`, `is_nested_layers`,
        `is_no_self_links`, `is_no_repeated_links`, `is_entry_on_top` and
        `is_one_node_per_point`."""
        return self.check_valid() is None

    def search_layer(
        self, dist: Callable[[int], float], entry_points: Found, ef: int, lc: int
    ) -> Found:
        """Algorithm 2: the `ef` nearest nodes the beam finds on layer `lc`, nearest first."""
        visited = {v for _, v in entry_points}
        candidates = list(entry_points)  # a min-heap: the nearest to expand next
        heapq.heapify(candidates)
        found = [(-d, -v) for d, v in entry_points]  # a max-heap: the worst found on top
        heapq.heapify(found)
        while len(found) > ef:
            heapq.heappop(found)
        while candidates:
            dc, c = heapq.heappop(candidates)
            if dc > -found[0][0]:
                break
            for e in self.links[c][lc]:
                if e in visited:
                    continue
                visited.add(e)
                de = dist(e)
                if de < -found[0][0] or len(found) < ef:
                    heapq.heappush(candidates, (de, e))
                    heapq.heappush(found, (-de, -e))
                    if len(found) > ef:
                        heapq.heappop(found)
        return sorted((-d, -v) for d, v in found)

    def search_by(self, dist: Callable[[int], float], ef: int) -> Found:
        """Algorithm 5's walk under any distance: greedy above layer 0, width `ef` on it."""
        if self.entry is None:
            return []
        entry_points: Found = [(dist(self.entry), self.entry)]
        for lc in range(self.max_level, 0, -1):
            entry_points = self.search_layer(dist, entry_points, 1, lc)[:1]
        return self.search_layer(dist, entry_points, ef, 0)

    def search(self, q: Sequence[float], k: int, ef: int) -> Found:
        """Algorithm 5: the `min(k, n)` nearest nodes the walk finds; a beam narrower than `k` is
        widened to `k`."""
        check_query(self.points, q)
        if k < 0:
            raise ValueError(f"k must be at least 0, got {k}")
        if k == 0:
            return []
        return finish(self.search_by(lambda i: sq_dist(self.points[i], q), max(ef, k)), k)
