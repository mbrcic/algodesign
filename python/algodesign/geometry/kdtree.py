# SPDX-License-Identifier: Apache-2.0
"""The k-d tree: a binary tree of axis-parallel cuts with the points in its leaves (dBCKO §5.2,
`BUILDKDTREE` p. 100 and `SEARCHKDTREE` p. 103; Bentley 1975). At depth `d` a node cuts on axis
`d mod dim` at the lower median of the points below; points equal to a cut may sit on either side,
so the tree stays balanced however many share a coordinate. The default leaf holds one point,
dBCKO's tree and the one the chapter traces.

The tree keeps the Lean `KDTree.Valid`: box invariant 1, every cut divides the points below it
(`is_cuts_separate`, Lean `CutsSeparate`), and box invariant 2, every cut splits them in half
(`is_cuts_halve`, Lean `CutsHalve`). Nearest neighbors come by best-first search (Samet §4.1;
Arya et al. 1998). A run of it, the tree, the query and the running state (the Lean
`BestFirst.Run`), keeps the Lean `BestFirst.Valid`: box invariant 3, `is_nothing_closer_skipped`,
and, not in the box, `is_queued_cuts_separate`, `is_offsets_bound` and `is_each_point_once`.

The Rust differs here: its leaves hold 8 points by default where these hold 1, it descends the
nearer sides instead of queueing both, it selects the median in linear time, and its `range` is
unsorted.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/KDTree/` (specification:
`KDTree/Spec.lean`): `far_side_bound`, `far_side_bound_left`, `boxSqDist_le`,
`rangeQuery_perm_filter`, `valid_start`, `valid_visit`, `search_kNearest_eq_scan`.
"""

from __future__ import annotations

import heapq
from collections.abc import Sequence
from dataclasses import dataclass

from .point import check_query, copy_points, dot, sq_dist


@dataclass
class Leaf:
    """Up to `bucket` points: positions `[start, end)` of the tree's ordering."""

    start: int
    end: int


@dataclass
class Node:
    """A cut on `axis` at the coordinate `split`, over positions [start, end) of the tree's
    ordering."""

    axis: int
    split: float
    start: int
    end: int
    left: Node | Leaf
    right: Node | Leaf


@dataclass
class SearchStats:
    """What one search cost: the points it measured and the regions it opened."""

    points_measured: int = 0
    regions_opened: int = 0


@dataclass
class Region:
    """A region waiting in a best-first search: a subtree, and how far the query is from it along
    each axis (signed; only the square is used). The Lean `BestFirst.Region`."""

    offsets: list[float]
    node: Node | Leaf


@dataclass
class SearchState:
    """A best-first search's running state, the Lean `BestFirst.State`: the ids measured
    so far, in the order measured, and the regions waiting, in the order they were queued. With
    the tree and the query it is the Lean `BestFirst.Run`, the three arguments every search piece
    takes."""

    measured: list[int]
    queue: list[Region]


class KDTree:
    """A static k-d tree over points of one dimension."""

    def __init__(self, points: Sequence[Sequence[float]], bucket: int = 1) -> None:
        if bucket < 1:
            raise ValueError(f"a k-d tree's bucket size must be at least 1, got {bucket}")
        self.points = copy_points(points)
        self.bucket = bucket
        # order[p] is the id at position p; every node's points are a run of positions.
        # The build appends the leaves' points left to right.
        self.order: list[int] = []
        self.dim = len(self.points[0]) if self.points else 0
        self.root: Node | Leaf | None = None
        if self.points:
            # One sort per axis, by (coordinate, id): the id breaks ties, so the tree is a
            # function of the input.
            by_axis = [self.sorted_along(a) for a in range(self.dim)]
            self.root = self.build(by_axis, 0)

    def sorted_along(self, axis: int) -> list[int]:
        """All ids in order of (coordinate on `axis`, id)."""
        return sorted(range(len(self.points)), key=lambda i: (self.points[i][axis], i))

    def build(self, by_axis: list[list[int]], depth: int) -> Node | Leaf:
        """`BUILDKDTREE` on lists `by_axis[a]`: the same ids, each in order along axis `a`.

        The left set is the first ceil(n/2) of the splitting axis's list, and the split is the
        coordinate of the last of them, the lower median. Every axis's list is then split, keeping
        its order, into the ids in the left set and the rest, asking a set of the node's own
        size about each id. Each split is linear, so the build is O(n log n) after the one
        sort per axis in `__init__`: dBCKO's own route (Lemma 5.3, p. 101). The Rust selects the
        median in linear time instead; the two trees agree up to which tied points go left. A
        leaf's points are in the order of axis 0.
        """
        n = len(by_axis[0])
        start = len(self.order)  # the positions of this subtree's points begin here
        if n <= self.bucket:
            self.order.extend(by_axis[0])
            return Leaf(start, start + n)
        axis = depth % self.dim
        left_set = by_axis[axis][: (n + 1) // 2]
        split = self.points[left_set[-1]][axis]
        goes_left = set(left_set)
        lefts = [[i for i in order if i in goes_left] for order in by_axis]
        rights = [[i for i in order if i not in goes_left] for order in by_axis]
        left = self.build(lefts, depth + 1)
        right = self.build(rights, depth + 1)
        return Node(axis, split, start, len(self.order), left, right)

    def below(self, v: Node | Leaf) -> list[int]:
        """The ids of the points in `v`'s subtree."""
        return self.order[v.start : v.end]

    def is_cuts_separate(self) -> bool:
        """Box invariant 1: every cut divides the points below it: none on its left lies past the
        cut, none on its right lies before it. The Lean `CutsSeparate`."""
        return self.root is None or self.cuts_separate(self.root)

    def cuts_separate(self, v: Node | Leaf) -> bool:
        """`is_cuts_separate` on the subtree `v`: at every node, the points below the left side
        have the node's coordinate <= the split, those below the right >= it."""
        if isinstance(v, Leaf):
            return True
        return (
            all(self.points[i][v.axis] <= v.split for i in self.below(v.left))
            and all(v.split <= self.points[i][v.axis] for i in self.below(v.right))
            and self.cuts_separate(v.left)
            and self.cuts_separate(v.right)
        )

    def is_cuts_halve(self) -> bool:
        """Box invariant 2: every cut splits the points below it in half. The Lean `CutsHalve`: at
        every node the left side holds ceil(n/2) of its n points, the right side the rest."""

        def halves(v: Node | Leaf) -> bool:
            if isinstance(v, Leaf):
                return True
            left, right = len(self.below(v.left)), len(self.below(v.right))
            return right <= left <= right + 1 and halves(v.left) and halves(v.right)

        return self.root is None or halves(self.root)

    def check_valid(self) -> str | None:
        """The first piece of the Lean `KDTree.Valid` the tree breaks, or `None`."""
        if not self.is_cuts_separate():
            return "invariant 1 (cuts_separate)"
        if not self.is_cuts_halve():
            return "invariant 2 (cuts_halve)"
        return None

    def is_valid(self) -> bool:
        """The Lean `KDTree.Valid`: `is_cuts_separate` and `is_cuts_halve`."""
        return self.check_valid() is None

    def depth(self) -> int:
        def d(v: Node | Leaf) -> int:
            return 0 if isinstance(v, Leaf) else 1 + max(d(v.left), d(v.right))

        return 0 if self.root is None else d(self.root)

    def range(self, lo: Sequence[float], hi: Sequence[float]) -> list[int]:
        """The ids, ascending, of the points with lo <= p <= hi on every axis.

        `SEARCHKDTREE` keeps the rectangle each node covers. A node whose rectangle lies inside the
        box is reported whole, without looking at its points; one whose rectangle misses the box is
        skipped; the rest are opened.
        """
        check_query(self.points, lo)
        check_query(self.points, hi)
        out: list[int] = []
        if self.root is not None:
            dim = len(self.points[0])
            self.search_kd_tree(self.root, lo, hi, [float("-inf")] * dim, [float("inf")] * dim, out)
        return sorted(out)

    def search_kd_tree(
        self,
        v: Node | Leaf,
        lo: Sequence[float],
        hi: Sequence[float],
        region_lo: list[float],
        region_hi: list[float],
        out: list[int],
    ) -> None:
        """`SEARCHKDTREE`: report `v` whole if its region lies in the box, else open it."""
        axes = range(len(lo))
        if all(lo[a] <= region_lo[a] and region_hi[a] <= hi[a] for a in axes):
            out.extend(self.below(v))
        elif isinstance(v, Leaf):
            out.extend(
                i for i in self.below(v) if all(lo[a] <= self.points[i][a] <= hi[a] for a in axes)
            )
        else:
            a = v.axis
            if lo[a] <= v.split:
                left_hi = region_hi[:a] + [v.split] + region_hi[a + 1 :]
                self.search_kd_tree(v.left, lo, hi, region_lo, left_hi, out)
            if v.split <= hi[a]:
                right_lo = region_lo[:a] + [v.split] + region_lo[a + 1 :]
                self.search_kd_tree(v.right, lo, hi, right_lo, region_hi, out)

    def nearest(self, q: Sequence[float]) -> int | None:
        """The id of the point nearest `q`, the one stored first on a tie; `None` if there are
        none."""
        found = self.k_nearest(q, 1)
        return found[0][1] if found else None

    def k_nearest(self, q: Sequence[float], k: int) -> list[tuple[float, int]]:
        """The `min(k, n)` nearest points as `(squared distance, id)`, as `scan.k_nearest`."""
        return self.k_nearest_with_stats(q, k)[0]

    def k_nearest_with_stats(
        self, q: Sequence[float], k: int
    ) -> tuple[list[tuple[float, int]], SearchStats]:
        """Best-first k-NN, and what it cost.

        Regions wait in a priority queue, keyed by a lower bound on the squared distance from the
        query to anything inside them: the sum over axes of `offset**2`, where an axis's offset is
        how far the query is from the region on that axis. Opening a node queues its far child,
        with the offset on the split axis replaced by `split - q[axis]`, and then its near child
        with the parent's offsets. The search stops when the nearest waiting region is strictly
        farther than the k-th best point found, so a point tied with it and stored earlier is still
        found. Equal bounds leave the queue in the order they entered it, far child before near.
        """
        check_query(self.points, q)
        if k < 0:
            raise ValueError(f"k must be at least 0, got {k}")
        return self.best_first(q, k)

    def best_first(
        self, q: Sequence[float], k: int, states: list[SearchState] | None = None
    ) -> tuple[list[tuple[float, int]], SearchStats]:
        """The search of `k_nearest_with_stats`, on a query already checked. If `states` is a
        list, the running state is appended to it at the start and after each region the search
        opens (`search_states`)."""
        stats = SearchStats()
        if k == 0 or self.root is None:
            return [], stats
        best: list[tuple[float, int]] = []  # the k best so far, as (-distance, -id)
        sequence = 0
        queue: list[tuple[float, int, list[float], Node | Leaf]] = [
            (0.0, sequence, [0.0] * len(q), self.root)
        ]
        measured: list[int] = []
        if states is not None:
            states.append(_snapshot(measured, queue))
        while queue:
            bound, _, offsets, v = heapq.heappop(queue)
            if len(best) == k and bound > -best[0][0]:
                break
            stats.regions_opened += 1
            if isinstance(v, Leaf):
                for i in self.below(v):
                    stats.points_measured += 1
                    d = sq_dist(self.points[i], q)
                    if len(best) < k:
                        heapq.heappush(best, (-d, -i))
                    elif (d, i) < (-best[0][0], -best[0][1]):
                        heapq.heapreplace(best, (-d, -i))
            else:
                near, far = (v.left, v.right) if q[v.axis] <= v.split else (v.right, v.left)
                far_offsets = list(offsets)
                far_offsets[v.axis] = v.split - q[v.axis]
                sequence += 1
                far_bound = dot(far_offsets, far_offsets)
                heapq.heappush(queue, (far_bound, sequence, far_offsets, far))
                sequence += 1
                heapq.heappush(queue, (bound, sequence, offsets, near))
            if states is not None:
                measured += self.below(v) if isinstance(v, Leaf) else []
                states.append(_snapshot(measured, queue))
        return sorted((-d, -i) for d, i in best), stats

    def search_states(self, q: Sequence[float], k: int) -> list[SearchState]:
        """The running state of `k_nearest`'s search: the start, then the state after each region
        it opened, each a state `is_search_valid` can check. Empty when `k == 0` or the tree is."""
        check_query(self.points, q)
        states: list[SearchState] = []
        self.best_first(q, k, states)
        return states


def _snapshot(
    measured: list[int], queue: list[tuple[float, int, list[float], Node | Leaf]]
) -> SearchState:
    """The search's state: a copy of what it measured, and its queue in the order queued."""
    in_order = sorted(queue, key=lambda entry: entry[1])
    return SearchState(list(measured), [Region(list(offsets), v) for _, _, offsets, v in in_order])


def is_nothing_closer_skipped(tree: KDTree, q: Sequence[float], state: SearchState) -> bool:
    """Box invariant 3: the search never skips a region that could hold a point closer than the
    best found so far. The Lean `BestFirst.NothingCloserSkipped`: every stored point is measured,
    or sits in a queued region whose bound, the sum of its squared offsets, is at most its squared
    distance to `q`. A query of another dimension than the tree's gives False."""
    if len(q) != tree.dim:
        return False
    return all(
        i in state.measured
        or any(
            i in tree.below(r.node) and dot(r.offsets, r.offsets) <= sq_dist(tree.points[i], q)
            for r in state.queue
        )
        for i in tree.order
    )


def is_queued_cuts_separate(tree: KDTree, q: Sequence[float], state: SearchState) -> bool:
    """Not in the box: every queued region's cuts separate its points. The Lean
    `BestFirst.QueuedCutsSeparate`."""
    if len(q) != tree.dim:
        return False
    return all(tree.cuts_separate(r.node) for r in state.queue)


def is_offsets_bound(tree: KDTree, q: Sequence[float], state: SearchState) -> bool:
    """Not in the box: every queued region's offsets are at most each of its points'
    distances from `q`, axis by axis. The Lean `BestFirst.OffsetsBound`."""
    if len(q) != tree.dim:
        return False
    return all(
        r.offsets[a] * r.offsets[a] <= (tree.points[i][a] - q[a]) * (tree.points[i][a] - q[a])
        for r in state.queue
        for i in tree.below(r.node)
        for a in range(len(q))
    )


def is_each_point_once(tree: KDTree, q: Sequence[float], state: SearchState) -> bool:
    """Not in the box: the measured points and the queued regions' points are the stored
    points, each once. The Lean `BestFirst.EachPointOnce` compares points; this compares ids."""
    if len(q) != tree.dim:
        return False
    held = state.measured + [i for r in state.queue for i in tree.below(r.node)]
    return sorted(held) == sorted(tree.order)


def check_search_valid(tree: KDTree, q: Sequence[float], state: SearchState) -> str | None:
    """The first piece of the Lean `BestFirst.Valid` the run breaks, or `None`."""
    if not is_nothing_closer_skipped(tree, q, state):
        return "invariant 3 (nothing_closer_skipped)"
    if not is_queued_cuts_separate(tree, q, state):
        return "not in the box (queued_cuts_separate)"
    if not is_offsets_bound(tree, q, state):
        return "not in the box (offsets_bound)"
    if not is_each_point_once(tree, q, state):
        return "not in the box (each_point_once)"
    return None


def is_search_valid(tree: KDTree, q: Sequence[float], state: SearchState) -> bool:
    """The Lean `BestFirst.Valid`: its four pieces. Lean: `valid_start`, `valid_visit`."""
    return check_search_valid(tree, q, state) is None
