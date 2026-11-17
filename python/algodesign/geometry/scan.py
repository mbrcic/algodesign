# SPDX-License-Identifier: Apache-2.0
"""Checking every point: the chapter's specification of the nearest-neighbor and box queries,
and the oracle every other structure in the chapter is tested against.

The nearest neighbor is the stored point at the least squared distance from the query, and among
equally near points **the one stored first**. `k_nearest` keeps the `k` best seen so far
in a heap whose top is the worst of them, so a new point either beats that one or is dropped.
Each query checks the points as well as itself (`ValueError` on a ragged or non-finite set): an
oracle that answered for a NaN would make every comparison against it meaningless.

The Rust differs here: its `k_nearest_among` takes candidates without repeats as the caller's
promise and does not check it, since every index that calls it lists each point once; an id out
of range panics there.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/Scan.lean`: `scanNearest_le`,
`scanNearest_lowest`, `scanNearest_mem`, `scanNearest_isSome_iff`.
"""

from __future__ import annotations

import heapq
from collections.abc import Sequence

from .point import check_query, copy_points, sq_dist


def nearest(points: Sequence[Sequence[float]], q: Sequence[float]) -> int | None:
    """The id of the point nearest `q`, the one stored first on a tie; `None` if there are none."""
    points = copy_points(points)
    check_query(points, q)
    best: int | None = None
    best_dist = 0.0
    for i, p in enumerate(points):
        d = sq_dist(p, q)
        if best is None or d < best_dist:
            best, best_dist = i, d
    return best


def k_nearest(
    points: Sequence[Sequence[float]], q: Sequence[float], k: int
) -> list[tuple[float, int]]:
    """The `min(k, n)` points nearest `q`, as `(squared distance, id)`, best first.

    The heap holds the best `k` so far as `(-distance, -id)`, so its top is the worst of them,
    the farthest, and among the farthest the one stored last. O(n log k).
    """
    points = copy_points(points)
    check_query(points, q)
    if k < 0:
        raise ValueError(f"k must be at least 0, got {k}")
    worst_first: list[tuple[float, int]] = []
    for i, p in enumerate(points):
        d = sq_dist(p, q)
        if len(worst_first) < k:
            heapq.heappush(worst_first, (-d, -i))
        elif worst_first and (d, i) < (-worst_first[0][0], -worst_first[0][1]):
            heapq.heapreplace(worst_first, (-d, -i))
    return sorted((-d, -i) for d, i in worst_first)


def k_nearest_among(
    points: Sequence[Sequence[float]], candidates: Sequence[int], q: Sequence[float], k: int
) -> list[tuple[float, int]]:
    """`k_nearest` over the listed points only: the exact re-rank every approximate index ends
    with. The candidates are put in id order first, so a tie goes to the one stored first,
    whatever order they came in. A candidate listed twice, or one that is not a point's id,
    raises `ValueError`."""
    ordered = sorted(candidates)
    for i, j in enumerate(ordered):
        if not 0 <= j < len(points):
            raise ValueError(f"candidate {j} is not a point's id; there are {len(points)} points")
        if i > 0 and ordered[i - 1] == j:
            raise ValueError(f"candidate {j} is listed twice")
    found = k_nearest([points[i] for i in ordered], q, k)
    return [(d, ordered[j]) for d, j in found]


def in_box(
    points: Sequence[Sequence[float]], lo: Sequence[float], hi: Sequence[float]
) -> list[int]:
    """The ids, ascending, of the points with `lo[j] <= p[j] <= hi[j]` on every axis."""
    points = copy_points(points)
    check_query(points, lo)
    check_query(points, hi)
    return [
        i
        for i, p in enumerate(points)
        if all(a <= x <= b for a, x, b in zip(lo, p, hi, strict=True))
    ]
