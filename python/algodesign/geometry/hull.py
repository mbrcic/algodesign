# SPDX-License-Identifier: Apache-2.0
"""The convex hull: the smallest fence around every pin, a convex polygon through some pins.

**The promise:** every point is inside or on the hull; points on a straight stretch of the fence
are left out. `convex_hull` returns the ids of the hull's corners, counterclockwise, starting
from the point with the lowest x (and, among those, the lowest y). A point given twice is one pin:
the one stored first stands for it. No points give `[]`, one distinct point gives `[i]`, and points
all on one line give the two ends of that line.

**Andrew's monotone chain** (A. M. Andrew, "Another efficient algorithm for convex hulls in two
dimensions", *Information Processing Letters* 9(5), 1979). Sort the points by x, then y. Walk them
left to right, building the **lower** chain: while the last two kept points and the new one do not
turn strictly left, the middle one cannot be a corner, so drop it. Walk right to left the same way
for the **upper** chain. The two chains share their end points; joined without repeating those,
they are the hull.

The cost is O(n log n), and the sort is all of it: each walk pushes every point once and pops it
at most once, so both walks together are O(n). The turn test is `orientation.orient2d`, which is
exact, so a point a hair off a line is never mistaken for one on it.
"""

from __future__ import annotations

import math
from collections.abc import Iterable, Sequence

from .orientation import Point2, orient2d


def convex_hull(points: Sequence[Sequence[float]]) -> list[int]:
    """The ids of the hull's corners, counterclockwise from the lowest (x, y) point.

    `ValueError` on a point that is not 2D or has a coordinate that is not finite.
    """
    pts = [check_point(i, p) for i, p in enumerate(points)]
    by_position = sorted(range(len(pts)), key=lambda i: (pts[i], i))
    # Equal points sit side by side after the sort, the one stored first leading: keep that one.
    distinct = [i for k, i in enumerate(by_position) if k == 0 or pts[i] != pts[by_position[k - 1]]]
    if len(distinct) <= 2:
        return distinct
    lower = chain(pts, distinct)
    upper = chain(pts, reversed(distinct))
    # Each chain ends where the other begins.
    return lower[:-1] + upper[:-1]


def chain(pts: list[Point2], order: Iterable[int]) -> list[int]:
    """One half of the hull: the points in `order`, keeping only strict left turns."""
    kept: list[int] = []
    for i in order:
        while len(kept) >= 2 and not turns_left(pts[kept[-2]], pts[kept[-1]], pts[i]):
            kept.pop()
        kept.append(i)
    return kept


def turns_left(a: Point2, b: Point2, c: Point2) -> bool:
    """Walking a -> b -> c turns strictly left (counterclockwise)."""
    return orient2d(a, b, c) > 0


def check_point(i: int, p: Sequence[float]) -> Point2:
    """Point `i` as an `(x, y)` pair, or `ValueError`."""
    if len(p) != 2:
        raise ValueError(f"point {i} has dimension {len(p)}, but a hull needs 2")
    if not all(math.isfinite(x) for x in p):
        raise ValueError(f"point {i} has a coordinate that is not finite")
    return (p[0], p[1])
