# SPDX-License-Identifier: Apache-2.0
"""Points, distances and normalization: the arithmetic every structure in the chapter shares.

A point is a `list[float]`, one entry per coordinate, and a point set is a list of them. Distances
are **squared** Euclidean: the square root changes no comparison, so no search takes it.

Every sum here is added left to right, in a plain loop. `dot` matches the Rust's bit for bit, so
what is built from it (normalized points, projections, LSH keys, RaBitQ codes) is the same in both
languages. The Rust sums `sq_dist` in four running sums for speed, so a distance can differ from
this one in its last bits. Python's `sum()` is avoided too: it compensates for rounding (since
3.12), which is a third order.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/Point.lean`: `sqDist_comm`,
`sqDist_nonneg`, `sq_axis_le_sqDist`.
"""

from __future__ import annotations

import math
from collections.abc import Sequence


def sq_dist(a: Sequence[float], b: Sequence[float]) -> float:
    """The squared Euclidean distance between `a` and `b`."""
    total = 0.0
    for x, y in zip(a, b, strict=True):
        total += (x - y) * (x - y)
    return total


def dot(a: Sequence[float], b: Sequence[float]) -> float:
    """The inner product of `a` and `b`."""
    total = 0.0
    for x, y in zip(a, b, strict=True):
        total += x * y
    return total


def normalized(points: Sequence[Sequence[float]]) -> list[list[float]]:
    """Each point scaled to length 1: on unit vectors, squared distance is `2 - 2 cos`, so the
    nearest by distance is the nearest by angle.

    Each vector is first divided by its largest coordinate, so neither a huge nor a tiny vector
    overflows or underflows on the way to its length. A zero vector has no direction and raises
    `ValueError`, as do points of different dimensions or a coordinate that is not finite
    (`copy_points`), which would otherwise come out as NaN.
    """
    out = []
    for i, p in enumerate(copy_points(points)):
        largest = max((abs(x) for x in p), default=0.0)
        if largest == 0.0:
            raise ValueError(f"point {i} is the zero vector, which has no direction")
        scaled = [x / largest for x in p]
        length = math.sqrt(dot(scaled, scaled))
        out.append([x / length for x in scaled])
    return out


def check_query(points: Sequence[Sequence[float]], q: Sequence[float]) -> None:
    """Raise `ValueError` if `q` cannot be compared with `points`: a different dimension, or a
    coordinate that is not a finite number."""
    if points and len(q) != len(points[0]):
        raise ValueError(f"the query has dimension {len(q)} but the points have {len(points[0])}")
    for i, x in enumerate(q):
        if not math.isfinite(x):
            raise ValueError(f"query coordinate {i} is not finite")


def copy_points(points: Sequence[Sequence[float]]) -> list[list[float]]:
    """A copy of `points` an index can keep: every point has the same dimension and finite
    coordinates, or `ValueError`. Copying means a caller who later changes their own list cannot
    break the index built from it."""
    out = [list(p) for p in points]
    if out and not out[0]:
        raise ValueError("points need dimension at least 1")
    for i, p in enumerate(out):
        if len(p) != len(out[0]):
            raise ValueError(f"point {i} has dimension {len(p)} but point 0 has {len(out[0])}")
        if not all(math.isfinite(x) for x in p):
            raise ValueError(f"point {i} has a coordinate that is not finite")
    return out
