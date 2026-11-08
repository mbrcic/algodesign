# SPDX-License-Identifier: Apache-2.0
"""The convex hull, against a naive hull built from the definition.

The naive hull keeps the edge i -> j when every other point is strictly left of it or on the
segment between i and j; those edges, chained, are the hull counterclockwise. It costs O(n^3)
and shares nothing with the monotone chain but the turn test.
"""

from __future__ import annotations

import math
from fractions import Fraction

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.geometry.hull import convex_hull
from algodesign.geometry.orientation import orient2d, orient2d_fast

Pt = tuple[float, float]


def between(a: Pt, b: Pt, c: Pt) -> bool:
    """`c`, collinear with `a` and `b`, lies on the segment between them."""
    return min(a[0], b[0]) <= c[0] <= max(a[0], b[0]) and min(a[1], b[1]) <= c[1] <= max(a[1], b[1])


def naive_hull(points: list[Pt]) -> list[int]:
    distinct: list[int] = []
    for i, p in enumerate(points):
        if all(points[j] != p for j in distinct):
            distinct.append(i)
    if len(distinct) <= 2:
        return sorted(distinct, key=lambda i: points[i])
    successor = {}
    for i in distinct:
        for j in distinct:
            if i == j:
                continue
            a, b = points[i], points[j]
            if all(
                orient2d(a, b, points[k]) > 0
                or (orient2d(a, b, points[k]) == 0 and between(a, b, points[k]))
                for k in distinct
                if k not in (i, j)
            ):
                successor[i] = j
    start = min(successor, key=lambda i: points[i])
    hull = [start]
    while successor[hull[-1]] != start:
        hull.append(successor[hull[-1]])
    return hull


def same_cycle(got: list[int], want: list[int]) -> bool:
    if len(got) != len(want):
        return False
    if not got:
        return True
    if want[0] not in got:
        return False
    k = got.index(want[0])
    return got[k:] + got[:k] == want


def check(points: list[Pt]) -> list[int]:
    got = convex_hull(points)
    want = naive_hull(points)
    assert same_cycle(got, want), (points, got, want)
    return got


def signed_area(points: list[Pt]) -> Fraction:
    """Twice the signed area of the polygon, exactly: positive when counterclockwise."""
    total = Fraction(0)
    for k, (x0, y0) in enumerate(points):
        x1, y1 = points[(k + 1) % len(points)]
        total += Fraction(x0) * Fraction(y1) - Fraction(x1) * Fraction(y0)
    return total


def test_no_points() -> None:
    assert convex_hull([]) == []


def test_one_point() -> None:
    assert convex_hull([(3.0, 4.0)]) == [0]


def test_two_points() -> None:
    assert convex_hull([(5.0, 0.0), (1.0, 2.0)]) == [1, 0]


def test_all_points_identical() -> None:
    assert convex_hull([(2.0, 2.0)] * 5) == [0]


@pytest.mark.parametrize(
    "points",
    [
        [(3.0, 0.0), (1.0, 0.0), (5.0, 0.0), (2.0, 0.0)],  # horizontal
        [(0.0, 3.0), (0.0, -1.0), (0.0, 5.0), (0.0, 2.0)],  # vertical
        [(3.0, 3.0), (-1.0, -1.0), (5.0, 5.0), (2.0, 2.0), (5.0, 5.0)],  # diagonal
    ],
)
def test_collinear_points_give_the_two_ends(points: list[Pt]) -> None:
    assert check(points) == [1, 2]


def test_points_on_the_edges_of_a_square_are_dropped() -> None:
    square = [(0.0, 0.0), (4.0, 0.0), (4.0, 4.0), (0.0, 4.0)]
    on_edges = [(2.0, 0.0), (4.0, 1.0), (4.0, 3.0), (1.0, 4.0), (0.0, 2.0)]
    assert check(on_edges + square) == [5, 6, 7, 8]


def test_a_duplicated_corner_keeps_its_lowest_index() -> None:
    points = [(1.0, 1.0), (0.0, 0.0), (2.0, 0.0), (0.0, 0.0), (1.0, 2.0), (2.0, 0.0)]
    assert check(points) == [1, 2, 4]


def test_interior_points_of_a_triangle_are_dropped() -> None:
    points = [(1.0, 1.0), (0.0, 0.0), (2.0, 1.0), (6.0, 0.0), (3.0, 2.0), (0.0, 6.0)]
    assert check(points) == [1, 3, 5]


@pytest.mark.parametrize("scale", [1.0, 2.0**40])
def test_a_point_one_ulp_off_a_line_is_decided_exactly(scale: float) -> None:
    # Kettner et al. 2008: p near (0.5, 0.5), q = (12, 12), r = (24, 24), all times `scale`. The
    # upper chain asks whether r -> q -> p turns left, and there the plain determinant gives some
    # p the wrong sign; the hull must follow the exact one.
    q, r = (12.0 * scale, 12.0 * scale), (24.0 * scale, 24.0 * scale)
    u = 2.0**-53
    flipped = 0
    for i in range(64):
        for j in range(64):
            p = ((0.5 + i * u) * scale, (0.5 + j * u) * scale)
            exact = orient2d(p, q, r)
            fast = -orient2d_fast(r, q, p)
            if (fast > 0) - (fast < 0) == -exact != 0:
                flipped += 1
                want = [0, 1, 2] if exact > 0 else [0, 2, 1]
                assert convex_hull([p, q, r]) == want, p
    assert flipped > 0


def test_nearly_collinear_points_at_large_magnitudes() -> None:
    big = 2.0**52
    line = [(big + k, big + k) for k in range(5)]
    above = (big + 2, math.nextafter(big + 2, math.inf))
    below = (big + 2, math.nextafter(big + 2, -math.inf))
    assert check(line) == [0, 4]
    assert check([*line, above]) == [0, 4, 5]
    assert check([*line, below]) == [0, 5, 4]
    assert check([*line, above, below]) == [0, 6, 4, 5]


def test_the_hull_is_counterclockwise() -> None:
    points = [(0.0, 0.0), (5.0, 1.0), (6.0, 6.0), (1.0, 5.0), (3.0, 3.0), (2.0, 4.0)]
    hull = convex_hull(points)
    assert len(hull) >= 3
    assert signed_area([points[i] for i in hull]) > 0


def test_the_hull_starts_at_the_lowest_point() -> None:
    points = [(3.0, 3.0), (0.0, 5.0), (6.0, 0.0), (0.0, 1.0), (3.0, -2.0)]
    assert convex_hull(points)[0] == 3


@pytest.mark.parametrize(
    "points",
    [[(0.0, 0.0), (1.0,)], [(0.0, 0.0, 0.0)], [(0.0, math.nan)], [(math.inf, 0.0)]],
)
def test_a_bad_point_is_rejected(points: list[tuple[float, ...]]) -> None:
    with pytest.raises(ValueError):
        convex_hull(points)


grid = st.integers(-4, 4).map(float)


@settings(max_examples=200)
@given(st.lists(st.tuples(grid, grid), min_size=3, max_size=60))
def test_grid_points_match_the_naive_hull(points: list[Pt]) -> None:
    # A 9 x 9 grid: many collinear and repeated points.
    hull = check(points)
    assert hull[0] == min(range(len(points)), key=lambda i: (points[i], i))
    if len(hull) >= 3:
        assert signed_area([points[i] for i in hull]) > 0


coord = st.floats(-1e6, 1e6, allow_nan=False, allow_infinity=False)


@given(st.lists(st.tuples(coord, coord), min_size=3, max_size=40))
def test_float_points_match_the_naive_hull(points: list[Pt]) -> None:
    check(points)
