# SPDX-License-Identifier: Apache-2.0
"""The scan: the specification of nearest-neighbor and box queries, and the oracle.

Mirrors the Rust's `scan::tests` and the Lean's `Scan.lean`: the answer is a stored point at the
least distance (`scanNearest_le`, `scanNearest_mem`), the one stored first on a tie
(`scanNearest_lowest`), and `None` only for no points (`scanNearest_isSome_iff`). Coordinates are
small integers, so every distance is exact and a tie is a real tie.
"""

from __future__ import annotations

import math
import random

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.geometry import scan
from algodesign.geometry.point import dot, normalized, sq_dist

coord = st.integers(-6, 6).map(float)


def points_2d(max_size: int = 40) -> st.SearchStrategy[list[list[float]]]:
    return st.lists(st.lists(coord, min_size=2, max_size=2), max_size=max_size)


def test_lean_examples() -> None:
    # Lean: the AlgoDesignTests/Geometry.lean scan examples, coordinate for coordinate.
    assert scan.nearest([], [0.0, 0.0]) is None
    assert scan.nearest([[5.0, 5.0], [1.0, 1.0], [9.0, 0.0]], [1.0, 1.0]) == 1
    assert scan.nearest([[1.0, 0.0], [4.0, 4.0], [-1.0, 0.0]], [0.0, 0.0]) == 0
    assert scan.nearest([[3.0, 3.0], [2.0, 2.0], [2.0, 2.0]], [2.0, 2.0]) == 1


@given(points_2d(), st.lists(coord, min_size=2, max_size=2))
def test_nearest_is_the_argmin_with_the_lowest_index(
    pts: list[list[float]], q: list[float]
) -> None:
    # Lean: scanNearest_le, scanNearest_lowest, scanNearest_mem, scanNearest_isSome_iff
    got = scan.nearest(pts, q)
    if not pts:
        assert got is None
        return
    assert got is not None
    best = min(sq_dist(p, q) for p in pts)
    assert sq_dist(pts[got], q) == best
    assert all(sq_dist(pts[i], q) > best for i in range(got))


@given(points_2d(), st.lists(coord, min_size=2, max_size=2), st.integers(0, 50))
def test_k_nearest_is_the_sorted_prefix(pts: list[list[float]], q: list[float], k: int) -> None:
    want = sorted((sq_dist(p, q), i) for i, p in enumerate(pts))[:k]
    assert scan.k_nearest(pts, q, k) == want


pair = st.lists(coord, min_size=2, max_size=2)


def test_k_nearest_among_breaks_ties_by_stored_index() -> None:
    # Points 1 and 2 are both at squared distance 4 from 0; listed 2 first, point 1, stored
    # first, still wins, as the Rust's `TopK` ranks by (distance, id).
    assert scan.k_nearest_among([[0.0], [2.0], [-2.0]], [2, 1], [0.0], 1) == [(4.0, 1)]
    assert scan.k_nearest_among([[0.0], [2.0], [-2.0]], [2, 1], [0.0], 2) == [(4.0, 1), (4.0, 2)]


def test_k_nearest_among_refuses_a_repeated_or_unknown_id() -> None:
    with pytest.raises(ValueError, match="twice"):
        scan.k_nearest_among([[0.0], [1.0]], [0, 0, 1], [0.0], 2)
    for bad in (2, -1):
        with pytest.raises(ValueError, match="not a point"):
            scan.k_nearest_among([[0.0], [1.0]], [0, bad], [0.0], 2)


@given(points_2d(), pair, st.integers(0, 50), st.randoms(use_true_random=False))
def test_k_nearest_among_is_the_sorted_prefix_of_the_candidates(
    pts: list[list[float]], q: list[float], k: int, rng: random.Random
) -> None:
    candidates = [i for i in range(len(pts)) if rng.random() < 0.5]
    rng.shuffle(candidates)
    want = sorted((sq_dist(pts[i], q), i) for i in candidates)[:k]
    assert scan.k_nearest_among(pts, candidates, q, k) == want


@given(points_2d(), pair, pair)
def test_in_box_is_the_coordinate_filter(
    pts: list[list[float]], lo: list[float], hi: list[float]
) -> None:
    want = [i for i, p in enumerate(pts) if all(lo[j] <= p[j] <= hi[j] for j in range(2))]
    assert scan.in_box(pts, lo, hi) == want


def test_invalid_input_is_rejected() -> None:
    pts = [[0.0, 0.0], [1.0, 1.0]]
    with pytest.raises(ValueError, match="dimension"):
        scan.nearest(pts, [0.0, 0.0, 0.0])
    with pytest.raises(ValueError, match="finite"):
        scan.nearest(pts, [math.nan, 0.0])
    with pytest.raises(ValueError, match="k"):
        scan.k_nearest(pts, [0.0, 0.0], -1)


def test_points_helpers() -> None:
    assert sq_dist([0.0, 0.0], [3.0, 4.0]) == 25.0
    assert dot([1.0, 2.0], [3.0, 4.0]) == 11.0
    assert normalized([[3.0, 4.0]]) == [[0.6, 0.8]]
    with pytest.raises(ValueError, match="zero"):
        normalized([[0.0, 0.0]])
    # Scaled by the largest coordinate first, as the Rust's, so huge and tiny vectors do not
    # overflow or underflow on the way to their length.
    assert normalized([[3e300, 4e300]]) == [[0.6, 0.8]]
    assert normalized([[3e-300, 4e-300]]) == [[0.6, 0.8]]


def test_sums_run_left_to_right_as_in_the_rust() -> None:
    # Python's sum() of floats is compensated (3.12 and later); the Rust's `dot` adds left to
    # right, and so does the library's, so a sum that cancels keeps the Rust's rounding.
    assert dot([1e16, 1.0, -1e16], [1.0, 1.0, 1.0]) == 0.0
    assert sq_dist([1e8, 1.0], [0.0, 0.0]) == 1e16


def test_the_oracle_rejects_bad_points_too() -> None:
    with pytest.raises(ValueError, match="finite"):
        scan.nearest([[math.nan], [1.0]], [1.0])
    with pytest.raises(ValueError, match="dimension"):
        scan.k_nearest([[0.0, 0.0], [1.0]], [0.0, 0.0], 1)
    with pytest.raises(ValueError, match="finite"):
        scan.in_box([[math.inf, 0.0]], [0.0, 0.0], [1.0, 1.0])


def test_normalized_refuses_a_coordinate_that_is_not_finite() -> None:
    for bad in (math.inf, -math.inf, math.nan):
        with pytest.raises(ValueError, match="not finite"):
            normalized([[1.0, 0.0], [bad, 1.0]])
