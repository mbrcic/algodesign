# SPDX-License-Identifier: Apache-2.0
"""RaBitQ: one bit per coordinate, a random rotation, an unbiased estimate, and an exact check.

Mirrors the Rust's `rabitq::tests`. The estimator's error bound (Gao-Long Theorem 3.2) is
probabilistic and not proved in the Lean, so its unbiasedness is held statistically here, as in
the Rust. The Python's query is not quantized (`quantize_query` returns it unchanged), so these
are the estimator's own properties, not those of the Rust's 4-bit path.
"""

from __future__ import annotations

import math
from collections.abc import Sequence

import pytest

from algodesign.geometry import scan
from algodesign.geometry._rng import SplitMix64
from algodesign.geometry.hnsw import HNSW
from algodesign.geometry.point import normalized, sq_dist
from algodesign.geometry.rabitq import (
    PreparedQuery,
    RaBitQ,
    SignCodes,
    random_orthogonal,
    search_quantized,
)


def gaussian(n: int, d: int, seed: int) -> list[list[float]]:
    r = SplitMix64(seed)
    return [[r.standard_normal() for _ in range(d)] for _ in range(n)]


def test_the_rotation_is_orthogonal() -> None:
    rows = random_orthogonal(16, 7)
    for i in range(16):
        for j in range(16):
            d = sum(a * b for a, b in zip(rows[i], rows[j], strict=True))
            assert abs(d - (1.0 if i == j else 0.0)) < 1e-9


def test_the_estimator_is_unbiased_in_the_mean() -> None:
    # Statistical (Theorem 3.2, Eq. 13). Data {o, -o} has centroid 0, so o is its own normalized
    # vector; o = e1 and q = 0.6 e1 + 0.8 e2, so <o, q> = 0.6 exactly. One estimate in D = 16 errs
    # by about 0.25, so over 1000 seeded rotations the mean's standard error is about 0.008, and
    # 0.04 is five of them. The uncorrected, unrotated sign code gives <(1, ..., 1)/4, q> = 0.35
    # for every seed: biased by 0.25.
    d = 16
    o = [1.0] + [0.0] * (d - 1)
    pts = [o, [-x for x in o]]
    q = [0.6, 0.8] + [0.0] * (d - 2)
    total = 0.0
    for seed in range(1000):
        r = RaBitQ(pts, seed)
        total += r.estimate_inner(r.prepare(q), 0)
    mean = total / 1000
    assert abs(mean - 0.6) < 0.04
    s = SignCodes(pts)
    assert abs(s.estimate_inner(s.prepare(q), 0) - 0.6) > 0.2


def test_a_vector_at_the_centroid_is_estimated_exactly() -> None:
    r = RaBitQ([[1.0, 1.0], [-1.0, -1.0], [0.0, 0.0]], 1)
    assert math.isclose(r.estimate_sq_dist(r.prepare([3.0, 4.0]), 2), 25.0, rel_tol=1e-12)


def test_a_query_at_the_centroid_is_estimated_exactly() -> None:
    # The query's own norm is 0, so Eq. 2 leaves only ||o - c||**2: no estimate is involved.
    pts = gaussian(20, 8, 4)
    r = RaBitQ(pts, 2)
    centroid = [sum(p[j] for p in pts) / 20 for j in range(8)]
    query = r.prepare(centroid)
    for i, p in enumerate(pts):
        assert math.isclose(r.estimate_sq_dist(query, i), sq_dist(p, centroid), rel_tol=1e-9)


def test_identical_points_are_all_at_the_centroid() -> None:
    r = RaBitQ([[2.0, -1.0, 0.5]] * 5, 3)
    query = r.prepare([0.0, 0.0, 0.0])
    assert all(math.isclose(r.estimate_sq_dist(query, i), 5.25) for i in range(5))


def test_estimates_track_distances() -> None:
    # Not a bound (that is probabilistic): on 500 Gaussian points in D = 128 the estimated
    # squared distances correlate with the exact ones above 0.8, as in the Rust's test.
    pts = gaussian(500, 128, 3)
    q = gaussian(1, 128, 4)[0]
    r = RaBitQ(pts, 5)
    query = r.prepare(q)
    est = [r.estimate_sq_dist(query, i) for i in range(500)]
    exact = [sq_dist(p, q) for p in pts]
    me, mx = sum(est) / 500, sum(exact) / 500
    cov = sum((a - me) * (b - mx) for a, b in zip(est, exact, strict=True))
    var_e = sum((a - me) ** 2 for a in est)
    var_x = sum((b - mx) ** 2 for b in exact)
    assert cov / math.sqrt(var_e * var_x) > 0.8


def test_quantize_query_returns_the_query_unchanged() -> None:
    # In the Python the query's quantization is a black box that may be
    # the identity; the Rust's is Gao-Long's 4-bit randomized quantization.
    r = RaBitQ(gaussian(10, 6, 1), 1)
    v = [0.5, -0.25, 0.125, 1.0, 0.0, -2.0]
    assert r.quantize_query(v) == v


def test_the_exact_check_makes_every_returned_distance_exact() -> None:
    # The box's claim: a cheap filter, then an exact check, so the returned distances and their
    # order are exact among the candidates the walk kept.
    pts = normalized(gaussian(400, 16, 4))
    h = HNSW(pts, m=8, ef_construction=64, seed=1)
    q = normalized(gaussian(1, 16, 5))[0]
    for codes in (RaBitQ(pts, 9), SignCodes(pts)):
        found = search_quantized(h, q, 10, 100, codes)
        assert len(found) == 10
        assert found == sorted(found)
        assert all(d == sq_dist(pts[i], q) for d, i in found)
    assert search_quantized(h, q, 1, 200, RaBitQ(pts, 9))[0][1] == scan.nearest(pts, q)
    assert search_quantized(h, q, 0, 200, RaBitQ(pts, 9)) == []


class HigherIndexFirst:
    """An estimator that ranks every node by its index, highest nearest: the walk then lists tied
    points in falling index order."""

    def __init__(self, points: list[list[float]]) -> None:
        self.norms = [0.0] * len(points)

    def prepare(self, q: Sequence[float]) -> PreparedQuery:
        return PreparedQuery(list(q), 0.0)

    def estimate_sq_dist(self, query: PreparedQuery, i: int) -> float:
        return -float(i)


def test_the_exact_check_breaks_ties_by_stored_index() -> None:
    # Duplicate points tie exactly; the walk hands them over highest index first, and the answer
    # still takes the lowest, as the Rust's does.
    pts = [[1.0, 0.0]] * 3 + [[5.0, 5.0]]
    h = HNSW(pts, m=4, seed=0)
    codes = HigherIndexFirst(pts)
    walked = h.search_by(lambda i: codes.estimate_sq_dist(codes.prepare([0.0, 0.0]), i), 4)
    assert [i for _, i in walked] == [3, 2, 1, 0]
    assert search_quantized(h, [0.0, 0.0], 1, 4, codes) == [(1.0, 0)]
    assert search_quantized(h, [0.0, 0.0], 2, 4, codes) == [(1.0, 0), (1.0, 1)]


def test_contracts() -> None:
    with pytest.raises(ValueError, match="at least one point"):
        RaBitQ([], 0)
    r = RaBitQ([[0.0, 1.0], [1.0, 0.0]], 0)
    with pytest.raises(ValueError, match="dimension"):
        r.prepare([0.0])
    # Encoding copies what it needs: changing the caller's list afterwards changes nothing.
    pts = [[0.0, 1.0], [1.0, 0.0]]
    r = RaBitQ(pts, 0)
    before = r.estimate_sq_dist(r.prepare([0.5, 0.5]), 0)
    pts[0][1] = 50.0
    assert r.estimate_sq_dist(r.prepare([0.5, 0.5]), 0) == before


def test_codes_must_encode_the_graphs_points() -> None:
    pts = normalized(gaussian(30, 4, 1))
    h = HNSW(pts, m=4)
    with pytest.raises(ValueError, match="encode"):
        search_quantized(h, pts[0], 3, 10, RaBitQ(pts[:20], 1))
