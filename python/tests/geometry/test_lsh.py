# SPDX-License-Identifier: Apache-2.0
"""Random projection and locality-sensitive hashing.

Mirrors the Rust's `projection::tests` and `lsh::tests` and the Lean's `LSH/`: projection is
linear (`dot_add`); whatever the hash family, LSH returns the nearest candidate
(`lshQuery_le_candidates`), and exactly the scan's answer when that answer collides
(`lshQuery_eq_scanNearest`); a SimHash bit is the orientation test in the plane
(`simBit_eq_orient`); points in one p-stable cell have shadows less than `w` apart
(`pStableKey_eq`). The collision probabilities and the Johnson-Lindenstrauss bound are not proved
in the Lean, so seeded statistical tests hold them, as in the Rust. The pinned values were printed by the Rust.
"""

from __future__ import annotations

import math
from collections.abc import Sequence

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.geometry import scan
from algodesign.geometry._rng import SplitMix64
from algodesign.geometry.lsh import (
    LSHIndex,
    PStable,
    SimHash,
    is_measured_exactly,
    p_stable_cell,
    sim_bit,
)
from algodesign.geometry.orientation import orient2d
from algodesign.geometry.point import dot, sq_dist
from algodesign.geometry.projection import GaussianProjection


class Quadrant:
    """The Lean examples' tables: the quadrant, (sign of x, sign of y), in each of two tables."""

    dim = 2
    tables = 2

    def key(self, table: int, v: Sequence[float]) -> tuple[bool, bool]:
        return (v[0] >= 0, v[1] >= 0)


def test_lean_examples() -> None:
    idx = LSHIndex([[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]], Quadrant())
    assert idx.nearest([4.0, 4.0]) == 0  # the true neighbor collides: exact
    assert idx.nearest([1.0, 1.0]) == 0  # the honest half: the true one (1) is missed
    assert idx.nearest([10.0, 10.0]) == 2  # a stored query finds itself
    assert LSHIndex([], Quadrant()).nearest([1.0, 1.0]) is None
    assert not sim_bit([1.0, 0.0], [-3.0, 7.0])


def test_the_seed_fixes_the_same_tables_as_the_rust() -> None:
    g = GaussianProjection(3, 2, 7)
    rust_columns = [
        [0.6989569034114226, -0.3742509013886548],
        [-1.3182279228060485, -0.32454052906316144],
        [0.002772005105516813, 0.32018871119029496],
    ]
    for j, column in enumerate(rust_columns):
        e = [1.0 if i == j else 0.0 for i in range(3)]
        for got, want in zip(g.project(e), column, strict=True):
            assert math.isclose(got, want, rel_tol=1e-15, abs_tol=0.0)
    s = SimHash(3, 4, 2, 5)
    p = PStable(3, 2, 2, 0.5, 9)

    def as_int(bits: tuple[bool, ...]) -> int:
        """The Rust's u64 key: bit i is plane i."""
        return sum(b << i for i, b in enumerate(bits))

    for v, sim, pst in [
        ([1.0, 2.0, 3.0], (8, 9), ((4, 5), (8, 0))),
        ([-0.5, 0.25, 4.0], (10, 9), ((5, 1), (4, -5))),
        ([3.0, -1.0, -2.0], (1, 2), ((-3, 7), (-3, -4))),
    ]:
        assert (as_int(s.key(0, v)), as_int(s.key(1, v))) == sim
        assert (p.key(0, v), p.key(1, v)) == pst


@given(
    st.lists(st.floats(-10, 10), min_size=3, max_size=3),
    st.lists(st.floats(-10, 10), min_size=3, max_size=3),
    st.floats(-10, 10),
)
def test_the_projection_is_linear(u: list[float], v: list[float], c: float) -> None:
    # Lean: dot_add -- each output coordinate is a dot product.
    g = GaussianProjection(3, 4, 1)
    combined = g.project([a + c * b for a, b in zip(u, v, strict=True)])
    separate = [a + c * b for a, b in zip(g.project(u), g.project(v), strict=True)]
    for x, y in zip(combined, separate, strict=True):
        assert math.isclose(x, y, rel_tol=1e-9, abs_tol=1e-9)


def test_pairwise_distances_survive_within_epsilon() -> None:
    # Statistical (JL, Dasgupta-Gupta), as the Rust's: 60 points in d = 400 projected to
    # k = 400; at most 2% of the 1770 pairs may be distorted beyond 30%.
    r = SplitMix64(3)
    pts = [[r.standard_normal() for _ in range(400)] for _ in range(60)]
    g = GaussianProjection(400, 400, 11)
    images = [g.project(p) for p in pts]
    pairs = [(i, j) for i in range(60) for j in range(i + 1, 60)]
    bad = sum(
        1
        for i, j in pairs
        if not 0.7 <= sq_dist(images[i], images[j]) / sq_dist(pts[i], pts[j]) <= 1.3
    )
    assert bad * 50 <= len(pairs)


def test_a_point_on_the_hyperplane_gets_bit_one() -> None:
    assert sim_bit([1.0, -1.0], [2.0, 2.0])


def test_same_cell_means_close_shadows() -> None:
    # Lean: pStableKey_eq -- one cell means projections less than w apart.
    r = SplitMix64(13)
    a = [r.standard_normal() for _ in range(3)]
    b, w = 0.3, 0.5
    pts = [[r.standard_normal() * 3 for _ in range(3)] for _ in range(300)]
    for p in pts:
        for q in pts:
            if p_stable_cell(a, b, w, p) == p_stable_cell(a, b, w, q):
                assert abs(dot(a, p) - dot(a, q)) < w


def test_sim_bit_is_orientation_in_the_plane() -> None:
    # Lean: simBit_eq_orient -- the bit for normal r is the orientation of p against the line
    # through the origin along (r1, -r0).
    g = SplitMix64(5)
    for _ in range(1000):
        r = [g.standard_normal(), g.standard_normal()]
        p = [g.standard_normal(), g.standard_normal()]
        assert sim_bit(r, p) == (orient2d((0.0, 0.0), (r[1], -r[0]), (p[0], p[1])) >= 0)


def test_simhash_collides_at_rate_one_minus_angle_over_pi() -> None:
    # Statistical (Charikar 2002): at angle pi/3 a bit is shared with probability 2/3; over
    # 20 000 seeded planes the standard error is 0.0033, and 0.015 is over four of them.
    theta = math.pi / 3
    u, v = [1.0, 0.0, 0.0], [math.cos(theta), math.sin(theta), 0.0]
    h = SimHash(3, 1, 20_000, 17)
    same = sum(h.key(t, u) == h.key(t, v) for t in range(20_000)) / 20_000
    assert abs(same - 2 / 3) < 0.015


def datar_rate(ratio: float) -> float:
    """Datar et al. 2004, the Gaussian case: the chance that two points at distance c share a
    cell of width w, as a function of w/c."""
    phi = 0.5 * (1 + math.erf(-ratio / math.sqrt(2)))
    return 1 - 2 * phi - 2 / (math.sqrt(2 * math.pi) * ratio) * (1 - math.exp(-(ratio**2) / 2))


def test_p_stable_collides_at_the_datar_rate() -> None:
    # Statistical: at w/c = 4, p is about 0.8006; standard error 0.0028 over 20 000 tables.
    h = PStable(2, 1, 20_000, 4.0, 23)
    same = sum(h.key(t, [0.0, 0.0]) == h.key(t, [1.0, 0.0]) for t in range(20_000)) / 20_000
    assert abs(same - datar_rate(4.0)) < 0.015


coord = st.integers(-6, 6).map(float)
pts_3d = st.lists(st.lists(coord, min_size=3, max_size=3), max_size=50)


@given(pts_3d, st.lists(coord, min_size=3, max_size=3))
def test_exact_when_the_neighbor_collides(pts: list[list[float]], q: list[float]) -> None:
    # Lean: lshQuery_eq_scanNearest
    idx = LSHIndex(pts, SimHash(3, 2, 3, 1))
    truth = scan.nearest(pts, q)
    if truth is not None and truth in idx.candidates(q):
        assert idx.nearest(q) == truth


@given(pts_3d, st.lists(coord, min_size=3, max_size=3), st.integers(0, 6))
def test_the_answer_beats_every_candidate(pts: list[list[float]], q: list[float], k: int) -> None:
    # Lean: lshQuery_le_candidates -- the exact re-rank of the candidates.
    idx = LSHIndex(pts, PStable(3, 2, 3, 2.0, 1))
    candidates = idx.candidates(q)
    want = sorted((sq_dist(pts[i], q), i) for i in candidates)[:k]
    assert idx.k_nearest(q, k) == want


@given(st.lists(st.lists(st.integers(-8, 7).map(float), min_size=2, max_size=2), min_size=1,
                max_size=60), st.integers(0, 59), st.integers(0, 2**64 - 1))
def test_a_stored_query_is_its_own_candidate(pts: list[list[float]], i: int, seed: int) -> None:
    # A stored point shares its own key in every table, so it is a candidate and its own answer.
    i %= len(pts)
    idx = LSHIndex(pts, SimHash(2, 3, 2, seed))
    assert i in idx.candidates(pts[i])
    assert idx.k_nearest(pts[i], 1)[0][0] == 0.0


def test_invalid_parameters_are_rejected() -> None:
    with pytest.raises(ValueError, match="bits"):
        SimHash(3, 0, 1, 0)
    with pytest.raises(ValueError, match="w"):
        PStable(3, 1, 1, 0.0, 0)
    with pytest.raises(ValueError, match="dimension"):
        LSHIndex([[0.0, 0.0]], SimHash(3, 2, 1, 0))
    with pytest.raises(ValueError, match="k"):
        GaussianProjection(3, 0, 0)


@given(pts_3d, st.lists(coord, min_size=3, max_size=3))
def test_the_candidates_are_every_point_sharing_a_key(
    pts: list[list[float]], q: list[float]
) -> None:
    # The candidates' definition, which the two theorems above are about: the points that share
    # q's key in at least one table.
    family = SimHash(3, 2, 4, 3)
    want = [
        i for i, p in enumerate(pts) if any(family.key(t, p) == family.key(t, q) for t in range(4))
    ]
    assert LSHIndex(pts, family).candidates(q) == want


def test_at_least_one_table() -> None:
    with pytest.raises(ValueError, match="tables"):
        SimHash(2, 4, 0, 0)
    with pytest.raises(ValueError, match="tables"):
        PStable(2, 1, 0, 1.0, 0)


class OneQuadrant:
    """The Lean `lshWith` examples' one table: the quadrant."""

    dim = 2
    tables = 1

    def key(self, table: int, v: Sequence[float]) -> tuple[bool, bool]:
        return (v[0] >= 0, v[1] >= 0)


def quadrant_with(buckets: dict[tuple[bool, bool], list[int]]) -> LSHIndex:
    idx = LSHIndex([[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]], OneQuadrant())
    idx.buckets = [{key: ids for key, ids in buckets.items()}]
    return idx


def test_in_its_bucket_fails_alone_on_each_defect() -> None:
    # Lean: the AlgoDesignTests/Geometry.lean `lshWith` examples
    good = LSHIndex([[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]], OneQuadrant())
    assert good.is_valid() and good.buckets[0][(True, True)] == [0, 2]
    for broken in [
        {(True, True): [0], (False, True): [1, 2]},  # another key's bucket
        {(True, True): [0, 2, 3], (False, True): [1]},  # past the points
        {(True, True): [0], (False, True): [1]},  # a point missing
    ]:
        idx = quadrant_with(broken)
        assert not idx.is_in_its_bucket()
        assert idx.check_valid() == "invariant 1 (in_its_bucket)"
    good.buckets = []
    assert not good.is_in_its_bucket()


def test_each_extra_lsh_piece_fails_alone() -> None:
    # An empty bucket: every point is still in its own, once.
    empty = quadrant_with({(True, True): [0, 2], (False, True): [1], (False, False): []})
    assert empty.is_in_its_bucket() and empty.is_each_point_once_per_table()
    assert not empty.is_one_bucket_per_key()
    assert empty.check_valid() == "not in the box (one_bucket_per_key)"
    # A point stored twice in its own bucket: in it, but not once.
    twice = quadrant_with({(True, True): [0, 2, 0], (False, True): [1]})
    assert twice.is_in_its_bucket() and twice.is_one_bucket_per_key()
    assert not twice.is_each_point_once_per_table()
    assert twice.check_valid() == "not in the box (each_point_once_per_table)"


def test_measured_exactly_on_the_lean_examples() -> None:
    # Lean: the AlgoDesignTests/Geometry.lean `MeasuredExactly` examples
    idx = LSHIndex([[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]], OneQuadrant())
    q = [9.0, 9.0]
    assert is_measured_exactly(idx, q, 1, [2])
    assert not is_measured_exactly(idx, q, 1, [0])  # a farther candidate
    assert not is_measured_exactly(idx, q, 2, [2, 2])  # a repeat
    assert not is_measured_exactly(idx, q, 2, [2])  # short
    assert not is_measured_exactly(idx, q, 1, [1])  # not a candidate
    assert not is_measured_exactly(idx, [9.0], 1, [2])  # wrong dimension
    assert is_measured_exactly(idx, q, 0, [])
    # a candidate past the points cannot be measured: every answer fails
    past = quadrant_with({(True, True): [0, 2, 7], (False, True): [1]})
    assert not is_measured_exactly(past, [1.0, 1.0], 1, [7])
    assert not is_measured_exactly(past, [1.0, 1.0], 1, [0])


@given(pts_3d, st.lists(coord, min_size=3, max_size=3), st.integers(0, 6))
def test_the_build_and_every_answer_keep_the_box(
    pts: list[list[float]], q: list[float], k: int
) -> None:
    # Lean: valid_build, measuredExactly_kNearest
    for family in (SimHash(3, 2, 3, 1), PStable(3, 1, 2, 2.0, 1)):
        idx = LSHIndex(pts, family)
        assert idx.is_valid()
        assert is_measured_exactly(idx, q, k, [i for _, i in idx.k_nearest(q, k)])


class OneQuadrant3:
    """The `lshWith` family, but hashing points of dimension 3."""

    dim = 3
    tables = 1

    def key(self, table: int, v: Sequence[float]) -> tuple[bool, bool]:
        return (v[0] >= 0, v[1] >= 0)


def test_measured_exactly_reads_the_points_dimension() -> None:
    # An unchecked index whose family hashes dimension 3 over points of dimension 2: the query's
    # dimension is checked against the points', as in the Rust.
    idx = LSHIndex([[5.0, 5.0], [-1.0, 1.0], [10.0, 10.0]], OneQuadrant())
    idx.family = OneQuadrant3()
    assert not is_measured_exactly(idx, [9.0, 9.0, 0.0], 1, [2])
    assert is_measured_exactly(idx, [9.0, 9.0], 1, [2])
