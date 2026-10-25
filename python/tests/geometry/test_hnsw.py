# SPDX-License-Identifier: Apache-2.0
"""HNSW: Malkov and Yashunin's graph, with the book's tie rule and the flat graph as one level.

Mirrors the Rust's `hnsw::tests` and the Lean's `GraphIndex/`: every graph is `HNSW.Valid` and
every picking `PicksDiverse` (`picksDiverse_selectNeighbors`); the neighbor rule keeps a
diverse set (`selectNeighbors_diverse`) of at most M (`selectNeighbors_length_le`) of the
candidates (`selectNeighbors_subset`), the nearest first (`selectNeighbors_head`); a greedy step
never moves away from the query (`greedyStep_le`). No search guarantee exists for this variant, so
recall is measured, not proved.

That the Python builds **the Rust's graph** -- the same levels, the same neighbor lists, the same
search answers, on integer and on Gaussian coordinates -- is a separate Rust–Python check's to
show.
"""

from __future__ import annotations

import math
from collections.abc import Sequence

import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

import algodesign.geometry.hnsw as hnsw_module
from algodesign.geometry import scan
from algodesign.geometry._rng import SplitMix64
from algodesign.geometry.hnsw import (
    HNSW,
    check_picking_valid,
    finish,
    greedy_step,
    is_picks_diverse,
    select_neighbors,
)
from algodesign.geometry.point import normalized, sq_dist

coord = st.integers(-5, 5).map(float)
pts_2d = st.lists(st.lists(coord, min_size=2, max_size=2), min_size=1, max_size=30)


def by_distance(points: list[list[float]], base: list[float]) -> list[tuple[float, int]]:
    return sorted((sq_dist(p, base), i) for i, p in enumerate(points))


def test_lean_examples() -> None:
    # Lean: AlgoDesignTests/Geometry.lean. Candidates nearest-first: (1, 0) at 1, (0, 2) at 4,
    # (2, 0) at 4; (2, 0) is nearer to the kept (1, 0) than to the base, so it is dropped.
    pts = [[1.0, 0.0], [0.0, 2.0], [2.0, 0.0]]
    base = [0.0, 0.0]
    assert select_neighbors(pts, base, by_distance(pts, base), 3) == [0, 1]
    assert select_neighbors(pts, base, by_distance(pts, base), 1) == [0]
    # A tie keeps the candidate, as hnswlib does: (1, 2) is as near (2, 0) as the base is.
    tie = [[2.0, 0.0], [1.0, 2.0]]
    assert select_neighbors(tie, base, by_distance(tie, base), 2) == [0, 1]


# Under load one draw can stall past Hypothesis's input-generation time check. The timing checks
# guard the test's speed, not its verdict, so they are off here; the same inputs are drawn.
@settings(deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(pts_2d, st.lists(coord, min_size=2, max_size=2), st.integers(1, 6))
def test_the_rule_keeps_a_diverse_nearest_first_subset(
    pts: list[list[float]], base: list[float], m: int
) -> None:
    # Lean: selectNeighbors_diverse, _length_le, _subset, _head
    candidates = by_distance(pts, base)
    kept = select_neighbors(pts, base, candidates, m)
    assert len(kept) <= m
    assert set(kept) <= {i for _, i in candidates}
    assert kept[0] == candidates[0][1]
    for a, earlier in enumerate(kept):
        for later in kept[a + 1 :]:
            assert sq_dist(pts[later], base) <= sq_dist(pts[later], pts[earlier])


@given(pts_2d, st.lists(coord, min_size=2, max_size=2), st.integers(0, 29))
def test_a_greedy_step_never_moves_away(
    pts: list[list[float]], q: list[float], start: int
) -> None:
    # Lean: greedyStep_le
    cur = start % len(pts)
    nxt = greedy_step(pts, q, cur, list(range(len(pts))))
    assert sq_dist(pts[nxt], q) <= sq_dist(pts[cur], q)


def unit_vectors(n: int, d: int, seed: int) -> list[list[float]]:
    r = SplitMix64(seed)
    return normalized([[r.standard_normal() for _ in range(d)] for _ in range(n)])


def test_degrees_and_nested_layers() -> None:
    h = HNSW(unit_vectors(300, 8, 1), m=6, ef_construction=40, seed=2)
    for v in range(300):
        for level, neighbors in enumerate(h.links[v]):
            assert len(neighbors) <= (h.m0 if level == 0 else h.m)
            assert all(h.level(u) >= level for u in neighbors)
            assert v not in neighbors


def test_the_flat_graph_is_one_level() -> None:
    h = HNSW(unit_vectors(200, 8, 1), m=6, flat=True)
    assert all(h.level(v) == 0 for v in range(200))
    assert h.max_level == 0


def test_recall_against_the_scan() -> None:
    # A floor, not a pin: the pins live in the Rust's tests. 300 unit vectors in d = 8.
    pts = unit_vectors(300, 8, 1)
    h = HNSW(pts, m=8, ef_construction=64, seed=2)
    queries = unit_vectors(50, 8, 9)
    hits = 0
    for q in queries:
        truth = {i for _, i in scan.k_nearest(pts, q, 10)}
        hits += len(truth & {i for _, i in h.search(q, 10, ef=50)})
    assert hits / 500 >= 0.9


def test_edge_cases_and_contracts() -> None:
    assert HNSW([], m=4).search([0.0, 0.0], 3, ef=10) == []
    h = HNSW([[0.0, 0.0], [1.0, 1.0]], m=4)
    assert h.search([0.0, 0.0], 0, ef=10) == []
    assert len(h.search([0.0, 0.0], 9, ef=1)) == 2
    pts = [[0.0, 0.0], [1.0, 1.0]]
    h = HNSW(pts, m=4)
    pts[0][0] = 99.0
    assert h.search([0.0, 0.0], 1, ef=4)[0][1] == 0
    with pytest.raises(ValueError, match="M"):
        HNSW([[0.0, 0.0]], m=1)
    with pytest.raises(ValueError, match="k"):
        h.search([0.0, 0.0], -1, ef=4)
    with pytest.raises(ValueError, match="dimension"):
        h.search([0.0], 1, ef=4)
    assert math.isclose(HNSW([[0.0]], m=16).ml, 1 / math.log(16))


def test_ef_construction_must_be_positive() -> None:
    with pytest.raises(ValueError, match="ef_construction"):
        HNSW([[0.0, 0.0], [1.0, 1.0]], m=4, ef_construction=0)


Picking = tuple[bool, list[float], list[int], int, list[int]]


def watch_pickings(monkeypatch: pytest.MonkeyPatch) -> list[Picking]:
    """Record every picking the builds make from now on, without the class knowing: `insert`
    calls the module's `select_neighbors`, so the test wraps it. Each picking is recorded as
    (whether it picks a new node's list, the base point, the candidates nearest first, the cap,
    the picks); a picking that is not a new node's re-picks a list a back-link overfilled."""
    pickings: list[Picking] = []
    real_insert, real_select = hnsw_module.HNSW.insert, hnsw_module.select_neighbors
    inserting: list[Sequence[float]] = []

    def insert(self: HNSW, v: int, level: int) -> None:
        inserting[:] = [self.points[v]]
        real_insert(self, v, level)

    def select(points: Sequence[Sequence[float]], base: Sequence[float],
               candidates: list[tuple[float, int]], m: int) -> list[int]:
        picked = real_select(points, base, candidates, m)
        new = bool(inserting) and base is inserting[0]
        pickings.append((new, list(base), [c for _, c in candidates], m, list(picked)))
        return picked

    monkeypatch.setattr(hnsw_module.HNSW, "insert", insert)
    monkeypatch.setattr(hnsw_module, "select_neighbors", select)
    return pickings


def grid(n: int, seed: int) -> list[list[float]]:
    r = SplitMix64(seed)
    return [[math.floor(r.next_f64() * 7), math.floor(r.next_f64() * 7)] for _ in range(n)]


@pytest.mark.parametrize("seed", range(10))
def test_every_graph_is_valid_and_every_picking_diverse(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    pickings = watch_pickings(monkeypatch)
    re_picks = 0
    for m in (2, 3):
        for flat in (False, True):
            pickings.clear()
            points = grid(30, seed)
            h = HNSW(points, m=m, ef_construction=4, seed=seed, flat=flat)
            assert h.check_valid() is None
            assert h.entry is not None and h.level(h.entry) == h.max_level
            assert pickings, "the build made no picking"
            for new, base, candidates, cap, picked in pickings:
                assert check_picking_valid(points, base, candidates, picked, cap) is None
                re_picks += not new
    assert re_picks > 0


def test_the_picking_piece_fails_where_it_should() -> None:
    points = [[2.0, 0.0], [1.0, 2.0], [1.0, 0.0], [2.0, 0.0]]
    base = [0.0, 0.0]
    assert is_picks_diverse(points, base, [0, 1], [0, 1], 2)  # the tie kept
    assert not is_picks_diverse(points, base, [0, 1], [0], 2)  # the tie dropped
    assert not is_picks_diverse(points, base, [0, 1], [1, 0], 2)
    assert is_picks_diverse(points, base, [0, 1], [0], 1)
    assert not is_picks_diverse(points, base, [1, 0], [1, 0], 2)
    assert is_picks_diverse(points, base, [2, 0], [2], 3)
    assert not is_picks_diverse(points, base, [2, 0], [2, 0], 3)
    assert is_picks_diverse(points, base, [0, 1], [3, 1], 2)  # same point, other index
    assert not is_picks_diverse(points, base, [9], [], 1)
    assert check_picking_valid(points, base, [0, 1], [0], 2) == "invariant 2 (picks_diverse)"


def test_each_graph_piece_fails_alone() -> None:
    def graph(links: list[list[list[int]]], entry: int | None, m0: int = 4) -> HNSW:
        h = HNSW([[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]], m=2)
        h.links, h.entry, h.m0 = links, entry, m0
        return h

    good = [[[1, 2], []], [[0, 2]], [[0, 1]]]
    assert graph(good, 0).check_valid() is None
    assert graph(good, 0, m0=1).check_valid() == "invariant 1 (degree_bounded)"
    assert graph([[[1, 2], [1]], [[0, 2]], [[0, 1]]], 0).check_valid() == \
        "invariant 3 (nested_layers)"
    assert graph([[[1, 7]], [[0]], [[0]]], 0).check_valid() == "invariant 3 (nested_layers)"
    assert graph([[[]], [], [[]]], 0).check_valid() == "invariant 3 (nested_layers)"
    assert graph([[[0]], [[]], [[]]], 0).check_valid() == "not in the box (no_self_links)"
    assert graph([[[1, 1]], [[0]], [[]]], 0).check_valid() == \
        "not in the box (no_repeated_links)"
    # Node 1 is on fewer layers than node 0, so it is no entry; no entry with nodes is none.
    assert graph(good, 1).check_valid() == "not in the box (entry_on_top)"
    assert graph(good, None).check_valid() == "not in the box (entry_on_top)"
    # Two nodes over three points: the third point has no node.
    assert graph([[[1]], [[0]]], 0).check_valid() == "not in the box (one_node_per_point)"


def test_search_ends_with_finish() -> None:
    assert finish([(9.0, 0), (1.0, 2), (1.0, 1)], 2) == [(1.0, 1), (1.0, 2)]
    assert finish([(1.0, 0)], 0) == []
