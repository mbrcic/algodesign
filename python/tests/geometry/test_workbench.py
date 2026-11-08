# SPDX-License-Identifier: Apache-2.0
"""The design project's bench: the reference is the scan, the counts count what they say, the
corpora come back the same from the same seed, and each kind of cheating is caught."""

from __future__ import annotations

import functools
import math
from array import array
from collections import deque

import pytest

from algodesign.geometry import scan
from algodesign.geometry import workbench as wb
from algodesign.geometry.point import sq_dist

N, QUERIES = 300, 8
SEED = 0x5EED_1234_ABCD_0042  # a judge's seed: 64 bits, nowhere in the library


def _judge(*entries: wb.Entry, families: tuple[str, ...] = ("clusters",)) -> list[wb.Verdict]:
    return wb.judge(list(entries), [SEED], families, n=N, queries=QUERIES)


def _failure(make: wb.Make) -> str | None:
    return _judge(wb.Entry("candidate", make))[0].seeds[0].failure


# --- The reference --------------------------------------------------------------------------


@pytest.mark.parametrize("family", list(wb.FAMILIES))
def test_the_reference_is_the_scan(family: str) -> None:
    corpus = wb.generate(family, 7, n=N, queries=QUERIES)
    for q in corpus.queries:
        assert wb.reference(corpus.points, q, wb.K) == scan.k_nearest(corpus.points, q, wb.K)


def test_the_reference_breaks_ties_by_the_lower_index() -> None:
    points = [[3.0, 0.0], [1.0, 0.0], [0.0, 2.0], [1.0, 0.0]]
    assert wb.reference(points, [0.0, 0.0], 2) == [(1.0, 1), (1.0, 3)]
    assert wb.reference(points, [0.0, 0.0], 9) == scan.k_nearest(points, [0.0, 0.0], 9)
    assert wb.reference([], [0.0, 0.0], 3) == []


def test_the_scan_as_a_candidate_has_recall_one_at_n_distances_and_fails_on_cost() -> None:
    [verdict] = _judge(wb.Entry("scan", wb.scan_candidate), families=tuple(wb.FAMILIES))
    for s in verdict.seeds:
        assert s.failure is None and s.recall == 1.0
        assert s.distances == N and s.dots == 0 and s.build_ticks == 0
    assert not verdict.passes()
    assert "more than half the scan's distances" in wb.report(verdict)


def test_the_scan_judges_the_same_trusted_or_not() -> None:
    """The scan holds nothing, so judged as one of the library's own it reports no memory, and
    untrusted the bench's own count finds nothing to charge either."""
    [trusted] = _judge(wb.Entry("scan", wb.scan_candidate, trusted=True))
    [untrusted] = _judge(wb.Entry("scan", wb.scan_candidate))
    for t, u in zip(trusted.seeds, untrusted.seeds, strict=True):
        assert t.failure is None and t.recall == 1.0 and t.memory == 0
        assert (t.recall, t.distances) == (u.recall, u.distances)


def test_the_graph_index_candidate_takes_the_graph_index_defaults() -> None:
    """`hnsw_candidate` builds `HNSW` with `HNSW`'s own `ef_construction` and argument order."""
    import inspect

    from algodesign.geometry.hnsw import HNSW

    graph = inspect.signature(HNSW).parameters
    made = inspect.signature(wb.hnsw_candidate).parameters
    assert made["ef_construction"].default == graph["ef_construction"].default
    assert [p for p in made if p in graph] == [p for p in graph if p in made]


# --- Recall, as the Lean `recallAt` states it -----------------------------------------------


def test_recall_agrees_with_the_lean_examples() -> None:
    points = [[3.0, 0.0], [1.0, 0.0], [0.0, 2.0], [1.0, 0.0]]
    q = [0.0, 0.0]
    truth = [d for d, _ in wb.reference(points, q, len(points))]

    def dist(i: int) -> float:
        return sq_dist(points[i], q)

    # equal points are distinct indices: either order of the two copies has recall 1
    assert wb.recall([(1.0, 3), (1.0, 1)], truth, 2, dist) == 1.0
    assert wb.recall([(1.0, 1), (9.0, 0)], truth, 2, dist) == 0.5
    assert wb.recall([], truth, 2, dist) == 0.0
    # a tie at the k-th distance counts whichever point is answered
    ring = [[1.0, 0.0], [0.0, 1.0], [-1.0, 0.0]]
    ring_truth = [d for d, _ in wb.reference(ring, q, 3)]
    assert wb.recall([(1.0, 2), (1.0, 1)], ring_truth, 2, lambda i: sq_dist(ring[i], q)) == 1.0
    # nothing wanted: no points, or k = 0
    assert wb.recall([], [], 3, dist) == 1.0
    assert wb.recall([], truth, 0, dist) == 1.0


# --- The contract, piece by piece -----------------------------------------------------------


def test_each_contract_piece_fails_alone() -> None:
    points = [[3.0, 0.0], [1.0, 0.0], [0.0, 2.0], [1.0, 0.0]]

    def dist(i: int) -> float:
        return sq_dist(points[i], [0.0, 0.0])

    good: wb.Answer = [(1.0, 1), (1.0, 3), (4.0, 2)]
    assert wb.check_answer(good, 3, 4, dist) is None
    assert wb.check_answer(good, 2, 4, dist) == "contract (up_to_k)"
    assert wb.check_answer([(1.0, 1), (0.0, 4)], 3, 4, dist) == "contract (stored)"
    assert wb.check_answer([(1.0, 1), (1.0, 1)], 3, 4, dist) == "contract (each_once)"
    assert wb.check_answer([(4.0, 2), (1.0, 1)], 3, 4, dist) == "contract (nearest_first)"
    assert wb.check_answer([(1.0, 1), (2.0, 3)], 3, 4, dist) == "contract (exact_distance)"
    assert wb.check_answer([(1, 1)], 3, 4, dist) is not None  # an int distance
    assert all(f(good) for f in (wb.is_each_once, wb.is_nearest_first))
    assert wb.is_up_to_k(good, 3) and wb.is_stored(good, 4) and wb.is_exact_distance(good, dist)


# --- The counted cost and the masked store --------------------------------------------------


def test_every_distance_and_inner_product_is_counted_and_exact() -> None:
    corpus = wb.generate("clusters", 5, n=20, queries=1)
    store = wb._Store(corpus.points)
    meter = wb.Meter()
    points = wb.Points(store, meter)
    query = wb.Query(store, store.scaled(corpus.queries[0]), meter)
    assert store.rows != corpus.points  # stored scaled, not as they are
    assert points.dist(2, 7) == sq_dist(corpus.points[2], corpus.points[7])
    assert query.dist(3) == sq_dist(corpus.points[3], corpus.queries[0])
    axis = [float(t == 4) for t in range(wb.DIM)]
    assert points.dot(5, axis) == corpus.points[5][4]
    assert query.dot(axis) == corpus.queries[0][4]
    assert (meter.distances, meter.dots, meter.ticks()) == (2, 2, 4)
    assert not hasattr(points, "meter") and not hasattr(query, "meter")
    wb.charge(query, -5)  # charging can only add
    assert meter.distances == 2
    with pytest.raises(ValueError):
        query.dot([1.0, 2.0])
    with pytest.raises(ValueError):
        points.dot(0, [math.nan] * wb.DIM)


# --- The corpora ----------------------------------------------------------------------------


@pytest.mark.parametrize("family", list(wb.FAMILIES))
def test_each_family_is_deterministic(family: str) -> None:
    a = wb.generate(family, SEED, n=50, queries=5)
    b = wb.generate(family, SEED, n=50, queries=5)
    c = wb.generate(family, SEED + 1, n=50, queries=5)
    assert a == b and a != c
    assert len(a.points) == 50 and len(a.queries) == 5
    assert all(len(p) == wb.DIM for p in a.points + a.queries)


def test_the_skewed_family_has_near_copies() -> None:
    corpus = wb.generate("skewed", 3, n=400, queries=1)
    nearest_other = [
        min(sq_dist(p, r) for j, r in enumerate(corpus.points) if j != i)
        for i, p in enumerate(corpus.points[:200])
    ]
    assert sum(d < 1e-9 for d in nearest_other) >= 5


def test_no_hidden_seed_is_reachable_from_the_candidates_side() -> None:
    """The library holds only the practice seeds, and nothing a candidate is handed holds the
    judge's seed."""
    names = {name for name, value in vars(wb).items()
             if isinstance(value, (int, tuple, list)) and not isinstance(value, bool)
             and name.isupper()}
    assert names == {"K", "DIM", "PRACTICE_SEEDS", "_WORD", "_SKIPPED"}
    assert SEED not in wb.PRACTICE_SEEDS
    seen: list[object] = []

    class Spy:
        def __init__(self, points: wb.Points) -> None:
            seen.append(points)

        def query(self, q: wb.Query, k: int) -> wb.Answer:
            seen.append(q)
            return []

    _judge(wb.Entry("spy", Spy))
    reached: set[int] = set()
    todo, ids = list(seen), set()
    while todo:
        obj = todo.pop()
        if id(obj) in ids:
            continue
        ids.add(id(obj))
        if isinstance(obj, int):
            reached.add(obj)
        elif isinstance(obj, (list, tuple, set, frozenset)):
            todo.extend(obj)
        elif isinstance(obj, dict):
            todo.extend([*obj.keys(), *obj.values()])
        elif hasattr(obj, "__dict__"):
            todo.extend(vars(obj).values())
    assert SEED not in reached and SEED & ((1 << 64) - 1) not in reached
    assert len(seen) == 1 + QUERIES


# --- Cheating candidates --------------------------------------------------------------------


class _Raw:
    """Reads the coordinates through the library's own route, then scans them for free."""

    def __init__(self, points: wb.Points) -> None:
        self.rows = wb.raw_points(points)

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        return []


class _Dig:
    """Reaches into the store behind `Points` and measures the stored rows itself."""

    def __init__(self, points: wb.Points) -> None:
        self.points = points

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        rows = self.points._Points__store.rows  # type: ignore[attr-defined]
        row = q._Query__row  # type: ignore[attr-defined]
        return sorted((sq_dist(r, row), i) for i, r in enumerate(rows))[:k]


class _Extract:
    """Reads every coordinate through inner products with the axes, keeps them, and answers
    from its copy."""

    def __init__(self, points: wb.Points) -> None:
        axes = [[float(a == b) for a in range(points.dim)] for b in range(points.dim)]
        self.copy = [[points.dot(i, axis) for axis in axes] for i in range(points.n)]
        self.axes = axes

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        row = [q.dot(axis) for axis in self.axes]
        return sorted((sq_dist(p, row), i) for i, p in enumerate(self.copy))[:k]


class _Hoard:
    """A correct scan that holds more numbers than the cap allows."""

    def __init__(self, points: wb.Points) -> None:
        self.n = points.n
        self.pile = list(range(int(wb.CAP * points.n * points.dim) + 1))

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        return sorted((q.dist(i), i) for i in range(self.n))[:k]


class _Bent:
    """A scan whose answers break the contract in one way, chosen by `how`."""

    def __init__(self, points: wb.Points, how: str) -> None:
        self.n, self.how = points.n, how

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        found = sorted((q.dist(i), i) for i in range(self.n))[:k]
        if self.how == "unsorted":
            return found[::-1]
        if self.how == "duplicate":
            return found[:-1] + [found[0]]
        if self.how == "too many":
            return sorted((q.dist(i), i) for i in range(self.n))[: k + 1]
        if self.how == "not stored":
            return found[:-1] + [(found[-1][0], self.n)]
        return [(d + 1e-9, i) for d, i in found]


def test_reading_the_coordinates_through_raw_points_is_caught() -> None:
    assert _failure(_Raw) == "read the coordinates through raw_points"


def test_measuring_the_stored_rows_directly_is_caught_by_exact() -> None:
    failure = _failure(_Dig)
    assert failure is not None and failure.endswith("contract (exact_distance)")


def test_keeping_a_copy_of_the_coordinates_is_caught() -> None:
    assert _failure(_Extract) == "holds copies of the coordinates"


def test_holding_more_than_the_cap_fails() -> None:
    [verdict] = _judge(wb.Entry("hoard", _Hoard))
    s = verdict.seeds[0]
    assert s.failure is None and s.memory > s.cap and not verdict.passes()
    assert "more memory than the cap" in wb.report(verdict)


@pytest.mark.parametrize("how, piece", [
    ("unsorted", "nearest_first"), ("duplicate", "each_once"), ("too many", "up_to_k"),
    ("not stored", "stored"), ("rounded", "exact_distance")])
def test_a_broken_answer_is_caught(how: str, piece: str) -> None:
    failure = _failure(lambda points: _Bent(points, how))
    assert failure is not None and failure.endswith(f"contract ({piece})")


def test_a_candidate_that_raises_fails() -> None:
    def make(points: wb.Points) -> wb.Candidate:
        raise RuntimeError("no index today")

    assert _failure(make) == "raised RuntimeError: no index today"


def test_memory_is_counted_in_numbers() -> None:
    class Holder:
        def __init__(self) -> None:
            self.a = [1, 2.5, None, (3, 4)]
            self.b = {"key": [5]}
            self.big = 1 << 100
            self.text = "x" * 17

    count, copies = wb.held(Holder(), frozenset([2.5]))
    # 1, 2.5, None and the tuple's two; the key and 5; two words; three of eight characters
    assert count == 5 + 2 + 2 + 3 and copies == 1


# --- The chapter's structures ---------------------------------------------------------------


def test_the_chapters_structures_keep_the_contract() -> None:
    verdicts = _judge(
        wb.Entry("k-d tree", wb.kdtree_candidate(8), trusted=True),
        wb.Entry("LSH", wb.lsh_candidate(2, 10, 12.0), trusted=True),
        wb.Entry("HNSW", wb.hnsw_candidate(8, 32, 16), trusted=True),
        wb.Entry("flat", wb.hnsw_candidate(8, 32, 16, flat=True), trusted=True),
        families=tuple(wb.FAMILIES))
    for v in verdicts:
        for s in v.seeds:
            assert s.failure is None, (v.name, s.failure)
            assert 0 < s.memory <= s.cap
    kd, lsh, hnsw, flat = verdicts
    assert kd.worst_recall() == 1.0 and kd.seeds[0].dots == wb.DIM
    assert not kd.passes() and "more than half the scan's distances" in wb.report(kd)
    assert hnsw.worst_recall() >= 0.9 and hnsw.worst_ticks() <= wb.SHARE * N
    assert flat.worst_recall() >= 0.9
    assert lsh.seeds[0].dots == 2 * 10
    assert wb.report(hnsw).startswith("HNSW: passes.")


class _SameInt(int):
    """An index that claims to equal every other, so ten copies look distinct to a set."""

    def __eq__(self, other: object) -> bool:
        return self is other

    def __hash__(self) -> int:
        return id(self)


class _AnyFloat(float):
    """A distance that claims to equal, and to be below, anything."""

    def __eq__(self, other: object) -> bool:
        return True

    def __le__(self, other: object) -> bool:
        return True

    def __hash__(self) -> int:
        return 0


class _Repeat:
    """Finds the nearest point and answers it ten times, each copy a 'different' index."""

    def __init__(self, points: wb.Points) -> None:
        self.n = points.n

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        d, i = min((q.dist(j), j) for j in range(self.n))
        return [(d, _SameInt(i)) for _ in range(k)]


class _Lazy:
    """Answers the first ten indices with distances that pass any comparison."""

    def __init__(self, points: wb.Points) -> None:
        pass

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        return [(_AnyFloat(0.0), i) for i in range(k)]


@pytest.mark.parametrize("make", [_Repeat, _Lazy])
def test_answers_of_disguised_types_are_refused(make: wb.Make) -> None:
    failure = _failure(make)
    assert failure is not None and "plain Python types" in failure


def test_a_number_type_of_the_candidates_never_meets_a_coordinate() -> None:
    caught: list[float] = []

    class Spy(float):
        def __rmul__(self, other: float) -> float:
            caught.append(other)
            return float(other) * float(self)

        def __mul__(self, other: float) -> float:
            caught.append(other)
            return float(other) * float(self)

    corpus = wb.generate("clusters", 5, n=5, queries=1)
    store = wb._Store(corpus.points)
    meter = wb.Meter()
    points = wb.Points(store, meter)
    query = wb.Query(store, store.scaled(corpus.queries[0]), meter)
    points.dot(0, [Spy(1.0)] * wb.DIM)
    query.dot([Spy(1.0)] * wb.DIM)
    assert caught == []


class _Arrays:
    """Copies every coordinate into an array and a closure, where a plain walk sees nothing."""

    def __init__(self, points: wb.Points) -> None:
        axes = [[float(a == b) for a in range(points.dim)] for b in range(points.dim)]
        flat = array("d", [points.dot(i, axis) for i in range(points.n) for axis in axes])
        self.copy = flat
        self.n = points.n

    def query(self, q: wb.Query, k: int) -> wb.Answer:
        return sorted((q.dist(i), i) for i in range(self.n))[:k]


class _Closure(_Arrays):
    def __init__(self, points: wb.Points) -> None:
        super().__init__(points)
        hidden = list(self.copy)
        self.copy = array("d")
        self.lookup = lambda i: hidden[i]


@pytest.mark.parametrize("make", [_Arrays, _Closure])
def test_copies_in_arrays_and_closures_are_counted(make: wb.Make) -> None:
    assert _failure(make) == "holds copies of the coordinates"


def test_arrays_and_deques_are_counted_as_numbers() -> None:
    class Holder:
        def __init__(self) -> None:
            self.a = array("d", [1.0, 2.0, 3.0])
            self.d = deque([4, 5])
            self.f = functools.partial(max, 6, 7)

    assert wb.held(Holder())[0] == 3 + 2 + 2
