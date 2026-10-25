# SPDX-License-Identifier: Apache-2.0
"""The k-d tree: dBCKO's leaf-stored tree, its range query, and best-first nearest neighbors.

Mirrors the Rust's `kdtree::tests` and the Lean's `KDTree/` (`CutsSeparate`, `far_side_bound`,
`far_side_bound_left`, `boxSqDist_le`, `rangeQuery_perm_filter`). Coordinates are small integers,
so repeats are common, distances are exact, and a tie is a real tie.
"""

from __future__ import annotations

import math
import random

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.geometry import scan
from algodesign.geometry.kdtree import (
    KDTree,
    Leaf,
    Node,
    Region,
    SearchState,
    check_search_valid,
    is_each_point_once,
    is_nothing_closer_skipped,
    is_offsets_bound,
    is_queued_cuts_separate,
)
from algodesign.geometry.point import sq_dist

coord = st.integers(-4, 4).map(float)


def points(dim: int, max_size: int = 80) -> st.SearchStrategy[list[list[float]]]:
    return st.lists(st.lists(coord, min_size=dim, max_size=dim), max_size=max_size)


def nodes(t: KDTree) -> list[Node | Leaf]:
    out: list[Node | Leaf] = []
    stack: list[Node | Leaf] = [t.root] if t.root is not None else []
    while stack:
        v = stack.pop()
        out.append(v)
        if isinstance(v, Node):
            stack += [v.left, v.right]
    return out


def test_lean_examples() -> None:
    # Lean: AlgoDesignTests/Geometry.lean, points on the split, both sides.
    t = KDTree([[2.0, 1.0], [1.0, 5.0], [3.0, 0.0], [2.0, 3.0]])
    assert t.range([2.0, 0.0], [4.0, 4.0]) == [0, 2, 3]
    assert t.range([0.0, 0.0], [2.0, 3.0]) == [0, 3]


@given(points(3, 120), st.sampled_from([1, 2, 3, 5, 8]))
def test_the_build_cuts_separate_and_halve(pts: list[list[float]], bucket: int) -> None:
    # Lean: KDTree.Valid -- CutsSeparate (left <= split <= right on the node's axis, repeats on both
    # sides) and CutsHalve, read here by a walk of its own and by `check_valid`.
    t = KDTree(pts, bucket)
    assert t.check_valid() is None
    for v in nodes(t):
        if isinstance(v, Node):
            assert all(t.points[i][v.axis] <= v.split for i in t.below(v.left))
            assert all(v.split <= t.points[i][v.axis] for i in t.below(v.right))
            assert len(t.below(v.right)) <= len(t.below(v.left)) <= len(t.below(v.right)) + 1
        else:
            assert len(t.below(v)) <= bucket


@given(points(2), st.lists(coord, min_size=2, max_size=2))
def test_the_region_bound_is_a_lower_bound(pts: list[list[float]], q: list[float]) -> None:
    # Lean: boxSqDist_le, far_side_bound, far_side_bound_left -- every region's bound is at most
    # the distance from q to each point inside it, on whichever side of a split it lies.
    t = KDTree(pts)
    stack: list[tuple[Node | Leaf, list[float]]] = [(t.root, [0.0, 0.0])] if t.root else []
    while stack:
        v, offsets = stack.pop()
        bound = sum(o * o for o in offsets)
        assert all(bound <= sq_dist(t.points[i], q) for i in t.below(v))
        if isinstance(v, Node):
            near, far = (v.left, v.right) if q[v.axis] <= v.split else (v.right, v.left)
            far_offsets = list(offsets)
            far_offsets[v.axis] = v.split - q[v.axis]
            stack += [(near, offsets), (far, far_offsets)]


@given(
    points(3),
    st.lists(coord, min_size=3, max_size=3),
    st.lists(coord, min_size=3, max_size=3),
    st.sampled_from([1, 2, 3, 5, 8]),
)
def test_the_range_query_is_the_box_filter(
    pts: list[list[float]], lo: list[float], hi: list[float], bucket: int
) -> None:
    # Lean: rangeQuery_perm_filter
    assert KDTree(pts, bucket).range(lo, hi) == scan.in_box(pts, lo, hi)


@given(
    points(3),
    st.lists(coord, min_size=3, max_size=3),
    st.integers(0, 12),
    st.sampled_from([1, 2, 3, 4, 5, 8]),
)
def test_best_first_is_the_scan(
    pts: list[list[float]], q: list[float], k: int, bucket: int
) -> None:
    # The same distances and the same ids, the one stored first on a tie, for every leaf size
    # the tests use, the Rust's default 8 included.
    assert KDTree(pts, bucket).k_nearest(q, k) == scan.k_nearest(pts, q, k)


@given(points(2, 60), st.lists(st.floats(-5, 5), min_size=2, max_size=2))
def test_best_first_is_the_scan_on_real_coordinates(pts: list[list[float]], q: list[float]) -> None:
    assert KDTree(pts).k_nearest(q, 3) == scan.k_nearest(pts, q, 3)


def test_identical_points_stay_shallow_and_are_all_found() -> None:
    t = KDTree([[1.5, -2.0]] * 1000)
    assert t.depth() <= 11
    assert len(t.range([1.5, -2.0], [1.5, -2.0])) == 1000
    assert t.nearest([1.5, -2.0]) == 0
    assert [i for _, i in t.k_nearest([0.0, 0.0], 3)] == [0, 1, 2]


def test_empty_and_k_edge_cases() -> None:
    assert KDTree([]).nearest([0.0, 0.0]) is None
    assert KDTree([]).range([0.0, 0.0], [1.0, 1.0]) == []
    t = KDTree([[0.0, 0.0], [1.0, 1.0]])
    assert t.k_nearest([0.0, 0.0], 0) == []
    assert len(t.k_nearest([0.0, 0.0], 9)) == 2


def test_stats_count_the_work() -> None:
    pts = [[float(i % 20), float(i // 20)] for i in range(400)]
    found, stats = KDTree(pts).k_nearest_with_stats([7.2, 9.1], 1)
    assert found[0][1] == 9 * 20 + 7
    assert 1 <= stats.points_measured < 400


def test_building_copies_the_input() -> None:
    pts = [[2.0, 1.0], [1.0, 5.0], [3.0, 0.0]]
    t = KDTree(pts)
    assert pts == [[2.0, 1.0], [1.0, 5.0], [3.0, 0.0]]
    pts[0][0] = 99.0
    assert t.nearest([2.0, 1.0]) == 0


def test_invalid_input_is_rejected() -> None:
    with pytest.raises(ValueError, match="bucket"):
        KDTree([[0.0, 0.0]], 0)
    with pytest.raises(ValueError, match="dimension"):
        KDTree([[0.0, 0.0], [1.0]])
    with pytest.raises(ValueError, match="finite"):
        KDTree([[0.0, float("nan")]])
    t = KDTree([[0.0, 0.0]])
    with pytest.raises(ValueError, match="dimension"):
        t.nearest([0.0])
    with pytest.raises(ValueError, match="k"):
        t.k_nearest([0.0, 0.0], -1)


def test_points_need_at_least_one_coordinate() -> None:
    with pytest.raises(ValueError, match="dimension"):
        KDTree([[], []])


def test_build_sorts_once_per_axis(monkeypatch: pytest.MonkeyPatch) -> None:
    """dBCKO's presort (Lemma 5.3, p. 101): one sort per axis, however many nodes it makes."""
    import builtins

    import algodesign.geometry.kdtree as module

    calls = 0

    def counting_sorted(*args: object, **kwargs: object) -> list[object]:
        nonlocal calls
        calls += 1
        return builtins.sorted(*args, **kwargs)  # type: ignore[call-overload, no-any-return]

    monkeypatch.setattr(module, "sorted", counting_sorted, raising=False)
    pts = [[float((i * 37 + a * 11) % 101) for a in range(3)] for i in range(200)]
    before = calls
    KDTree(pts, bucket=1)
    assert calls - before == 3


def test_ties_on_the_split_go_left_by_index() -> None:
    """By (coordinate, id): of the three points with x = 1, the one stored first goes left."""
    t = KDTree([[1.0, 0.0], [1.0, 1.0], [1.0, 2.0], [0.0, 5.0]], bucket=1)
    assert isinstance(t.root, Node)
    assert t.root.axis == 0 and t.root.split == 1.0
    assert set(t.below(t.root.left)) == {3, 0}
    assert set(t.below(t.root.right)) == {1, 2}


def assert_same_as_reference(
    t: KDTree, pts: list[list[float]], v: Node | Leaf, ids: list[int], depth: int
) -> None:
    dim = len(pts[0])
    if len(ids) <= t.bucket:
        assert isinstance(v, Leaf)
        assert t.below(v) == sorted(ids, key=lambda i: (pts[i][0], i))
        return
    assert isinstance(v, Node)
    axis = depth % dim
    ordered = sorted(ids, key=lambda i: (pts[i][axis], i))
    m = (len(ids) + 1) // 2
    assert v.axis == axis
    assert v.split == pts[ordered[m - 1]][axis]
    assert_same_as_reference(t, pts, v.left, ordered[:m], depth + 1)
    assert_same_as_reference(t, pts, v.right, ordered[m:], depth + 1)
    assert sorted(t.below(v)) == sorted(ids)


@pytest.mark.parametrize("dim", [1, 2, 3])
@pytest.mark.parametrize("bucket", [1, 3])
def test_build_matches_a_node_by_node_resort(dim: int, bucket: int) -> None:
    """Every node: the axis, the split, and each leaf's exact order equal a fresh sort of the
    node's indices by (coordinate, index), on inputs where most coordinates repeat."""
    rng = random.Random(40 + dim * 10 + bucket)
    for _ in range(60):
        n = rng.randint(1, 60)
        pts = [[float(rng.randint(0, 3)) for _ in range(dim)] for _ in range(n)]
        t = KDTree(pts, bucket=bucket)
        assert t.root is not None
        assert_same_as_reference(t, pts, t.root, list(range(n)), 0)


@pytest.mark.parametrize("n", [1024, 8192])
def test_build_work_per_node_is_its_own_size(n: int) -> None:
    """Every node works on lists of its own size, never the input's, so the build is O(n log n):
    at each node every axis's list has the node's n indices, and the left set it makes holds
    ceil(n/2) of them; over the build the nodes' sizes total at most N * ceil(log2 N)."""
    total = 0

    class Counted(KDTree):
        def build(self, by_axis: list[list[int]], depth: int) -> Node | Leaf:
            nonlocal total
            assert len({len(order) for order in by_axis}) == 1
            if len(by_axis[0]) > self.bucket:
                total += len(by_axis[0])
            return super().build(by_axis, depth)

    rng = random.Random(1)
    Counted([[float(rng.randint(0, 50)) for _ in range(3)] for _ in range(n)])
    assert total <= n * math.ceil(math.log2(n))


def by_hand(xs: list[float], split: float, mid: int) -> KDTree:
    """One-dimensional points under one cut at `split`, the first `mid` on its left."""
    t = KDTree([[x] for x in xs], bucket=len(xs))
    n = len(xs)
    t.order = list(range(n))
    t.root = Node(0, split, 0, n, Leaf(0, mid), Leaf(mid, n))
    return t


def test_each_tree_piece_fails_alone() -> None:
    # The split below the left point: the cut does not divide, the counts still halve.
    t = by_hand([0.0, 1.0], -1.0, 1)
    assert not t.is_cuts_separate() and t.is_cuts_halve()
    assert t.check_valid() == "invariant 1 (cuts_separate)"
    # Three equal points, one left and two right: the cut divides, the counts do not halve.
    t = by_hand([0.0, 0.0, 0.0], 0.0, 1)
    assert t.is_cuts_separate() and not t.is_cuts_halve()
    assert t.check_valid() == "invariant 2 (cuts_halve)"
    assert by_hand([0.0, 1.0, 2.0], -1.0, 1).check_valid() == "invariant 1 (cuts_separate)"
    # The pieces read the internal nodes over buckets: a bucket of 2 under each side.
    assert by_hand([0.0, 0.0, 1.0, 1.0], 0.0, 2).is_valid()


def test_the_search_states_of_a_two_point_tree() -> None:
    # Lean: BestFirst.start, BestFirst.visit -- the far child is queued before the near one and
    # wins the tie at bound 0, so the search measures point 1 before point 0.
    t = KDTree([[0.0], [1.0]])
    assert isinstance(t.root, Node)
    left, right = t.root.left, t.root.right
    assert t.search_states([0.0], 1) == [
        SearchState([], [Region([0.0], t.root)]),
        SearchState([], [Region([0.0], right), Region([0.0], left)]),
        SearchState([1], [Region([0.0], left)]),
        SearchState([1, 0], []),
    ]
    assert t.search_states([0.0], 0) == []


def test_each_search_piece_fails_where_it_should() -> None:
    # One point (1, 3), the query at the origin: the whole tree is the root leaf.
    t = KDTree([[1.0, 3.0]])
    assert t.root is not None
    q = [0.0, 0.0]
    assert check_search_valid(t, q, SearchState([], [Region([0.0, 0.0], t.root)])) is None
    # Offsets (2, 0): axis 0 overshoots (4 > 1), the bound 4 is still below the distance 10.
    over = SearchState([], [Region([2.0, 0.0], t.root)])
    assert is_nothing_closer_skipped(t, q, over) and is_each_point_once(t, q, over)
    assert check_search_valid(t, q, over) == "not in the box (offsets_bound)"
    # Measured twice: the point is not once.
    twice = SearchState([0, 0], [])
    assert is_nothing_closer_skipped(t, q, twice) and is_offsets_bound(t, q, twice)
    assert check_search_valid(t, q, twice) == "not in the box (each_point_once)"
    # A root cut that does not separate (split below the left point): the search's start, the
    # root queued at offsets zero, fails only `queued_cuts_separate`.
    broken = by_hand([0.0, 1.0], -1.0, 1)
    assert broken.root is not None
    start = SearchState([], [Region([0.0], broken.root)])
    assert is_nothing_closer_skipped(broken, [0.0], start)
    assert is_offsets_bound(broken, [0.0], start) and is_each_point_once(broken, [0.0], start)
    assert not is_queued_cuts_separate(broken, [0.0], start)
    assert check_search_valid(broken, [0.0], start) == "not in the box (queued_cuts_separate)"
    # Invariant 3 has no sole failure: `offsets_bound` and `each_point_once` imply it. It fails
    # beside one of them: the point forgotten, or its region's bound past its distance.
    empty = SearchState([], [])
    assert not is_nothing_closer_skipped(t, q, empty) and not is_each_point_once(t, q, empty)
    assert check_search_valid(t, q, empty) == "invariant 3 (nothing_closer_skipped)"
    past = SearchState([], [Region([2.0, 3.0], t.root)])
    assert not is_nothing_closer_skipped(t, q, past) and not is_offsets_bound(t, q, past)


def test_each_search_piece_answers_false_on_a_query_of_another_dimension() -> None:
    # As the Rust's: a query the tree cannot measure fails every piece, without raising.
    t = KDTree([[1.0, 3.0], [2.0, 0.0]])
    assert t.root is not None
    start = SearchState([], [Region([0.0, 0.0], t.root)])
    assert check_search_valid(t, [0.0, 0.0], start) is None
    for q in ([0.0], [0.0, 0.0, 0.0]):
        assert not is_nothing_closer_skipped(t, q, start)
        assert not is_queued_cuts_separate(t, q, start)
        assert not is_offsets_bound(t, q, start)
        assert not is_each_point_once(t, q, start)
        assert check_search_valid(t, q, start) == "invariant 3 (nothing_closer_skipped)"


@given(points(2, 60), st.lists(coord, min_size=2, max_size=2), st.integers(1, 5),
       st.sampled_from([1, 2, 3, 5]))
def test_every_search_step_is_valid(
    pts: list[list[float]], q: list[float], k: int, bucket: int
) -> None:
    # Lean: BestFirst.valid_start, BestFirst.valid_visit -- every piece after every step, for k = 1
    # and k > 1; the last state has measured exactly what the search counted.
    t = KDTree(pts, bucket)
    states = t.search_states(q, k)
    for state in states:
        assert check_search_valid(t, q, state) is None
    if pts:
        _, stats = t.k_nearest_with_stats(q, k)
        assert len(states) == stats.regions_opened + 1
        assert len(states[-1].measured) == stats.points_measured


@given(st.lists(st.lists(st.floats(-1e3, 1e3), min_size=3, max_size=3), max_size=60),
       st.lists(st.floats(-1e3, 1e3), min_size=3, max_size=3), st.integers(1, 5))
def test_every_search_step_is_valid_on_real_coordinates(
    pts: list[list[float]], q: list[float], k: int
) -> None:
    # Rounding: the recomputed bound never passes a computed distance in its region.
    t = KDTree(pts, 8)
    for state in t.search_states(q, k):
        assert check_search_valid(t, q, state) is None
