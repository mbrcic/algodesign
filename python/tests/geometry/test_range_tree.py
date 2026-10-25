# SPDX-License-Identifier: Apache-2.0
"""Range trees: the in-range keys, exactly, with repeated keys and dBCKO's split-node walk.

Mirrors the Rust's `range_tree::tests` and the Lean's `RangeTree/` (`query_eq_filter`: the
1D query reports exactly the in-range keys, in order, each once). Keys come from a tiny range, so
repeats are common and copies of a split key land on both sides.
"""

from __future__ import annotations

from typing import Any

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.geometry.range_tree import Leaf, Leaf2, Node, Node2, RangeTree1D, RangeTree2D


def filter_1d(keys: list[int], lo: int, hi: int) -> list[int]:
    """The in-range input indices, in key order, ties in input order: the specification."""
    return [i for _, i in sorted((k, i) for i, k in enumerate(keys) if lo <= k <= hi)]


def test_lean_examples() -> None:
    # Lean: the AlgoDesignTests/Geometry.lean range-tree examples.
    t = RangeTree1D([1, 3, 5, 7])
    assert t.query_keys(3, 5) == [3, 5]
    assert t.query(6, 4) == []
    assert t.query_keys(3, 3) == [3]
    assert t.query_keys(0, 9) == [1, 3, 5, 7]
    assert RangeTree1D([1, 3, 3, 5]).query_keys(3, 3) == [3, 3]


@given(st.lists(st.integers(-4, 4), max_size=60), st.integers(-5, 5), st.integers(-5, 5))
def test_the_query_is_the_filter(keys: list[int], lo: int, hi: int) -> None:
    # Lean: query_eq_filter
    assert RangeTree1D(keys).query(lo, hi) == filter_1d(keys, lo, hi)


def de_berg_query(t: RangeTree1D[int], lo: int, hi: int) -> list[int]:
    """dBCKO's `FINDSPLITNODE` and `1DRANGEQUERY` (§5.1) as printed: the walk to the split node
    goes left when `hi <= split`. The input indices found, in key order."""
    found: list[int] = []

    def report_leaf(v: Leaf) -> None:
        if lo <= t.keys[v.start] <= hi:
            found.append(v.start)

    if t.root is None or hi < lo:
        return []
    v = t.root
    while isinstance(v, Node) and (hi <= v.split or lo > v.split):
        v = v.left if hi <= v.split else v.right
    if isinstance(v, Leaf):
        report_leaf(v)
    else:
        w = v.left
        while isinstance(w, Node):
            if lo <= w.split:
                found.extend(range(w.right.start, w.right.end))
                w = w.left
            else:
                w = w.right
        report_leaf(w)
        w = v.right
        while isinstance(w, Node):
            if hi >= w.split:
                found.extend(range(w.left.start, w.left.end))
                w = w.right
            else:
                w = w.left
        report_leaf(w)
    return [t.order[p] for p in sorted(found)]


@given(st.sets(st.integers(-40, 39), max_size=40), st.integers(-45, 44), st.integers(-45, 44))
def test_distinct_keys_answer_as_de_berg(keys: set[int], lo: int, hi: int) -> None:
    # With distinct keys the walk going left only when `hi < split` returns de Berg's answer, also
    # when a bound equals a stored key; only the node the walk stops at may differ.
    t = RangeTree1D(sorted(keys))
    assert t.query(lo, hi) == de_berg_query(t, lo, hi)


def test_copies_of_the_split_at_both_ends_are_all_reported() -> None:
    keys = [3, 3, 3, 3, 3, 1, 5]
    t = RangeTree1D(keys)
    for lo, hi in [(3, 3), (1, 3), (3, 5), (2, 4), (0, 3)]:
        assert t.query(lo, hi) == filter_1d(keys, lo, hi), (lo, hi)


@given(st.lists(st.integers(-4, 4), min_size=1, max_size=60))
def test_the_build_keeps_the_split_invariant(keys: list[int]) -> None:
    # Lean: keysSeparate_build, splitsHalve_build, build_split_mem -- every split is a stored key,
    # the largest on its left, and no smaller than any key on its right; every node halves.
    t = RangeTree1D(keys)
    assert t.check_valid() is None
    stack: list[Node[int] | Leaf] = [t.root] if t.root is not None else []
    while stack:
        v = stack.pop()
        if isinstance(v, Node):
            left = t.keys[v.left.start : v.left.end]
            right = t.keys[v.right.start : v.right.end]
            assert v.split == max(left)
            assert all(v.split <= k for k in right)
            stack += [v.left, v.right]


def test_identical_keys_build_a_shallow_tree() -> None:
    t = RangeTree1D([7] * 1000)
    assert t.depth() <= 11
    assert len(t.query(7, 7)) == 1000
    t2 = RangeTree2D([(2, 2)] * 1000)
    assert t2.depth() <= 11
    assert len(t2.query((2, 2), (2, 2))) == 1000


def test_empty_trees_answer_nothing() -> None:
    assert RangeTree1D[int]([]).query(0, 9) == []
    assert RangeTree2D[int]([]).query((0, 0), (9, 9)) == []


def test_building_leaves_the_input_alone() -> None:
    keys = [5, 1, 3]
    points = [(5, 1), (1, 5), (3, 3)]
    RangeTree1D(keys)
    RangeTree2D(points)
    assert keys == [5, 1, 3] and points == [(5, 1), (1, 5), (3, 3)]


@given(
    st.lists(st.tuples(st.integers(-6, 6), st.integers(-6, 6)), max_size=60),
    st.tuples(st.integers(-7, 7), st.integers(-7, 7)),
    st.tuples(st.integers(-7, 7), st.integers(-7, 7)),
)
def test_the_2d_query_is_the_box_filter(
    pts: list[tuple[int, int]], lo: tuple[int, int], hi: tuple[int, int]
) -> None:
    # The 2D query reports in the walk's order, unsorted: compare sorted copies, which also
    # checks that each point is reported once.
    want = [i for i, (x, y) in enumerate(pts) if lo[0] <= x <= hi[0] and lo[1] <= y <= hi[1]]
    assert sorted(RangeTree2D(pts).query(lo, hi)) == want


@given(st.lists(st.tuples(st.integers(-6, 6), st.integers(-6, 6)), min_size=1, max_size=60))
def test_each_associated_tree_holds_its_subtree_sorted_by_y(pts: list[tuple[int, int]]) -> None:
    # dBCKO §5.3: the associated structure of a node holds the points below it, ordered by y,
    # built by merging the children's lists (left first on equal y), never by sorting again.
    t = RangeTree2D(pts)
    x_position = {i: pos for pos, (_, i) in enumerate(t.points)}
    stack: list[Node2[int] | Leaf2] = [t.root] if t.root is not None else []
    while stack:
        v = stack.pop()
        if isinstance(v, Node2):
            ys = v.assoc.keys
            assert ys == [pts[i][1] for i in v.ids]
            assert v.ids == sorted(v.ids, key=lambda i: (pts[i][1], x_position[i]))
            assert sorted(v.ids) == sorted(i for _, i in t.points[v.start : v.end])
            stack += [v.left, v.right]


def test_the_2d_tree_copies_and_checks_its_points() -> None:
    pts = [[1, 2], [3, 4]]
    t: RangeTree2D[int] = RangeTree2D(pts)  # type: ignore[arg-type]
    pts[0][0] = 100
    assert sorted(t.query((0, 0), (5, 5))) == [0, 1]
    with pytest.raises(ValueError, match="two coordinates"):
        RangeTree2D([(1, 2, 3)])  # type: ignore[arg-type]


def test_a_nan_key_is_rejected() -> None:
    # NaN has no place in a total order, and would silently corrupt the tree.
    with pytest.raises(ValueError, match="NaN"):
        RangeTree1D([float("nan"), 1.0, 0.0])
    with pytest.raises(ValueError, match="NaN"):
        RangeTree2D([(0.0, float("nan"))])


def from_shape(shape: Any) -> RangeTree1D[Any]:
    """A tree written out as a shape, unchecked: a key is a leaf, `[split, left, right]` a node;
    its keys are its leaves, left to right."""
    tree: RangeTree1D[Any] = RangeTree1D([])

    def build_from(s: Any) -> Node[Any] | Leaf:
        start = len(tree.keys)
        if not isinstance(s, list):
            tree.keys.append(s)
            return Leaf(start)
        left, right = build_from(s[1]), build_from(s[2])
        return Node(s[0], start, len(tree.keys), left, right)

    tree.root = build_from(shape)
    tree.order = list(range(len(tree.keys)))
    return tree


def test_each_piece_fails_alone() -> None:
    # Lean: KeysSeparate, SplitsHalve -- a split below its left side breaks only the first; one key
    # on the left of three breaks only the second.
    t = from_shape([0, 1, 2])
    assert not t.is_keys_separate() and t.is_splits_halve()
    assert t.check_valid() == "invariant 1 (keys_separate)"
    t = from_shape([1, 1, [2, 2, 3]])
    assert t.is_keys_separate() and not t.is_splits_halve()
    assert t.check_valid() == "invariant 2 (splits_halve)"
    assert from_shape([2, [1, 1, 2], 3]).is_valid()


@given(st.lists(st.tuples(st.integers(-6, 6), st.integers(-6, 6)), max_size=60))
def test_the_2d_build_is_valid(pts: list[tuple[int, int]]) -> None:
    assert RangeTree2D(pts).check_valid() is None


def test_each_2d_piece_fails_alone() -> None:
    """A split below its left side breaks only the first piece; one point on the left of three
    only the second; a tree on y missing a point only the third."""
    t = RangeTree2D([(1, 5), (2, 4), (3, 6), (4, 3)])
    assert isinstance(t.root, Node2)
    t.root.split = 0
    assert not t.is_keys_separate() and t.is_splits_halve() and t.is_y_trees_hold_subtrees()
    assert t.check_valid() == "invariant 1 (keys_separate)"

    t = RangeTree2D([(1, 5), (2, 4), (3, 6)])
    lopsided: RangeTree2D[int] = RangeTree2D([])
    lopsided.points = t.points
    right = Node2(2, RangeTree1D.from_sorted([4, 6]), [1, 2], 1, 3, Leaf2(1), Leaf2(2))
    lopsided.root = Node2(1, RangeTree1D.from_sorted([4, 5, 6]), [1, 0, 2], 0, 3, Leaf2(0), right)
    assert lopsided.is_keys_separate() and lopsided.is_y_trees_hold_subtrees()
    assert lopsided.check_valid() == "invariant 2 (splits_halve)"

    t = RangeTree2D([(1, 5), (2, 4), (3, 6), (4, 3)])
    assert isinstance(t.root, Node2)
    t.root.ids[0] = t.root.ids[1]
    assert t.is_keys_separate() and t.is_splits_halve()
    assert t.check_valid() == "not in the box (y_trees_hold_subtrees)"
