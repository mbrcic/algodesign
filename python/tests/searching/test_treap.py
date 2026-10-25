# SPDX-License-Identifier: Apache-2.0
"""Property-based tests for `algodesign.searching.treap.Treap`.

`Treap/` proves the updates over `ℕ` priorities: `valid_insert` and `valid_delete` (both
invariants survive), `insertSpec` and `deleteSpec` (exactly the one key gained or lost, every other
priority untouched), `removeRoot_eq_join` (rotating the node down builds the join of its
children), and `existsUnique_of_nodup` (distinct keys and priorities fix the shape). The
priorities here are floats, which no Lean statement speaks of directly, and the expected
`O(log n)` height is proved nowhere.

These tests check BST order and max-heap order after arbitrary sequences of
operations with explicit (deterministic) priorities, exact-key-affected checks, `is_valid` on
hand-built trees that break one invariant each, the recursion limit that caller-chosen priorities
reach, and an empirical nod to Theorem 8.8's expected-rotation-count bound under real randomness.
"""
from __future__ import annotations

import random
import sys
from unittest import mock

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import algodesign.searching.treap as treap_module
from algodesign.searching.treap import (
    Treap,
    _heap_ordered,
    _is_sorted,
    _Node,
    rotate_left,
    rotate_right,
)

from .treap_rotations import delete_rotation_count, rotation_count

# --- invariant checkers, mirroring `Treap/Spec.lean`'s `Sorted`/`HeapOrdered` --------------------


def _check_sorted(node: _Node[int] | None, lo: int | None, hi: int | None) -> None:
    """`Sorted`: every key in `node`'s left subtree is `< node.key`, every key in its right
    subtree is `> node.key`, recursively — same shape as `Treap/Spec.lean`'s `Sorted`."""
    if node is None:
        return
    if lo is not None:
        assert lo < node.key
    if hi is not None:
        assert node.key < hi
    _check_sorted(node.left, lo, node.key)
    _check_sorted(node.right, node.key, hi)


def _check_heap_ordered(
    node: _Node[int] | None, ceiling: float | None = None
) -> None:
    """`HeapOrdered`: every priority anywhere in the tree is `<=` the priority at its own
    subtree's root — checked as "`<=` every ancestor's priority," the same "everywhere below, not
    just immediate children" phrasing `Treap/Spec.lean`'s `HeapOrdered` uses."""
    if node is None:
        return
    if ceiling is not None:
        assert node.priority <= ceiling
    _check_heap_ordered(node.left, node.priority)
    _check_heap_ordered(node.right, node.priority)


def hand_check(tree: Treap[int]) -> None:
    _check_sorted(tree.root, None, None)
    _check_heap_ordered(tree.root)


def check_invariants(tree: Treap[int]) -> None:
    """The hand checkers above, and `Treap.is_valid`, which must agree with them."""
    hand_check(tree)
    assert tree.is_valid()


# --- property tests, explicit priorities --------------------------------------------------------

_ops = st.lists(
    st.one_of(
        st.tuples(
            st.just("insert"),
            st.integers(min_value=-50, max_value=50),
            st.floats(min_value=0.0, max_value=1.0, allow_nan=False),
        ),
        st.tuples(
            st.just("delete"), st.integers(min_value=-50, max_value=50), st.just(0.0)
        ),
    ),
    max_size=150,
)


@given(ops=_ops)
@settings(deadline=None, max_examples=75)
def test_invariants_hold_after_any_sequence_of_operations(
    ops: list[tuple[str, int, float]],
) -> None:
    tree: Treap[int] = Treap()
    model: set[int] = set()
    for kind, key, priority in ops:
        if kind == "insert":
            tree.insert(key, priority)
            model.add(key)
        else:
            tree.delete(key)
            model.discard(key)
    check_invariants(tree)
    assert set(tree) == model
    assert list(tree) == sorted(model)
    for key in range(-50, 51):
        assert (key in tree) == (key in model)


@given(
    key=st.integers(),
    priority=st.floats(min_value=0.0, max_value=1.0, allow_nan=False),
    other_keys=st.lists(st.integers(min_value=-50, max_value=50), max_size=40),
)
@settings(deadline=None, max_examples=75)
def test_insert_only_adds_the_given_key(
    key: int, priority: float, other_keys: list[int]
) -> None:
    tree: Treap[int] = Treap()
    for k in other_keys:
        tree.insert(k, 0.5)
    before = set(tree)
    tree.insert(key, priority)
    assert set(tree) == before | {key}
    check_invariants(tree)


@given(
    key=st.integers(),
    other_keys=st.lists(st.integers(min_value=-50, max_value=50), max_size=40),
)
@settings(deadline=None, max_examples=75)
def test_delete_only_removes_the_given_key(key: int, other_keys: list[int]) -> None:
    tree: Treap[int] = Treap()
    for k in other_keys:
        tree.insert(k, 0.5)
    tree.insert(key, 0.9)
    before = set(tree)
    tree.delete(key)
    assert set(tree) == before - {key}
    check_invariants(tree)


# --- delete rotates down: the same tree as joining the two subtrees, by rotations ---------------


def _join(left: _Node[int] | None, right: _Node[int] | None) -> _Node[int] | None:
    """The other way to delete: merge the doomed node's two subtrees, the root of higher priority
    on top (the right one on a tie), as `Treap.join` in the Lean does. Seidel & Aragon note the
    two are equivalent, and a treap with distinct priorities is unique anyway; this is the oracle
    for the ties, where only the tie rule decides the shape."""
    if left is None:
        return right
    if right is None:
        return left
    if left.priority > right.priority:
        left.right = _join(left.right, right)
        return left
    right.left = _join(left, right.left)
    return right


def _delete_by_join(node: _Node[int] | None, key: int) -> _Node[int] | None:
    if node is None:
        return None
    if key < node.key:
        node.left = _delete_by_join(node.left, key)
    elif node.key < key:
        node.right = _delete_by_join(node.right, key)
    else:
        return _join(node.left, node.right)
    return node


def _shape(node: _Node[int] | None) -> str:
    if node is None:
        return "."
    return f"({_shape(node.left)} {node.key}/{node.priority} {_shape(node.right)})"


# Priorities from five values, so that ties -- where the tie rule alone decides the shape -- are
# common.
_tie_heavy_ops = st.lists(
    st.tuples(
        st.sampled_from(["insert", "delete"]),
        st.integers(min_value=0, max_value=30),
        st.integers(min_value=0, max_value=4),
    ),
    max_size=120,
)


@given(ops=_tie_heavy_ops)
@settings(deadline=None, max_examples=150)
def test_delete_builds_the_tree_joining_the_subtrees_would(ops: list[tuple[str, int, int]]) -> None:
    """Rotating the node down and joining its two subtrees leave the same tree, ties included.
    After every delete the two trees are compared node for node, priorities and all."""
    rotated: Treap[int] = Treap()
    joined: Treap[int] = Treap()
    for kind, key, priority in ops:
        if kind == "insert":
            rotated.insert(key, priority)
            joined.insert(key, priority)
        else:
            rotated.delete(key)
            joined.root = _delete_by_join(joined.root, key)
            assert _shape(rotated.root) == _shape(joined.root)
            check_invariants(rotated)


@given(ops=_tie_heavy_ops)
@settings(deadline=None, max_examples=150)
def test_delete_rotates_the_node_all_the_way_down_to_a_leaf(
    ops: list[tuple[str, int, int]],
) -> None:
    """The procedure, not only the tree: a delete makes exactly one rotation per node on the right
    spine of the doomed node's left subtree and the left spine of its right subtree
    (`delete_rotation_count`). Joining makes none, and splicing the node out as soon as it has one
    child makes fewer; both leave the same tree, and only this count tells them apart."""
    tree: Treap[int] = Treap()
    for kind, key, priority in ops:
        if kind == "insert":
            tree.insert(key, priority)
            continue
        expected = delete_rotation_count(tree, key)
        with (
            mock.patch.object(treap_module, "rotate_left", wraps=rotate_left) as left,
            mock.patch.object(treap_module, "rotate_right", wraps=rotate_right) as right,
        ):
            tree.delete(key)
        assert left.call_count + right.call_count == expected


# --- deterministic edge cases, explicit priorities -----------------------------------------------


def test_insert_promotes_to_root_on_highest_priority() -> None:
    tree: Treap[int] = Treap()
    tree.insert(5, 0.1)
    tree.insert(3, 0.2)
    tree.insert(8, 0.3)
    # Each insert so far has beaten the current root's priority, so 8 (the latest, highest) sits
    # at the root: 5 (0.1) -> 3 (0.2, beats 5) -> 8 (0.3, beats 3).
    assert tree.root is not None and tree.root.key == 8

    tree.insert(1, 0.9)  # beats every existing priority -> becomes the new root.

    assert tree.root is not None and tree.root.key == 1
    check_invariants(tree)
    assert list(tree) == [1, 3, 5, 8]


def test_reinsert_existing_key_at_higher_priority_changes_nothing() -> None:
    """A duplicate is ignored, priority included, as the textbooks treat it."""
    tree: Treap[int] = Treap()
    tree.insert(5, 0.1)
    tree.insert(3, 0.2)
    tree.insert(8, 0.3)
    root_before = tree.root.key if tree.root is not None else None

    tree.insert(5, 0.9)

    assert tree.root is not None and tree.root.key == root_before == 8
    assert len(tree) == 3
    check_invariants(tree)
    assert list(tree) == [3, 5, 8]


def test_reinsert_existing_key_at_lower_priority_is_a_noop() -> None:
    tree: Treap[int] = Treap()
    tree.insert(5, 0.9)
    tree.insert(3, 0.2)

    tree.insert(5, 0.1)  # lower priority than the existing node at key 5 -> no-op.

    assert tree.root is not None and tree.root.key == 5
    assert tree.root.priority == 0.9
    check_invariants(tree)


def test_delete_on_empty_tree_is_a_noop() -> None:
    tree: Treap[int] = Treap()
    tree.delete(1)
    assert len(tree) == 0


def test_delete_absent_key_is_a_noop() -> None:
    tree: Treap[int] = Treap()
    for k, p in [(5, 0.5), (3, 0.3), (8, 0.8)]:
        tree.insert(k, p)
    tree.delete(999)
    check_invariants(tree)
    assert set(tree) == {3, 5, 8}


def test_search_on_empty_tree() -> None:
    tree: Treap[int] = Treap()
    assert tree.search(1) is False
    assert 1 not in tree


def test_constructor_accepts_a_seed() -> None:
    tree: Treap[int] = Treap(seed=0)
    assert len(tree) == 0


# --- random-priority convenience path -------------------------------------------------------------


def test_auto_generated_random_priorities_produce_a_valid_findable_tree() -> None:
    """`insert` with no explicit `priority` argument should work end to end: produce a `Valid`
    tree, and every inserted key should be findable afterward."""
    tree: Treap[int] = Treap(seed=0)
    keys = list(range(300))
    random.Random(1).shuffle(keys)
    for k in keys:
        tree.insert(k)  # no explicit priority -> auto-generated via the tree's own rng.
    check_invariants(tree)
    assert set(tree) == set(keys)
    for k in keys:
        assert k in tree
    assert -1 not in tree


# --- Theorem 8.8 (expected <= 2 rotations per insert): loose empirical sanity check ---------------


def test_average_rotation_count_stays_well_under_a_generous_bound() -> None:
    """Motwani & Raghavan Ch. 8, Theorem 8.8 (neither stated nor proved in `Treap/`): under
    uniformly random priorities, a treap insert costs an expected `<= 2` rotations (here,
    `rotation_count` — see that method's docstring for exactly what it measures and why). This is
    a loose sanity check, not a tight statistical test of the "~2" headline figure: it only
    confirms the average stays well under a generous bound (10) across a few thousand random
    inserts, as empirical evidence the randomized balancing is doing its job at all.
    """
    rng = random.Random(42)
    tree: Treap[int] = Treap(seed=42)
    n = 4000
    keys = list(range(n))
    rng.shuffle(keys)

    total_rotations = 0
    for k in keys:
        priority = rng.random()
        total_rotations += rotation_count(tree, k, priority)
        tree.insert(k, priority)

    check_invariants(tree)
    average_rotations = total_rotations / n
    assert average_rotations < 10



def test_insert_and_delete_report_whether_they_changed_the_tree() -> None:
    """As every tree in the chapter: `insert` says whether the key was new, `delete` whether it
    was there. A duplicate still consumes one draw from the tree's priority stream,
    so a seeded run builds the same tree whether or not it repeats a key."""
    tree: Treap[int] = Treap(seed=3)
    assert tree.insert(5) is True and tree.insert(5) is False
    assert tree.delete(7) is False and tree.delete(5) is True
    assert list(tree) == []

    with_duplicate: Treap[int] = Treap(seed=4)
    without: Treap[int] = Treap(seed=4)
    for k in [3, 1, 3, 2]:
        with_duplicate.insert(k)
    for k in [3, 1, 99, 2]:
        without.insert(k)
    without.delete(99)
    # The same keys at the same priorities make the same treap, so the shapes agree only if the
    # duplicate took the draw 99 took.
    assert _shape(with_duplicate.root) == _shape(without.root)


def test_the_rotations_have_no_guard() -> None:
    """The chapter's rotation, which the treap shares with the red-black tree: called on a node
    without the child it lifts, it raises rather than returning the node unchanged."""
    lone: _Node[int] = _Node(1, 0.5)
    with pytest.raises(AttributeError):
        treap_module.rotate_left(lone)
    with pytest.raises(AttributeError):
        treap_module.rotate_right(lone)


# --- The checkers themselves, on trees that break one invariant each --------------------------
#
# Every test above hands `is_valid` a tree `insert` and `delete` built, and those are valid, so
# `is_valid` replaced by `lambda: True` would pass them all. These hand-built trees each break
# exactly one of the two invariants: that invariant's checker and `is_valid` must reject it, and
# the other checker must still accept it. The hand checkers at the top of this file must reject
# each one too, which shows the tree really is broken without trusting the code under test.


def _tn(key: int, priority: float, left: _Node[int] | None = None,
        right: _Node[int] | None = None) -> _Node[int]:
    node: _Node[int] = _Node(key, priority)
    node.left, node.right = left, right
    return node


def _treap(root: _Node[int] | None) -> Treap[int]:
    tree: Treap[int] = Treap()
    tree.root = root
    return tree


def _verdicts(tree: Treap[int]) -> dict[str, bool]:
    return {
        "key_order": _is_sorted(tree.root),
        "heap_order": _heap_ordered(tree.root),
        "valid": tree.is_valid(),
    }


ALL_HOLD = {"key_order": True, "heap_order": True, "valid": True}

VALID = {
    "empty": _treap(None),
    "a parent above its children": _treap(_tn(2, 0.9, _tn(1, 0.5), _tn(3, 0.7))),
    # The heap order is `<=`: `insert` leaves a newcomer that ties its parent below it.
    "every priority tied": _treap(_tn(2, 0.5, _tn(1, 0.5), _tn(3, 0.5))),
}


@pytest.mark.parametrize("name", list(VALID))
def test_a_valid_treap_passes_every_checker(name: str) -> None:
    assert _verdicts(VALID[name]) == ALL_HOLD
    check_invariants(VALID[name])


# (the invariant it breaks, how, the tree)
BROKEN = [
    # 12 is above its parent's 5, as a right child should be, but it hangs left of the root's 10:
    # only a bound carried down from the root sees it.
    ("key_order", "a key on the wrong side of its grandparent",
     _treap(_tn(10, 0.9, _tn(5, 0.8, None, _tn(12, 0.7))))),
    ("key_order", "a key twice", _treap(_tn(3, 0.9, None, _tn(3, 0.5)))),
    ("heap_order", "a child above its parent", _treap(_tn(2, 0.5, _tn(1, 0.9)))),
    ("heap_order", "a grandchild above its parent, below the root",
     _treap(_tn(3, 0.9, _tn(2, 0.5, _tn(1, 0.7))))),
]


@pytest.mark.parametrize("name,how,tree", BROKEN, ids=[how for _, how, _ in BROKEN])
def test_each_checker_rejects_the_invariant_it_names_and_only_that(
    name: str, how: str, tree: Treap[int]
) -> None:
    assert _verdicts(tree) == {**ALL_HOLD, name: False, "valid": False}, how
    with pytest.raises(AssertionError):
        hand_check(tree)


# --- Caller-chosen priorities, and the recursion limit ------------------------------------------
#
# `insert` and `delete` recurse once per level (the class docstring says so), and a caller who
# passes priorities can make a path: keys in increasing order at decreasing priorities each land
# at the bottom right and stay there. This is the BST's degenerate case (`test_bst.py`), reached
# through the priorities rather than the key order. The treap is kept recursive on purpose; what
# these pin is where the limit bites, what it leaves behind, and that raising it is the remedy.


def _is_valid_deep(tree: Treap[int]) -> bool:
    """`is_valid` recurses too, so on a path this deep it needs the raised limit as well."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(4 * (old + 200))
    try:
        return tree.is_valid()
    finally:
        sys.setrecursionlimit(old)


def _right_path(n: int) -> Treap[int]:
    """Keys `0..n-1` on one right-leaning path, built under a raised recursion limit."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(4 * n)
    try:
        tree: Treap[int] = Treap()
        for k in range(n):
            tree.insert(k, float(n - k))
        return tree
    finally:
        sys.setrecursionlimit(old)


def test_insert_on_decreasing_priorities_raises_at_the_limit_and_changes_nothing() -> None:
    n = sys.getrecursionlimit() + 200
    tree: Treap[int] = Treap()
    with pytest.raises(RecursionError):
        for k in range(n):
            tree.insert(k, float(n - k))
    # `k` is the key whose insert ran out of frames. Nothing had been rewired yet: the tree is
    # still the valid path of every key before it, and `k` is not in it.
    assert 0 < k < n
    assert _is_valid_deep(tree)
    assert not tree.search(k)
    assert all(tree.search(j) for j in range(k))


def test_delete_whose_descent_runs_out_raises_and_changes_nothing() -> None:
    n = sys.getrecursionlimit() + 200
    tree = _right_path(n)
    assert _is_valid_deep(tree)
    with pytest.raises(RecursionError):
        tree.delete(n - 1)  # the bottom of the path: the descent itself is too deep
    assert _is_valid_deep(tree)
    assert tree.search(0) and tree.search(n - 1)


def test_delete_that_runs_out_while_rotating_down_loses_keys() -> None:
    """The hazard the class docstring names. A root whose left child heads a long right path
    has to be rotated down that whole path; each rotation rewires links before the next call,
    so when the frames run out the tree has been cut: the root is still there, still holding the
    key being deleted, and the keys it had been rotated past are gone. The tree left behind is a
    valid treap, only of fewer keys. Pinned so that a change to this behaviour is seen."""
    n = sys.getrecursionlimit() + 200
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(4 * n)
    try:
        tree: Treap[int] = Treap()
        tree.insert(n, float(2 * n))  # the root: the largest key at the highest priority
        for k in range(n):
            tree.insert(k, float(n - k))  # a right path under the root's left
    finally:
        sys.setrecursionlimit(old)
    assert _is_valid_deep(tree) and tree.root is not None and tree.root.key == n
    with pytest.raises(RecursionError):
        tree.delete(n)
    assert _is_valid_deep(tree)
    assert tree.search(n)  # the key being deleted is still there
    assert not tree.search(0)  # the top of the path, rotated past, is lost
    assert tree.search(n - 1)  # the bottom of the path, never reached, is kept


def test_a_raised_recursion_limit_is_the_whole_remedy() -> None:
    n = sys.getrecursionlimit() + 200
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(4 * n)
    try:
        tree = _right_path(n)
        assert tree.delete(n - 1) and tree.delete(0) and tree.delete(n // 2)
        assert tree.is_valid() and len(tree) == n - 3
    finally:
        sys.setrecursionlimit(old)


# --- Seeded priorities and the counted updates --------------------------------------------------


def _preorder(node: _Node[int] | None) -> list[tuple[int, float]]:
    if node is None:
        return []
    return [(node.key, node.priority), *_preorder(node.left), *_preorder(node.right)]


def test_a_seed_builds_the_tree_the_rust_builds() -> None:
    """`Treap(seed=7)` draws SplitMix64's stream, one draw per call, the duplicate 3 included.
    The Rust's `Treap::with_seed(7)` test holds the same preorder."""
    tree: Treap[int] = Treap(seed=7)
    for k in [5, 3, 8, 3, 1, 9, 2]:
        tree.insert(k)
    assert _preorder(tree.root) == [
        (8, 16616101746815609346),
        (2, 8632209307422871798),
        (1, 8346079845500723674),
        (5, 7191089600892374487),
        (3, 309689372594955804),
        (9, 4601199455465548305),
    ]


@given(st.lists(st.tuples(st.integers(0, 40), st.integers(0, 6)), max_size=40))
def test_the_counted_insert_rotates_once_per_level_risen(pairs: list[tuple[int, int]]) -> None:
    tree: Treap[int] = Treap()
    for key, priority in pairs:
        if key in tree:
            assert tree.insert_with_rotations(key, priority) == (False, 0)
            continue
        plain = rotation_count(tree, key, priority)
        assert tree.insert_with_rotations(key, priority) == (True, plain)
    check_invariants(tree)


def test_random_updates_average_fewer_than_two_rotations() -> None:
    """The chapter's claim, on 4,000 keys at seeded priorities: both averages come out below two
    (measured: 1.98 per insert and 1.98 per delete)."""
    order = random.Random(1)
    tree: Treap[int] = Treap(seed=1)
    keys = list(range(4000))
    order.shuffle(keys)
    inserted = sum(tree.insert_with_rotations(k)[1] for k in keys)
    order.shuffle(keys)
    deleted = sum(tree.delete_with_rotations(k)[1] for k in keys)
    assert inserted / len(keys) < 2 and deleted / len(keys) < 2
    assert tree.delete_with_rotations(0) == (False, 0)


def test_the_docstring_names_every_method_a_deep_path_breaks() -> None:
    """Keys in increasing order at decreasing priorities hang on one right spine. On a spine
    deeper than the recursion limit, every method the class docstring names raises
    `RecursionError`, and `search`, a loop, does not."""
    depth = sys.getrecursionlimit() + 100
    tree: Treap[int] = Treap()
    tree.root = _Node(0, float(depth))
    node = tree.root
    for k in range(1, depth):
        node.right = _Node(k, float(depth - k))
        node = node.right
    calls = {
        "insert": lambda: tree.insert(depth, 0.0),
        "delete": lambda: tree.delete(depth - 1),
        "iteration": lambda: list(tree),
        "len": lambda: len(tree),
        "is_valid": tree.is_valid,
    }
    for name, call in calls.items():
        with pytest.raises(RecursionError):
            call()
        assert name in (Treap.__doc__ or ""), name
    assert tree.search(depth // 2)
