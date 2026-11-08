# SPDX-License-Identifier: Apache-2.0
"""Property-based tests for `algodesign.searching.btree.BTree`.

`BTree/` proves both updates and prices all three operations: `insertSpec`, `deleteSpec`,
`delete_found`, and `time_searchM_le_log`/`time_insertM_le_log`/`time_deleteM_le_log` in block
transfers.

These tests check that every piece of `Valid` survives arbitrary operation sequences across several
minimum degrees: the library's `is_<piece>` checkers, and hand checkers written the way the proofs
state it (`Bounded`, `SameDepth`, `KeyCountOk`; `valid_iff_legal` ties the two forms together).
"""

from __future__ import annotations

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.searching.btree import (
    BTree,
    _BTNode,
    _leaf_has_no_children,
    is_half_full_to_full,
    is_keys_in_order,
    is_one_more_child,
    is_root_branches,
    is_same_depth,
)

DEGREES = [2, 3, 5]


# --- hand checkers, in the proofs' form: `Bounded`/`SameDepth`/`KeyCountOk` (`BTree/Basic.lean`) ---


def _check_bounded(node: _BTNode[int], lo: int | None, hi: int | None) -> None:
    """`Bounded`: keys sorted (and distinct — this is a `Set`) within `node`, each key strictly
    between `lo` and `hi`, and each child's keys strictly between the two keys (or tree-wide
    bound) flanking it — same recursive shape as `BTree/Basic.lean`'s `Bounded`/`boundsList`.
    """
    keys = node.keys
    assert keys == sorted(keys)
    assert len(keys) == len(set(keys))
    if lo is not None:
        assert all(lo < k for k in keys)
    if hi is not None:
        assert all(k < hi for k in keys)
    if node.leaf:
        return
    assert len(node.children) == len(keys) + 1
    los = [lo, *keys]
    his = [*keys, hi]
    for child, child_lo, child_hi in zip(node.children, los, his):
        _check_bounded(child, child_lo, child_hi)


def _leaf_depths(node: _BTNode[int], depth: int = 0) -> list[int]:
    if node.leaf:
        return [depth]
    depths: list[int] = []
    for child in node.children:
        depths.extend(_leaf_depths(child, depth + 1))
    return depths


def _check_same_depth(node: _BTNode[int]) -> None:
    """`SameDepth`: every leaf in the tree is at the same depth."""
    assert len(set(_leaf_depths(node))) == 1


def _check_key_count(node: _BTNode[int], t: int, is_root: bool) -> None:
    """`KeyCountOk t`: at most `2t - 1` keys everywhere, at least `t - 1` except at the root."""
    n = len(node.keys)
    assert n <= 2 * t - 1
    if not is_root:
        assert n >= t - 1
    if not node.leaf:
        assert (
            n >= 1
        )  # a non-root-collapsed internal node always has a real separator key
        for child in node.children:
            _check_key_count(child, t, is_root=False)


def _check_leaf_flags(node: _BTNode[int]) -> None:
    """`leaf` is stored, as the chapter's node stores it, so it is a second source of truth: it
    must say exactly what the children say, at every node."""
    assert node.leaf == (not node.children)
    for child in node.children:
        _check_leaf_flags(child)


def hand_check(tree: BTree[int]) -> None:
    _check_leaf_flags(tree.root)
    _check_bounded(tree.root, None, None)
    _check_same_depth(tree.root)
    _check_key_count(tree.root, tree.t, is_root=True)


def check_invariants(tree: BTree[int]) -> None:
    """The hand checkers above, then each piece of `Valid` on its own, so a failure names it, and
    `BTree.is_valid`, which must agree with them."""
    hand_check(tree)
    assert is_keys_in_order(tree.root)
    assert is_one_more_child(tree.root)
    assert is_half_full_to_full(tree.root, tree.t)
    assert is_root_branches(tree.root)
    assert is_same_depth(tree.root)
    assert tree.is_valid()


# --- property tests --------------------------------------------------------------------------

_ops = st.lists(
    st.tuples(
        st.sampled_from(["insert", "delete"]), st.integers(min_value=-30, max_value=30)
    ),
    max_size=150,
)


@pytest.mark.parametrize("t", DEGREES)
@given(ops=_ops)
@settings(deadline=None, max_examples=50)
def test_invariants_hold_after_any_sequence_of_operations(
    t: int, ops: list[tuple[str, int]]
) -> None:
    tree: BTree[int] = BTree(t)
    model: set[int] = set()
    for kind, key in ops:
        if kind == "insert":
            tree.insert(key)
            model.add(key)
        else:
            tree.delete(key)
            model.discard(key)
    check_invariants(tree)
    assert set(tree) == model
    assert list(tree) == sorted(model)
    for key in range(-30, 31):
        assert tree.search(key) == (key in model)


@pytest.mark.parametrize("t", DEGREES)
@given(
    key=st.integers(),
    other_keys=st.lists(st.integers(min_value=-30, max_value=30), max_size=40),
)
@settings(deadline=None, max_examples=50)
def test_insert_only_adds_the_given_key(
    t: int, key: int, other_keys: list[int]
) -> None:
    tree: BTree[int] = BTree(t)
    for k in other_keys:
        tree.insert(k)
    before = set(tree)
    tree.insert(key)
    assert set(tree) == before | {key}
    check_invariants(tree)


@pytest.mark.parametrize("t", DEGREES)
@given(
    key=st.integers(),
    other_keys=st.lists(st.integers(min_value=-30, max_value=30), max_size=40),
)
@settings(deadline=None, max_examples=50)
def test_delete_only_removes_the_given_key(
    t: int, key: int, other_keys: list[int]
) -> None:
    tree: BTree[int] = BTree(t)
    for k in other_keys:
        tree.insert(k)
    tree.insert(key)
    before = set(tree)
    tree.delete(key)
    assert set(tree) == before - {key}
    check_invariants(tree)


# --- edge cases --------------------------------------------------------------------------------


def test_constructor_rejects_degree_below_two() -> None:
    with pytest.raises(ValueError):
        BTree(1)


@pytest.mark.parametrize("t", DEGREES)
def test_root_split_on_insert(t: int) -> None:
    tree: BTree[int] = BTree(t)
    for k in range(2 * t - 1):
        tree.insert(k)
    assert tree.root.leaf
    assert len(tree.root.keys) == 2 * t - 1
    check_invariants(tree)

    tree.insert(2 * t - 1)  # one more key forces the root to split.

    assert not tree.root.leaf
    assert len(tree.root.keys) == 1
    assert len(tree.root.children) == 2
    check_invariants(tree)
    assert set(tree) == set(range(2 * t))


@pytest.mark.parametrize("t", DEGREES)
def test_delete_triggers_merge_and_eventual_root_collapse(t: int) -> None:
    tree: BTree[int] = BTree(t)
    keys = list(range(10 * t))
    for k in keys:
        tree.insert(k)
    check_invariants(tree)
    assert (
        not tree.root.leaf
    )  # tall enough that deletes will need to merge along the way.

    for k in keys:
        tree.delete(k)
        check_invariants(tree)

    assert len(tree) == 0
    assert tree.root.leaf
    assert tree.root.keys == []


def test_delete_on_empty_tree_is_a_noop() -> None:
    tree: BTree[int] = BTree(3)
    tree.delete(5)
    assert len(tree) == 0
    check_invariants(tree)


def test_delete_absent_key_is_a_noop() -> None:
    tree: BTree[int] = BTree(2)
    for k in [1, 2, 3, 4, 5]:
        tree.insert(k)
    tree.delete(999)
    check_invariants(tree)
    assert set(tree) == {1, 2, 3, 4, 5}


def test_insert_duplicate_key_is_a_noop() -> None:
    tree: BTree[int] = BTree(2)
    for k in [5, 3, 5, 3, 1]:
        tree.insert(k)
    assert list(tree) == [1, 3, 5]
    assert len(tree) == 3


def test_search_on_empty_tree() -> None:
    tree: BTree[int] = BTree(2)
    assert tree.search(1) is False
    assert 1 not in tree


def test_a_duplicate_of_a_full_roots_median_still_splits_the_root() -> None:
    """`insert`'s docstring, both halves. A full root is split before the descent looks at any
    key, so re-inserting its median grows the tree by a level; a full child whose median is the
    key is left whole. The Lean and the Rust do the same (`AlgoDesignTests/Searching.lean`)."""
    root_case: BTree[int] = BTree(2)
    for k in (1, 2, 3):
        root_case.insert(k)
    assert root_case.root.keys == [1, 2, 3] and not root_case.root.children
    root_case.insert(2)
    assert root_case.root.keys == [2]
    assert [c.keys for c in root_case.root.children] == [[1], [3]]

    child_case: BTree[int] = BTree(2)
    for k in (10, 20, 30, 40, 50, 60, 70):
        child_case.insert(k)
    assert child_case.root.keys == [20, 40]  # the root has room
    full = [c for c in child_case.root.children if len(c.keys) == 3]
    assert len(full) == 1
    median = full[0].keys[1]
    before = [c.keys for c in child_case.root.children]
    child_case.insert(median)
    assert [c.keys for c in child_case.root.children] == before


def test_insert_and_delete_report_whether_they_changed_the_key_set() -> None:
    """`True` when the key set changed. A duplicate of a full root's median returns `False` even
    though the root is split and the tree grows a level: the keys did not change."""
    tree: BTree[int] = BTree(2)
    assert [tree.insert(k) for k in (1, 2, 3)] == [True, True, True]
    assert tree.insert(2) is False
    assert tree.root.keys == [2] and len(tree.root.children) == 2  # a new level all the same
    assert tree.delete(9) is False and tree.delete(1) is True
    assert list(tree) == [2, 3]
    check_invariants(tree)


# --- The checkers themselves, on trees that break one invariant each --------------------------
#
# Every test above hands `is_valid` a tree `insert` and `delete` built, and a correct
# implementation only builds valid ones, so `is_valid` replaced by `lambda: True` would pass them
# all. These hand-built trees each break exactly one piece: that piece's checker and
# `is_valid` must reject it, and every other checker must still accept it, so a checker that
# rejected everything would fail here too. The hand checkers at the top of this file must reject
# each one as well, which shows the tree really is broken without trusting the code under test.


def _bt(keys: list[int], *children: _BTNode[int], leaf: bool | None = None) -> _BTNode[int]:
    """A node with these keys and children; a leaf exactly when it has no children, unless
    `leaf` says otherwise."""
    node: _BTNode[int] = _BTNode(leaf=not children if leaf is None else leaf)
    node.keys, node.children = list(keys), list(children)
    return node


def _btree(root: _BTNode[int], t: int = 2) -> BTree[int]:
    tree: BTree[int] = BTree(t)
    tree.root = root
    return tree


def _verdicts(tree: BTree[int]) -> dict[str, bool]:
    return {
        "keys_in_order": is_keys_in_order(tree.root),
        "one_more_child": is_one_more_child(tree.root),
        "half_full_to_full": is_half_full_to_full(tree.root, tree.t),
        "root_branches": is_root_branches(tree.root),
        "same_depth": is_same_depth(tree.root),
        "leaf_has_no_children": _leaf_has_no_children(tree.root),
        "valid": tree.is_valid(),
    }


ALL_HOLD = {"keys_in_order": True, "one_more_child": True, "half_full_to_full": True,
            "root_branches": True, "same_depth": True, "leaf_has_no_children": True,
            "valid": True}


def _built(t: int, keys: list[int]) -> BTree[int]:
    tree: BTree[int] = BTree(t)
    for k in keys:
        tree.insert(k)
    return tree


VALID = {
    "empty": _btree(_bt([])),
    "one level": _btree(_bt([5], _bt([1]), _bt([7]))),
    "full nodes at t=2": _btree(_bt([4], _bt([1, 2, 3]), _bt([5, 6, 7]))),
    "built at t=3": _built(3, list(range(40))),
}


@pytest.mark.parametrize("name", list(VALID))
def test_a_valid_tree_passes_every_checker(name: str) -> None:
    assert _verdicts(VALID[name]) == ALL_HOLD
    check_invariants(VALID[name])


# (the piece it breaks, how, the tree)
BROKEN = [
    ("leaf_has_no_children", "a node flagged leaf that has children",
     _btree(_bt([5], _bt([1]), _bt([7]), leaf=True))),
    ("one_more_child", "an internal node with one child too many",
     _btree(_bt([5], _bt([1]), _bt([7]), _bt([9])))),
    ("one_more_child", "an internal node with one child too few",
     _btree(_bt([3, 5], _bt([1]), _bt([4])))),
    ("keys_in_order", "a key out of order inside one node", _btree(_bt([2, 1]))),
    ("keys_in_order", "a key twice in one node", _btree(_bt([3, 3]))),
    # 12 is above its parent's 5, as a right child's keys should be, but it hangs left of the
    # root's 10: only an order checked across nodes, not just parent against child, sees it.
    ("keys_in_order", "a key on the wrong side of a separator two levels up",
     _btree(_bt([10], _bt([5], _bt([1]), _bt([12])), _bt([15], _bt([11]), _bt([20]))))),
    ("same_depth", "one leaf a level higher than the others",
     _btree(_bt([5], _bt([1]), _bt([7], _bt([6]), _bt([8]))))),
    ("half_full_to_full", "a node over 2t - 1 keys", _btree(_bt([1, 2, 3, 4]))),
    ("half_full_to_full", "a non-root node under t - 1 keys",
     _btree(_bt([5], _bt([1, 2]), _bt([7])), t=3)),
    ("root_branches", "an internal root with one child and no key", _btree(_bt([], _bt([1])))),
]


@pytest.mark.parametrize("name,how,tree", BROKEN, ids=[how for _, how, _ in BROKEN])
def test_each_checker_rejects_the_invariant_it_names_and_only_that(
    name: str, how: str, tree: BTree[int]
) -> None:
    assert _verdicts(tree) == {**ALL_HOLD, name: False, "valid": False}, how
    with pytest.raises(AssertionError):
        hand_check(tree)
