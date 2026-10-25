# SPDX-License-Identifier: Apache-2.0
"""Tests for `algodesign.searching.bst.BST`.

Property-based tests (via `hypothesis`) check the same correctness statements the Lean file
proves formally (`mem_insert`, `search_correct`, `mem_delete`, `rank_select?`/`select?_rank`,
`floor?_correct`/`ceiling?_correct`, ...) empirically, against reference implementations built
from plain Python `list`/`set`. Hand-written cases cover the structural edge cases (empty tree,
single node, deleting nodes with 0/1/2 children) that random generation covers only probabilistically.
"""

from __future__ import annotations

import sys
from typing import Any
from unittest import mock

import pytest
from hypothesis import assume, given
from hypothesis import strategies as st

from algodesign.searching.bst import BST, _Node, is_sorted, sizes_add_up

# Generated trees stay small: the reference answers below are naive, and small trees are enough to
# reach every case.
_KEYS = st.integers(min_value=-1000, max_value=1000)
_KEY_LISTS = st.lists(_KEYS, max_size=60)
_UNIQUE_KEY_LISTS = st.lists(_KEYS, max_size=60, unique=True)


def _build(keys: list[int]) -> BST[int]:
    tree: BST[int] = BST()
    for k in keys:
        tree.insert(k)
    return tree


def _naive_floor(keys: list[int], a: int) -> int | None:
    candidates = [k for k in keys if k <= a]
    return max(candidates) if candidates else None


def _naive_ceiling(keys: list[int], a: int) -> int | None:
    candidates = [k for k in keys if k >= a]
    return min(candidates) if candidates else None


# --- Empty tree / single node edge cases --------------------------------------------------------


def test_built_from_an_iterable() -> None:
    """`BST(keys)` inserts each key in turn, as `LLRB(keys)` does; duplicates are dropped."""
    tree: BST[int] = BST([2, 1, 3, 2])
    assert list(tree) == [1, 2, 3]
    assert tree.is_valid()


def test_empty_tree() -> None:
    tree: BST[int] = BST()
    assert tree.size() == 0
    assert len(tree) == 0
    assert tree.search(0) is False
    assert 0 not in tree
    assert tree.min() is None
    assert tree.max() is None
    assert tree.floor(0) is None
    assert tree.ceiling(0) is None
    assert tree.rank(0) == 0
    assert tree.select(0) is None
    assert list(tree) == []
    tree.delete(0)  # no-op, must not raise
    assert tree.size() == 0


def test_single_node() -> None:
    tree: BST[int] = BST()
    tree.insert(42)
    assert tree.size() == 1
    assert 42 in tree
    assert tree.min() == 42
    assert tree.max() == 42
    assert tree.floor(42) == 42
    assert tree.floor(100) == 42
    assert tree.floor(0) is None
    assert tree.ceiling(42) == 42
    assert tree.ceiling(0) == 42
    assert tree.ceiling(100) is None
    assert tree.rank(42) == 0
    assert tree.rank(100) == 1
    assert tree.select(0) == 42
    assert tree.select(1) is None
    assert list(tree) == [42]


def test_delete_single_node_root_empties_tree() -> None:
    tree: BST[int] = BST()
    tree.insert(7)
    tree.delete(7)
    assert tree.size() == 0
    assert 7 not in tree
    assert list(tree) == []


# --- Hand-built cases for delete with 0/1/2 children --------------------------------------------


def test_delete_leaf_zero_children() -> None:
    #      5
    #    /   \
    #   3     8
    tree: BST[int] = BST()
    for k in (5, 3, 8):
        tree.insert(k)
    tree.delete(3)
    assert list(tree) == [5, 8]
    assert 3 not in tree


def test_delete_node_one_child() -> None:
    #      5
    #    /   \
    #   3     8
    #    \
    #     4
    tree: BST[int] = BST()
    for k in (5, 3, 8, 4):
        tree.insert(k)
    tree.delete(3)
    assert list(tree) == [4, 5, 8]
    assert 3 not in tree
    assert 4 in tree


def test_delete_node_two_children_successor_is_direct_child() -> None:
    #      5
    #    /   \
    #   3     8
    #  / \
    # 1   4
    tree: BST[int] = BST()
    for k in (5, 3, 8, 1, 4):
        tree.insert(k)
    tree.delete(3)
    # In-order successor of 3 is 4 (min of 3's right subtree, which is just {4}).
    assert list(tree) == [1, 4, 5, 8]
    assert 3 not in tree
    assert set(tree) == {1, 4, 5, 8}


def test_delete_node_two_children_successor_is_deeper() -> None:
    #          5
    #        /   \
    #       3     10
    #      / \    /
    #     1   4  7
    #            \
    #             8
    tree: BST[int] = BST()
    for k in (5, 3, 10, 1, 4, 7, 8):
        tree.insert(k)
    tree.delete(5)
    # In-order successor of 5 is 7 (min of 5's right subtree {10, 7, 8}).
    assert list(tree) == [1, 3, 4, 7, 8, 10]
    assert 5 not in tree
    assert 7 in tree


def test_delete_root_with_two_children() -> None:
    tree: BST[int] = BST()
    for k in (5, 3, 8, 1, 4, 7, 9):
        tree.insert(k)
    tree.delete(5)
    assert 5 not in tree
    assert list(tree) == [1, 3, 4, 7, 8, 9]


# --- Property-based tests ------------------------------------------------------------------------


@given(_KEY_LISTS)
def test_insert_then_search_finds_every_inserted_key(keys: list[int]) -> None:
    """`mem_insert`: after inserting a key, searching for it succeeds."""
    tree = _build(keys)
    for k in keys:
        assert tree.search(k) is True
        assert k in tree


@given(_UNIQUE_KEY_LISTS, _KEYS)
def test_search_never_inserted_key_fails(keys: list[int], probe: int) -> None:
    """`search_correct`: searching for a key that was never inserted fails."""
    assume(probe not in keys)
    tree = _build(keys)
    assert tree.search(probe) is False
    assert probe not in tree


@given(st.lists(st.tuples(st.sampled_from(["insert", "delete"]), _KEYS), max_size=80))
def test_inorder_stays_sorted_after_any_operation_sequence(ops: list[tuple[str, int]]) -> None:
    """In-order traversal stays sorted (strictly increasing, no duplicates) after any sequence
    of `insert`/`delete` operations — the empirical counterpart of `Sorted` being preserved by
    both (`sorted_insert`, `sorted_delete`), witnessed via `inorder`."""
    tree: BST[int] = BST()
    reference: set[int] = set()
    for op, key in ops:
        if op == "insert":
            tree.insert(key)
            reference.add(key)
        else:
            tree.delete(key)
            reference.discard(key)

        result = list(tree)
        assert result == sorted(result), "in-order traversal must be sorted"
        assert len(result) == len(
            set(result)
        ), "in-order traversal must have no duplicates"
        assert set(result) == reference
        assert tree.size() == len(reference)


@given(_UNIQUE_KEY_LISTS, _KEYS)
def test_delete_removes_exactly_the_target_key(keys: list[int], target: int) -> None:
    """`mem_delete`: deleting `a` removes `a` and leaves every other key untouched."""
    tree = _build(keys)
    was_present = target in keys
    tree.delete(target)

    assert target not in tree
    expected_remaining = {k for k in keys if k != target}
    assert set(tree) == expected_remaining
    assert tree.size() == len(expected_remaining)
    assert tree.size() == len(keys) - (1 if was_present else 0)


@given(_UNIQUE_KEY_LISTS)
def test_rank_select_are_inverses_on_present_keys(keys: list[int]) -> None:
    """`rank_select?` / `select?_rank`: `rank` and `select` are inverse operations on present
    keys."""
    tree = _build(keys)
    for k in keys:
        r = tree.rank(k)
        assert 0 <= r < tree.size()
        assert tree.select(r) == k

    # And select-then-rank round-trips over every valid index, i.e. select? enumerates the sorted
    # order exactly (this also re-derives that `select(i)` matches plain sorted-list indexing).
    sorted_keys = sorted(keys)
    for i, k in enumerate(sorted_keys):
        assert tree.select(i) == k
        assert tree.rank(k) == i


@given(_UNIQUE_KEY_LISTS, _KEYS)
def test_floor_matches_naive_linear_scan(keys: list[int], probe: int) -> None:
    """`floor?_correct`, checked against a naive O(n) linear-scan reference."""
    tree = _build(keys)
    assert tree.floor(probe) == _naive_floor(keys, probe)


@given(_UNIQUE_KEY_LISTS, _KEYS)
def test_ceiling_matches_naive_linear_scan(keys: list[int], probe: int) -> None:
    """`ceiling?_correct`, checked against a naive O(n) linear-scan reference."""
    tree = _build(keys)
    assert tree.ceiling(probe) == _naive_ceiling(keys, probe)


@given(_KEY_LISTS, _KEYS, _KEYS)
def test_range_matches_a_sorted_list(keys: list[int], lo: int, hi: int) -> None:
    oracle = [k for k in sorted(set(keys)) if lo <= k <= hi]
    assert _build(keys).range(lo, hi) == oracle


def test_range_includes_both_ends() -> None:
    tree = BST(k * 10 for k in range(1, 10))
    assert tree.range(35, 60) == [40, 50, 60]
    assert tree.range(40, 40) == [40]
    assert tree.range(60, 35) == []
    assert BST[int]().range(0, 9) == []


@given(_KEY_LISTS)
def test_min_max_match_naive_reference(keys: list[int]) -> None:
    tree = _build(keys)
    if keys:
        assert tree.min() == min(keys)
        assert tree.max() == max(keys)
    else:
        assert tree.min() is None
        assert tree.max() is None


@given(_KEY_LISTS)
def test_size_matches_number_of_distinct_keys(keys: list[int]) -> None:
    tree = _build(keys)
    assert tree.size() == len(set(keys))
    assert len(tree) == len(set(keys))


@given(_UNIQUE_KEY_LISTS)
def test_duplicate_insert_is_a_no_op(keys: list[int]) -> None:
    """Inserting an already-present key doesn't change the tree's key set or size (this models a
    *set*, per the Lean file's docstring)."""
    tree = _build(keys)
    before = list(tree)
    before_size = tree.size()
    for k in keys:
        tree.insert(k)
    assert list(tree) == before
    assert tree.size() == before_size


# --- The cached sizes, and the depth the chapter is about -------------------------------------


def _check_sizes(node: _Node[int] | None) -> int:
    """Walk the tree the way the Lean `size` does, and require every node's cached `size` to be
    that walked count. Returns the count. Iterative, so it can check the degenerate path too."""
    if node is None:
        return 0
    order: list[_Node[int]] = []
    stack = [node]
    while stack:
        n = stack.pop()
        order.append(n)
        stack.extend(c for c in (n.left, n.right) if c is not None)
    walked: dict[int, int] = {}
    for n in reversed(order):  # children before parents
        count = 1 + sum(walked[id(c)] for c in (n.left, n.right) if c is not None)
        assert n.size == count, f"node {n.key} caches size {n.size}, holds {count}"
        walked[id(n)] = count
    return walked[id(node)]


_OPS = st.lists(
    st.tuples(st.sampled_from(["insert", "delete", "delete_hibbard"]), st.integers(0, 40)),
    max_size=80,
)


@given(_OPS)
def test_every_cached_size_is_the_walked_size_after_any_operations(ops: Any) -> None:
    """The cache is what makes `rank` and `select` `O(h)`; this is what makes it trustworthy.
    Every node, after every operation, across both deletions and absent keys too."""
    tree: BST[int] = BST()
    model: set[int] = set()
    for op, k in ops:
        if op == "insert":
            assert tree.insert(k) == (k not in model)
            model.add(k)
        else:
            assert getattr(tree, op)(k) == (k in model)
            model.discard(k)
        assert _check_sizes(tree.root) == len(model) == len(tree)
        assert tree.is_valid()


def test_sorted_keys_build_a_path() -> None:
    """The chapter's degenerate case: keys arriving in order each go right, so the tree is a path
    as deep as the list is long, and every operation costs `n` instead of `log n`."""
    n = 500
    tree = _build(list(range(n)))
    depth, node = 0, tree.root
    while node is not None:
        assert node.left is None
        depth, node = depth + 1, node.right
    assert depth == n
    assert tree.rank(n // 2) == n // 2 and tree.select(n - 1) == n - 1
    assert tree.delete(n - 1) and tree.delete_hibbard(0)
    assert len(tree) == n - 2 == _check_sizes(tree.root)


def test_a_path_past_the_recursion_limit_raises_and_survives_a_raised_recursion_limit() -> None:
    """The documented limit. Sorted keys build a path; `insert`, the page's loop, hangs every one
    of them, but the recursive walks run out of frames past Python's recursion limit and raise
    `RecursionError` -- the chapter's degenerate case arriving as a crash. Recursion is kept on
    purpose, as the plainest rendering of the walk; what this pins is that the limit is the one
    the docstring states and that raising it is the whole remedy."""
    n = sys.getrecursionlimit() + 200
    tree: BST[int] = BST()
    for k in range(n):
        assert tree.insert(k)
    assert len(tree) == n  # the root's stored size: no walk
    with pytest.raises(RecursionError):
        tree.search(n - 1)

    old = sys.getrecursionlimit()
    sys.setrecursionlimit(4 * n)
    try:
        deep = _build(list(range(n)))
        assert len(deep) == n and deep.search(n - 1) and deep.rank(n - 1) == n - 1
        assert deep.delete(n - 1) and deep.delete_hibbard(0) and len(deep) == n - 2
    finally:
        sys.setrecursionlimit(old)


# --- rank, select and len read the cached sizes ------------------------------------------------


def _balanced(n_levels: int) -> BST[int]:
    """The perfect tree on `0 .. 2**n_levels - 2`, built by inserting medians first."""
    tree: BST[int] = BST()

    def fill(lo: int, hi: int) -> None:
        if lo < hi:
            mid = (lo + hi) // 2
            tree.insert(mid)
            fill(lo, mid)
            fill(mid + 1, hi)

    fill(0, 2**n_levels - 1)
    return tree


def test_len_rank_and_select_read_the_cached_sizes() -> None:
    """The cache is only worth keeping if the queries read it. Walking the subtrees instead gives
    every answer right on an honest tree and costs `O(n)` a query, which is what the size field
    exists to avoid -- and it passes every test that checks the cache's *values*. So the cache is
    tampered with here, and each query must report the tampered number: proof that it read the
    field rather than counting."""
    tree = _balanced(4)  # 15 keys, 7 at the root
    root = tree.root
    assert root is not None and root.left is not None and root.key == 7
    root.size = 1000
    assert len(tree) == tree.size() == 1000
    root.size = 15
    root.left.size += 100
    assert tree.rank(7) == 107  # the left subtree's size, as stored
    assert tree.select(7) != 7  # position 7 now looks as if it were inside the left subtree


class _Counted(int):
    """An `int` key that counts every comparison made with it, whichever side it is on: Python
    asks a subclass's reflected method first, so `node.key < key` with `key` a `_Counted` comes
    here as `key.__gt__(node.key)`. All six are counted, so no spelling of a comparison escapes."""

    comparisons = 0

    def __lt__(self, other: int) -> bool:
        _Counted.comparisons += 1
        return int(self) < int(other)

    def __gt__(self, other: int) -> bool:
        _Counted.comparisons += 1
        return int(self) > int(other)

    def __le__(self, other: int) -> bool:
        _Counted.comparisons += 1
        return int(self) <= int(other)

    def __ge__(self, other: int) -> bool:
        _Counted.comparisons += 1
        return int(self) >= int(other)

    def __eq__(self, other: object) -> bool:
        _Counted.comparisons += 1
        return isinstance(other, int) and int(self) == int(other)

    def __ne__(self, other: object) -> bool:
        _Counted.comparisons += 1
        return not (isinstance(other, int) and int(self) == int(other))

    def __hash__(self) -> int:
        return int.__hash__(self)


def test_rank_costs_the_height() -> None:
    """On a perfect tree of 1023 keys, height 10, `rank` makes at most two comparisons a level --
    one to go left, one to go right -- for every key present and every gap between them."""
    tree = _balanced(10)
    height = 10
    worst = 0
    for probe in range(-1, 1024):
        _Counted.comparisons = 0
        assert tree.rank(_Counted(probe)) == max(0, min(probe, 1023))
        worst = max(worst, _Counted.comparisons)
    assert worst <= 2 * height, worst


# --- delete is CLRS's TREE-DELETE, TRANSPLANT and all -------------------------------------------


def test_transplant_re_points_the_parent_and_nothing_else() -> None:
    """CLRS's `TRANSPLANT(T, u, v)`: `u`'s parent -- or the root, when `u` is the root -- now
    points at `v`, on the side `u` was on; `v` keeps its own children, and `u` is not touched."""
    tree = _balanced(3)  # 3 at the root, 1 and 5 below it
    root = tree.root
    assert root is not None and root.left is not None and root.right is not None
    left, right = root.left, root.right
    v = _Node(42)
    v_left = _Node(41)
    v.left = v_left

    tree._transplant(root, left, v)
    assert root.left is v and root.right is right and v.left is v_left and v.right is None
    tree._transplant(root, right, None)
    assert root.left is v and root.right is None
    tree._transplant(None, root, left)
    assert tree.root is left and left.left is not None and left.left.key == 0


def _transplant_calls(method: str, keys: list[int], key: int) -> list[tuple[int | None, ...]]:
    """The `(parent, u, v)` keys of every `_transplant` call one deletion makes."""
    tree = _build(keys)
    with mock.patch.object(BST, "_transplant", autospec=True, side_effect=BST._transplant) as spy:
        assert getattr(tree, method)(key)
    return [
        tuple(None if n is None else n.key for n in call.args[1:]) for call in spy.call_args_list
    ]


def test_delete_runs_tree_delete_through_transplant() -> None:
    """The procedure the chapter names, told apart from a recursive delete that returns the new
    subtree to its caller -- the same nodes move either way, so node identity cannot tell them
    apart, but the `TRANSPLANT` calls can. One for a node with at most one child, and one for a
    successor that is `z.right` itself; two for a successor deeper down, which is first replaced
    by its right child and then stands in for `z`."""
    #        50
    #      /    \
    #    30      70
    #   /  \    /  \
    #  20  40  60   80
    #            \
    #             65
    keys = [50, 30, 70, 20, 40, 60, 80, 65]
    assert _transplant_calls("delete", keys, 20) == [(30, 20, None)]  # a leaf
    assert _transplant_calls("delete", keys, 60) == [(70, 60, 65)]  # one child
    assert _transplant_calls("delete", keys, 30) == [(50, 30, 40)]  # y is z.right
    assert _transplant_calls("delete", keys, 50) == [(70, 60, 65), (None, 50, 60)]  # y deeper
    # Copying the key moves no successor into z's place: its one TRANSPLANT removes y.
    assert _transplant_calls("delete_hibbard", keys, 50) == [(70, 60, 65)]
    # Here y's parent is z itself, which already holds 40 by the time y is replaced.
    assert _transplant_calls("delete_hibbard", keys, 30) == [(40, 40, None)]


def test_insert_and_delete_report_whether_they_changed_the_tree() -> None:
    """The chapter's warning: a structure that refuses duplicates loses the second one, and the
    only warning is the value `insert` returns. So a duplicate insert returns `False`, and so does
    deleting a key that is not there; both leave every size alone."""
    tree = _build([50, 30, 70])
    assert tree.insert(40) is True and tree.insert(40) is False
    assert tree.delete(99) is False and tree.delete_hibbard(99) is False
    assert tree.delete(30) is True and tree.delete_hibbard(70) is True
    assert list(tree) == [40, 50] and _check_sizes(tree.root) == 2


def test_the_delete_walk_asks_what_search_asks() -> None:
    """Every walk decides "is this the key?" the way `search` does, `==` first. A key that is
    equal to nothing -- `nan` -- is therefore absent to both: `delete` must not find, and remove,
    a node that `search` says is not there, which is the chapter's wrong-key story again."""
    tree: BST[float] = BST()
    for k in [2.0, 1.0, 3.0]:
        tree.insert(k)
    nan = float("nan")
    assert nan not in tree
    assert tree.delete(nan) is False and tree.delete_hibbard(nan) is False
    assert list(tree) == [1.0, 2.0, 3.0] and tree.size() == 3


def test_insert_is_one_descent() -> None:
    """The page's loop asks each node on the way down `==` and then `<`, once each, and hangs the
    key: one descent. A second walk -- a membership check first, or a pass to fix the sizes
    afterwards -- costs a second round of comparisons for the same answer. On a perfect tree of
    1023 keys every new key passes ten nodes, and every present key at most ten."""
    tree = _balanced(10)
    for probe in [-5, 0, 511, 1022, 1030]:
        _Counted.comparisons = 0
        new = tree.insert(_Counted(probe))
        assert new == (probe not in range(1023))
        assert _Counted.comparisons <= 2 * 10, (probe, _Counted.comparisons)
    assert _check_sizes(tree.root) == 1023 + 2


# --- The checker itself, on trees that break one invariant each ----------------------------------
#
# Every other `is_valid` call in this file is on a tree `insert` and the deletions built, and
# those are valid, so `is_valid` replaced by `lambda: True` would pass them all. These hand-built
# trees each break exactly one of the two conjuncts: that conjunct's checker and `is_valid` must
# reject it, and the other must still accept it. `_check_sizes`, the walked count above, rejects
# each broken size too, without trusting the code under test.


def _bn(key: int, left: _Node[int] | None = None, right: _Node[int] | None = None,
        size: int | None = None) -> _Node[int]:
    """A node over these children, its `size` the true count unless `size` says otherwise."""
    node: _Node[int] = _Node(key)
    node.left, node.right = left, right
    node.size = size if size is not None else (
        1 + (left.size if left else 0) + (right.size if right else 0))
    return node


def _bst(root: _Node[int] | None) -> BST[int]:
    tree: BST[int] = BST()
    tree.root = root
    return tree


def _verdicts(tree: BST[int]) -> dict[str, bool]:
    return {
        "key_order": is_sorted(tree.root),
        "sizes": sizes_add_up(tree.root),
        "valid": tree.is_valid(),
    }


ALL_HOLD = {"key_order": True, "sizes": True, "valid": True}


@pytest.mark.parametrize("tree", [_bst(None), _bst(_bn(2, _bn(1), _bn(3))), _balanced(4)],
                         ids=["empty", "three keys", "fifteen keys"])
def test_a_valid_tree_passes_every_checker(tree: BST[int]) -> None:
    assert _verdicts(tree) == ALL_HOLD


# (the conjunct it breaks, how, the tree)
BROKEN = [
    # 12 is above its parent's 5, as a right child should be, but it hangs left of the root's 10:
    # only a bound carried down from the root sees it.
    ("key_order", "a key on the wrong side of its grandparent",
     _bst(_bn(10, _bn(5, None, _bn(12))))),
    ("key_order", "a key twice", _bst(_bn(3, None, _bn(3)))),
    ("sizes", "a leaf counting two", _bst(_bn(1, size=2))),
    ("sizes", "a root that missed a key below it", _bst(_bn(2, _bn(1), _bn(3), size=2))),
    # The root's 4 is one more than its children's stored 2 and 1, so only the leaf is wrong.
    ("sizes", "a wrong size below a root that agrees with it",
     _bst(_bn(2, _bn(1, size=2), _bn(3), size=4))),
]


@pytest.mark.parametrize("name,how,tree", BROKEN, ids=[how for _, how, _ in BROKEN])
def test_each_checker_rejects_the_invariant_it_names_and_only_that(
    name: str, how: str, tree: BST[int]
) -> None:
    assert _verdicts(tree) == {**ALL_HOLD, name: False, "valid": False}, how
    if name == "sizes":
        with pytest.raises(AssertionError):
            _check_sizes(tree.root)
