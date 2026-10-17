# SPDX-License-Identifier: Apache-2.0
"""Property-based tests for `algodesign.searching.llrb`, checking exactly the invariants
`lean/AlgoDesign/Searching/LLRB/Spec.lean` states: `LeftLeaning` (no right link is ever red),
`NoRedRed` (no two red links touch), and `BlackHeightOk` (every root-to-leaf path has the same
black-link count, via `black_height`), plus the ordinary BST ordering and exact-key-affected
behavior of `insert`/`delete`.

`insert` mirrors the Lean file's `LLRB.insert` (`insertSpec`, `valid_insert`). `delete` mirrors
`LLRB.deleteTop`, which is proved too: `valid_deleteTop` for the invariant and
`mem_deleteTop_iff` for exactly which key is removed, assembled as `deleteTopSpec`.

The stress test at the bottom checks every invariant after *every* operation in a long random
sequence. Note that `LLRB.mem_delete` is an
*implication*, unlike the same-named iff in `BST/Delete.lean` and `RedBlackStandard/Delete.lean`; the iff for
this file is `mem_delete_iff`, and `deleteTop` is what the public method actually mirrors.
"""

from __future__ import annotations

import random
from itertools import pairwise
from typing import Any

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.searching._ordering import SupportsLT
from algodesign.searching.llrb import (
    LLRB,
    _Node,
    black_height,
    flip_colors,
    is_left_leaning,
    is_no_red_red,
    is_root_black,
    rotate_left,
    rotate_right,
)


def assert_valid[K: SupportsLT](tree: LLRB[K]) -> None:
    """Every invariant `LLRB.Valid` bundles, checked together."""
    keys = list(tree)
    assert all(
        a < b for a, b in pairwise(keys)
    ), f"not sorted / has duplicates: {keys}"
    assert tree.root is None or not tree.root.red, "root link is not black"
    assert is_left_leaning(tree.root), "a right link is red"
    assert is_no_red_red(tree.root), "two red links touch"
    assert (
        black_height(tree.root) is not None
    ), "root-to-leaf paths disagree on black-link count"
    assert tree.is_valid()


# --- Edge cases --------------------------------------------------------------------------------


def test_empty_tree() -> None:
    tree: LLRB[int] = LLRB()
    assert tree.root is None
    assert len(tree) == 0
    assert list(tree) == []
    assert not tree.search(0)
    assert 0 not in tree
    assert_valid(tree)


def test_single_insert() -> None:
    tree: LLRB[int] = LLRB()
    tree.insert(42)
    assert 42 in tree
    assert list(tree) == [42]
    assert len(tree) == 1
    assert_valid(tree)


def test_delete_only_key() -> None:
    tree: LLRB[int] = LLRB()
    tree.insert(7)
    tree.delete(7)
    assert tree.root is None
    assert 7 not in tree
    assert len(tree) == 0
    assert_valid(tree)


def test_delete_absent_key_is_a_no_op() -> None:
    tree: LLRB[int] = LLRB([1, 2, 3])
    tree.delete(999)
    assert list(tree) == [1, 2, 3]
    assert_valid(tree)


def test_delete_absent_key_leaves_the_shape_alone() -> None:
    """The membership check in `delete` is what makes this true.

    Without it the walk borrows red links on the way down and only then finds out the key was
    never there, and those borrows stay: the tree comes back a different, equally legal LLRB
    holding exactly the same keys. This pins the shape the check protects.
    """
    tree: LLRB[int] = LLRB([1, 2, 3, 4])
    before = _shape(tree)
    tree.delete(0)
    assert list(tree) == [1, 2, 3, 4]
    assert_valid(tree)
    assert _shape(tree) == before


@given(st.lists(st.integers(min_value=-1000, max_value=1000), unique=True))
@settings(max_examples=200)
def test_a_key_that_search_finds_but_no_node_equals_removes_nothing(keys: list[int]) -> None:
    """The chapter's own bug story (the Search chapter, "An early version of the deletion
    definition spliced out a node on reaching an empty right child"): `_delete` must splice only
    when it is standing on the key. Without that check a key that is not there removes the
    largest key below where the walk ends.

    `delete` checks membership first, so an ordinary absent key never reaches that clause. `nan`
    does, through the public method: it is neither below nor above any key, so `search`, which
    decides equality by two `<` tests, reports it present; but it is `==` to no key, so `_delete`
    walks the right spine to the largest key, finds it is not `nan`, and must leave it there.
    It is an absent key that gets past the guard, which is all the story needs."""
    tree: LLRB[float] = LLRB(float(k) for k in keys)
    before = list(tree)
    assert (float("nan") in tree) == bool(keys), (
        "nan must get past delete's membership guard, or this test no longer reaches the clause"
    )
    tree.delete(float("nan"))
    assert list(tree) == before
    assert_valid(tree)


def _shape(tree: LLRB[int]) -> str:
    def go(n: Any) -> str:
        if n is None:
            return "."
        return f"({go(n.left)} {'R' if n.red else 'B'}{n.key} {go(n.right)})"

    return go(tree.root)


def test_insert_duplicate_is_a_no_op() -> None:
    tree: LLRB[int] = LLRB([1, 2, 3])
    tree.insert(2)
    assert list(tree) == [1, 2, 3]
    assert len(tree) == 3
    assert_valid(tree)


def test_search_on_empty_tree() -> None:
    tree: LLRB[int] = LLRB()
    assert not tree.search(123)


# --- BST ordering and exact-key-affected, via Hypothesis -----------------------------------


@given(st.lists(st.integers(min_value=-1000, max_value=1000)))
@settings(max_examples=200)
def test_insert_matches_set_semantics_and_is_sorted(keys: list[int]) -> None:
    tree: LLRB[int] = LLRB()
    for key in keys:
        tree.insert(key)
    assert list(tree) == sorted(set(keys))
    assert len(tree) == len(set(keys))
    assert_valid(tree)


@given(
    st.lists(st.integers(min_value=-1000, max_value=1000), unique=True),
    st.data(),
)
@settings(max_examples=200)
def test_delete_removes_exactly_the_target_key(keys: list[int], data: st.DataObject) -> None:
    tree: LLRB[int] = LLRB(keys)
    to_delete = data.draw(st.sampled_from(keys)) if keys else None
    if to_delete is None:
        return
    tree.delete(to_delete)
    expected = sorted(k for k in keys if k != to_delete)
    assert list(tree) == expected
    assert to_delete not in tree
    assert_valid(tree)


# --- The stress test: every invariant, after every single operation ------------------------


@given(
    st.lists(
        st.tuples(
            st.sampled_from(["insert", "delete"]),
            st.integers(min_value=-30, max_value=30),
        ),
        min_size=1,
        max_size=300,
    )
)
@settings(max_examples=200)
def test_stress_random_insert_delete_sequence_checks_invariants_after_every_op(
    ops: list[tuple[str, int]],
) -> None:
    """The most valuable test in this file: a long random sequence of inserts/deletes, small
    enough key range to force plenty of duplicate inserts and both present- and absent-key
    deletes, asserting every invariant (`LeftLeaning`, `NoRedRed`, `BlackHeightOk`, root black,
    BST ordering, exact membership against a reference `set`) after *every single operation* —
    not merely once at the end.
    """
    tree: LLRB[int] = LLRB()
    reference: set[int] = set()
    for op, key in ops:
        if op == "insert":
            tree.insert(key)
            reference.add(key)
        else:
            tree.delete(key)
            reference.discard(key)

        # Checked after this one operation, before moving to the next:
        assert list(tree) == sorted(reference)
        assert len(tree) == len(reference)
        for k in reference:
            assert k in tree
        assert_valid(tree)


# --- The checkers themselves, on trees that break one invariant each --------------------------
#
# Every test above feeds `assert_valid` and `is_valid` trees the implementation built, and a
# correct implementation only builds valid ones -- so replacing every checker with `lambda n:
# True` left this file green. These hand-built trees each break exactly one of `LLRB.Valid`'s
# conjuncts, and each must be rejected by that conjunct's checker and by `is_valid`, while the
# other checkers still accept it: a checker that rejected everything would fail here too.


def _llrb(root: _Node[int] | None) -> LLRB[int]:
    tree: LLRB[int] = LLRB()
    tree.root = root
    return tree


def _node(key: int, red: bool, left: Any, right: Any) -> _Node[int]:
    node: _Node[int] = _Node(key)
    node.red, node.left, node.right = red, left, right
    return node


def _red(key: int, left: Any = None, right: Any = None) -> _Node[int]:
    return _node(key, True, left, right)


def _black(key: int, left: Any = None, right: Any = None) -> _Node[int]:
    return _node(key, False, left, right)


def _verdicts(tree: LLRB[int]) -> dict[str, bool]:
    return {
        "root_black": is_root_black(tree.root),
        "left_leaning": is_left_leaning(tree.root),
        "no_red_red": is_no_red_red(tree.root),
        "black_height": black_height(tree.root) is not None,
        "valid": tree.is_valid(),
    }


ALL_HOLD = {"root_black": True, "left_leaning": True, "no_red_red": True, "black_height": True,
            "valid": True}


def test_a_valid_hand_built_tree_passes_every_checker() -> None:
    assert _verdicts(_llrb(_black(2, _red(1)))) == ALL_HOLD


def test_each_checker_rejects_the_invariant_it_names_and_only_that() -> None:
    broken = {
        # A red *right* link: legal in a classical red-black tree, forbidden here.
        "left_leaning": _black(1, None, _red(2)),
        # Two red links in a row down the left spine.
        "no_red_red": _black(3, _red(2, _red(1))),
        # A black node on one side and nothing on the other: black heights 2 and 1.
        "black_height": _black(2, _black(1)),
        # A red root link.
        "root_black": _red(1),
    }
    for name, root in broken.items():
        assert _verdicts(_llrb(root)) == {**ALL_HOLD, name: False, "valid": False}, name


def test_is_valid_rejects_a_tree_out_of_key_order() -> None:
    # Every color invariant holds; only the ordering is wrong.
    tree = _llrb(_black(2, _red(3)))
    assert _verdicts(tree) == {**ALL_HOLD, "valid": False}


# --- The printed helpers have no guard ----------------------------------------------------------


def test_a_helper_called_without_the_child_it_needs_raises() -> None:
    """The chapter's `rotate_left`, `rotate_right` and `flip_colors` have no guard, and neither do
    these: a call without the child it needs raises, rather than returning the node unchanged
    and hiding a caller's bug."""
    lone = _black(1)
    with pytest.raises(AttributeError):
        rotate_left(lone)
    with pytest.raises(AttributeError):
        rotate_right(lone)
    with pytest.raises(AttributeError):
        flip_colors(_black(2, _red(1)))  # no right child
    assert lone.left is None and lone.right is None and not lone.red


# --- delete_min, the chapter's delete_min_from ---------------------------------------------------


@given(st.lists(st.integers(min_value=-1000, max_value=1000), unique=True, max_size=60))
@settings(max_examples=200)
def test_delete_min_removes_the_smallest_key_and_keeps_every_invariant(keys: list[int]) -> None:
    """`LLRB.delete_min` runs the chapter's `delete_min_from`: color the root red if it has no
    red link below, walk left pushing a red link ahead, color the root black. Drained key by key,
    the tree gives the keys back in order and stays valid after every step; an empty tree answers
    `None` and stays empty, where the printed function assumes a root."""
    tree: LLRB[int] = LLRB(keys)
    for expected in sorted(keys):
        assert tree.delete_min() == expected
        assert expected not in tree
        assert_valid(tree)
    assert tree.root is None and tree.delete_min() is None and tree.root is None


def test_insert_and_delete_report_whether_they_changed_the_tree() -> None:
    tree: LLRB[int] = LLRB([2, 1])
    assert tree.insert(3) is True and tree.insert(3) is False
    assert tree.delete(9) is False and tree.delete(1) is True
    assert list(tree) == [2, 3]


def test_the_chapters_rotation_counts() -> None:
    """The chapter's figures, rerun: three trees of 4,096 distinct random keys from 0 to 40,959,
    seed 1, each built in random order and then half deleted in another. Measured: up to 11
    rotations for one insert, up to 15 for one delete, 4.91 per delete on average."""
    rng = random.Random(1)
    most_insert = most_delete = deleted = rotations = 0
    for _ in range(3):
        keys = rng.sample(range(40960), 4096)
        tree: LLRB[int] = LLRB()
        for k in keys:
            most_insert = max(most_insert, tree.insert_with_rotations(k)[1])
        order = keys[:]
        rng.shuffle(order)
        for k in order[:2048]:
            removed, made = tree.delete_with_rotations(k)
            assert removed
            most_delete = max(most_delete, made)
            rotations += made
            deleted += 1
        assert tree.is_valid()
    assert (most_insert, most_delete, round(rotations / deleted, 2)) == (11, 15, 4.91)
    assert LLRB([1]).insert_with_rotations(1) == (False, 0)
