# SPDX-License-Identifier: Apache-2.0
"""Property-based tests for `algodesign.searching.red_black_standard`, checking exactly the
invariants `lean/AlgoDesign/Searching/RedBlackStandard/Spec.lean` states: `RootBlack` (the root is
black, or the tree is empty), `NoRedRed` (a red node's children are both black), and
`BlackHeightOk` (every root-to-leaf path has the same black-node count, via `black_height`), plus
the ordinary BST ordering and exact-key-affected behavior of `insert`/`delete`.

`RedBlackStandard/` proves both updates -- `insertSpec`, `valid_insert`, `deleteSpec`,
`valid_delete`, `mem_delete` (an iff) and the rotation bounds. Neither is costed there.

`test_the_mirrored_case_1_of_delete_fixup_runs_and_builds_clrs_tree` reaches the mirrored Case 1
of `RB-DELETE-FIXUP` by name. The stress
test at the bottom of this file checks every invariant after *every* operation in a long random
sequence.
"""

from __future__ import annotations

import random
import sys
from itertools import pairwise
from typing import Any
from unittest import mock

from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.searching.red_black_standard import (
    Color,
    RBTree,
    _Node,
    black_height,
    is_no_red_red,
    is_root_black,
)


def assert_valid(tree: RBTree[int]) -> None:
    """Every invariant `RBTree.Valid` bundles, checked together."""
    keys = list(tree)
    assert all(
        a < b for a, b in pairwise(keys)
    ), f"not sorted / has duplicates: {keys}"
    assert is_root_black(tree.root), "root is not black (and tree is non-empty)"
    assert is_no_red_red(tree.root), "a red node has a red child"
    assert (
        black_height(tree.root) is not None
    ), "root-to-leaf paths disagree on black-node count"
    assert tree.is_valid()


# --- Edge cases --------------------------------------------------------------------------------


def test_is_valid_catches_a_stale_parent_pointer() -> None:
    """The colors, the order and the black height all still hold, so only the parent check can
    refuse this tree: one child pointing at the wrong parent, then the root pointing at one."""
    tree = RBTree(range(7))
    assert tree.is_valid()
    assert tree.root is not None and tree.root.left is not None
    tree.root.left.parent = tree.root.right
    assert not tree.is_valid()
    tree.root.left.parent = tree.root
    assert tree.is_valid()
    tree.root.parent = tree.root.left
    assert not tree.is_valid()


def test_check_valid_names_each_invariant_in_the_appendix_order() -> None:
    """Break one rule at a time on a fresh tree and `check_valid` names it, numbered as in the
    book's appendix; invariant 3 is how an empty spot is read, so nothing stored can break it."""

    def tree() -> RBTree[int]:
        t = RBTree(range(15))
        assert t.check_valid() is None and t.root is not None
        return t

    t = tree()
    t.root.left.color = "purple"  # type: ignore[union-attr]
    assert t.check_valid() == "invariant 1 (red_or_black)"
    t = tree()
    t.root.color = Color.RED  # type: ignore[union-attr]
    assert t.check_valid() == "invariant 2 (root_black)"
    t = tree()
    node = t.root.left  # type: ignore[union-attr]
    assert node is not None and node.left is not None
    node.color = node.left.color = Color.RED
    assert t.check_valid() == "invariant 4 (no_red_red)"
    t = tree()
    assert t.root is not None and t.root.left is not None
    t.root.left.color = Color.RED if t.root.left.color is Color.BLACK else Color.BLACK
    assert t.check_valid() == "invariant 5 (black_height_ok)"
    t = tree()
    assert t.root is not None
    t.root.key = -1
    assert t.check_valid() == "not in the box (sorted)"
    t = tree()
    assert t.root is not None and t.root.left is not None
    t.root.left.parent = t.root.right
    assert t.check_valid() == "layout (parents_point_back)"


def test_empty_tree() -> None:
    tree: RBTree[int] = RBTree()
    assert tree.root is None
    assert len(tree) == 0
    assert list(tree) == []
    assert not tree.search(0)
    assert 0 not in tree
    assert_valid(tree)


def test_single_insert() -> None:
    tree: RBTree[int] = RBTree()
    tree.insert(42)
    assert 42 in tree
    assert list(tree) == [42]
    assert len(tree) == 1
    assert_valid(tree)


def test_delete_only_key() -> None:
    tree: RBTree[int] = RBTree()
    tree.insert(7)
    tree.delete(7)
    assert tree.root is None
    assert 7 not in tree
    assert len(tree) == 0
    assert_valid(tree)


def test_delete_absent_key_is_a_no_op() -> None:
    tree: RBTree[int] = RBTree([1, 2, 3])
    tree.delete(999)
    assert list(tree) == [1, 2, 3]
    assert_valid(tree)


def test_insert_duplicate_is_a_no_op() -> None:
    tree: RBTree[int] = RBTree([1, 2, 3])
    tree.insert(2)
    assert list(tree) == [1, 2, 3]
    assert len(tree) == 3
    assert_valid(tree)


def test_search_on_empty_tree() -> None:
    tree: RBTree[int] = RBTree()
    assert not tree.search(123)


# --- BST ordering and exact-key-affected, via Hypothesis -----------------------------------


@given(st.lists(st.integers(min_value=-1000, max_value=1000)))
@settings(max_examples=200)
def test_insert_matches_set_semantics_and_is_sorted(keys: list[int]) -> None:
    tree: RBTree[int] = RBTree()
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
    tree: RBTree[int] = RBTree(keys)
    to_delete = data.draw(st.sampled_from(keys)) if keys else None
    if to_delete is None:
        return
    tree.delete(to_delete)
    expected = sorted(k for k in keys if k != to_delete)
    assert list(tree) == expected
    assert to_delete not in tree
    assert_valid(tree)


# --- The stress test: every invariant, after every single operation ------------------------


def _assert_parent_pointers(tree: RBTree[int]) -> None:
    """Every child points back at its parent, and the root at nothing. `is_valid` checks this
    too, last; the fixups walk *up*, so a wrong parent pointer is a bug the color checks can miss
    until a later fixup follows it."""
    assert tree.root is None or tree.root.parent is None
    stack = [tree.root] if tree.root is not None else []
    while stack:
        node = stack.pop()
        for child in (node.left, node.right):
            if child is not None:
                assert child.parent is node
                stack.append(child)


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
    deletes, asserting every invariant (`RootBlack`, `NoRedRed`, `BlackHeightOk`, BST ordering,
    exact membership against a reference `set`) after *every single operation* — not merely once
    at the end.
    """
    tree: RBTree[int] = RBTree()
    reference: set[int] = set()
    for op, key in ops:
        if op == "insert":
            tree.insert(key)
            reference.add(key)
        else:
            tree.delete(key)
            reference.discard(key)
        _assert_parent_pointers(tree)

        # Checked after this one operation, before moving to the next:
        assert list(tree) == sorted(reference)
        assert len(tree) == len(reference)
        for k in reference:
            assert k in tree
        assert_valid(tree)


# --- The checkers themselves, on trees that break one invariant each --------------------------
#
# Every test above checks trees the implementation built, and a correct implementation only
# builds valid ones -- so replacing every checker with `lambda n: True` left this file green.
# These hand-built trees each break exactly one of `RBTree.Valid`'s conjuncts, and each must be
# rejected by that conjunct's checker and by `is_valid`, while the other checkers still accept
# it. Parent pointers are set as the implementation would set them, though nothing checks them.


def _rb(root: _Node[int] | None) -> RBTree[int]:
    tree: RBTree[int] = RBTree()
    tree.root = root
    return tree


def _node(key: int, color: Color, left: Any = None, right: Any = None) -> _Node[int]:
    node = _Node(key, color, left, right)
    for child in (left, right):
        if child is not None:
            child.parent = node
    return node


def _verdicts(tree: RBTree[int]) -> dict[str, bool]:
    return {
        "root_black": is_root_black(tree.root),
        "no_red_red": is_no_red_red(tree.root),
        "black_height": black_height(tree.root) is not None,
        "valid": tree.is_valid(),
    }


ALL_HOLD = {"root_black": True, "no_red_red": True, "black_height": True, "valid": True}
R, B = Color.RED, Color.BLACK


def test_a_valid_hand_built_tree_passes_every_checker() -> None:
    assert _verdicts(_rb(_node(2, B, _node(1, R), _node(3, R)))) == ALL_HOLD


def test_a_red_right_child_is_legal_here() -> None:
    # The one shape that separates this tree from the LLRB: CLRS allows it, `LLRB.LeftLeaning`
    # does not, and `test_llrb.py` checks the same tree the other way round.
    assert _verdicts(_rb(_node(1, B, None, _node(2, R)))) == ALL_HOLD


def test_each_checker_rejects_the_invariant_it_names_and_only_that() -> None:
    broken = {
        # A red node with a red child.
        "no_red_red": _node(3, B, _node(2, R, _node(1, R))),
        # A black node on one side and NIL on the other: black heights 2 and 1.
        "black_height": _node(2, B, _node(1, B)),
        # A red root.
        "root_black": _node(1, R),
    }
    for name, root in broken.items():
        assert _verdicts(_rb(root)) == {**ALL_HOLD, name: False, "valid": False}, name


def test_is_valid_rejects_a_tree_out_of_key_order() -> None:
    tree = _rb(_node(2, B, _node(3, R)))
    assert _verdicts(tree) == {**ALL_HOLD, "valid": False}


def _rb_shape(node: _Node[int] | None) -> str:
    if node is None:
        return "."
    color = "R" if node.color is Color.RED else "B"
    return f"({_rb_shape(node.left)} {node.key}{color} {_rb_shape(node.right)})"


def test_the_mirrored_case_1_of_delete_fixup_runs_and_builds_clrs_tree() -> None:
    """`RB-DELETE-FIXUP` has eight cases, four and their mirror images, and the Python-to-Rust
    corpus never reaches the mirrored Case 1: `x` a right child whose sibling `w` is red. This tree
    does. Deleting 4, the root, moves its successor 5 up; 5 was black, so `x` (empty) is 5's right
    child, and its sibling 1 is red.

    The case is recognised as it runs: the rotation it makes is `RIGHT-ROTATE(x.p)` while `x.p`
    is red and `x` is its right child -- Case 1 has just colored `x.p` red, and the mirrored
    Case 4, the only other right rotation of `x.p`, colors it black first. Then the result is
    held to the exact tree CLRS's procedure builds, colors included, so a body that runs but
    recolors wrongly fails too. A second tree, whose 4 is deleted the same way, is the one on
    which a Case 1 that forgets to blacken `w` shows."""
    for keys, before, after in [
        (
            [0, 4, 5, 1, 2, 3],
            "(((. 0B .) 1R (. 2B (. 3R .))) 4B (. 5B .))",
            "((. 0B .) 1B ((. 2B .) 3R (. 5B .)))",
        ),
        (  # here a Case 1 that forgets to blacken `w` leaves a red root
            [0, 4, 5, 2, 3, 1],
            "(((. 0B (. 1R .)) 2R (. 3B .)) 4B (. 5B .))",
            "((. 0B (. 1R .)) 2B ((. 3R .) 5B .))",
        ),
    ]:
        _delete_through_the_mirrored_case_1(keys, before, after)


def _delete_through_the_mirrored_case_1(keys: list[int], before: str, after: str) -> None:
    tree: RBTree[int] = RBTree(keys)
    assert _rb_shape(tree.root) == before

    ran = 0
    original = RBTree._rotate_right

    def spy(self: RBTree[int], x: _Node[int]) -> None:
        nonlocal ran
        caller = sys._getframe(1)
        if (
            # A substring, not equality: mutation testing runs the method under a longer name.
            "_delete_fixup" in caller.f_code.co_name
            and caller.f_locals.get("x_parent") is x
            and x.color is Color.RED
            and x.right is caller.f_locals.get("x")
        ):
            ran += 1
        original(self, x)

    with mock.patch.object(RBTree, "_rotate_right", spy):
        tree.delete(4)
    assert ran == 1
    assert _rb_shape(tree.root) == after
    assert_valid(tree)
    _assert_parent_pointers(tree)


def test_insert_and_delete_report_whether_they_changed_the_tree() -> None:
    tree: RBTree[int] = RBTree([2, 1])
    assert tree.insert(3) is True and tree.insert(3) is False
    assert tree.delete(9) is False and tree.delete(1) is True
    assert list(tree) == [2, 3]
    assert_valid(tree)


@given(st.lists(st.integers(0, 200), max_size=120), st.randoms(use_true_random=False))
def test_an_update_makes_at_most_two_or_three_rotations(keys: list[int], rng: random.Random) -> None:
    """CLRS's bounds, as the chapter's appendix states them: at most two rotations per insert,
    at most three per delete."""
    tree: RBTree[int] = RBTree()
    for k in keys:
        assert tree.insert_with_rotations(k)[1] <= 2
    order = list(set(keys))
    rng.shuffle(order)
    for k in order:
        removed, made = tree.delete_with_rotations(k)
        assert removed and made <= 3
    assert tree.delete_with_rotations(0) == (False, 0)
