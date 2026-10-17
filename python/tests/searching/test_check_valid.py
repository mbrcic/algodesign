# SPDX-License-Identifier: Apache-2.0
"""`check_valid` on Searching's boxed structures: each label fires on a structure that breaks
that piece alone, in the order of the Lean `Valid`, and a structure the operations built passes.
"""

from __future__ import annotations

from typing import Any

import pytest

from algodesign.searching.bst import BST
from algodesign.searching.bst import _Node as BSTNode
from algodesign.searching.btree import BTree, _BTNode
from algodesign.searching.llrb import LLRB
from algodesign.searching.llrb import _Node as LLRBNode
from algodesign.searching.lsm import LSM, Shape, is_shape_usable

# --- LLRB ------------------------------------------------------------------------------------


def llrb(red: bool, left: LLRBNode[int] | None, key: int,
         right: LLRBNode[int] | None) -> LLRBNode[int]:
    node: LLRBNode[int] = LLRBNode(key)
    node.red, node.left, node.right = red, left, right
    return node


R, B = True, False


@pytest.mark.parametrize(("root", "label"), [
    (llrb(B, llrb(R, None, 2, None), 1, None), "invariant 1 (sorted)"),
    (llrb(R, None, 1, None), "invariant 2 (root_black)"),
    (llrb(B, None, 1, llrb(R, None, 2, None)), "invariant 3 (left_leaning)"),
    (llrb(B, llrb(R, llrb(R, None, 1, None), 2, None), 3, None), "invariant 4 (no_red_red)"),
    (llrb(B, llrb(B, None, 1, None), 2, None), "invariant 5 (black_height_ok)"),
])
def test_llrb_check_valid_names_each_piece(root: LLRBNode[int], label: str) -> None:
    tree: LLRB[int] = LLRB()
    tree.root = root
    assert tree.check_valid() == label
    assert not tree.is_valid()


def test_llrb_check_valid_passes_a_built_tree() -> None:
    tree: LLRB[int] = LLRB()
    for k in range(20):
        tree.insert(k)
    assert tree.check_valid() is None


# --- B-tree ----------------------------------------------------------------------------------


def bt(keys: list[int], children: list[_BTNode[int]] | None = None) -> _BTNode[int]:
    node: _BTNode[int] = _BTNode(leaf=children is None)
    node.keys = keys
    node.children = children or []
    return node


def btree(root: _BTNode[int], t: int) -> BTree[int]:
    tree: BTree[int] = BTree.__new__(BTree)
    tree.root, tree.t = root, t
    return tree


@pytest.mark.parametrize(("root", "t", "label"), [
    (bt([2, 1]), 2, "invariant 1 (keys_in_order)"),
    (bt([2], [bt([1])]), 2, "invariant 2 (one_more_child)"),
    (bt([1, 2, 3, 4]), 2, "invariant 3 (half_full_to_full)"),
    (bt([], [bt([1])]), 2, "invariant 4 (root_branches)"),
    (bt([3], [bt([1], [bt([0]), bt([2])]), bt([4])]), 2, "invariant 5 (same_depth)"),
    (bt([]), 1, "not in the box (degree_at_least_two)"),
])
def test_btree_check_valid_names_each_piece(root: _BTNode[int], t: int, label: str) -> None:
    tree = btree(root, t)
    assert tree.check_valid() == label
    assert not tree.is_valid()


def test_btree_check_valid_names_the_python_layout_check() -> None:
    leaf = bt([1])
    leaf.children = [bt([0])]
    assert btree(leaf, 2).check_valid() == "layout (leaf_has_no_children)"


def test_btree_check_valid_passes_a_built_tree() -> None:
    tree: BTree[int] = BTree(2)
    for k in range(50):
        tree.insert(k)
    assert tree.check_valid() is None


# --- BST -------------------------------------------------------------------------------------


def bst(left: BSTNode[int] | None, key: int, right: BSTNode[int] | None) -> BSTNode[int]:
    node: BSTNode[int] = BSTNode(key)
    node.left, node.right = left, right
    node.size = 1 + (left.size if left else 0) + (right.size if right else 0)
    return node


def test_bst_check_valid_names_each_check() -> None:
    tree: BST[int] = BST()
    tree.root = bst(bst(None, 2, bst(None, 7, None)), 5, None)
    assert tree.check_valid() == "invariant 1 (sorted)"
    tree.root = bst(bst(None, 2, None), 5, None)
    assert tree.check_valid() is None
    tree.root.size = 3
    assert tree.check_valid() == "layout (sizes_add_up)"


# --- LSM -------------------------------------------------------------------------------------


def live(*keys: int) -> tuple[tuple[int, int | None], ...]:
    return tuple((k, k) for k in keys)


def store(levels: Any) -> LSM[int, int]:
    s: LSM[int, int] = LSM(capacity=2, ratio=2, level0_runs=2)
    s._levels = levels
    return s


@pytest.mark.parametrize(("levels", "label"), [
    (((live(2, 1),),), "invariant 1 (runs_sorted)"),
    (((live(1), live(2), live(3)),), "invariant 2 (few_batches)"),
    (((), (live(1, 2, 3, 4, 5),), (live(6),)), "invariant 2 (few_batches)"),
    (((),), None),
    ((((),),), "not in the box (runs_non_empty)"),
    (((), (((1, None),),)), "not in the box (oldest_run_clean)"),
])
def test_lsm_check_valid_names_each_piece(levels: Any, label: str | None) -> None:
    s = store(levels)
    assert s.check_valid() == label
    assert s.is_valid() == (label is None)


def test_lsm_check_valid_passes_a_built_store() -> None:
    s: LSM[int, int] = LSM(capacity=2, ratio=2, level0_runs=2)
    for k in range(40):
        s.write(k % 7, k)
        if k % 5 == 0:
            s.delete(k % 3)
    assert s.check_valid() is None


@pytest.mark.parametrize("shape", [Shape(0, 2, 2), Shape(2, 1, 2), Shape(2, 2, 0)])
def test_lsm_check_valid_names_an_unusable_shape(shape: Shape) -> None:
    """`ShapeUsable` breaks alone on the empty store at a shape `LSM` would refuse: one shape per
    condition."""
    s = store(())
    s._shape = shape
    assert not is_shape_usable(shape)
    assert s.check_valid() == "not in the box (shape_usable)"
    assert not s.is_valid()
