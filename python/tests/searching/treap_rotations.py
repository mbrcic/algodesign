# SPDX-License-Identifier: Apache-2.0
"""Test-only instrumentation for the treap: how many rotations an insert or a delete makes.

Motwani & Raghavan's Theorem 8.8 bounds the expected number of rotations per insert by 2, and a
delete, which runs the same rotations backwards, by the same. The tests measure both with the
functions below, which read the tree without changing it. They live here, not in `treap.py`,
because the printed code is the algorithm and this is a measurement of it.
"""

from __future__ import annotations

from typing import Any

from algodesign.searching.treap import Treap


def insert_steps(node: Any, key: Any, priority: float) -> int:
    """The depth `key` would end up at if inserted at `priority` below `node` right now: walk the
    search path until an empty subtree or a node whose priority `priority` beats -- the point
    where `insert` would make `key` that subtree's root."""
    if node is None or priority > node.priority:
        return 0
    if key < node.key:
        return insert_steps(node.left, key, priority) + 1
    if node.key < key:
        return insert_steps(node.right, key, priority) + 1
    return 0


def rotation_count(tree: Treap[int], key: Any, priority: float) -> int:
    """The rotations inserting `key` at `priority` would make, computed before the insert. Each
    rotation lifts the new node one level, so the count is where a plain BST insert would put the
    key (priority `-inf`, which beats nothing) minus where its priority puts it. A key already
    present makes none: `insert` then changes nothing."""
    if key in tree:
        return 0
    return insert_steps(tree.root, key, float("-inf")) - insert_steps(tree.root, key, priority)


def _spine(node: Any, side: str) -> int:
    """Nodes on the path from `node` that always steps to the `side` child."""
    count = 0
    while node is not None:
        count += 1
        node = getattr(node, side)
    return count


def delete_rotation_count(tree: Treap[int], key: Any) -> int:
    """The rotations deleting `key` would make, computed before the delete. Each rotation lifts
    one node above the doomed one: the root of its left subtree, after which its new left subtree
    is that node's right subtree, or the root of its right subtree, symmetrically. It stops at a
    leaf, so it lifts exactly the right spine of its left subtree and the left spine of its right
    subtree, whatever order the priorities pick. A key not present makes none."""
    node = tree.root
    while node is not None and node.key != key:
        node = node.left if key < node.key else node.right
    if node is None:
        return 0
    return _spine(node.left, "right") + _spine(node.right, "left")
