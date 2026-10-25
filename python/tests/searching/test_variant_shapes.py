# SPDX-License-Identifier: Apache-2.0
"""Pin *which variant* of each algorithm this package runs, by pinning the trees it builds.

All three renderings run the same variant of each algorithm: the variant and its discipline --
proactive against reactive, predecessor against successor -- **must correspond**. Swaps such as

    BST delete promoting the predecessor instead of the successor
    treap delete splicing a child instead of joining the subtrees
    B-tree fill merging with the right sibling instead of the left
    B-tree internal delete taking the successor before the predecessor

all leave the key set untouched, so contents, `len`, `in_order`, membership and every order
query agree. Only the arrangement differs -- and the arrangement *is* the variant. These tests
compare it.

The expected strings are literal and were read off a correct run, which is the point: an
assertion computed from the implementation cannot disagree with it. When one of these fails,
either a variant changed deliberately -- in which case the Lean and the Rust must change with it
-- or it changed by accident, which is what this is for.
"""

from __future__ import annotations

from typing import Any

import algodesign.searching.treap as treap_module
from algodesign.searching import BST, LLRB, BTree
from algodesign.searching.treap import Treap, rotate_left, rotate_right

from .treap_rotations import insert_steps, rotation_count


def bst_shape(node: Any) -> str:
    """`.` for the empty tree, `(left key right)` for a node."""
    if node is None:
        return "."
    return f"({bst_shape(node.left)} {node.key} {bst_shape(node.right)})"


def btree_shape(node: Any) -> str:
    keys = ",".join(str(k) for k in node.keys)
    if node.leaf:
        return f"L[{keys}]"
    return f"N[{keys}](" + "|".join(btree_shape(c) for c in node.children) + ")"


def treap_shape(node: Any) -> str:
    if node is None:
        return "."
    return (f"({treap_shape(node.left)} {node.key}/{node.priority:g} "
            f"{treap_shape(node.right)})")


def llrb_shape(node: Any) -> str:
    if node is None:
        return "."
    color = "R" if node.red else "B"
    return f"{color}({llrb_shape(node.left)} {node.key} {llrb_shape(node.right)})"


def test_bst_delete_promotes_the_successor() -> None:
    """Deletion takes the in-order **successor**, as `BST/Delete.lean` states it.

    50 has two children. Promoting the successor puts 60 at the root; promoting the predecessor
    would put 30 there. Both are correct deletions leaving `[30, 60, 65, 70, 80]`, which is why
    no contents-based test can tell them apart.
    """
    t: BST[int] = BST()
    for k in [50, 30, 70, 60, 80, 65]:
        t.insert(k)
    assert bst_shape(t.root) == "((. 30 .) 50 ((. 60 (. 65 .)) 70 (. 80 .)))"
    t.delete(50)
    assert bst_shape(t.root) == "((. 30 .) 60 ((. 65 .) 70 (. 80 .)))"
    assert list(t) == [30, 60, 65, 70, 80]


def _bst_nodes(node: Any) -> list[Any]:
    """Every node object in the tree under `node`."""
    out, stack = [], [node]
    while stack:
        n = stack.pop()
        if n is not None:
            out.append(n)
            stack.extend((n.left, n.right))
    return out


def test_bst_delete_moves_the_successor_node_rather_than_copying_its_key() -> None:
    """CLRS `TREE-DELETE` (§12.3), which is what `delete` runs, against copying the key up.

    Both leave the same tree. What differs is which node *object* survives, and only a
    rendering with shared references can see it: `delete` puts 60's own node where 50's stood
    and frees 50's; `delete_hibbard` keeps 50's node and writes 60 into it, freeing 60's node
    instead. Anything outside the tree still holding the freed node now holds a node that is no
    longer in the tree -- so each side is checked for the node it must have let go, not only for
    the one it kept.
    """
    moved: BST[int] = BST()
    copied: BST[int] = BST()
    for t in (moved, copied):
        for k in [50, 30, 70, 60, 80]:
            t.insert(k)
    moved_root: Any = moved.root
    copied_root: Any = copied.root
    moved_50, moved_60 = moved_root, moved_root.right.left
    copied_50, copied_60 = copied_root, copied_root.right.left
    assert (moved_60.key, copied_60.key) == (60, 60)

    moved.delete(50)
    copied.delete_hibbard(50)

    assert bst_shape(moved.root) == bst_shape(copied.root) == "((. 30 .) 60 (. 70 (. 80 .)))"
    assert moved.root is moved_60  # 60's own node now stands where 50's did
    assert all(n is not moved_50 for n in _bst_nodes(moved.root))  # 50's node is gone
    assert copied.root is copied_50 and copied_root.key == 60  # 50's node, relabelled
    assert all(n is not copied_60 for n in _bst_nodes(copied.root))  # 60's node is gone


def test_bst_both_deletions_leave_the_same_tree_on_every_small_case() -> None:
    """Exhaustively, over every tree built by inserting up to five keys from 0..5 and every
    deletion of a key in 0..6, `delete` and `delete_hibbard` leave the same shape. A
    `delete_hibbard` that copies keys up in a chain, which no textbook teaches, differs from
    `delete` on 278 of these 4186 deletions."""
    import copy
    import itertools

    seen: set[str] = set()
    deletions = 0
    for length in range(1, 6):
        for keys in itertools.product(range(6), repeat=length):
            t: BST[int] = BST()
            for k in keys:
                t.insert(k)
            shape = bst_shape(t.root)
            if shape in seen:
                continue
            seen.add(shape)
            for k in range(7):
                a, b = copy.deepcopy(t), copy.deepcopy(t)
                a.delete(k)
                b.delete_hibbard(k)
                assert bst_shape(a.root) == bst_shape(b.root), (shape, k)
                deletions += 1
    assert (len(seen), deletions) == (598, 4186)


def test_btree_fill_merges_with_the_left_sibling() -> None:
    """When neither sibling can spare a key, merge with the **left** one.

    `BTree.ensureSpare` in the Lean and `top_up` in the Rust both do. Deleting
    6 here tells a merge with the left sibling from one with the right.
    """
    t: BTree[int] = BTree(2)
    for k in [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]:
        t.insert(k)
    assert btree_shape(t.root) == "N[9](N[3,5,7](L[1,2]|L[4]|L[6]|L[8])|N[11](L[10]|L[12]))"
    t.delete(6)
    # Merging right would give N[9](N[3,5](L[1,2]|L[4]|L[7,8])|N[11](L[10]|L[12])) -- same keys.
    assert btree_shape(t.root) == "N[9](N[3,7](L[1,2]|L[4,5]|L[8])|N[11](L[10]|L[12]))"
    assert list(t) == [1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12]


def test_btree_internal_delete_prefers_the_predecessor() -> None:
    """CLRS §18.3 case 2a before 2b: when the left child can spare a key, take the predecessor.

    40 sits in the root. Its left child holds three keys and can spare one, so 35 comes up. Taking
    the successor would bring 45 up and empty a child that cannot afford it.
    """
    t: BTree[int] = BTree(2)
    for k in [10, 20, 30, 40, 50, 5, 15, 25, 35, 45, 55, 60]:
        t.insert(k)
    assert btree_shape(t.root) == "N[20,40,50](L[5,10,15]|L[25,30,35]|L[45]|L[55,60])"
    t.delete(40)
    assert btree_shape(t.root) == "N[20,35,50](L[5,10,15]|L[25,30]|L[45]|L[55,60])"


def test_treap_delete_rotates_the_node_down_to_a_leaf() -> None:
    """Deletion is insert's rotate-up run backwards -- the node is rotated down, the child of
    higher priority lifted each time, until it is a leaf -- and not a BST splice that promotes one
    child wholesale.

    Priorities are given explicitly so the tree is determined; `Treap.insert` takes one for
    exactly this reason. Removing the root 50 lifts 70 (priority 0.7 beats 30's 0.5), then 60
    (0.6 beats 0.5), then 30, and 50 is a leaf. A splice promoting the left child would leave 30
    at the root, and a splice promoting the right would leave the heap order below it untouched
    rather than interleaved.
    """
    t: Treap[int] = Treap()
    for key, priority in [(50, 0.9), (30, 0.5), (70, 0.7), (60, 0.6), (80, 0.3), (65, 0.4)]:
        t.insert(key, priority)
    assert treap_shape(t.root) == (
        "((. 30/0.5 .) 50/0.9 ((. 60/0.6 (. 65/0.4 .)) 70/0.7 (. 80/0.3 .)))"
    )
    t.delete(50)
    assert treap_shape(t.root) == (
        "(((. 30/0.5 .) 60/0.6 (. 65/0.4 .)) 70/0.7 (. 80/0.3 .))"
    )
    assert list(t) == [30, 60, 65, 70, 80]


def test_llrb_delete_leaves_sedgewicks_tree() -> None:
    """The LLRB's own fix-up discipline, pinned by the colors as well as the shape.

    The colors are what a reader of this file will change by accident, and `is_valid` alone
    would accept several wrong answers.
    """
    t: LLRB[int] = LLRB()
    for k in [10, 20, 30, 40, 50, 60, 70]:
        t.insert(k)
    assert llrb_shape(t.root) == "B(B(B(. 10 .) 20 B(. 30 .)) 40 B(B(. 50 .) 60 B(. 70 .)))"
    t.delete(40)
    assert llrb_shape(t.root) == "B(R(B(. 10 .) 20 B(. 30 .)) 50 B(R(. 60 .) 70 .))"
    assert t.is_valid()
    assert list(t) == [10, 20, 30, 50, 60, 70]


def test_btree_fill_borrows_from_the_left_sibling_first() -> None:
    """When both siblings could spare a key, borrow from the **left** one: `_top_up` tries borrow
    left, borrow right, merge left, merge right, in that order, as the Lean `ensureSpare` and the
    Rust `top_up` do. Deleting 4 needs L[4] topped up, and both L[1,2] and
    L[6,7] have a key to spare."""
    t: BTree[int] = BTree(2)
    for k in [2, 3, 5, 7, 4, 1, 6]:
        t.insert(k)
    assert btree_shape(t.root) == "N[3,5](L[1,2]|L[4]|L[6,7])"
    t.delete(4)
    # Borrowing right first would give N[3,6](L[1,2]|L[5]|L[7]) -- same keys.
    assert btree_shape(t.root) == "N[2,5](L[1]|L[3]|L[6,7])"


def test_treap_insert_leaves_the_newcomer_below_on_a_priority_tie() -> None:
    """Rotate up only on a strictly higher priority. On a tie the newcomer stays where the BST
    insert put it, as `Treap.insert` in the Lean and the Rust's descent both decide."""
    t: Treap[int] = Treap()
    t.insert(2, 5.0)
    t.insert(1, 5.0)
    # Rotating on a tie would give (. 1/5 (. 2/5 .)).
    assert treap_shape(t.root) == "((. 1/5 .) 2/5 .)"


def test_treap_delete_lifts_the_right_child_on_a_priority_tie() -> None:
    """Deleting a node rotates it down; when its two children tie, the **right** one is lifted,
    as Seidel–Aragon and Weiss break it, and as `Treap.join` in the Lean (`rp < lp`) and the
    Rust's `remove_root` both decide."""
    t: Treap[int] = Treap()
    for key, priority in [(2, 9.0), (1, 5.0), (3, 5.0)]:
        t.insert(key, priority)
    assert treap_shape(t.root) == "((. 1/5 .) 2/9 (. 3/5 .))"
    t.delete(2)
    # Lifting the left child on the tie would give (. 1/5 (. 3/5 .)).
    assert treap_shape(t.root) == "((. 1/5 .) 3/5 .)"


def test_treap_rotation_count_is_the_rotations_insert_makes() -> None:
    """`rotation_count` predicts, before the insert, how many levels the new key rises. Compare
    it with what the insert actually did: the key's depth under a plain BST insert minus its
    depth afterwards. A tie is not a beat, so it counts no rotation."""
    import random

    def depth(node: Any, key: Any) -> int:
        d = 0
        while node.key != key:
            node = node.left if key < node.key else node.right
            d += 1
        return d

    rng = random.Random(7)
    for _ in range(300):
        t: Treap[int] = Treap()
        for key in rng.sample(range(40), 15):
            t.insert(key, float(rng.randrange(6)))
        key = rng.choice([k for k in range(40) if k not in set(t)])
        priority = float(rng.randrange(6))
        plain_depth = insert_steps(t.root, key, float("-inf"))
        predicted = rotation_count(t, key, priority)
        t.insert(key, priority)
        assert predicted == plain_depth - depth(t.root, key)


def test_treap_insert_rotates_the_new_key_up_one_level_per_rotation() -> None:
    """The procedure, not only the tree. The chapter inserts "as an ordinary node, then rotate it
    upward only while its priority beats its parent's"; splitting the subtree at the key
    (Seidel-Aragon's other formulation) builds the same tree with no
    rotation at all, so the test above, which compares depths, cannot tell them apart. Here the
    rotations themselves are counted as they are called: exactly `rotation_count` of them per
    insert, and the sequence as a whole must make some."""
    import random
    from unittest import mock

    rng = random.Random(11)
    total = 0
    for _ in range(200):
        t: Treap[int] = Treap()
        for key in rng.sample(range(40), 15):
            t.insert(key, float(rng.randrange(6)))
        key = rng.choice(range(40))
        priority = float(rng.randrange(6))
        expected = rotation_count(t, key, priority)
        with (
            mock.patch.object(treap_module, "rotate_left", wraps=rotate_left) as left,
            mock.patch.object(treap_module, "rotate_right", wraps=rotate_right) as right,
        ):
            t.insert(key, priority)
        assert left.call_count + right.call_count == expected
        total += expected
    assert total > 100, total


def test_treap_insert_of_a_present_key_changes_nothing() -> None:
    """A key already present keeps its node and its priority, as the textbooks leave it: a higher
    priority offered with the duplicate does not lift it."""
    t: Treap[int] = Treap()
    for key, priority in [(2, 9.0), (1, 5.0)]:
        t.insert(key, priority)
    t.insert(1, 20.0)
    assert treap_shape(t.root) == "((. 1/5 .) 2/9 .)"
    assert rotation_count(t, 1, 20.0) == 0
