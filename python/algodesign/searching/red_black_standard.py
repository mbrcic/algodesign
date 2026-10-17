# SPDX-License-Identifier: Apache-2.0
"""Red-black tree in the standard (CLRS) form, where red children may lean either way.

The five invariants, in the order the book's appendix and CLRS give them: (1) every node is red
or black; (2) the root is black; (3) every empty spot where a node could hang counts as black;
(4) a red node's children are both black; (5) every path from the root down to an empty spot
crosses the same number of black nodes. Together they keep the height at most `2 log2(n + 1)`,
so search, insert and delete cost `O(log n)`. `check_valid` names the first one a tree breaks.

An update is an ordinary BST insert or delete followed by a *fixup* loop that walks up the tree
repairing the one rule it may have broken. Insertion adds a red node and repairs a red-red
violation, in three cases, using at most two rotations. Deletion that removes a black node leaves
one path "a black short", and the fixup pushes that extra blackness up or absorbs it, in four
cases, using at most three rotations. Rotations only relink nodes; colors are changed separately.

Nodes have parent pointers, because the fixups walk upward. Where CLRS uses a shared black
sentinel for NIL, this module uses `None` and passes "the parent of `x`" explicitly to
`_delete_fixup`.

The code reads like CLRS's pseudocode, which asserts nothing: the nodes it reads exist because of
the tree's invariants. `insert` and `delete` return whether they changed the tree;
`insert_with_rotations` and `delete_with_rotations` also return how many rotations the update
made, at most two and three. They read a module-wide count of rotations before and after.

Source: CLRS Ch. 13.

The Rust differs here: it is recursive with no parent pointers, its fix-ups the Lean's with Case 3
folded into Case 4, and its `len` is O(1).

The Lean statements behind this module, in `lean/AlgoDesign/Searching/RedBlackStandard/`
(specification: `RedBlackStandard/Spec.lean`): `valid_insert`, `insertSpec`, `valid_delete`,
`deleteSpec`, `mem_delete`.
"""

from __future__ import annotations

import enum
from collections.abc import Iterable, Iterator
from itertools import pairwise

from ._ordering import SupportsLT

# Every rotation this module has made. `insert_with_rotations` and `delete_with_rotations` read it
# before and after their one update.
_rotations_made = 0


class Color(enum.Enum):
    """A node's color. CLRS colors nodes; the LLRB colors links."""

    RED = "red"
    BLACK = "black"


class _Node[K: SupportsLT]:
    """A node of an `RBTree`, with a pointer to its parent: CLRS's algorithms walk up from a node
    to its parent and grandparent. `None` plays the role of CLRS's NIL.
    """

    __slots__ = ("key", "color", "left", "right", "parent")

    def __init__(
        self,
        key: K,
        color: Color = Color.RED,
        left: _Node[K] | None = None,
        right: _Node[K] | None = None,
        parent: _Node[K] | None = None,
    ) -> None:
        self.key = key
        self.color = color
        self.left = left
        self.right = right
        self.parent = parent


def is_black[K: SupportsLT](node: _Node[K] | None) -> bool:
    """NIL counts as black (CLRS property 3)."""
    return node is None or node.color is Color.BLACK


def is_red[K: SupportsLT](node: _Node[K] | None) -> bool:
    """NIL is never red."""
    return node is not None and node.color is Color.RED


class RBTree[K: SupportsLT]:
    """A red-black tree of keys: a set, not a map."""

    def __init__(self, keys: Iterable[K] | None = None) -> None:
        self.root: _Node[K] | None = None
        if keys is not None:
            for key in keys:
                self.insert(key)

    # --- Rotation, CLRS's LEFT-ROTATE / RIGHT-ROTATE -------------------------------------------

    def _rotate_left(self, x: _Node[K]) -> None:
        """CLRS's `LEFT-ROTATE`: `x`'s right child `y` comes up to take `x`'s place, and `x` becomes
        `y`'s new left child. No node's color changes.
        """
        global _rotations_made
        _rotations_made += 1
        y = x.right
        x.right = y.left
        if y.left is not None:
            y.left.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x is x.parent.left:
            x.parent.left = y
        else:
            x.parent.right = y
        y.left = x
        x.parent = y

    def _rotate_right(self, x: _Node[K]) -> None:
        """CLRS's `RIGHT-ROTATE`, symmetric to `_rotate_left`."""
        global _rotations_made
        _rotations_made += 1
        y = x.left
        x.left = y.right
        if y.right is not None:
            y.right.parent = x
        y.parent = x.parent
        if x.parent is None:
            self.root = y
        elif x is x.parent.right:
            x.parent.right = y
        else:
            x.parent.left = y
        y.right = x
        x.parent = y

    # --- Search --------------------------------------------------------------------------------

    def _find_node(self, key: K) -> _Node[K] | None:
        node = self.root
        while node is not None:
            if key < node.key:
                node = node.left
            elif node.key < key:
                node = node.right
            else:
                return node
        return None

    def search(self, key: K) -> bool:
        """Is `key` a key of the tree?"""
        return self._find_node(key) is not None

    def __contains__(self, key: K) -> bool:
        return self.search(key)

    @staticmethod
    def _minimum(node: _Node[K]) -> _Node[K]:
        while node.left is not None:
            node = node.left
        return node

    # --- Insert, CLRS's RB-INSERT + RB-INSERT-FIXUP --------------------------------------------

    def insert(self, key: K) -> bool:
        """Insert `key`; `True` if it was new (the tree is a set). Ordinary BST insert as a red
        leaf, then `_insert_fixup` restores the color rules.
        """
        parent: _Node[K] | None = None
        node = self.root
        while node is not None:
            parent = node
            if key < node.key:
                node = node.left
            elif node.key < key:
                node = node.right
            else:
                return False  # duplicate key: no-op
        z: _Node[K] = _Node(key, color=Color.RED, parent=parent)
        if parent is None:
            self.root = z
        elif key < parent.key:
            parent.left = z
        else:
            parent.right = z
        self._insert_fixup(z)
        return True

    def insert_with_rotations(self, key: K) -> tuple[bool, int]:
        """`insert`, and how many rotations it made."""
        before = _rotations_made
        added = self.insert(key)
        return added, _rotations_made - before

    def delete_with_rotations(self, key: K) -> tuple[bool, int]:
        """`delete`, and how many rotations it made."""
        before = _rotations_made
        removed = self.delete(key)
        return removed, _rotations_made - before

    def _insert_fixup(self, z: _Node[K]) -> None:
        """CLRS's `RB-INSERT-FIXUP`: while `z`'s parent is red, there is a red-red violation at
        `z`/`z.parent` to repair, via one of three cases:

        * **Case 1** (uncle red): recolor `z.parent` and the uncle black, the grandparent red --
          pushes the violation up to the grandparent, which becomes the new `z` for the next
          iteration (CLRS's `z := z.p.p`).
        * **Case 2** (uncle black, `z` a "triangle" child): rotate at `z.parent` to turn the
          triangle into a line, then fall through to Case 3.
        * **Case 3** (uncle black, `z` a "line" child): recolor `z.parent` black and the
          grandparent red, then rotate at the grandparent. Terminates the loop.
        """
        while True:
            parent = z.parent
            if parent is None or parent.color is not Color.RED:
                break
            grandparent = parent.parent

            if parent is grandparent.left:
                uncle = grandparent.right
                if is_red(uncle):
                    parent.color = Color.BLACK
                    uncle.color = Color.BLACK
                    grandparent.color = Color.RED
                    z = grandparent  # type: ignore[assignment]
                else:
                    if z is parent.right:
                        z = parent
                        self._rotate_left(z)
                        parent = z.parent
                    parent.color = Color.BLACK
                    grandparent.color = Color.RED
                    self._rotate_right(grandparent)  # type: ignore[arg-type]
            else:
                uncle = grandparent.left
                if is_red(uncle):
                    parent.color = Color.BLACK
                    uncle.color = Color.BLACK
                    grandparent.color = Color.RED
                    z = grandparent  # type: ignore[assignment]
                else:
                    if z is parent.left:
                        z = parent
                        self._rotate_right(z)
                        parent = z.parent
                    parent.color = Color.BLACK
                    grandparent.color = Color.RED
                    self._rotate_left(grandparent)  # type: ignore[arg-type]

        self.root.color = Color.BLACK

    # --- Delete, CLRS's RB-TRANSPLANT + RB-DELETE + RB-DELETE-FIXUP ----------------------------

    def _transplant(self, u: _Node[K], v: _Node[K] | None) -> None:
        """CLRS's `RB-TRANSPLANT`: replace the subtree rooted at `u` with the subtree rooted at
        `v`, re-pointing `u`'s parent at `v`. Doesn't touch `v`'s children.
        """
        if u.parent is None:
            self.root = v
        elif u is u.parent.left:
            u.parent.left = v
        else:
            u.parent.right = v
        if v is not None:
            v.parent = u.parent

    def delete(self, key: K) -> bool:
        """Delete `key`; `True` if it was there. CLRS's `RB-DELETE`: splice out `z` (or, if `z` has
        two children, its in-order successor `y`) via `_transplant`, then run `_delete_fixup` if
        the spliced-out node was black -- removing a black node is the only case that can break
        the black-height or no-red-red rule.
        """
        z = self._find_node(key)
        if z is None:
            return False
        y = z
        y_original_color = y.color
        x: _Node[K] | None
        x_parent: _Node[K] | None
        if z.left is None:
            x = z.right
            x_parent = z.parent
            self._transplant(z, z.right)
        elif z.right is None:
            x = z.left
            x_parent = z.parent
            self._transplant(z, z.left)
        else:
            y = self._minimum(z.right)
            y_original_color = y.color
            x = y.right
            if y.parent is z:
                x_parent = y
            else:
                x_parent = y.parent
                self._transplant(y, y.right)
                y.right = z.right
                y.right.parent = y
            self._transplant(z, y)
            y.left = z.left
            y.left.parent = y
            y.color = z.color
        if y_original_color is Color.BLACK:
            self._delete_fixup(x, x_parent)
        return True

    def _delete_fixup(self, x: _Node[K] | None, x_parent: _Node[K] | None) -> None:
        """CLRS's `RB-DELETE-FIXUP`: `x` carries one "extra" unit of blackness (it's either a red
        node about to be recolored black, or NIL/black and needs help from its sibling `w`) --
        loop until that extra blackness is absorbed, via one of four cases:

        * **Case 1** (sibling `w` red): rotate at `x_parent` so `w` moves up and a new, black
          sibling takes its place -- not a terminal case, falls through to one of 2-4 with the new
          `w`.
        * **Case 2** (`w` black, both of `w`'s children black): recolor `w` red -- this pushes the
          extra blackness up to `x_parent`, which becomes the new `x` for the next iteration (and
          if that new `x` is red, the loop condition below ends the loop, absorbing it there).
        * **Case 3** (`w` black, `w`'s near child red, far child black): rotate at `w` to turn the
          near-red child into a far-red child, then fall through to Case 4.
        * **Case 4** (`w` black, far child red): recolor and rotate at `x_parent` -- this restores
          the black-height without changing it further up, so `x` is set to the root to end the
          loop.
        """
        while x is not self.root and is_black(x):
            if x is x_parent.left:
                w = x_parent.right
                if w.color is Color.RED:
                    w.color = Color.BLACK
                    x_parent.color = Color.RED
                    self._rotate_left(x_parent)  # type: ignore[arg-type]
                    w = x_parent.right
                if is_black(w.left) and is_black(w.right):
                    w.color = Color.RED
                    x = x_parent
                    x_parent = x.parent
                else:
                    if is_black(w.right):
                        w.left.color = Color.BLACK
                        w.color = Color.RED
                        self._rotate_right(w)  # type: ignore[arg-type]
                        w = x_parent.right
                    w.color = x_parent.color
                    x_parent.color = Color.BLACK
                    w.right.color = Color.BLACK
                    self._rotate_left(x_parent)  # type: ignore[arg-type]
                    x = self.root
                    x_parent = None
            else:
                w = x_parent.left
                if w.color is Color.RED:
                    w.color = Color.BLACK
                    x_parent.color = Color.RED
                    self._rotate_right(x_parent)  # type: ignore[arg-type]
                    w = x_parent.left
                if is_black(w.right) and is_black(w.left):
                    w.color = Color.RED
                    x = x_parent
                    x_parent = x.parent
                else:
                    if is_black(w.left):
                        w.right.color = Color.BLACK
                        w.color = Color.RED
                        self._rotate_left(w)  # type: ignore[arg-type]
                        w = x_parent.left
                    w.color = x_parent.color
                    x_parent.color = Color.BLACK
                    w.left.color = Color.BLACK
                    self._rotate_right(x_parent)  # type: ignore[arg-type]
                    x = self.root
                    x_parent = None
        if x is not None:
            x.color = Color.BLACK

    # --- Traversal and iteration ----------------------------------------------------------------

    def __iter__(self) -> Iterator[K]:
        """Keys in sorted order (in-order traversal)."""
        yield from _in_order(self.root)

    def __len__(self) -> int:
        """How many keys: a walk of the whole tree, `O(n)`."""
        return sum(1 for _ in self)

    def is_sorted(self) -> bool:
        """The keys in order strictly ascend: the search tree's order, which the five invariants
        take for granted. The Lean `Sorted`."""
        return all(a < b for a, b in pairwise(self))

    def check_valid(self) -> str | None:
        """The first rule the tree breaks, or `None`: the five invariants in the appendix's
        order, then the search tree's order, then the one stored field the Lean model has no
        counterpart for, the parent pointers the fixups walk up through.

        `"invariant 1 (red_or_black)"`, `"invariant 2 (root_black)"`, `"invariant 4
        (no_red_red)"`, `"invariant 5 (black_height_ok)"`, `"not in the box (sorted)"` or
        `"layout (parents_point_back)"`."""
        # Invariant 3, every empty spot counts as black, is how `is_black` reads `None`: no
        # stored part can break it.
        if not is_red_or_black(self.root):
            return "invariant 1 (red_or_black)"
        if not is_root_black(self.root):
            return "invariant 2 (root_black)"
        if not is_no_red_red(self.root):
            return "invariant 4 (no_red_red)"
        if not is_black_height_ok(self.root):
            return "invariant 5 (black_height_ok)"
        if not self.is_sorted():
            return "not in the box (sorted)"
        if not _parents_point_back(self.root):
            return "layout (parents_point_back)"
        return None

    def is_valid(self) -> bool:
        """The five invariants, the search tree's order and the parent pointers: `check_valid`
        finds nothing broken."""
        return self.check_valid() is None


def _parents_point_back[K: SupportsLT](root: _Node[K] | None) -> bool:
    """Every child points back at its parent, and the root at nothing. A loop, not recursion."""
    if root is not None and root.parent is not None:
        return False
    stack = [root] if root is not None else []
    while stack:
        node = stack.pop()
        for child in (node.left, node.right):
            if child is not None:
                if child.parent is not node:
                    return False
                stack.append(child)
    return True


def _in_order[K: SupportsLT](node: _Node[K] | None) -> Iterator[K]:
    if node is not None:
        yield from _in_order(node.left)
        yield node.key
        yield from _in_order(node.right)


def black_height[K: SupportsLT](node: _Node[K] | None) -> int | None:
    """The black-height of `node`, if every root-to-leaf path agrees on it, else `None`. NIL
    contributes `1`, red nodes contribute nothing.
    """
    if node is None:
        return 1
    left_height = black_height(node.left)
    right_height = black_height(node.right)
    if left_height is None or right_height is None or left_height != right_height:
        return None
    return left_height + (1 if node.color is Color.BLACK else 0)


def is_red_or_black[K: SupportsLT](node: _Node[K] | None) -> bool:
    """CLRS property 1: every node is red or black."""
    if node is None:
        return True
    return (node.color is Color.RED or node.color is Color.BLACK) and (
        is_red_or_black(node.left) and is_red_or_black(node.right)
    )


def is_black_height_ok[K: SupportsLT](node: _Node[K] | None) -> bool:
    """CLRS property 5: every path from `node` down to an empty spot crosses the same number of
    black nodes. The Lean `BlackHeightOk`."""
    return black_height(node) is not None


def is_no_red_red[K: SupportsLT](node: _Node[K] | None) -> bool:
    """CLRS property 4: a red node's children are both black."""
    if node is None:
        return True
    if node.color is Color.RED and not (is_black(node.left) and is_black(node.right)):
        return False
    return is_no_red_red(node.left) and is_no_red_red(node.right)


def is_root_black[K: SupportsLT](node: _Node[K] | None) -> bool:
    """CLRS property 2: the root is black; true of the empty tree (NIL) too."""
    return node is None or node.color is Color.BLACK
