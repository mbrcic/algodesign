# SPDX-License-Identifier: Apache-2.0
"""Left-leaning red-black tree (LLRB).

A red-black tree is a binary search tree that encodes a 2-3 tree: a red link glues a node to its
parent into one 3-node, and a black link is an ordinary parent-child link. The left-leaning
variant adds one rule, that red links lean left, so each 2-3 tree has exactly one LLRB. Since no
path has two red links in a row and every root-to-leaf path has the same number of black links,
the height is at most `2 log2 n`, and search, insert and delete all cost `O(log n)`.

Updates are ordinary BST walks plus local repairs. On the way back up, `fix_up` rotates a
right-leaning red link left, rotates two reds in a row right, and flips colors to split a
temporary 4-node. Deletion also works on the way down (`move_red_left`, `move_red_right`), so
that the node it descends into is never a bare 2-node, from which a key could not be removed.

`h.red` is the color of the link coming down into node `h` from the node above it.

`is_red`, `rotate_left`, `rotate_right`, `flip_colors`, `fix_up`, `move_red_left`,
`move_red_right`, `delete_min` and `delete_min_from` are the chapter's listings. They have no
guards: the children they read exist because of the tree's invariants, and called outside them
they raise. `_insert` and `_delete` are Sedgewick's; `LLRB.delete` checks membership first.

`insert_with_rotations` and `delete_with_rotations` also return how many rotations the update
made, the counts the chapter reports. The two rotations add each call to a module-wide count,
which those two read before and after; that count is the only line the listings do not print.

Source: Sedgewick §3.3, Algorithm 3.4; deletion from exercises 3.3.39-3.3.41.

The Rust differs here: it keeps a count per node, so its `len` is O(1), and its rotations and
`flip_colors` do nothing on an empty child where these raise.

The Lean statements behind this module, in `lean/AlgoDesign/Searching/LLRB/` (specification:
`LLRB/Spec.lean`): `valid_insert`, `mem_insert`, `valid_deleteTop`, `mem_deleteTop_iff`,
`valid_deleteMinTop`, `mem_deleteMinTop_iff`.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from itertools import pairwise

from ._ordering import SupportsLT

# Every rotation this module has made. `insert_with_rotations` and `delete_with_rotations` read it
# before and after their one update.
_rotations_made = 0


class _Node[K: SupportsLT]:
    """A node of an `LLRB`. `red` is the color of the link into it; a new node arrives red."""

    __slots__ = ("key", "left", "right", "red")

    def __init__(self, key: K) -> None:
        self.key = key
        self.left: _Node[K] | None = None
        self.right: _Node[K] | None = None
        self.red = True


# --- The chapter's listings ----------------------------------------------------------------


def is_red[K: SupportsLT](h: _Node[K] | None) -> bool: return h is not None and h.red


def rotate_left[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    global _rotations_made
    _rotations_made += 1
    x = h.right; h.right = x.left; x.left = h
    x.red, h.red = h.red, True
    return x  # type: ignore[return-value]


def rotate_right[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    global _rotations_made
    _rotations_made += 1
    x = h.left; h.left = x.right; x.right = h
    x.red, h.red = h.red, True
    return x  # type: ignore[return-value]


def flip_colors[K: SupportsLT](h: _Node[K]) -> None:
    h.red = not h.red
    h.left.red = not h.left.red
    h.right.red = not h.right.red


def fix_up[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    if is_red(h.right) and not is_red(h.left):
        h = rotate_left(h)
    if is_red(h.left) and is_red(h.left.left):
        h = rotate_right(h)
    if is_red(h.left) and is_red(h.right):
        flip_colors(h)
    return h


def move_red_left[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    flip_colors(h)
    if is_red(h.right.left):
        h.right = rotate_right(h.right)  # type: ignore[arg-type]
        h = rotate_left(h)
        flip_colors(h)
    return h


def move_red_right[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    flip_colors(h)
    if is_red(h.left.left):
        h = rotate_right(h)
        flip_colors(h)
    return h


def delete_min[K: SupportsLT](h: _Node[K]) -> _Node[K] | None:
    if h.left is None:
        return None
    nxt = h.left
    spare = is_red(nxt) or is_red(nxt.left)
    if not spare:
        h = move_red_left(h)
    h.left = delete_min(h.left)  # type: ignore[arg-type]
    return fix_up(h)


def delete_min_from[K: SupportsLT](tree: LLRB[K]) -> None:
    r = tree.root
    if not is_red(r.left) and not is_red(r.right):
        r.red = True
    tree.root = delete_min(r)  # type: ignore[arg-type]
    if tree.root is not None:
        tree.root.red = False


# --- Insert and delete, which the chapter walks through but does not print ------------------


def min_key[K: SupportsLT](h: _Node[K]) -> K:
    """The smallest key below `h`: its leftmost node's."""
    while h.left is not None:
        h = h.left
    return h.key


def _insert[K: SupportsLT](h: _Node[K] | None, key: K) -> _Node[K]:
    """An ordinary BST insert of a new red node, then `fix_up` on the way back up from every
    level. A key already present is left alone: the tree is a set."""
    if h is None:
        return _Node(key)
    if key < h.key:
        h.left = _insert(h.left, key)
    elif h.key < key:
        h.right = _insert(h.right, key)
    return fix_up(h)


def _delete[K: SupportsLT](h: _Node[K], key: K) -> _Node[K] | None:
    """Delete `key` below `h`. On the way down, `move_red_left` and `move_red_right` keep the node
    about to be entered from being a bare 2-node. A key in an interior node is overwritten by its
    successor, the right subtree's minimum, which `delete_min` then removes. `fix_up` repairs on
    the way back up. On reaching an empty right child, the node goes only if it holds `key`;
    without that comparison an absent key would remove the largest key below where the walk ends.
    """
    if key < h.key:
        if not is_red(h.left) and not is_red(h.left.left):
            h = move_red_left(h)
        h.left = _delete(h.left, key)  # type: ignore[arg-type]
    else:
        if is_red(h.left):
            h = rotate_right(h)
        if h.right is None:
            return h.left if key == h.key else fix_up(h)
        if not is_red(h.right) and not is_red(h.right.left):
            h = move_red_right(h)
        if key == h.key:
            h.key = min_key(h.right)  # type: ignore[arg-type]
            h.right = delete_min(h.right)  # type: ignore[arg-type]
        else:
            h.right = _delete(h.right, key)  # type: ignore[arg-type]
    return fix_up(h)


# --- In-order traversal, and the invariant checkers the tests assert -------------------------


def _in_order[K: SupportsLT](h: _Node[K] | None) -> Iterator[K]:
    if h is not None:
        yield from _in_order(h.left)
        yield h.key
        yield from _in_order(h.right)


def black_height[K: SupportsLT](h: _Node[K] | None) -> int | None:
    """The black-height of `h`, if every root-to-leaf path agrees on it, else `None`. The empty
    tree contributes `1`, red links contribute nothing.
    """
    if h is None:
        return 1
    left_height = black_height(h.left)
    right_height = black_height(h.right)
    if left_height is None or right_height is None or left_height != right_height:
        return None
    return left_height + (0 if h.red else 1)


def is_left_leaning[K: SupportsLT](h: _Node[K] | None) -> bool:
    """No right link is red."""
    if h is None:
        return True
    return not is_red(h.right) and is_left_leaning(h.left) and is_left_leaning(h.right)


def is_no_red_red[K: SupportsLT](h: _Node[K] | None) -> bool:
    """No two red links touch."""
    if h is None:
        return True
    if h.red and (is_red(h.left) or is_red(h.right)):
        return False
    return is_no_red_red(h.left) and is_no_red_red(h.right)


def is_root_black[K: SupportsLT](h: _Node[K] | None) -> bool:
    """The root's link is black; true of the empty tree too."""
    return h is None or not h.red


def is_sorted[K: SupportsLT](h: _Node[K] | None) -> bool:
    """The keys are in order, as in any search tree: read left to right, each is smaller than the
    next."""
    keys = list(_in_order(h))
    return all(a < b for a, b in pairwise(keys))


def is_black_height_ok[K: SupportsLT](h: _Node[K] | None) -> bool:
    """Every path from the root down to a leaf crosses the same number of black links."""
    return black_height(h) is not None


class LLRB[K: SupportsLT]:
    """A left-leaning red-black tree of keys: a set, not a map."""

    def __init__(self, keys: Iterable[K] | None = None) -> None:
        self.root: _Node[K] | None = None
        if keys is not None:
            for key in keys:
                self.insert(key)

    def insert(self, key: K) -> bool:
        """Insert `key`; `True` if it was new. The fix-ups can leave the root's link red, and the
        root's link is always black, so it is colored black again afterwards."""
        if self.search(key):
            return False
        self.root = _insert(self.root, key)
        self.root.red = False
        return True

    def delete(self, key: K) -> bool:
        """Delete `key`; `True` if it was there.

        The membership check comes first, because `_delete` restructures nodes on the way down
        before it can know whether the key is there. The root is colored red if both its children
        are black, so even the root is never a bare 2-node, and black again afterwards.
        """
        if not self.search(key):
            return False
        r = self.root
        if not is_red(r.left) and not is_red(r.right):
            r.red = True
        self.root = _delete(r, key)  # type: ignore[arg-type]
        if self.root is not None:
            self.root.red = False
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

    def delete_min(self) -> K | None:
        """Delete the smallest key and return it; `None`, with nothing changed, on an empty tree."""
        if self.root is None:
            return None
        smallest = min_key(self.root)
        delete_min_from(self)
        return smallest

    def search(self, key: K) -> bool:
        """Is `key` a key of the tree? Ordinary iterative BST search; colors play no part."""
        h = self.root
        while h is not None:
            if key < h.key:
                h = h.left
            elif h.key < key:
                h = h.right
            else:
                return True
        return False

    def __contains__(self, key: K) -> bool:
        return self.search(key)

    def __iter__(self) -> Iterator[K]:
        """Keys in sorted order (in-order traversal)."""
        yield from _in_order(self.root)

    def __len__(self) -> int:
        """How many keys: a walk of the whole tree, `O(n)`."""
        return sum(1 for _ in self)

    def check_valid(self) -> str | None:
        """The first box invariant the tree breaks, in order, or `None`:
        `"invariant 1 (sorted)"`, `"invariant 2 (root_black)"`, `"invariant 3 (left_leaning)"`,
        `"invariant 4 (no_red_red)"` or `"invariant 5 (black_height_ok)"`."""
        if not is_sorted(self.root):
            return "invariant 1 (sorted)"
        if not is_root_black(self.root):
            return "invariant 2 (root_black)"
        if not is_left_leaning(self.root):
            return "invariant 3 (left_leaning)"
        if not is_no_red_red(self.root):
            return "invariant 4 (no_red_red)"
        if not is_black_height_ok(self.root):
            return "invariant 5 (black_height_ok)"
        return None

    def is_valid(self) -> bool:
        """All the LLRB invariants -- keys in order, root black, red links lean left, no two reds
        in a row, the same black height on every path."""
        return self.check_valid() is None
