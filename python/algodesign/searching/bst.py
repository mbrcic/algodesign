# SPDX-License-Identifier: Apache-2.0
"""Binary search tree, without balancing.

Every key in a node's left subtree is smaller than the node's key, and every key in its right
subtree is larger. Search, insert and delete each walk one path from the root, so they cost the
tree's height -- about `log n` when the keys arrive in random order, and `n` when they arrive
sorted, because then every insert goes right and the tree is a path.

Each node also stores the size of its subtree. That one extra number is what makes `rank` ("how
many keys are smaller?") and `select` ("which key is at position i?") cost the height too, instead
of a walk over the whole tree (CLRS 4th ed. §17.1).

Deletion is CLRS's `TREE-DELETE` (§12.3): it moves the in-order successor's *node* into the gap,
re-pointing links with `TRANSPLANT`. `delete_hibbard` is the older variant that copies the
successor's *key* up instead (Weiss §4.3.4). Both leave the same tree; they differ in which node
object survives.

`insert` and `floor` are the chapter's listings; `insert` adds the size bookkeeping rank and
select need (`passed`, `_one_more_below`).

Sources: Sedgewick §3.2, CLRS 4th ed. §12 and §17.1.

The Rust differs here: it counts sizes on the way down and undoes the count on a duplicate, restores
them after a missed delete, and every walk is a loop. Its `range` takes any Rust range, open or
closed at either end, and panics on a start above the end, where this one is closed at both ends
and answers nothing.

The Lean statements behind this module, in `lean/AlgoDesign/Searching/BST/` (specification:
`BST/Spec.lean`): `mem_insert`, `sorted_insert`, `search_correct`, `mem_delete`, `sorted_delete`,
`deleteHibbard_eq_delete`, `rank_select?`, `select?_rank`, `floor?_correct`, `ceiling?_correct`.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator

from ._ordering import SupportsLT


class _Node[K: SupportsLT]:
    """One node: a key, its two subtrees, and how many keys hang at or below it."""

    __slots__ = ("key", "left", "right", "size")

    def __init__(self, key: K) -> None:
        self.key = key
        self.left: _Node[K] | None = None
        self.right: _Node[K] | None = None
        self.size = 1


def size[K: SupportsLT](node: _Node[K] | None) -> int:
    """How many keys hang at or below `node`: the stored count, read, never walked."""
    return 0 if node is None else node.size


def search[K: SupportsLT](node: _Node[K] | None, key: K) -> bool:
    """Is `key` at or below `node`? One question per node: smaller goes left, larger right."""
    if node is None:
        return False
    if key == node.key:
        return True
    if key < node.key:
        return search(node.left, key)
    return search(node.right, key)


def min_key[K: SupportsLT](node: _Node[K] | None) -> K | None:
    """The smallest key at or below `node`: walk left until there is no left."""
    if node is None:
        return None
    return node.key if node.left is None else min_key(node.left)


def max_key[K: SupportsLT](node: _Node[K] | None) -> K | None:
    """The largest key at or below `node`: walk right until there is no right."""
    if node is None:
        return None
    return node.key if node.right is None else max_key(node.right)


def floor[K: SupportsLT](node: _Node[K] | None, key: K) -> K | None:
    """The closest key at or below `key`, if any. The chapter's listing."""
    if node is None:
        return None
    if key == node.key:
        return node.key
    if key < node.key:
        return floor(node.left, key)
    right = floor(node.right, key)
    return right if right is not None else node.key


def ceiling[K: SupportsLT](node: _Node[K] | None, key: K) -> K | None:
    """The closest key at or above `key`, if any: `floor`'s mirror image."""
    if node is None:
        return None
    if key == node.key:
        return node.key
    if node.key < key:
        return ceiling(node.right, key)
    left = ceiling(node.left, key)
    return left if left is not None else node.key


def rank[K: SupportsLT](node: _Node[K] | None, key: K) -> int:
    """How many keys at or below `node` are smaller than `key`. Every step right passes this node
    and its whole left subtree, all smaller."""
    if node is None:
        return 0
    if key == node.key:
        return size(node.left)
    if key < node.key:
        return rank(node.left, key)
    return size(node.left) + 1 + rank(node.right, key)


def select[K: SupportsLT](node: _Node[K] | None, index: int) -> K | None:
    """The key at position `index` (from 0) in sorted order below `node`, if any: the left
    subtree's size says whether that position is to the left, here, or to the right."""
    if node is None:
        return None
    left_size = size(node.left)
    if index < left_size:
        return select(node.left, index)
    if index == left_size:
        return node.key
    return select(node.right, index - left_size - 1)


def _one_more_below[K: SupportsLT](passed: list[_Node[K]]) -> None:
    """A new key now hangs below every node in `passed`: each counts one more."""
    for node in passed:
        node.size += 1


def _walk_to_delete[K: SupportsLT](
    root: _Node[K] | None, key: K
) -> tuple[_Node[K] | None, _Node[K]] | None:
    """TREE-SEARCH for `key`, remembering the way down. `None` if `key` is absent, and then nothing
    has changed. Otherwise every node passed on the way loses one from its size -- the key is about
    to leave its subtree -- and the answer is `(parent, z)`: the node holding `key` and its parent,
    `None` at the root."""
    path: list[_Node[K]] = []
    z = root
    while z is not None and key != z.key:
        path.append(z)
        z = z.left if key < z.key else z.right
    if z is None:
        return None
    for node in path:
        node.size -= 1
    return (path[-1] if path else None), z


def is_sorted[K: SupportsLT](
    node: _Node[K] | None, lo: K | None = None, hi: K | None = None
) -> bool:
    """Every key strictly between the bounds its ancestors set: above each ancestor it hangs to
    the right of, below each one it hangs to the left of."""
    if node is None:
        return True
    if (lo is not None and not lo < node.key) or (hi is not None and not node.key < hi):
        return False
    return is_sorted(node.left, lo, node.key) and is_sorted(node.right, node.key, hi)


def sizes_add_up[K: SupportsLT](node: _Node[K] | None) -> bool:
    """Every node's stored `size` is one more than its two children's."""
    if node is None:
        return True
    return (
        node.size == 1 + size(node.left) + size(node.right)
        and sizes_add_up(node.left)
        and sizes_add_up(node.right)
    )


def keys_in_range[K: SupportsLT](node: _Node[K] | None, lo: K, hi: K) -> Iterator[K]:
    """The keys at or below `node` from `lo` to `hi`, both included, in increasing order: the
    in-order walk, skipping a side whose keys all lie outside. Left of a key at or below `lo` every
    key is smaller still, and right of a key at or above `hi` every key is larger."""
    if node is None:
        return
    if lo < node.key:
        yield from keys_in_range(node.left, lo, hi)
    if not node.key < lo and not hi < node.key:
        yield node.key
    if node.key < hi:
        yield from keys_in_range(node.right, lo, hi)


def in_order[K: SupportsLT](node: _Node[K] | None) -> Iterator[K]:
    """Left subtree, this key, right subtree: the keys in sorted order."""
    if node is None:
        return
    yield from in_order(node.left)
    yield node.key
    yield from in_order(node.right)


class BST[K: SupportsLT]:
    """A binary search tree of keys -- a set, not a map.

    `root` is the tree's top node, `None` for the empty tree. `insert` and the deletions are loops;
    the other walks recurse once per level, so on a path deeper than Python's recursion limit
    (sorted keys build one) they raise `RecursionError`.
    """

    __slots__ = ("root",)

    def __init__(self, keys: Iterable[K] | None = None) -> None:
        self.root: _Node[K] | None = None
        if keys is not None:
            for key in keys:
                self.insert(key)

    def insert(self, key: K) -> bool:
        """True if newly added, False if already present. The walk remembers the nodes it passes
        and counts the new key into each only when it is hung, so a duplicate changes no size.
        """
        if self.root is None:
            self.root = _Node(key)
            return True
        node = self.root
        passed: list[_Node[K]] = []
        while True:
            passed.append(node)
            if key == node.key:
                return False
            elif key < node.key:
                if node.left is None:
                    node.left = _Node(key)
                    _one_more_below(passed)
                    return True
                node = node.left
            else:
                if node.right is None:
                    node.right = _Node(key)
                    _one_more_below(passed)
                    return True
                node = node.right

    def search(self, key: K) -> bool:
        return search(self.root, key)

    def __contains__(self, key: K) -> bool:
        return self.search(key)

    def min(self) -> K | None:
        return min_key(self.root)

    def max(self) -> K | None:
        return max_key(self.root)

    def floor(self, key: K) -> K | None:
        return floor(self.root, key)

    def ceiling(self, key: K) -> K | None:
        return ceiling(self.root, key)

    def size(self) -> int:
        """How many keys: the root's stored size, `O(1)`."""
        return size(self.root)

    def __len__(self) -> int:
        return self.size()

    def rank(self, key: K) -> int:
        return rank(self.root, key)

    def select(self, index: int) -> K | None:
        return select(self.root, index)

    def range(self, lo: K, hi: K) -> list[K]:
        """The keys from `lo` to `hi`, both ends included, in increasing order; none if
        `hi < lo`. The walk visits the keys it returns and the two paths that bound them, so it
        costs the height plus the number of keys returned."""
        return list(keys_in_range(self.root, lo, hi))

    def _transplant(self, parent: _Node[K] | None, u: _Node[K], v: _Node[K] | None) -> None:
        """CLRS's `TRANSPLANT(T, u, v)` (§12.3): replace the subtree rooted at `u` by the one rooted
        at `v`, by re-pointing `u`'s parent -- or the root, if `u` has none -- at `v`. `v`'s own
        children are left as they are. The nodes keep no parent pointer, so the caller passes it."""
        if parent is None:
            self.root = v
        elif u is parent.left:
            parent.left = v
        else:
            parent.right = v

    def delete(self, key: K) -> bool:
        """Delete `key`; `True` if it was there.

        CLRS's `TREE-DELETE` (§12.3), which **moves the successor's node** into the gap. With at
        most one child, `z` is replaced by that child. With two, the successor `y` is the minimum
        of `z.right`; if `y` is not `z.right` itself, it is first replaced by its own right child
        and takes over `z.right`; then `y` replaces `z` and takes over `z.left`. The node that
        held `key` is the one that leaves the tree.
        """
        found = _walk_to_delete(self.root, key)
        if found is None:
            return False
        parent, z = found
        if z.left is None:
            self._transplant(parent, z, z.right)
        elif z.right is None:
            self._transplant(parent, z, z.left)
        else:
            y_parent, y = z, z.right  # y = TREE-MINIMUM(z.right), with its parent
            while y.left is not None:
                y.size -= 1  # y is leaving this subtree
                y_parent, y = y, y.left
            if y is not z.right:
                self._transplant(y_parent, y, y.right)
                y.right = z.right
            self._transplant(parent, z, y)
            y.left = z.left
            y.size = z.size - 1
        return True

    def delete_hibbard(self, key: K) -> bool:
        """Delete `key` by **copying the successor's key** into its node instead of moving the
        successor's node; `True` if it was there. With at most one child, as in `delete`. With
        two, the successor's key is written into `z`, and the successor's own node -- it has no
        left child -- is replaced by its right child: one `TRANSPLANT`, never a chain of copies.

        The tree has the same shape as `delete` leaves; here the node that held `key` stays,
        holding the successor's key, and the successor's node is the one freed.
        """
        found = _walk_to_delete(self.root, key)
        if found is None:
            return False
        parent, z = found
        if z.left is None:
            self._transplant(parent, z, z.right)
        elif z.right is None:
            self._transplant(parent, z, z.left)
        else:
            z.size -= 1
            y_parent, y = z, z.right  # y = TREE-MINIMUM(z.right), with its parent
            while y.left is not None:
                y.size -= 1
                y_parent, y = y, y.left
            z.key = y.key
            self._transplant(y_parent, y, y.right)
        return True

    def __iter__(self) -> Iterator[K]:
        return in_order(self.root)

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, or `None`: `"invariant 1 (sorted)"` or
        `"layout (sizes_add_up)"`."""
        if not is_sorted(self.root):
            return "invariant 1 (sorted)"
        if not sizes_add_up(self.root):
            return "layout (sizes_add_up)"
        return None

    def is_valid(self) -> bool:
        """The BST order -- every key strictly between the bounds its ancestors set -- and every
        stored `size` true."""
        return self.check_valid() is None

    def __repr__(self) -> str:
        return f"{type(self).__name__}({list(self)!r})"
