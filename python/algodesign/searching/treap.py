# SPDX-License-Identifier: Apache-2.0
"""Treap: a binary search tree on keys that is also a max-heap on priorities.

Every key gets a random priority. Keys are in BST order, and every node's priority is at least
its children's. With distinct priorities there is exactly one such tree for a given set of keys --
the key of highest priority is the root, and the rest splits by key -- so the tree has the shape
it would have had if the keys had arrived in random order, whatever order they really came in.
Its expected height is `O(log n)`, and search, insert and delete take expected `O(log n)` time,
with no rebalancing rules to maintain.

Insert puts the new key where an ordinary BST insert would, at a leaf, and then rotates it up for
as long as its priority beats its parent's: each rotation moves it one level closer to the root
without disturbing the key order. Delete does the reverse: it rotates the doomed node down,
lifting whichever child has the higher priority, until the node is a leaf, and then drops it.
Either way, a random priority means an expected fewer-than-two rotations per update.

The rotations are the chapter's red-black rotations without the colors: `h` and `x`, three
links rewired. `insert` and `delete` return whether they changed the tree;
`insert_with_rotations` and `delete_with_rotations` also return how many rotations the update
made, the count the chapter states. They read a module-wide count of rotations before and after.

Priorities are integers drawn from SplitMix64, the library's seeded generator, one draw per
`insert` that is given none, a present key included. `Treap(seed=7)` and the Rust's
`Treap::with_seed(7)`, given the same calls, build the same tree.

Sources: Seidel & Aragon, *Randomized Search Trees* (Algorithmica 16, 1996), for the structure,
rotate-up insert and rotate-down delete; Motwani & Raghavan, *Randomized Algorithms*, §8.2, for the
expected cost.

The Lean statements behind this module, in `lean/AlgoDesign/Searching/Treap/` (specification:
`Treap/Spec.lean`): `valid_insert`, `mem_insert`, `valid_delete`, `mem_delete`,
`removeRoot_eq_join`, `existsUnique_of_nodup`.
"""

from __future__ import annotations

import random
from collections.abc import Iterator

from .._rng import SplitMix64
from ._ordering import SupportsLT

# Every rotation this module has made. `insert_with_rotations` and `delete_with_rotations` read it
# before and after their one update.
_rotations_made = 0


class _Node[K: SupportsLT]:
    """One treap node: a key, its priority, and its two (possibly absent) children."""

    __slots__ = ("key", "priority", "left", "right")

    def __init__(self, key: K, priority: float) -> None:
        self.key = key
        self.priority = priority
        self.left: _Node[K] | None = None
        self.right: _Node[K] | None = None


def rotate_left[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    """Lift `h`'s right child above it. Key order is unchanged: the child's left subtree, whose
    keys lie between the two, moves across to become `h`'s right subtree."""
    global _rotations_made
    _rotations_made += 1
    x = h.right; h.right = x.left; x.left = h
    return x  # type: ignore[return-value]


def rotate_right[K: SupportsLT](h: _Node[K]) -> _Node[K]:
    """Lift `h`'s left child above it; the mirror image of `rotate_left`."""
    global _rotations_made
    _rotations_made += 1
    x = h.left; h.left = x.right; x.right = h
    return x  # type: ignore[return-value]


def _insert[K: SupportsLT](h: _Node[K] | None, key: K, priority: float) -> _Node[K]:
    """Insert below `h` as an ordinary BST insert would, then, on the way back up, rotate the
    child that was just inserted into above `h` whenever its priority is strictly higher. A tie
    leaves the newcomer below."""
    if h is None:
        return _Node(key, priority)
    if key < h.key:
        h.left = _insert(h.left, key, priority)
        if h.left.priority > h.priority:
            h = rotate_right(h)
    elif h.key < key:
        h.right = _insert(h.right, key, priority)
        if h.right.priority > h.priority:
            h = rotate_left(h)
    return h


def _delete[K: SupportsLT](h: _Node[K] | None, key: K) -> _Node[K] | None:
    """Find `key` by an ordinary BST descent, then `_remove_root` it."""
    if h is None:
        return None
    if key < h.key:
        h.left = _delete(h.left, key)
        return h
    if h.key < key:
        h.right = _delete(h.right, key)
        return h
    return _remove_root(h)


def _remove_root[K: SupportsLT](h: _Node[K]) -> _Node[K] | None:
    """Rotate `h` down until it is a leaf, then drop it. Each rotation lifts the child of higher
    priority -- the only child if there is one, the right one on a tie -- above `h`, so the heap
    order holds everywhere except at `h` itself, which is on its way out."""
    if h.left is None and h.right is None:
        return None
    if h.right is None or (h.left is not None and h.left.priority > h.right.priority):
        x = rotate_right(h)
        x.right = _remove_root(h)
    else:
        x = rotate_left(h)
        x.left = _remove_root(h)
    return x


def _is_sorted[K: SupportsLT](
    node: _Node[K] | None, lo: K | None = None, hi: K | None = None
) -> bool:
    """Every key strictly between the bounds its ancestors set: above each ancestor it hangs to
    the right of, below each one it hangs to the left of."""
    if node is None:
        return True
    if (lo is not None and not lo < node.key) or (hi is not None and not node.key < hi):
        return False
    return _is_sorted(node.left, lo, node.key) and _is_sorted(node.right, node.key, hi)


def _heap_ordered[K: SupportsLT](node: _Node[K] | None) -> bool:
    """No child's priority above its parent's; a tie is allowed."""
    if node is None:
        return True
    for child in (node.left, node.right):
        if child is not None and child.priority > node.priority:
            return False
    return _heap_ordered(node.left) and _heap_ordered(node.right)


def _in_order[K: SupportsLT](h: _Node[K] | None) -> Iterator[K]:
    if h is None:
        return
    yield from _in_order(h.left)
    yield h.key
    yield from _in_order(h.right)


class Treap[K: SupportsLT]:
    """A treap of keys (a set), each carrying a numeric priority.

    `seed`, if given, seeds the SplitMix64 stream the priorities of `insert` calls that don't
    supply one are drawn from, so a seed reproduces a run, and the Rust's tree too. Otherwise the
    seed is drawn at random.

    `insert`, `delete`, iteration, `len` and `is_valid` recurse once per level, so priorities the
    caller chooses badly (keys in increasing order at decreasing priorities) can build a path deep
    enough to hit Python's recursion limit, and each of them then raises `RecursionError`; `search`
    is a loop. Random priorities keep the expected depth about `2 ln n`, far from it.
    """

    def __init__(self, seed: int | None = None) -> None:
        self.root: _Node[K] | None = None
        self._priorities = SplitMix64(seed if seed is not None else random.getrandbits(64))

    def search(self, key: K) -> bool:
        """Is `key` one of the tree's keys? An ordinary BST descent."""
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

    def insert(self, key: K, priority: float | None = None) -> bool:
        """Insert `key` at `priority`, or at the next priority of the tree's stream if none is
        given; `True` if it was new. A present key keeps its old priority.
        """
        if priority is None:
            priority = self._priorities.next_u64()  # drawn even for a duplicate: one per call
        if self.search(key):
            return False
        self.root = _insert(self.root, key, priority)
        return True

    def insert_with_rotations(self, key: K, priority: float | None = None) -> tuple[bool, int]:
        """`insert`, and how many rotations it made: one per ancestor the new key outranks."""
        before = _rotations_made
        added = self.insert(key, priority)
        return added, _rotations_made - before

    def delete(self, key: K) -> bool:
        """Delete `key`; `True` if it was there. Find its node by an ordinary BST descent, then
        rotate it down to a leaf and drop it (`_remove_root`)."""
        if not self.search(key):
            return False
        self.root = _delete(self.root, key)
        return True

    def delete_with_rotations(self, key: K) -> tuple[bool, int]:
        """`delete`, and how many rotations it made: one per level the node sinks."""
        before = _rotations_made
        removed = self.delete(key)
        return removed, _rotations_made - before

    def __iter__(self) -> Iterator[K]:
        """Keys in ascending order."""
        yield from _in_order(self.root)

    def __len__(self) -> int:
        """How many keys: a walk of the whole tree, `O(n)`."""
        return sum(1 for _ in self)

    def is_valid(self) -> bool:
        """Both treap invariants: BST order on the keys, max-heap order on the priorities."""
        return _is_sorted(self.root) and _heap_ordered(self.root)
