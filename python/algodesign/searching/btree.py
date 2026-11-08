# SPDX-License-Identifier: Apache-2.0
"""B-tree of minimum degree `t`, in CLRS's convention.

A node holds many sorted keys, and an internal node has one more child than it has keys; the keys
separate the children's key ranges. One node is meant to be one disk block, so what counts is how
many nodes an operation reads. Every node except the root holds between `t - 1` and `2t - 1` keys,
and every leaf is at the same depth, so a tree of `n` keys has height `O(log_t n)`. Search, insert
and delete each read one node per level: `O(log_t n)` blocks, `O(t log_t n)` comparisons.

Both updates repair on the way *down*, in a single pass. Insert splits every full node before
entering it, so the leaf it reaches has room (CLRS §18.2). Delete tops every child up to at least
`t` keys before entering it, by borrowing from a sibling or merging with one, so the node it
removes from can spare a key (CLRS §18.3).

Like the chapter's other trees, this is a set: keys only, no values. `insert` and `delete` return
whether they changed the key set.

Sources: CLRS §18, Vitter §11.1.

The Rust differs here: it binary-searches a node's keys, gives a split node its full capacity, and
keeps `len` in O(1).

The Lean statements behind this module, in `lean/AlgoDesign/Searching/BTree/` (specification:
`BTree/Spec.lean`): `search_correct_valid`, `insertSpec`, `deleteSpec`, `delete_found`,
`time_insertM_le_log`.
"""

from __future__ import annotations

from collections.abc import Iterator
from itertools import pairwise

from ._ordering import SupportsLT


class _BTNode[K: SupportsLT]:
    """One B-tree node, the chapter's: sorted keys and, for an internal node, one more child than
    keys. `leaf` says which it is, set when the node is made, as CLRS's `x.leaf` is."""

    __slots__ = ("leaf", "keys", "children")

    def __init__(self, leaf: bool) -> None:
        self.leaf = leaf
        self.keys: list[K] = []
        self.children: list[_BTNode[K]] = []


# --- The invariant, one piece per box line ---------------------------------------------------
#
# Each piece reads `leaf` as the Lean reads its two constructors: a leaf is its keys alone.


def _keys_listed[K: SupportsLT](node: _BTNode[K]) -> list[K]:
    """The keys in the order the tree lists them: child, key, child, key, ..., then whatever is
    left over, so it is defined however many children a node has."""
    if node.leaf:
        return list(node.keys)
    listed: list[K] = []
    for i in range(max(len(node.keys), len(node.children))):
        if i < len(node.children):
            listed += _keys_listed(node.children[i])
        if i < len(node.keys):
            listed.append(node.keys[i])
    return listed


def is_keys_in_order[K: SupportsLT](root: _BTNode[K]) -> bool:
    """The keys are in strictly increasing order, inside every node and across nodes."""
    keys = _keys_listed(root)
    return all(a < b for a, b in pairwise(keys))


def is_one_more_child[K: SupportsLT](node: _BTNode[K]) -> bool:
    """A node that is not a leaf has one more child than it has keys."""
    if node.leaf:
        return True
    return len(node.children) == len(node.keys) + 1 and all(
        is_one_more_child(child) for child in node.children
    )


def is_half_full_to_full[K: SupportsLT](root: _BTNode[K], t: int) -> bool:
    """No node is ever more than full, `2t - 1` keys; every node but the root is at least half
    full, `t - 1` keys: the root holds at most `2t - 1`, and every node below it is half full."""
    return len(root.keys) <= max(0, 2 * t - 1) and (
        root.leaf or all(_is_node_half_full(child, t) for child in root.children)
    )


def _is_node_half_full[K: SupportsLT](node: _BTNode[K], t: int) -> bool:
    """A node below the root holds between `t - 1` and `2t - 1` keys, and so does every node
    beneath it."""
    return t - 1 <= len(node.keys) <= max(0, 2 * t - 1) and (
        node.leaf or all(_is_node_half_full(child, t) for child in node.children)
    )


def is_root_branches[K: SupportsLT](root: _BTNode[K]) -> bool:
    """The root is either a leaf or has at least two children."""
    return root.leaf or len(root.children) >= 2


def _leaf_depth[K: SupportsLT](node: _BTNode[K]) -> int | None:
    """How far below `node` its leaves are, if they all agree, else `None`; `None` too for a node
    that is not a leaf and has no children."""
    if node.leaf:
        return 0
    depths = {_leaf_depth(child) for child in node.children}
    if len(depths) != 1:
        return None
    (depth,) = depths
    return None if depth is None else depth + 1


def is_same_depth[K: SupportsLT](root: _BTNode[K]) -> bool:
    """Every leaf sits at the same depth."""
    return _leaf_depth(root) is not None


def _leaf_has_no_children[K: SupportsLT](node: _BTNode[K]) -> bool:
    """Not a box line but the Python node's own: `leaf` is stored, so a node that says it is a
    leaf must have no children."""
    if node.leaf:
        return not node.children
    return all(_leaf_has_no_children(child) for child in node.children)


class BTree[K: SupportsLT]:
    """A B-tree of minimum degree `t`: every node except the root has between `t - 1` and
    `2t - 1` keys, so between `t` and `2t` children if it is internal. `t` must be at least 2.
    """

    def __init__(self, t: int) -> None:
        if t < 2:
            raise ValueError(f"btree.BTree: the minimum degree t must be at least 2, got {t}")
        self.t = t
        self.root: _BTNode[K] = _BTNode(leaf=True)

    # --- search --------------------------------------------------------------------------------

    def search(self, key: K) -> bool:
        """Is `key` one of the tree's keys? In each node, find the first key not smaller than
        `key`; if it is `key` we are done, otherwise descend into the child just to its left."""
        return self._search(self.root, key)

    def __contains__(self, key: K) -> bool:
        return self.search(key)

    def _find_key(self, node: _BTNode[K], key: K) -> int:
        """Index of the first key in `node` that is `>= key` (`== len(node.keys)` if there is
        none). One left-to-right scan, as CLRS writes it."""
        i = 0
        while i < len(node.keys) and node.keys[i] < key:
            i += 1
        return i

    def _search(self, node: _BTNode[K], key: K) -> bool:
        i = self._find_key(node, key)
        if i < len(node.keys) and node.keys[i] == key:
            return True
        if node.leaf:
            return False
        return self._search(node.children[i], key)

    # --- insert ----------------------------------------------------------------------------------

    def insert(self, key: K) -> bool:
        """Insert `key`; `True` if it was new, and the key set is unchanged if it was not.

        CLRS's *proactive* splitting: split every full (`2t - 1`-key) node the descent is about
        to enter, before entering it, so the leaf finally reached has room. A full root is split
        first, and that is the only way the tree grows taller.

        There is no separate lookup first, so inserting a present key may still split full nodes
        above it (a full root always): the same keys, a different shape, and `False`.
        """
        if len(self.root.keys) == 2 * self.t - 1:
            new_root: _BTNode[K] = _BTNode(leaf=False)
            new_root.children.append(self.root)
            self._split_child(new_root, 0)
            self.root = new_root
        return self._insert_nonfull(self.root, key)

    def _split_child(self, parent: _BTNode[K], i: int) -> None:
        """Split the full node `parent.children[i]` (exactly `2t - 1` keys) into two nodes of
        `t - 1` keys each, its middle key rising into `parent` at position `i` and the new right
        half becoming `parent.children[i + 1]`. CLRS's `B-TREE-SPLIT-CHILD`: `y` the full node,
        `z` its new right sibling, `mid` the middle key."""
        t = self.t
        y = parent.children[i]
        z: _BTNode[K] = _BTNode(leaf=y.leaf)
        mid = y.keys[t - 1]
        z.keys = y.keys[t:]
        y.keys = y.keys[: t - 1]
        if not y.leaf:
            z.children = y.children[t:]
            y.children = y.children[:t]
        parent.children.insert(i + 1, z)
        parent.keys.insert(i, mid)

    def _insert_nonfull(self, node: _BTNode[K], key: K) -> bool:
        """Insert `key` into the subtree rooted at `node`, which is *not* full. Returns `False`
        early if it meets `key`."""
        i = self._find_key(node, key)
        if i < len(node.keys) and node.keys[i] == key:
            return False  # already present at this level: nothing to insert, nothing to split
        if node.leaf:
            node.keys.insert(i, key)
            return True
        child = node.children[i]
        if len(child.keys) == 2 * self.t - 1:
            # If the median is the key, the key is already here: don't split.
            if child.keys[self.t - 1] == key:
                return False
            self._split_child(node, i)
            if node.keys[i] < key:
                i += 1
        return self._insert_nonfull(node.children[i], key)

    # --- delete ----------------------------------------------------------------------------------

    def delete(self, key: K) -> bool:
        """Delete `key`; `True` if it was there.

        CLRS's top-down scheme: before descending into a child, top it up to at least `t` keys,
        by borrowing a key from a sibling or merging with one. Every node the descent reaches can
        then lose a key without underflowing. An absent key may still leave the tree rebalanced.
        """
        found = self._delete(self.root, key)
        if not self.root.leaf and not self.root.keys:
            # The root's only key went into a merge: its sole child is the new root.
            self.root = self.root.children[0]
        return found

    def _delete(self, node: _BTNode[K], key: K) -> bool:
        """Delete `key` from the subtree at `node`; `True` if it was there."""
        idx = self._find_key(node, key)
        if idx < len(node.keys) and node.keys[idx] == key:
            if node.leaf:
                del node.keys[idx]
            else:
                self._delete_from_internal(node, idx)
            return True
        if node.leaf:
            return False  # `key` isn't in the tree at all.
        # `key`, if present, is in `node.children[idx]` — top it up to `>= t` keys first.
        if len(node.children[idx].keys) < self.t:
            # A merge moves the child, so `_top_up` says where it ended up.
            idx = self._top_up(node, idx)
        return self._delete(node.children[idx], key)

    def _delete_from_internal(self, node: _BTNode[K], idx: int) -> None:
        """Delete `node.keys[idx]`, known to be in the internal node `node` itself: replace it
        with its predecessor or successor, taken out of whichever side has a spare key to donate
        (`>= t`) -- or, if neither side can spare one, merge the two children (absorbing
        `node.keys[idx]` into the merge) and recurse into the merged node. The predecessor is
        found and removed in one walk down."""
        key = node.keys[idx]
        left, right = node.children[idx], node.children[idx + 1]
        if len(left.keys) >= self.t:
            node.keys[idx] = self._take_max(left)
        elif len(right.keys) >= self.t:
            node.keys[idx] = self._take_min(right)
        else:
            self._merge(node, idx)
            self._delete(node.children[idx], key)

    def _take_max(self, node: _BTNode[K]) -> K:
        """Remove and return the largest key under `node`, which has at least `t` keys: walk down
        the last children, topping each up to `t` keys before entering it, as `_delete` does."""
        while not node.leaf:
            last = len(node.children) - 1
            if len(node.children[last].keys) < self.t:
                last = self._top_up(node, last)  # a merge moves the last child one to the left
            node = node.children[last]
        return node.keys.pop()

    def _take_min(self, node: _BTNode[K]) -> K:
        """Remove and return the smallest key under `node`: the mirror image of `_take_max`. The
        first child has no left sibling, so topping it up leaves it at index 0."""
        while not node.leaf:
            if len(node.children[0].keys) < self.t:
                self._top_up(node, 0)
            node = node.children[0]
        return node.keys.pop(0)

    def _top_up(self, node: _BTNode[K], idx: int) -> int:
        """Top up `node.children[idx]` (currently `t - 1` keys) to at least `t` keys: borrow a key
        from whichever immediate sibling has one to spare, or merge with a sibling if neither
        does. Returns the index the child sits at afterwards -- merging with the left sibling puts
        it at `idx - 1`. Tried in order: borrow left, borrow right, merge left, merge right."""
        if idx != 0 and len(node.children[idx - 1].keys) >= self.t:
            self._borrow_from_prev(node, idx)
            return idx
        if idx != len(node.keys) and len(node.children[idx + 1].keys) >= self.t:
            self._borrow_from_next(node, idx)
            return idx
        if idx != 0:
            self._merge(node, idx - 1)
            return idx - 1
        self._merge(node, idx)
        return idx

    def _borrow_from_prev(self, node: _BTNode[K], idx: int) -> None:
        """Rotate one key from `node.children[idx - 1]` through `node.keys[idx - 1]` into the
        front of `node.children[idx]` (and, for internal nodes, carry the matching child pointer
        along with it)."""
        child, sibling = node.children[idx], node.children[idx - 1]
        child.keys.insert(0, node.keys[idx - 1])
        if not child.leaf:
            child.children.insert(0, sibling.children.pop())
        node.keys[idx - 1] = sibling.keys.pop()

    def _borrow_from_next(self, node: _BTNode[K], idx: int) -> None:
        """Mirror image of `_borrow_from_prev`: rotate one key from `node.children[idx + 1]`
        through `node.keys[idx]` onto the back of `node.children[idx]`."""
        child, sibling = node.children[idx], node.children[idx + 1]
        child.keys.append(node.keys[idx])
        if not child.leaf:
            child.children.append(sibling.children.pop(0))
        node.keys[idx] = sibling.keys.pop(0)

    def _merge(self, node: _BTNode[K], idx: int) -> None:
        """Merge `node.children[idx]`, the separator `node.keys[idx]`, and `node.children[idx +
        1]` into a single node of `2t - 1` keys, removing the now-absorbed separator and right
        sibling from `node`."""
        child, sibling = node.children[idx], node.children[idx + 1]
        child.keys.append(node.keys.pop(idx))
        child.keys.extend(sibling.keys)
        child.children.extend(sibling.children)
        node.children.pop(idx + 1)

    # --- misc --------------------------------------------------------------------------------

    def __iter__(self) -> Iterator[K]:
        """Keys in ascending order: each node's children and keys, interleaved left to right."""
        yield from self._in_order(self.root)

    def _in_order(self, node: _BTNode[K]) -> Iterator[K]:
        if node.leaf:
            yield from node.keys
            return
        for i, key in enumerate(node.keys):
            yield from self._in_order(node.children[i])
            yield key
        yield from self._in_order(node.children[-1])

    def __len__(self) -> int:
        """How many keys: a walk of the whole tree, `O(n)`."""
        return sum(1 for _ in self)

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, in its order, or `None`:
        `"invariant 1 (keys_in_order)"`, `"invariant 2 (one_more_child)"`,
        `"invariant 3 (half_full_to_full)"`, `"invariant 4 (root_branches)"`,
        `"invariant 5 (same_depth)"` or `"layout (leaf_has_no_children)"`."""
        if not is_keys_in_order(self.root):
            return "invariant 1 (keys_in_order)"
        if not is_one_more_child(self.root):
            return "invariant 2 (one_more_child)"
        if not is_half_full_to_full(self.root, self.t):
            return "invariant 3 (half_full_to_full)"
        if not is_root_branches(self.root):
            return "invariant 4 (root_branches)"
        if not is_same_depth(self.root):
            return "invariant 5 (same_depth)"
        if not _leaf_has_no_children(self.root):
            return "layout (leaf_has_no_children)"
        return None

    def is_valid(self) -> bool:
        """All the B-tree invariants, the five box lines in order -- keys in order, one more child
        than keys, half full to full, a root that branches, every leaf at the same depth -- and
        last that no node flagged a leaf has children."""
        return self.check_valid() is None
