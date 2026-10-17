# SPDX-License-Identifier: Apache-2.0
"""An R-way trie over byte keys (Sedgewick-Wayne §5.2).

**The key is the path.** Each edge is labelled with one byte, and a node holds the value of the key
spelled by the path from the root to it, so `keys` rebuilds each key from the path walked.

`insert`, `get` and `contains` take O(m) steps for a key of m bytes, however many keys are stored.
The trie holds one node per distinct prefix of a stored key, plus the root. Children live in a
`dict`, so the `ALPHABET` (256) slots of an array-based node are not allocated.

`remove` and the subtree walks recurse once per level, so a key longer than Python's recursion
limit raises `RecursionError`.

The Rust differs here: a node is an array of 256 child slots, and `remove` is two loops.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/Trie/` (specification:
`Trie/Spec.lean`): `get_insert`, `get_insert_other`, `distinctLetters_insert`, and for removal
`get_remove`, `get_remove_other`, `distinctLetters_remove`.
"""

from __future__ import annotations

from ._constants import BYTE_VALUES

ALPHABET = BYTE_VALUES
"""The R in "R-way": how many distinct symbols a byte key can use, and therefore how many child
slots an array-based node allocates whether or not they are used.

This module's nodes do not allocate them -- children live in a `dict`. The constant is here so that
the cost `Patricia` exists to remove is a number a reader can compute (`node_count() * ALPHABET`
child slots).
"""


class _Node[V]:
    """One node: the value stored at this exact path, and the children filed by next byte.
    `has_value` lets `None` be a stored value."""

    __slots__ = ("value", "has_value", "children")

    def __init__(self) -> None:
        self.value: V | None = None
        self.has_value: bool = False
        self.children: dict[int, _Node[V]] = {}


class Trie[V]:
    """A trie mapping `bytes` keys to values of type `V`. The empty key is stored at the root."""

    def __init__(self) -> None:
        self.root: _Node[V] = _Node()
        self._len = 0

    def __len__(self) -> int:
        """How many keys hold a value. Maintained by `insert` and `remove`, not walked."""
        return self._len

    def insert(self, key: bytes, value: V) -> V | None:
        """Store `value` at `key`, returning whatever value was there before, or `None`.

        Walk down from the root, creating the missing path one node per byte, and write at the end
        of the walk. A key that is not `bytes` raises `TypeError`.
        """
        if not isinstance(key, bytes):
            raise TypeError(f"a trie key is bytes, not {type(key).__name__}")
        node = self.root
        for byte in key:
            child = node.children.get(byte)
            if child is None:
                child = _Node()
                node.children[byte] = child
            node = child
        old = node.value
        if not node.has_value:
            self._len += 1
        node.value = value
        node.has_value = True
        return old

    def remove(self, key: bytes) -> V | None:
        """Take `key` out, returning the value it held, or `None` if it held none -- absent, or
        merely a prefix of a stored key, in which case nothing changes.

        Sedgewick and Wayne's `TrieST.delete`: go down to the key's node and clear its value, and
        on the way back up drop every node left with no value and no children, so only the part of
        the path this key alone used goes.
        """
        node = self._node_at(key)
        if node is None or not node.has_value:
            return None
        old = node.value
        self._remove(self.root, key, 0)
        self._len -= 1
        return old

    def _remove(self, node: _Node[V], key: bytes, depth: int) -> bool:
        """Clear `key`'s value below `node` (reached by `key[:depth]`), unlinking emptied children;
        `True` if `node` itself is now empty, for its parent to unlink."""
        if depth == len(key):
            node.value = None
            node.has_value = False
        elif self._remove(node.children[key[depth]], key, depth + 1):
            del node.children[key[depth]]
        return not node.has_value and not node.children

    def _node_at(self, key: bytes) -> _Node[V] | None:
        """The node `key` leads to, or `None` if the path stops short."""
        node = self.root
        for byte in key:
            child = node.children.get(byte)
            if child is None:
                return None
            node = child
        return node

    def get(self, key: bytes) -> V | None:
        """The value stored at `key`, or `None` if `key` was never inserted.

        A key that is merely a prefix of some stored key is not itself stored: the node is there,
        but it holds no value.
        """
        node = self._node_at(key)
        return node.value if node is not None and node.has_value else None

    def contains(self, key: bytes) -> bool:
        """Whether `key` holds a value -- exact, where `get` is not, for a stored `None`."""
        node = self._node_at(key)
        return node is not None and node.has_value

    def keys(self) -> list[bytes]:
        """Every stored key, in lexicographic order.

        Visiting a node before its children, children in ascending byte order, is lexicographic
        order: a node's key is a prefix of every key below it, and a prefix sorts first.
        """
        return self.keys_with_prefix(b"")

    def keys_with_prefix(self, prefix: bytes) -> list[bytes]:
        """Every stored key beginning with `prefix`, in lexicographic order: one descent to the
        node `prefix` leads to, then a walk of everything below it."""
        node = self._node_at(prefix)
        if node is None:
            return []
        out: list[bytes] = []
        self._collect(node, prefix, out)
        return out

    def _collect(self, node: _Node[V], path: bytes, out: list[bytes]) -> None:
        """Append every key at or below `node`, which `path` leads to, in lexicographic order. One
        frame per level: below a chain deeper than the recursion limit this raises
        `RecursionError`."""
        if node.has_value:
            out.append(path)
        for byte in sorted(node.children):
            child = node.children[byte]
            step = path + bytes([byte])
            self._collect(child, step, out)

    def longest_prefix(self, key: bytes) -> bytes | None:
        """The longest prefix of `key` that is itself a stored key, or `None` if none is.

        Descend along `key`, remembering the last length at which the node reached held a value
        -- the longest-prefix match of a router's forwarding table.
        """
        node = self.root
        best = 0 if node.has_value else None
        for i, byte in enumerate(key):
            child = node.children.get(byte)
            if child is None:
                break
            node = child
            if node.has_value:
                best = i + 1
        return None if best is None else key[:best]

    def node_count(self) -> int:
        """How many nodes the trie holds, the root included -- so an empty trie counts 1.

        A key with no branching neighbours costs as many nodes as it has bytes; `Patricia`
        collapses each such chain into a single labelled edge.
        """
        return self._count(self.root)

    def _count(self, node: _Node[V]) -> int:
        """This node plus everything below it."""
        total = 1
        for child in node.children.values():
            total += self._count(child)
        return total

    def _nodes(self) -> list[_Node[V]]:
        """Every node, the root first, gathered by a loop rather than recursion."""
        out: list[_Node[V]] = []
        todo = [self.root]
        while todo:
            node = todo.pop()
            out.append(node)
            todo.extend(node.children.values())
        return out

    def is_distinct_letters(self) -> bool:
        """Box invariant 2: paths leaving the same point carry different letters. The Lean
        `Trie.DistinctLetters`. The `dict` of children already guarantees it."""
        for node in self._nodes():
            keys = list(node.children)
            if len(set(keys)) != len(keys):
                return False
        return True

    def is_no_dead_branches(self) -> bool:
        """Box invariant 3: every branch leads to a stored word, so no node below the root is both
        valueless and childless. The Lean `Trie.NoDeadBranches`. The root is exempt: the empty trie
        is such a node."""
        return all(node.has_value or node.children for node in self._nodes()[1:])

    def is_len_matches(self) -> bool:
        """Layout check: `len` counts the nodes that hold a value."""
        held = 0
        for node in self._nodes():
            if node.has_value:
                held += 1
        return held == self._len

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, in its order, or `None`:
        `"invariant 2 (distinct_letters)"`, `"invariant 3 (no_dead_branches)"` or
        `"layout (len_matches)"`."""
        # Box invariant 1, a word is a path of letters to a mark, is what `get` means: the paths
        # are the words. A child moved to another letter spells other words in a legal trie, so
        # no check of the tree alone can see it; the tests compare `keys()` with the words put in.
        if not self.is_distinct_letters():
            return "invariant 2 (distinct_letters)"
        if not self.is_no_dead_branches():
            return "invariant 3 (no_dead_branches)"
        if not self.is_len_matches():
            return "layout (len_matches)"
        return None

    def is_valid(self) -> bool:
        """The Lean `Trie.Valid` (`is_distinct_letters`, `is_no_dead_branches`) plus the layout
        check `is_len_matches`."""
        return self.check_valid() is None
