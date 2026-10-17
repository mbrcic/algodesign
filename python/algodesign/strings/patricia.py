# SPDX-License-Identifier: Apache-2.0
"""Patricia tree -- a path-compressed trie over byte keys.

A trie spends a node per byte, so a key with no branching neighbours costs a chain of nodes. Path
compression collapses those chains: every edge carries a **non-empty label**, a whole run of bytes
rather than a single one, and a node below the root survives only if it holds a value or branches.

Only the node count gets smaller: every byte still sits in a label, in order. Lookups still compare
O(m) bytes for a key of length m, but the tree has O(k) nodes for k keys, however long the keys are.

This is an edge-labelled compressed trie, also called a radix tree (Weiss §12.4.2); the book calls
it a Patricia tree (Nipkow et al. §12.3). Morrison's PATRICIA (1968) is its bit-level relative.

`insert` **splits an edge** when a new key diverges partway along its label; `remove` clears a
value, unlinks a node left with nothing, and **re-collapses** a valueless single-child node into
its child.

The Rust differs here: children are a list sorted by first byte, found by binary search, so it also
checks `is_sorted_heads`; `remove` is a loop.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/Patricia/` (specification:
`Patricia/Spec.lean`): `get_insert`, `get_insert_other`, `valid_insert` for insertion;
`get_ofTrie`, `noEmptyBranches_ofTrie`, `words_perm_ofTrie` for compressing a whole trie at once,
which holds the same words; and `get_remove`, `get_remove_other`, `valid_remove` for removal.
"""

from __future__ import annotations


class _Node[V]:
    """One node: the label of the edge coming in (empty at the root), the value stored where that
    edge ends, and the children filed by the first byte of *their* labels."""

    __slots__ = ("label", "value", "has_value", "children")

    def __init__(self, label: bytes) -> None:
        self.label = label
        self.value: V | None = None
        self.has_value: bool = False
        self.children: dict[int, _Node[V]] = {}


def _leaf[V](label: bytes, value: V) -> _Node[V]:
    """A new childless node holding `value` at the end of `label`."""
    node: _Node[V] = _Node(label)
    node.value = value
    node.has_value = True
    return node


def _common_prefix_len(a: bytes, b: bytes) -> int:
    """How many leading bytes `a` and `b` share -- where an edge splits."""
    n = 0
    while n < len(a) and n < len(b) and a[n] == b[n]:
        n += 1
    return n


class Patricia[V]:
    """A path-compressed trie mapping `bytes` keys to values of type `V`, with `Trie`'s operations.
    The empty key is stored at the root."""

    def __init__(self) -> None:
        self.root: _Node[V] = _Node(b"")
        self._len = 0

    def __len__(self) -> int:
        """How many keys hold a value. Maintained by `insert` and `remove`, not walked."""
        return self._len

    def insert(self, key: bytes, value: V) -> V | None:
        """Store `value` at `key`, returning whatever value was there before, or `None`.

        A loop that walks down whole edge labels while they still match the unconsumed remainder of
        `key`, ending in one of three moves:

        * the remainder runs out on a node -- write the value there;
        * no child is filed under the remainder's first byte -- hang a new leaf whose label is the
          whole remainder, however long it is. This is where compression happens: a run of bytes
          with nothing to branch off it becomes one edge, not one node per byte;
        * the remainder agrees with an edge's label for a while and then diverges -- **split the
          edge** at the divergence. The shared part becomes a new intermediate node's label; the
          rest of the old label stays with the old child, now filed under the new node. If `key`
          ends exactly at the split point the new node holds the value itself; if `key` runs on, the
          new node is valueless with two children, which is allowed because it branches.

        A key that is not `bytes` raises `TypeError`.
        """
        if not isinstance(key, bytes):
            raise TypeError(f"a Patricia key is bytes, not {type(key).__name__}")
        node = self.root
        rest = key
        while True:
            if not rest:
                old = node.value
                if not node.has_value:
                    self._len += 1
                node.value = value
                node.has_value = True
                return old
            byte = rest[0]
            child = node.children.get(byte)
            if child is None:
                node.children[byte] = _leaf(rest, value)
                self._len += 1
                return None
            common = _common_prefix_len(child.label, rest)
            if common == len(child.label):
                # The whole label matched: descend.
                rest = rest[common:]
                node = child
                continue
            # `rest` diverges after `common` bytes -- at least one, since the first byte matched.
            split: _Node[V] = _Node(child.label[:common])
            child.label = child.label[common:]
            split.children[child.label[0]] = child
            if common == len(rest):
                split.value = value
                split.has_value = True
            else:
                tail = _leaf(rest[common:], value)
                split.children[tail.label[0]] = tail
            node.children[byte] = split
            self._len += 1
            return None

    def remove(self, key: bytes) -> V | None:
        """Take `key` out, returning the value it held, or `None` if it held none -- absent, a bare
        prefix of a stored key, or ending inside an edge label, in which cases nothing changes.

        Go down to the key's node and clear its value; then, on the way back up, repair the child
        just returned from, since below the root a node must hold a value or branch:

        * no value and no children -- unlink it;
        * no value and one child -- **merge** it into that child, joining the two labels.

        The root is exempt. Recursive, one frame per edge on the path.
        """
        node = self._node_at(key)
        if node is None or not node.has_value:
            return None
        old = node.value
        self._remove(self.root, key)
        self._len -= 1
        return old

    def _remove(self, node: _Node[V], rest: bytes) -> None:
        """Clear the value `rest` leads to below `node`, then repair the child it went through."""
        if not rest:
            node.value = None
            node.has_value = False
            return
        child = node.children[rest[0]]
        self._remove(child, rest[len(child.label) :])
        if child.has_value:
            return
        if not child.children:
            del node.children[rest[0]]
        elif len(child.children) == 1:
            (only,) = child.children.values()
            only.label = child.label + only.label
            node.children[rest[0]] = only

    def _node_at(self, key: bytes) -> _Node[V] | None:
        """The node `key` leads to, or `None` if no edge boundary falls exactly on `key` (a key
        ending inside a label is not in the tree)."""
        node = self.root
        rest = key
        while rest:
            child = node.children.get(rest[0])
            if child is None or not rest.startswith(child.label):
                return None
            rest = rest[len(child.label) :]
            node = child
        return node

    def get(self, key: bytes) -> V | None:
        """The value stored at `key`, or `None` if `key` was never inserted -- including when
        `key` is merely a prefix of a stored key, or falls strictly inside an edge label."""
        node = self._node_at(key)
        return node.value if node is not None and node.has_value else None

    def contains(self, key: bytes) -> bool:
        """Whether `key` holds a value -- exact, where `get` is not, for a stored `None`."""
        node = self._node_at(key)
        return node is not None and node.has_value

    def keys(self) -> list[bytes]:
        """Every stored key, in lexicographic order.

        Rebuilt from the labels walked; children taken in ascending order of their first byte.
        """
        return self.keys_with_prefix(b"")

    def keys_with_prefix(self, prefix: bytes) -> list[bytes]:
        """Every stored key beginning with `prefix`, in lexicographic order.

        Unlike in `Trie`, `prefix` may end inside an edge label; then every key below that edge
        begins with `prefix`, and the subtree below it is the answer.
        """
        node = self.root
        consumed = b""
        rest = prefix
        while rest:
            child = node.children.get(rest[0])
            if child is None:
                return []
            if len(child.label) <= len(rest):
                if not rest.startswith(child.label):
                    return []
                consumed += child.label
                rest = rest[len(child.label) :]
                node = child
            else:
                if not child.label.startswith(rest):
                    return []
                consumed += child.label
                node = child
                rest = b""
        out: list[bytes] = []
        self._collect(node, consumed, out)
        return out

    def _collect(self, node: _Node[V], path: bytes, out: list[bytes]) -> None:
        """Append every key at or below `node`, which `path` leads to, in lexicographic order."""
        if node.has_value:
            out.append(path)
        for byte in sorted(node.children):
            child = node.children[byte]
            self._collect(child, path + child.label, out)

    def longest_prefix(self, key: bytes) -> bytes | None:
        """The longest prefix of `key` that is itself a stored key, or `None` if none is.

        The descent stops the moment `key`'s remainder fails to match a whole label.
        """
        node = self.root
        best = 0 if node.has_value else None
        consumed = 0
        rest = key
        while rest:
            child = node.children.get(rest[0])
            if child is None or not rest.startswith(child.label):
                break
            consumed += len(child.label)
            rest = rest[len(child.label) :]
            node = child
            if node.has_value:
                best = consumed
        return None if best is None else key[:best]

    def node_count(self) -> int:
        """How many nodes the tree holds, the root included, as `Trie.node_count` counts."""
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

    def is_distinct_first_letters(self) -> bool:
        """Box invariant 2: the branches leaving a node start with different letters. The Lean
        `DistinctFirstLetters`: in every node, no two children's labels begin with the same byte.

        Read from the labels, not the `dict` keys; an empty label's head is `b""`.
        """
        for node in self._nodes():
            heads = [child.label[:1] for child in node.children.values()]
            if len(set(heads)) != len(heads):
                return False
        return True

    def is_branches_unless_word_ends(self) -> bool:
        """Box invariant 3: every node below the root where no word ends has two children or more.
        The Lean `BranchesUnlessWordEnds`.
        """
        for node in self._nodes()[1:]:
            if not node.has_value and len(node.children) < 2:
                return False
        return True

    def is_no_empty_branches(self) -> bool:
        """Box invariant 4: every branch carries at least one letter. The Lean
        `NoEmptyBranches`."""
        return all(node.label != b"" for node in self._nodes()[1:])

    def is_children_filed_by_head(self) -> bool:
        """Layout check: every child is filed under the first byte of its own label."""
        for node in self._nodes():
            for key, child in node.children.items():
                if child.label == b"" or child.label[0] != key:
                    return False
        return True

    def is_len_matches(self) -> bool:
        """Layout check: `len` counts the nodes that hold a value."""
        held = 0
        for node in self._nodes():
            if node.has_value:
                held += 1
        return held == self._len

    def check_valid(self) -> str | None:
        """The first check `is_valid` finds broken, in its order, or `None`:
        `"invariant 2 (distinct_first_letters)"`, `"invariant 3 (branches_unless_word_ends)"`,
        `"invariant 4 (no_empty_branches)"`, `"layout (children_filed_by_head)"` or
        `"layout (len_matches)"`."""
        # Box invariant 1, a word is the path from the root to a mark, is what `get` means. An
        # edge relabelled to start with another letter fails `is_children_filed_by_head`; one
        # changed after its first letter spells other words in a legal tree, which no check of the
        # tree alone can see, so the tests compare `keys()` with the words put in.
        if not self.is_distinct_first_letters():
            return "invariant 2 (distinct_first_letters)"
        if not self.is_branches_unless_word_ends():
            return "invariant 3 (branches_unless_word_ends)"
        if not self.is_no_empty_branches():
            return "invariant 4 (no_empty_branches)"
        if not self.is_children_filed_by_head():
            return "layout (children_filed_by_head)"
        if not self.is_len_matches():
            return "layout (len_matches)"
        return None

    def is_valid(self) -> bool:
        """The Lean `Patricia.Valid` (`is_distinct_first_letters`, `is_branches_unless_word_ends`,
        `is_no_empty_branches`) plus the layout checks `is_children_filed_by_head` and
        `is_len_matches`."""
        return self.check_valid() is None
