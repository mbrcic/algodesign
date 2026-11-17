# SPDX-License-Identifier: Apache-2.0
"""The range tree: every key in [lo, hi], found in O(log n + k) (dBCKO §5.1 in 1D, §5.3 in 2D).

**The 1D tree** is a balanced binary tree with the keys in its **leaves**, sorted left to right.
Each inner node holds a split key, the largest key in its left subtree: the **lower median** of
the keys below it. A query walks from the root to the **split node**, the first node where the
range sends it both ways (`FINDSPLITNODE`). Then it follows `lo` down the left side and `hi` down
the right side (`1DRANGEQUERY`), and reports every whole subtree that hangs between the two paths:
those lie inside the range without looking at their keys.

**Equal keys may sit on both sides of a split.** The build halves the sorted keys by *position*,
so the tree stays balanced however many keys repeat, and copies of the split key can land in
either child. So the walk to the split node goes left only when `hi < split` (dBCKO: `hi <=
split`); with distinct keys the answer is dBCKO's, though the walk may stop at a different node.

**The invariant** has two pieces, the design box's: every split key separates its two sides
(`is_keys_separate`), and every node splits the keys below it in half (`is_splits_halve`).

**The 2D tree** is a 1D tree on x whose every inner node also carries an *associated* 1D tree
on the y-keys of the points below it (`2DRANGEQUERY`). A whole subtree found by the x-walk is
searched by its associated tree on y. The build makes each node's y-list by **merging** its
children's, left child first on equal y, so no list is sorted twice: O(n log n) (dBCKO Theorem
5.8). A 2D query returns its points in the order the walk finds them; sort them if order matters.

Keys may be of any type that can be compared: nothing is averaged, so strings and dates work as
numbers do. Building copies its input, so the caller's list is left as it was.

The Rust differs here: only in being compiled; its 2D query reports in walk order, as this one does.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/RangeTree/`:
`query_eq_filter`, `leaves_build`, `keysSeparate_build`, `splitsHalve_build`, `build_split_mem`,
`time_queryM_le`, `query_build`.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any, Generic, Protocol, TypeVar


class SupportsLT(Protocol):
    """Keys with a total order: numbers, strings, tuples of those."""

    def __lt__(self, other: Any, /) -> bool: ...


K = TypeVar("K", bound=SupportsLT)


@dataclass
class Leaf:
    """One key, at sorted position `start` (its subtree covers `[start, start + 1)`)."""

    start: int

    @property
    def end(self) -> int:
        return self.start + 1


@dataclass
class Node(Generic[K]):
    """A split key, and the sorted positions `[start, end)` of the keys below."""

    split: K
    start: int
    end: int
    left: Node[K] | Leaf
    right: Node[K] | Leaf


def build(keys: Sequence[K], start: int, end: int) -> Node[K] | Leaf:
    """The tree over sorted positions `[start, end)`, nonempty: the first ceil(n/2) go left, and
    the split is the key at the last of them, the lower median."""
    if end - start == 1:
        return Leaf(start)
    m = start + (end - start + 1) // 2
    return Node(keys[m - 1], start, end, build(keys, start, m), build(keys, m, end))


class RangeTree1D(Generic[K]):
    """A static range tree over keys of any comparable type, repeats allowed."""

    def __init__(self, keys: Sequence[K]) -> None:
        reject_nan(keys)
        # Sorted stably, so equal keys keep their input order.
        pairs = sorted(zip(keys, range(len(keys))), key=lambda p: p[0])
        self.keys: list[K] = [k for k, _ in pairs]
        self.order: list[int] = [i for _, i in pairs]
        self.root = build(self.keys, 0, len(self.keys)) if self.keys else None

    @classmethod
    def from_sorted(cls, keys: list[K]) -> RangeTree1D[K]:
        """A tree over keys already in order, without sorting them again: the associated trees of
        the 2D build, whose keys arrive merged. Position `p` is id `p`."""
        tree: RangeTree1D[K] = cls([])  # an empty tree, then filled with keys already in order
        tree.keys = keys
        tree.order = list(range(len(keys)))
        tree.root = build(keys, 0, len(keys)) if keys else None
        return tree

    def below(self, v: Node[K] | Leaf) -> list[K]:
        """The keys in `v`'s subtree, left to right."""
        return self.keys[v.start : v.end]

    def is_keys_separate(self) -> bool:
        """Box invariant 1: every inner key separates its two sides: nothing on its left is
        larger, nothing on its right is smaller. The Lean `KeysSeparate`."""

        def separate(v: Node[K] | Leaf) -> bool:
            if isinstance(v, Leaf):
                return True
            return (
                all(not v.split < k for k in self.below(v.left))
                and all(not k < v.split for k in self.below(v.right))
                and separate(v.left)
                and separate(v.right)
            )

        return self.root is None or separate(self.root)

    def is_splits_halve(self) -> bool:
        """Box invariant 2: every inner node splits the points below it in half. The Lean
        `SplitsHalve`: at every node the left side holds ceil(n/2) of its n keys, the right the
        rest."""

        def halves(v: Node[K] | Leaf) -> bool:
            if isinstance(v, Leaf):
                return True
            left, right = len(self.below(v.left)), len(self.below(v.right))
            return right <= left <= right + 1 and halves(v.left) and halves(v.right)

        return self.root is None or halves(self.root)

    def check_valid(self) -> str | None:
        """The first piece of the Lean `RangeTree1D.Valid` the tree breaks, or `None`."""
        if not self.is_keys_separate():
            return "invariant 1 (keys_separate)"
        if not self.is_splits_halve():
            return "invariant 2 (splits_halve)"
        return None

    def is_valid(self) -> bool:
        """The Lean `RangeTree1D.Valid`: `is_keys_separate` and `is_splits_halve`."""
        return self.check_valid() is None

    def depth(self) -> int:
        """The tree's height: 0 for one key, and at most ceil(log2 n)."""
        return height(self.root)

    def query(self, lo: K, hi: K) -> list[int]:
        """The ids of the keys in [lo, hi], in key order, equal keys in input order."""
        return [self.order[p] for p in self.query_positions(lo, hi)]

    def query_keys(self, lo: K, hi: K) -> list[K]:
        """The keys in [lo, hi], in order."""
        return [self.keys[p] for p in self.query_positions(lo, hi)]

    def query_positions(self, lo: K, hi: K) -> list[int]:
        """The sorted positions of the keys in [lo, hi], ascending: the canonical subtrees' runs,
        left to right."""
        subtrees = sorted(self.canonical_subtrees(lo, hi), key=lambda v: v.start)
        return [p for v in subtrees for p in range(v.start, v.end)]

    def canonical_subtrees(self, lo: K, hi: K) -> list[Node[K] | Leaf]:
        """The whole subtrees, and the single leaves, whose keys are exactly those in [lo, hi]:
        `FINDSPLITNODE`, then `1DRANGEQUERY`'s two walks."""
        if self.root is None or hi < lo:
            return []
        v = self.root
        while isinstance(v, Node) and (hi < v.split or v.split < lo):
            v = v.left if hi < v.split else v.right
        if isinstance(v, Leaf):
            return [v] if self.in_range(v, lo, hi) else []
        found: list[Node[K] | Leaf] = []
        # Follow lo down the left side; a right child hanging off the path lies inside.
        w = v.left
        while isinstance(w, Node):
            if not w.split < lo:
                found.append(w.right)
                w = w.left
            else:
                w = w.right
        if self.in_range(w, lo, hi):
            found.append(w)
        # Follow hi down the right side; a left child hanging off the path lies inside.
        w = v.right
        while isinstance(w, Node):
            if not hi < w.split:
                found.append(w.left)
                w = w.right
            else:
                w = w.left
        if self.in_range(w, lo, hi):
            found.append(w)
        return found

    def in_range(self, leaf: Leaf, lo: K, hi: K) -> bool:
        key = self.keys[leaf.start]
        return not key < lo and not hi < key


def height(v: Node[Any] | Leaf | None) -> int:
    if not isinstance(v, Node):
        return 0
    return 1 + max(height(v.left), height(v.right))


@dataclass
class Leaf2:
    """One point, at x-sorted position `start`."""

    start: int


@dataclass
class Node2(Generic[K]):
    """An x-split, the associated tree on the y-keys of the points below (their ids in
    `ids`, in the same y order), and the x-sorted positions `[start, end)` below."""

    split: K
    assoc: RangeTree1D[K]
    ids: list[int]
    start: int
    end: int
    left: Node2[K] | Leaf2
    right: Node2[K] | Leaf2


class RangeTree2D(Generic[K]):
    """A static 2D range tree: an x-tree with associated y-trees (dBCKO §5.3)."""

    def __init__(self, points: Sequence[tuple[K, K]]) -> None:
        for p in points:
            if len(p) != 2:
                raise ValueError(f"a 2D range tree needs points of two coordinates, got {p!r}")
        copied = [(p[0], p[1]) for p in points]
        reject_nan([c for p in copied for c in p])
        # Sorted stably by x, each point with its id.
        self.points: list[tuple[tuple[K, K], int]] = sorted(
            zip(copied, range(len(copied))), key=lambda p: p[0][0]
        )
        self.root = self.build(0, len(self.points))[0] if self.points else None

    def build(self, start: int, end: int) -> tuple[Node2[K] | Leaf2, list[tuple[K, int]]]:
        """The subtree over x-sorted positions `[start, end)`, and its points as `(y, id)`
        in y order, equal y in x order: the list its parent merges."""
        if end - start == 1:
            (_, y), i = self.points[start]
            return Leaf2(start), [(y, i)]
        m = start + (end - start + 1) // 2
        left, from_left = self.build(start, m)
        right, from_right = self.build(m, end)
        by_y = merge_by_y(from_left, from_right)
        assoc = RangeTree1D.from_sorted([y for y, _ in by_y])
        node = Node2(self.points[m - 1][0][0], assoc, [i for _, i in by_y], start, end, left, right)
        return node, by_y

    def below(self, v: Node2[K] | Leaf2) -> list[tuple[tuple[K, K], int]]:
        """The points in `v`'s subtree, with their ids, in x order."""
        end = v.start + 1 if isinstance(v, Leaf2) else v.end
        return self.points[v.start : end]

    def is_keys_separate(self) -> bool:
        """Box invariant 1, on the x-tree: every inner key separates its two sides: no point on
        its left has a larger x, none on its right a smaller one."""

        def separate(v: Node2[K] | Leaf2) -> bool:
            if isinstance(v, Leaf2):
                return True
            return (
                all(not v.split < p[0] for p, _ in self.below(v.left))
                and all(not p[0] < v.split for p, _ in self.below(v.right))
                and separate(v.left)
                and separate(v.right)
            )

        return self.root is None or separate(self.root)

    def is_splits_halve(self) -> bool:
        """Box invariant 2, on the x-tree: every inner node splits the points below it in half,
        ceil(n/2) of its n points on the left and the rest on the right."""

        def halves(v: Node2[K] | Leaf2) -> bool:
            if isinstance(v, Leaf2):
                return True
            left, right = len(self.below(v.left)), len(self.below(v.right))
            return left in (right, right + 1) and halves(v.left) and halves(v.right)

        return self.root is None or halves(self.root)

    def is_y_trees_hold_subtrees(self) -> bool:
        """Not in the box: every inner node's tree on y holds exactly the points below the
        node, sorted by y, each with its id, and is itself a valid 1D range tree. This is what
        lets a query read a whole subtree off its tree on y."""

        def holds(v: Node2[K] | Leaf2) -> bool:
            if isinstance(v, Leaf2):
                return True
            ys = v.assoc.keys
            stored = sorted(zip(ys, v.ids), key=lambda p: (p[0], p[1]))
            below = sorted(((p[1], i) for p, i in self.below(v)), key=lambda p: (p[0], p[1]))
            return (
                stored == below
                and all(not ys[j + 1] < ys[j] for j in range(len(ys) - 1))
                and v.assoc.is_valid()
                and holds(v.left)
                and holds(v.right)
            )

        return self.root is None or holds(self.root)

    def check_valid(self) -> str | None:
        """The first piece the tree breaks, or `None`: the box's two invariants on the x-tree,
        then the trees on y."""
        pieces = [
            (self.is_keys_separate, "invariant 1 (keys_separate)"),
            (self.is_splits_halve, "invariant 2 (splits_halve)"),
            (self.is_y_trees_hold_subtrees, "not in the box (y_trees_hold_subtrees)"),
        ]
        for holds, name in pieces:
            if not holds():
                return name
        return None

    def is_valid(self) -> bool:
        """`is_keys_separate`, `is_splits_halve` and `is_y_trees_hold_subtrees`."""
        return self.check_valid() is None

    def depth(self) -> int:
        """The x-tree's height."""

        def d(v: Node2[K] | Leaf2) -> int:
            return 0 if isinstance(v, Leaf2) else 1 + max(d(v.left), d(v.right))

        return 0 if self.root is None else d(self.root)

    def query(self, lo: tuple[K, K], hi: tuple[K, K]) -> list[int]:
        """The ids of the points with lo <= (x, y) <= hi on both axes, each once, in the
        order the walk reports them (`2DRANGEQUERY`)."""
        out: list[int] = []
        if self.root is None or hi[0] < lo[0] or hi[1] < lo[1]:
            return out
        v = self.root
        while isinstance(v, Node2) and (hi[0] < v.split or v.split < lo[0]):
            v = v.left if hi[0] < v.split else v.right
        if isinstance(v, Leaf2):
            self.report_leaf(v, lo, hi, out)
            return out
        w = v.left
        while isinstance(w, Node2):
            if not w.split < lo[0]:
                self.report_subtree(w.right, lo, hi, out)
                w = w.left
            else:
                w = w.right
        self.report_leaf(w, lo, hi, out)
        w = v.right
        while isinstance(w, Node2):
            if not hi[0] < w.split:
                self.report_subtree(w.left, lo, hi, out)
                w = w.right
            else:
                w = w.left
        self.report_leaf(w, lo, hi, out)
        return out

    def report_subtree(
        self, v: Node2[K] | Leaf2, lo: tuple[K, K], hi: tuple[K, K], out: list[int]
    ) -> None:
        """A subtree whose x-range lies inside the query: search its associated tree on y."""
        if isinstance(v, Leaf2):
            self.report_leaf(v, lo, hi, out)
        else:
            out.extend(v.ids[p] for p in v.assoc.query_positions(lo[1], hi[1]))

    def report_leaf(self, v: Leaf2, lo: tuple[K, K], hi: tuple[K, K], out: list[int]) -> None:
        (x, y), i = self.points[v.start]
        if not (x < lo[0] or hi[0] < x or y < lo[1] or hi[1] < y):
            out.append(i)


def reject_nan(keys: Sequence[Any]) -> None:
    """A NaN is not equal to itself and has no place in a total order: it would silently corrupt
    the sorted keys, so it is refused."""
    if any(k != k for k in keys):
        raise ValueError("range-tree keys need a total order, and NaN has none")


def merge_by_y(left: list[tuple[K, int]], right: list[tuple[K, int]]) -> list[tuple[K, int]]:
    """Two y-sorted lists as one, the left's first on equal y."""
    out = []
    i = j = 0
    while i < len(left) and j < len(right):
        if right[j][0] < left[i][0]:
            out.append(right[j])
            j += 1
        else:
            out.append(left[i])
            i += 1
    return out + left[i:] + right[j:]
