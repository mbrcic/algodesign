# SPDX-License-Identifier: Apache-2.0
"""The Search chapter's design project: a bench for finding a new set design with an AI.

The chapter's boxes split a design in two. The top half (goal, promise, cost, assumptions) is the
problem, and stays the reader's; the bottom half (idea, invariants) is what a search, a person's
or an AI's, may change. This module holds the top half fixed for one family, ordered sets of
integer keys, so that candidates can be compared on it:

- `Memory`, the cost model: memory hands over whole blocks of `BLOCK` slots, each one 64-bit
  integer, and a candidate keeps its keys there and nowhere else. `load` counts one fetch, `new` and
  `store` one write. The counts are exact and the same on every machine; no clock is read.
- `Reference` and `check_promise`, the promise: every answer a candidate gives is compared with a
  plain sorted list's. The reader picks the seeds and keeps some of them from whoever writes the
  candidate, so some of the checks are ones the candidate has never seen.
- `measure`, the cost: fetches and writes per operation, and blocks in use at the end.
- `timers`, a workload: timers come and go, and most questions are "is this one set?" and "which
  one fires next after time t?".
- `llrb_baseline` and `btree_baseline`, the chapter's two trees on the same workload. They keep
  the trees as the chapter wrote them and charge one fetch for every node an operation's walk
  from the root touches, and one write for an insert or delete that changes the set. A write's
  repairs are not charged, so a candidate that beats them beats them by at least that much.

A candidate is any class built as `make(memory)` with the four operations of `OrderedSet`.
Between operations it may hold a few block numbers and counters, and nothing else:
`outside_memory` counts what it holds, and `check_promise` and `measure` refuse a candidate that
holds more than `HELD` slots outside its memory. That is a check, not a proof; a candidate can
still hide keys where the check does not look, and judging that is the reader's part.

The promise comes first, in Lean: `lean/AlgoDesign/Searching/Workbench/Spec.lean` states what
every candidate owes (`Contract`, with `NextLargerSpec` for "next larger"), and
`Workbench.lean` proves a plain set meets it (`reference_contract`). `Reference` here is that
set, and `check_promise` tests a candidate against it; the cost and the assumptions are measured
here, not stated there.

Python only: this is a tool for the chapter's project, not a structure the chapter teaches, so it
has no Rust counterpart.
"""

from __future__ import annotations

import bisect
import random
import types
from collections.abc import Callable, Iterable
from dataclasses import dataclass, field
from typing import Literal, Protocol

from .btree import BTree
from .llrb import LLRB

BLOCK = 64
"""Slots in one block. A slot holds one 64-bit integer (a key, a block number, a count) or
`None`; a tuple of such integers takes one slot per item."""

_WORD = 1 << 63


def _slots(item: object) -> int:
    """How many slots `item` takes, or a `ValueError` if no slot can hold it."""
    if item is None:
        return 1
    if isinstance(item, int) and not isinstance(item, bool) and -_WORD <= item < _WORD:
        return 1
    if isinstance(item, tuple) and all(_slots(x) == 1 and x is not None for x in item):
        return len(item)
    raise ValueError(f"a slot holds a 64-bit integer or None, not {item!r:.40}")

HELD = 32
"""How many slots a candidate may hold outside `Memory` between operations."""

Op = tuple[Literal["insert", "delete", "contains", "next_larger"], int]
"""One operation of a workload and its key."""


class Memory:
    """Block memory: numbered blocks of at most `block` slots each.

    `load` hands back a copy, so a change reaches memory only through `store`.
    """

    def __init__(self, block: int = BLOCK) -> None:
        self.block = block
        self._blocks: dict[int, list[object]] = {}
        self._next = 0
        self.fetches = 0
        self.writes = 0

    def new(self, items: Iterable[object] = ()) -> int:
        """A fresh block holding `items`, and its number. One write."""
        ref = self._next
        self._next += 1
        self._blocks[ref] = []
        self.store(ref, items)
        return ref

    def load(self, ref: int) -> list[object]:
        """A copy of block `ref`'s slots. One fetch."""
        self.fetches += 1
        return list(self._blocks[ref])

    def store(self, ref: int, items: Iterable[object]) -> None:
        """Replace block `ref`'s slots with `items`. One write."""
        slots = list(items)
        used = sum(_slots(item) for item in slots)
        if used > self.block:
            raise ValueError(f"a block holds {self.block} slots, not {used}")
        if ref not in self._blocks:
            raise KeyError(f"no block {ref}")
        self._blocks[ref] = slots
        self.writes += 1

    def free(self, ref: int) -> None:
        """Give block `ref` back. Free of charge."""
        del self._blocks[ref]

    def in_use(self) -> int:
        """How many blocks are allocated now."""
        return len(self._blocks)

    def charge(self, fetches: int, writes: int = 0) -> None:
        """Count fetches and writes without a `load` or a `store`: for the baselines, which keep
        the chapter's own trees outside `Memory`."""
        self.fetches += fetches
        self.writes += writes


class OrderedSet(Protocol):
    """The promise every candidate keeps: a set of integer keys, with "next larger"."""

    def insert(self, key: int) -> bool:
        """Add `key`; `True` if it was not there."""
        ...

    def delete(self, key: int) -> bool:
        """Take `key` out; `True` if it was there."""
        ...

    def contains(self, key: int) -> bool:
        """Is `key` in the set?"""
        ...

    def next_larger(self, key: int) -> int | None:
        """The smallest key in the set larger than `key`, or `None` if there is none."""
        ...


Make = Callable[[Memory], OrderedSet]
"""How a candidate is built: given the memory it must keep its keys in."""


class Reference:
    """The promise, as plainly as it can be written: a sorted Python list. Not a candidate."""

    def __init__(self) -> None:
        self.keys: list[int] = []

    def insert(self, key: int) -> bool:
        i = bisect.bisect_left(self.keys, key)
        if i < len(self.keys) and self.keys[i] == key:
            return False
        self.keys.insert(i, key)
        return True

    def delete(self, key: int) -> bool:
        i = bisect.bisect_left(self.keys, key)
        if i < len(self.keys) and self.keys[i] == key:
            del self.keys[i]
            return True
        return False

    def contains(self, key: int) -> bool:
        i = bisect.bisect_left(self.keys, key)
        return i < len(self.keys) and self.keys[i] == key

    def next_larger(self, key: int) -> int | None:
        i = bisect.bisect_right(self.keys, key)
        return self.keys[i] if i < len(self.keys) else None


def _run(target: OrderedSet | Reference, op: Op) -> bool | int | None:
    name, key = op
    if name == "insert":
        return target.insert(key)
    if name == "delete":
        return target.delete(key)
    if name == "contains":
        return target.contains(key)
    return target.next_larger(key)


_SKIPPED = (type, types.ModuleType, types.FunctionType, types.BuiltinFunctionType,
            types.MethodType)


def _parts(obj: object) -> list[object]:
    """What `obj` holds: a container's items, an instance's attributes."""
    if isinstance(obj, dict):
        return [*obj.keys(), *obj.values()]
    if isinstance(obj, (list, tuple, set, frozenset)):
        return list(obj)
    if isinstance(obj, (int, float, str, bytes, type(None))):
        return []
    parts = list(vars(obj).values()) if hasattr(obj, "__dict__") else []
    for cls in type(obj).__mro__:
        for name in getattr(cls, "__slots__", ()):
            if hasattr(obj, name):
                parts.append(getattr(obj, name))
    return parts


def outside_memory(candidate: object, memory: Memory) -> int:
    """How many slots the candidate holds outside `memory`: every attribute, and every item of
    every list, dict, set or tuple it reaches, counts one."""
    seen = {id(candidate), id(memory)}
    todo = _parts(candidate)
    count = 0
    while todo and count <= HELD:
        obj = todo.pop()
        if id(obj) in seen or isinstance(obj, _SKIPPED):
            continue
        count += 1
        if not isinstance(obj, (int, float, str, bytes, type(None))):
            seen.add(id(obj))
            todo.extend(_parts(obj))
    return count


@dataclass
class Mismatch:
    """The first operation where a candidate broke the promise."""

    index: int
    op: Op
    expected: bool | int | None
    got: bool | int | None | str


def check_promise(make: Make, ops: list[Op], trusted: bool = False) -> Mismatch | None:
    """Run `ops` on a fresh candidate and on `Reference`; the first answer that differs, or
    `None` if every answer agrees. Unless `trusted`, a candidate that holds more than `HELD`
    slots outside its memory after an operation fails there too. `trusted` is for the bench's own
    baselines, which hold their trees outside memory and charge for them; they are trusted
    whether or not it is passed."""
    trusted = trusted or make in _BASELINES
    memory = Memory()
    candidate = make(memory)
    reference = Reference()
    for index, op in enumerate(ops):
        expected = _run(reference, op)
        got = _run(candidate, op)
        if got != expected:
            return Mismatch(index, op, expected, got)
        if not trusted and outside_memory(candidate, memory) > HELD:
            return Mismatch(index, op, expected, f"holds more than {HELD} slots outside memory")
    return None


@dataclass
class Costs:
    """What a run cost: fetches and writes per operation, by kind, and blocks in use at the end."""

    ops: dict[str, int] = field(default_factory=dict)
    fetches: dict[str, int] = field(default_factory=dict)
    writes: dict[str, int] = field(default_factory=dict)
    blocks: int = 0

    def per_op(self, kind: str | None = None) -> tuple[float, float]:
        """Mean fetches and writes per operation, of one kind or of all."""
        kinds = [kind] if kind is not None else list(self.ops)
        n = sum(self.ops.get(k, 0) for k in kinds)
        if n == 0:
            return 0.0, 0.0
        return (sum(self.fetches.get(k, 0) for k in kinds) / n,
                sum(self.writes.get(k, 0) for k in kinds) / n)


def measure(make: Make, preload: list[int], ops: list[Op], trusted: bool = False) -> Costs:
    """Insert `preload`, then run `ops` and count what each costs. The preload is not counted.
    Answers are not checked here; `check_promise` does that. A `trusted` candidate, one of the
    bench's baselines, reports its own blocks; any other is charged the blocks it has in use."""
    trusted = trusted or make in _BASELINES
    memory = Memory()
    candidate = make(memory)
    for key in preload:
        candidate.insert(key)
    costs = Costs()
    for name, key in ops:
        before_f, before_w = memory.fetches, memory.writes
        _run(candidate, (name, key))
        costs.ops[name] = costs.ops.get(name, 0) + 1
        costs.fetches[name] = costs.fetches.get(name, 0) + memory.fetches - before_f
        costs.writes[name] = costs.writes.get(name, 0) + memory.writes - before_w
    if not trusted and outside_memory(candidate, memory) > HELD:
        raise ValueError(f"the candidate holds more than {HELD} slots outside memory")
    blocks = getattr(candidate, "blocks", None)
    costs.blocks = blocks() if trusted and callable(blocks) else memory.in_use()
    return costs


def timers(seed: int, start: int = 50_000, ops: int = 20_000, reads_per_write: int = 50,
           span: int = 10**9, next_share: float = 0.5) -> tuple[list[int], list[Op]]:
    """A timer workload: `start` timers already set, then `ops` operations.

    For every write there are about `reads_per_write` reads. A write sets a new timer or cancels
    one that is set, as often as each other. A read asks which timer fires next after a time
    (a share `next_share` of the reads) or else whether a time is set (a set one or any time at
    all, half and half). Keys are times in `[0, span)`.
    """
    rng = random.Random(seed)
    preload = rng.sample(range(span), start)
    live = list(preload)
    where = {k: i for i, k in enumerate(live)}
    out: list[Op] = []
    for _ in range(ops):
        if rng.random() < 1 / (1 + reads_per_write):
            if rng.random() < 0.5 or not live:
                key = rng.randrange(span)
                if key not in where:
                    where[key] = len(live)
                    live.append(key)
                out.append(("insert", key))
            else:
                key = live[rng.randrange(len(live))]
                i = where.pop(key)
                last = live.pop()
                if last != key:
                    live[i] = last
                    where[last] = i
                out.append(("delete", key))
        elif rng.random() >= next_share:
            if live and rng.random() < 0.5:
                out.append(("contains", live[rng.randrange(len(live))]))
            else:
                out.append(("contains", rng.randrange(span)))
        else:
            out.append(("next_larger", rng.randrange(span)))
    return preload, out


# --- The chapter's trees, charged by the nodes their walks touch ------------------------------


class _LLRBBaseline:
    """The chapter's `LLRB`, one node to a block."""

    def __init__(self, memory: Memory) -> None:
        self.memory = memory
        self.tree: LLRB[int] = LLRB()
        self.size = 0

    def _walk(self, key: int) -> tuple[int, int | None]:
        """Nodes touched walking down towards `key`, and the next key larger than `key`."""
        h, touched, larger = self.tree.root, 0, None
        while h is not None:
            touched += 1
            if key < h.key:
                larger = h.key
                h = h.left
            elif h.key < key:
                h = h.right
            else:
                h = h.right
        return touched, larger

    def _path(self, key: int) -> None:
        h, touched = self.tree.root, 0
        while h is not None:
            touched += 1
            if key < h.key:
                h = h.left
            elif h.key < key:
                h = h.right
            else:
                break
        self.memory.charge(touched)

    def insert(self, key: int) -> bool:
        self._path(key)
        added = self.tree.insert(key)
        self.size += added
        self.memory.charge(0, added)
        return added

    def delete(self, key: int) -> bool:
        self._path(key)
        removed = self.tree.delete(key)
        self.size -= removed
        self.memory.charge(0, removed)
        return removed

    def contains(self, key: int) -> bool:
        self._path(key)
        return self.tree.search(key)

    def next_larger(self, key: int) -> int | None:
        touched, larger = self._walk(key)
        self.memory.charge(touched)
        return larger

    def blocks(self) -> int:
        return self.size


def llrb_baseline(memory: Memory) -> OrderedSet:
    """The chapter's LLRB as a candidate: one node per block. The bench trusts it: it holds its
    tree outside memory and charges a fetch per node touched."""
    return _LLRBBaseline(memory)


class _BTreeBaseline:
    """The chapter's `BTree`, one node to a block."""

    def __init__(self, memory: Memory, t: int) -> None:
        self.memory = memory
        self.tree: BTree[int] = BTree(t)

    def _path(self, key: int) -> None:
        node = self.tree.root
        touched = 0
        while True:
            touched += 1
            i = bisect.bisect_left(node.keys, key)
            if (i < len(node.keys) and node.keys[i] == key) or node.leaf:
                break
            node = node.children[i]
        self.memory.charge(touched)

    def insert(self, key: int) -> bool:
        self._path(key)
        added = self.tree.insert(key)
        self.memory.charge(0, added)
        return added

    def delete(self, key: int) -> bool:
        self._path(key)
        removed = self.tree.delete(key)
        self.memory.charge(0, removed)
        return removed

    def contains(self, key: int) -> bool:
        self._path(key)
        return self.tree.search(key)

    def next_larger(self, key: int) -> int | None:
        node = self.tree.root
        touched, larger = 0, None
        while True:
            touched += 1
            i = bisect.bisect_right(node.keys, key)
            if i < len(node.keys):
                larger = node.keys[i]
            if node.leaf:
                break
            node = node.children[i]
        self.memory.charge(touched)
        return larger

    def blocks(self) -> int:
        count, todo = 0, [self.tree.root]
        while todo:
            node = todo.pop()
            count += 1
            todo.extend(node.children)
        return count


def btree_t(block: int = BLOCK) -> int:
    """The largest minimum degree whose full node fits a block: `2t - 1` keys and `2t`
    children, `4t - 1` slots."""
    return (block + 1) // 4


def btree_baseline(memory: Memory) -> OrderedSet:
    """The chapter's B-tree as a candidate, its nodes as wide as a block allows (`btree_t`).
    The bench trusts it, as it does `llrb_baseline`."""
    return _BTreeBaseline(memory, btree_t(memory.block))


_BASELINES: tuple[Make, ...] = (llrb_baseline, btree_baseline)
"""The bench's own candidates, trusted to report their memory: `check_promise` and `measure`
compare a `make` against these, so a candidate cannot declare itself one."""
