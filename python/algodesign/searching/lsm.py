# SPDX-License-Identifier: Apache-2.0
"""Log-structured merge tree (LSM-tree): a key/value store that never updates in place.

Writes go to a small in-memory buffer, the *memtable*: a write costs one dict insert, with no seek
and nothing already stored read, and repeated writes of a key coalesce. When the memtable fills it
is sorted and *flushed*: filed away whole as a new sealed run in level 0, in front of the runs
already there, which it never edits. Level 0 gathers such runs, and they may overlap; the flush
that brings it to `level0_runs` of them merges them all into level 1, as LevelDB and RocksDB
compact level 0 when it *reaches* its trigger (four in both). Every deeper level `i`
is one sorted run and may hold `capacity * ratio ** i` entries; a level over its budget is merged
into the next one down. That repeated merging is where write amplification comes from.

A deletion is a write too: it records a *tombstone*. A lookup checks the memtable, then every run
from newest to oldest, and stops at the first that mentions the key, so newer entries shadow older
ones; each run costs one binary search, `O(log r)` for a run of `r` entries. A flush files its
tombstones as they are; a merge with nothing older beneath it drops them, since nothing is left
for them to shadow.

Left out, because none changes the asymptotics: Bloom filters, a write-ahead log, background
compaction, sparse block indexes, and deeper levels cut into files by key range.

A *run* here is what the chapter's box calls a batch and its prose a file on disk, an SSTable.

Sources: O'Neil, Cheng, Gawlick & O'Neil, *The Log-Structured Merge-Tree*; Luo & Carey,
*LSM-based storage techniques: a survey* (VLDB J 29(1), 2020).

The Rust differs here: its memtable is a `BTreeMap`, kept sorted as it is written.

The Lean statements behind this module, in `lean/AlgoDesign/Searching/LSM/` (specification:
`LSM/Spec.lean`): `lookup_write_self`, `lookup_write_other`, `runsSorted_write`,
`preservesGet_compactAt`.
"""

from __future__ import annotations

import bisect
from collections.abc import Iterator
from itertools import pairwise
from typing import Any, NamedTuple

from ._ordering import SupportsLT

# --- Runs ----------------------------------------------------------------------------------
#
# A run is one immutable, key-sorted tuple of entries. A `None` value marks a tombstone (a recorded
# deletion), which is different from the key being absent from the run; `run_lookup` reports that
# difference as `(found, value)`.

type Run[K, V] = tuple[tuple[K, V | None], ...]


def run_sorted[K: SupportsLT](run: Run[K, Any]) -> bool:
    """Keys strictly increasing, so no key appears twice in one run."""
    return all(a[0] < b[0] for a, b in pairwise(run))


def run_lookup[K: SupportsLT, V](run: Run[K, V], key: K) -> tuple[bool, V | None]:
    """`(False, None)` if this run says nothing about `key`, `(True, None)` for a tombstone,
    `(True, v)` for a live value.

    A binary search, because a run is sorted: `O(log r)` for a run of `r` entries."""
    i = bisect.bisect_left(run, key, key=lambda entry: entry[0])
    if i < len(run) and run[i][0] == key:
        return True, run[i][1]
    return False, None


# --- The LSM-tree itself --------------------------------------------------------------------
#
# The levels are a tuple, level 0 first, and each level is a tuple of runs, **newest first**:
# level 0 holds sealed flushes, every deeper level at most one run. A run is never changed once
# written, only replaced; the memtable is a plain dict edited in place.

type Level[K, V] = tuple[Run[K, V], ...]


DEFAULT_MEMTABLE_CAPACITY = 1024
"""How many entries the memtable buffers before it is flushed down into the levels."""

DEFAULT_LEVEL_RATIO = 10
"""How much bigger each level may be than the one above it. Ten is the figure the chapter uses."""

DEFAULT_LEVEL0_RUNS = 4
"""How many sealed flushes level 0 gathers before they are merged into level 1: the fourth flush
merges all four. LevelDB's `kL0_CompactionTrigger` and RocksDB's
`level0_file_num_compaction_trigger` are four as well, and they too compact when level 0 reaches
it."""


class Shape(NamedTuple):
    """The three numbers that decide the layering, chosen when a store is made. The Lean
    `Shape`."""

    capacity: int
    """How many entries the memtable buffers before it is flushed."""
    ratio: int
    """How much bigger each level may be than the one above it."""
    level0_runs: int
    """How many sealed flushes level 0 gathers before they are merged down."""


def budget(level: int, shape: Shape) -> int:
    """How many entries level `level` (1 or deeper) may hold before it is pushed into the next one
    down. Level 0 is counted in runs, not entries: see `DEFAULT_LEVEL0_RUNS`."""
    return int(shape.capacity * shape.ratio**level)


def runs_of[K, V](levels: tuple[Level[K, V], ...]) -> tuple[Run[K, V], ...]:
    """Every run in the store, newest first: level 0's sealed flushes, then each deeper level."""
    return tuple(run for level in levels for run in level)


def is_runs_sorted[K: SupportsLT](levels: tuple[Level[K, Any], ...]) -> bool:
    """Every batch written to disk is sorted: each run's keys strictly increase. The memtable is a
    dict, sorted when it is flushed."""
    return all(run_sorted(run) for run in runs_of(levels))


def is_few_batches[K: SupportsLT](levels: tuple[Level[K, Any], ...], shape: Shape) -> bool:
    """Only a few batches pile up: level 0 at most `level0_runs` runs, every deeper level at most
    one, and no level between them over its budget. The deepest level takes whatever is pushed
    into it."""
    if levels and len(levels[0]) > shape.level0_runs:
        return False
    if any(len(level) > 1 for level in levels[1:]):
        return False
    deepest = len(levels) - 1
    return not any(len(level[0]) > budget(i, shape)
                   for i, level in enumerate(levels) if 0 < i < deepest and level)


def is_runs_non_empty[K: SupportsLT](levels: tuple[Level[K, Any], ...]) -> bool:
    """Not in the box: no run is empty. It keeps the next rule honest: an empty run at the
    bottom would satisfy it while leaving spent tombstones standing above."""
    return all(run for run in runs_of(levels))


def is_oldest_run_clean[K: SupportsLT](levels: tuple[Level[K, Any], ...]) -> bool:
    """Not in the box: no tombstone in the oldest run below level 0 -- a merge with nothing
    older beneath it drops them, having nothing left to shadow. Level 0 is exempt: a flush files
    its tombstones as they are, even into an empty store."""
    deeper = runs_of(levels[1:])
    return not deeper or all(value is not None for _, value in deeper[-1])


def is_shape_usable(shape: Shape) -> bool:
    """Box invariant 2: each level allowed several times the data of the one above. The
    memtable holds at least one entry, each level is at least twice the one above, and level 0
    holds at least one run. `LSM` refuses any other shape."""
    return shape.capacity >= 1 and shape.ratio >= 2 and shape.level0_runs >= 1


def is_memtable_within_capacity(memtable_len: int, shape: Shape) -> bool:
    """Not in the box: the memtable holds at most `capacity` entries. A write that fills it
    flushes it."""
    return memtable_len <= shape.capacity


def check_valid[K: SupportsLT](
    levels: tuple[Level[K, Any], ...], shape: Shape, memtable_len: int
) -> str | None:
    """The first piece the store breaks, in order, or `None`: `"invariant 1 (runs_sorted)"`,
    `"invariant 2 (few_batches)"`, `"invariant 2 (shape_usable)"`,
    `"not in the box (runs_non_empty)"`, `"not in the box (oldest_run_clean)"` or
    `"not in the box (memtable_within_capacity)"`."""
    if not is_runs_sorted(levels):
        return "invariant 1 (runs_sorted)"
    if not is_few_batches(levels, shape):
        return "invariant 2 (few_batches)"
    if not is_shape_usable(shape):
        return "invariant 2 (shape_usable)"
    if not is_runs_non_empty(levels):
        return "not in the box (runs_non_empty)"
    if not is_oldest_run_clean(levels):
        return "not in the box (oldest_run_clean)"
    if not is_memtable_within_capacity(memtable_len, shape):
        return "not in the box (memtable_within_capacity)"
    return None


def is_valid[K: SupportsLT](
    levels: tuple[Level[K, Any], ...], shape: Shape, memtable_len: int
) -> bool:
    """All six pieces: `check_valid` finds none broken."""
    return check_valid(levels, shape, memtable_len) is None


def lookup[K: SupportsLT, V](runs: tuple[Run[K, V], ...], key: K) -> tuple[bool, V | None]:
    """**The newest-first rule**: scan the runs in order and stop at the first that mentions `key`
    at all. This rule is not derived from anything; it *is* what the store means."""
    for run in runs:
        found, value = run_lookup(run, key)
        if found:
            return True, value
    return False, None


def drop_tombstones[K: SupportsLT, V](run: Run[K, V]) -> Run[K, V]:
    """Throw away recorded deletions with nothing older left to shadow; only a merge with nothing
    older beneath it may do this."""
    return tuple((k, v) for k, v in run if v is not None)


def flush_into_levels[K: SupportsLT, V](
    fresh: Run[K, V],
    levels: tuple[Level[K, V], ...],
    shape: Shape,
) -> tuple[Level[K, V], ...]:
    """The chapter's *flush*: file one freshly-sorted run in front of level 0, and then run the
    leveled compaction it triggers, if any.

    Nothing already stored is read or rewritten. The fresh run is sealed as it is, tombstones and
    all, even into a store holding no run: neither LevelDB nor RocksDB drops a deletion on a flush.
    (An empty run is not filed.) When level 0 then holds `shape.level0_runs` runs, they are all
    merged, newest winning on a tied key, into level 1, and from there a level over its budget is
    merged into the one below it. A merge drops tombstones when nothing older lies beneath the
    level it fills -- at the bottom, or above slots that earlier merges emptied. An emptied level
    stays in the list holding nothing, since a level's index decides its budget.
    """
    out: list[Level[K, V]] = list(levels) or [()]
    if fresh:
        out[0] = (fresh, *out[0])
    if len(out[0]) < shape.level0_runs:
        return tuple(out)

    if len(out) == 1:
        out.append(())
    sealed = out[0][0]
    for older in out[0][1:]:  # newest first, so each older run loses a tied key
        sealed = _merge_runs(sealed, older)
    out[0] = ()
    out[1] = _push_down(sealed, out[1], nothing_below=not runs_of(tuple(out[2:])))

    i = 1
    while i < len(out):
        if not out[i] or len(out[i][0]) <= budget(i, shape):
            i += 1
            continue
        if i + 1 == len(out):
            out.append(())
        nothing_below = not runs_of(tuple(out[i + 2 :]))
        out[i + 1] = _push_down(out[i][0], out[i + 1], nothing_below=nothing_below)
        out[i] = ()
        i += 1
    return tuple(out)


def _push_down[K: SupportsLT, V](
    newer: Run[K, V], below: Level[K, V], *, nothing_below: bool
) -> Level[K, V]:
    """Merge `newer` into the one run of the level below, and drop tombstones if nothing older lies
    beneath that level. A merge that cancels out -- values and their own tombstones, nothing else
    -- leaves the level empty rather than holding an empty run (see `is_runs_non_empty`)."""
    merged = _merge_runs(newer, below[0] if below else ())
    if nothing_below:
        merged = drop_tombstones(merged)
    return (merged,) if merged else ()


def _merge_runs[K: SupportsLT, V](newer: Run[K, V], older: Run[K, V]) -> Run[K, V]:
    """Two-pointer merge of two sorted runs into one, `newer`'s entry winning on a tied key. Keeps
    every tombstone."""
    i = j = 0
    out: list[tuple[K, V | None]] = []
    while i < len(newer) and j < len(older):
        nk, nv = newer[i]
        ok, ov = older[j]
        if nk < ok:
            out.append((nk, nv))
            i += 1
        elif ok < nk:
            out.append((ok, ov))
            j += 1
        else:  # same key: newer wins, older's entry is shadowed and dropped
            out.append((nk, nv))
            i += 1
            j += 1
    out.extend(newer[i:])
    out.extend(older[j:])
    return tuple(out)


# --- The public, stateful wrapper -----------------------------------------------------------


class LSM[K: SupportsLT, V]:
    """A log-structured key/value store: a *map* with deletion, unlike the chapter's other
    structures, which are sets. The difference between "never written" and "written, then
    deleted" is the point of an LSM-tree, and a set has no room for it.

    `write` and `delete` are the same operation, with a value or with a tombstone. Nothing is
    ever found and removed, only shadowed by a newer entry.
    """

    __slots__ = ("_memtable", "_levels", "_shape")

    def __init__(
        self,
        capacity: int = DEFAULT_MEMTABLE_CAPACITY,
        ratio: int = DEFAULT_LEVEL_RATIO,
        level0_runs: int = DEFAULT_LEVEL0_RUNS,
    ) -> None:
        """The empty store. `capacity` is the memtable's size: how many entries it buffers before
        it is flushed (the Rust's `memtable_capacity`); `ratio` is how much bigger each level may
        be than the one above; `level0_runs` is how many sealed flushes level 0 gathers before
        they are merged down."""
        if capacity < 1:
            raise ValueError("lsm.LSM: the memtable must hold at least one entry")
        if ratio < 2:
            raise ValueError("lsm.LSM: each level must be at least twice the one above it")
        if level0_runs < 1:
            raise ValueError("lsm.LSM: level 0 must hold at least one run")
        self._memtable: dict[K, V | None] = {}
        self._levels: tuple[Level[K, V], ...] = ()
        self._shape = Shape(capacity, ratio, level0_runs)

    def _flush_if_full(self) -> None:
        if len(self._memtable) >= self._shape.capacity:
            self.flush()

    def write(self, key: K, value: V) -> None:
        """Record `key`'s new value in the memtable, flushing if that fills it. No seek, and
        nothing already stored is read. `None` is the tombstone, so it is refused as a value."""
        if value is None:
            raise ValueError(
                "lsm.LSM.write: None marks a deletion in this store; call delete(key) instead"
            )
        self._memtable[key] = value
        self._flush_if_full()

    def delete(self, key: K) -> None:
        """Write a tombstone for `key`."""
        self._memtable[key] = None
        self._flush_if_full()

    def lookup(self, key: K) -> tuple[bool, V | None]:
        """`(mentioned, value)`: the memtable first, then each level newest to oldest, stopping at
        the first source that mentions `key` at all. Once a merge drops the tombstone,
        "written, then deleted" reads as "never written".
        """
        if key in self._memtable:
            return True, self._memtable[key]
        return lookup(runs_of(self._levels), key)

    def get(self, key: K) -> V | None:
        """The value a client sees: "never written" and "written, then deleted" both give `None`."""
        _, value = self.lookup(key)
        return value

    def __contains__(self, key: K) -> bool:
        return self.get(key) is not None

    def flush(self) -> None:
        """The chapter's flush: file the memtable as a sealed run in level 0, then run whatever
        leveled compaction that triggers (`flush_into_levels`). A no-op on an empty memtable.
        A full memtable flushes itself; calling this files a part-full one now.
        """
        if not self._memtable:
            return
        fresh: Run[K, V] = tuple(sorted(self._memtable.items(), key=lambda kv: kv[0]))
        self._memtable = {}
        self._levels = flush_into_levels(fresh, self._levels, self._shape)

    def compact_fully(self) -> None:
        """Flush, then compact everything into a single run -- all the merging an LSM-tree defers,
        done eagerly, dropping every tombstone."""
        self.flush()
        merged: Run[K, V] = ()
        for run in reversed(runs_of(self._levels)):  # oldest first, each newer run winning
            merged = _merge_runs(run, merged)
        merged = drop_tombstones(merged)
        self._levels = ((merged,),) if merged else ()

    def items(self) -> Iterator[tuple[K, V]]:
        """Live entries in key order, newest write winning and tombstones skipped."""
        live = [(key, value) for key, value in self._newest().items() if value is not None]
        return iter(sorted(live, key=lambda kv: kv[0]))

    def _newest(self) -> dict[K, V | None]:
        """Every key the store has seen, mapped to its newest entry -- a value or a tombstone."""
        merged: dict[K, V | None] = {}
        for run in reversed(runs_of(self._levels)):  # oldest run first, so newer runs overwrite
            merged.update(run)
        merged.update(self._memtable)  # the memtable is newer than every level
        return merged

    def __iter__(self) -> Iterator[K]:
        """The live keys in order."""
        return iter(key for key, _ in self.items())

    def __len__(self) -> int:
        """How many keys are live. `O(n)`, and not cached: a counter would need a lookup on
        every write."""
        return sum(1 for value in self._newest().values() if value is not None)

    def check_valid(self) -> str | None:
        """The module-level `check_valid`, at this store's own shape and memtable."""
        return check_valid(self._levels, self._shape, len(self._memtable))

    def is_valid(self) -> bool:
        """The module-level `is_valid`, at this store's own shape and memtable."""
        return is_valid(self._levels, self._shape, len(self._memtable))

    def levels(self) -> tuple[Level[K, V], ...]:
        """The levels, level 0 first, each a tuple of runs newest first. An LSM-tree's layered
        shape is part of what it shows, so it is exposed; the memtable is not among them."""
        return self._levels

    def memtable_len(self) -> int:
        """How many entries are buffered and not yet flushed."""
        return len(self._memtable)

    def level_count(self) -> int:
        """How many levels, level 0 included; `len(levels())`."""
        return len(self._levels)

    def __repr__(self) -> str:
        return (
            f"{type(self).__name__}(memtable={len(self._memtable)}, "
            f"levels={[[len(r) for r in level] for level in self._levels]!r})"
        )
