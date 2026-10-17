# SPDX-License-Identifier: Apache-2.0
"""Tests for `algodesign.searching.lsm`.

Property-based tests (via `hypothesis`) check the same correctness statements the Lean file
states or proves (`lookup_write_self`, `lookup_write_other`, `runsSorted_write`, and that `flush`
changes nothing a client can `get`, which Lean proves of each merge step and of the policy's flush
and cascade, `Store.preservesGet_flush`) empirically, against a reference `dict`-with-tombstone model. Hand-written cases cover
the structural edge cases (empty store, single write, a run that shrinks to nothing) that random
generation covers only probabilistically.
"""

from __future__ import annotations

import math
from collections.abc import Iterator
from copy import deepcopy
from typing import Any

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st
from sorting_probe import sorts_during

from algodesign.searching.lsm import LSM

_KEYS = st.integers(min_value=-50, max_value=50)
_VALUES = st.integers(min_value=-1000, max_value=1000)


def _ops(
    keys: st.SearchStrategy[int], min_size: int = 0, max_size: int = 80
) -> st.SearchStrategy[list[tuple[str, int | None, int | None]]]:
    """Writes, deletes and compactions over `keys`, between `min_size` and `max_size` of them."""
    return st.lists(
        st.one_of(
            st.tuples(st.just("write"), keys, _VALUES),
            st.tuples(st.just("delete"), keys, st.none()),
            st.tuples(st.just("flush"), st.none(), st.none()),
        ),
        min_size=min_size,
        max_size=max_size,
    )


_OPS = _ops(_KEYS)

# The shapes the dict-model properties run at. At the defaults, 80 operations never fill a level
# past level 1, so level 1 is always the deepest and every tombstone that reaches it is collected:
# the rule "only the deepest level may drop tombstones" is never put to the test. At (capacity 2,
# ratio 2, level 0 merged at three runs) a few dozen writes build three or four levels, and a run carrying
# tombstones is routinely pushed into a level that has another beneath it. That takes sequences
# long enough to build the levels, over few enough keys that a deletion usually hits a key written
# and pushed down before, and not so few that every merged run fits in level 1: sixteen keys and
# 40 to 120 operations. (With four keys no run outgrows level 1, and Hypothesis' usual short
# lists rarely build the levels.)
_DEFAULT_SHAPE: tuple[int, int, int] | None = None
_SMALL_SHAPE = (2, 2, 3)
_SHAPES = pytest.mark.parametrize(
    ("shape", "ops_strategy"),
    [
        (_DEFAULT_SHAPE, _OPS),
        (_SMALL_SHAPE, _ops(st.integers(min_value=0, max_value=15), min_size=40, max_size=120)),
    ],
    ids=["default", "small"],
)


def _new_store(shape: tuple[int, int, int] | None) -> LSM[int, int]:
    """An empty store at `shape` -- `(capacity, ratio, level0_runs)` -- or at the defaults."""
    if shape is None:
        return LSM()
    capacity, ratio, level0_runs = shape
    return LSM(capacity=capacity, ratio=ratio, level0_runs=level0_runs)


def _apply(
    ops: list[tuple[str, int | None, int | None]],
    shape: tuple[int, int, int] | None = _DEFAULT_SHAPE,
) -> tuple[LSM[int, int], dict[int, int]]:
    """Replay `ops` against both the real `LSM` and a plain `dict` (tombstones as key absence —
    a `dict` alone already has "never written" and "not present" collapsed to one thing, exactly
    the client-facing view `LSM.get`/`__contains__` expose)."""
    store = _new_store(shape)
    reference: dict[int, int] = {}
    for op, key, value in ops:
        if op == "write":
            assert key is not None and value is not None
            store.write(key, value)
            reference[key] = value
        elif op == "delete":
            assert key is not None
            store.delete(key)
            reference.pop(key, None)
        else:
            store.flush()
    return store, reference


# --- Empty / single-write edge cases --------------------------------------------------------


def test_empty_store() -> None:
    store: LSM[int, int] = LSM()
    assert store.get(0) is None
    assert 0 not in store
    assert store.level_count() == 0
    assert store.memtable_len() == 0
    assert store.is_valid()
    store.flush()  # no-op, must not raise
    assert store.level_count() == 0


def test_single_write_stays_in_the_memtable() -> None:
    store: LSM[int, int] = LSM()
    store.write(1, 100)
    assert store.get(1) == 100
    assert 1 in store
    assert store.get(2) is None
    assert 2 not in store
    # A write does not touch the levels: that is the point of buffering it.
    assert store.memtable_len() == 1
    assert store.level_count() == 0


def test_write_then_delete_leaves_a_tombstone_not_absence() -> None:
    store: LSM[int, int] = LSM()
    store.write(1, 100)
    store.delete(1)
    assert store.get(1) is None
    assert 1 not in store
    # Still a recorded deletion rather than a key never mentioned — until a merge reaches the
    # bottom, which is where the distinction is allowed to be collected.
    assert store.lookup(1) == (True, None)


def test_writing_none_is_refused_rather_than_silently_deleting() -> None:
    # None is this store's tombstone, so a write of None would be a delete in disguise.
    store: LSM[int, int | None] = LSM()
    store.write(1, 10)
    try:
        store.write(1, None)
    except ValueError:
        pass
    else:
        raise AssertionError("write(k, None) must be refused")
    assert store.get(1) == 10


def test_a_tombstone_with_nothing_beneath_it_is_collected() -> None:
    store: LSM[int, int] = LSM()
    store.write(1, 100)
    store.delete(1)
    store.compact_fully()
    assert store.lookup(1) == (False, None)
    assert store.is_valid()


def test_rewrite_coalesces_in_the_memtable() -> None:
    store: LSM[int, int] = LSM()
    store.write(1, 100)
    store.write(1, 200)
    assert store.get(1) == 200
    # One entry, not two: the second write overwrote the first before either reached a level.
    assert store.memtable_len() == 1


def test_flush_on_an_empty_memtable_is_a_no_op() -> None:
    store: LSM[int, int] = LSM()
    store.flush()
    assert store.level_count() == 0
    store.write(1, 1)
    store.flush()
    assert store.level_count() == 1
    assert store.memtable_len() == 0
    store.flush()
    assert store.level_count() == 1
    assert store.get(1) == 1


def test_a_full_memtable_flushes_itself() -> None:
    store: LSM[int, int] = LSM(capacity=8, ratio=10)
    for k in range(8):
        store.write(k, k * 10)
    assert store.memtable_len() == 0
    assert store.level_count() == 1
    assert len(store.levels()[0]) == 1, "one flush, one sealed run in level 0"
    assert len(store.levels()[0][0]) == 8
    for k in range(8):
        assert store.get(k) == k * 10
    assert store.is_valid()


def test_a_level_over_budget_is_pushed_into_the_next() -> None:
    # Capacity 4, ratio 2, level 0 merged at three runs: level 1 may hold 8 entries, level 2 16.
    store: LSM[int, int] = LSM(capacity=4, ratio=2, level0_runs=3)
    for k in range(40):
        store.write(k, k)
    store.flush()
    assert store.level_count() >= 2, "40 keys at this shape must reach a second level"
    assert store.is_valid()
    for k in range(40):
        assert store.get(k) == k


def test_a_tombstone_pushed_into_a_level_with_another_below_it_is_kept() -> None:
    """Only the deepest level may drop tombstones. Here a deletion reaches level 1 while the value
    it deletes still sits in level 2, and it is the tombstone alone that keeps `get` from finding
    that value. Collected one level too early, the deletion would be undone."""
    store: LSM[int, int] = LSM(capacity=2, ratio=2, level0_runs=3)
    for k in range(6):
        store.write(k, 10 * k)  # three flushes: level 0 fills, and the cascade ends in level 2
    for v in (11, 12, 13):
        store.delete(0)
        store.write(1, v)  # three more flushes, merged into a level 1 of two entries
    level0, level1, level2 = store.levels()
    assert level0 == ()
    assert level1 == (((0, None), (1, 13)),), "the tombstone for 0 is in level 1"
    assert level2[0][0] == (0, 0), "and the value it shadows is in level 2, beneath it"
    assert store.get(0) is None
    assert 0 not in store
    assert store.lookup(0) == (True, None)
    assert store.get(1) == 13
    assert store.is_valid()


def test_compact_resolves_a_duplicate_key_in_favour_of_the_newer_entry() -> None:
    store: LSM[int, int] = LSM(capacity=2, ratio=2)
    store.write(1, 100)
    store.write(9, 9)  # fills the memtable, flushing both to level 0
    store.write(1, 200)
    store.compact_fully()
    assert store.level_count() == 1
    assert store.get(1) == 200


def test_compact_fully_on_many_writes_matches_direct_lookup() -> None:
    store: LSM[int, int] = LSM()
    for k, v in [(3, 30), (1, 10), (4, 40), (1, 11), (2, 20)]:
        store.write(k, v)
    before = {k: store.get(k) for k in range(6)}
    store.compact_fully()
    assert store.level_count() == 1
    after = {k: store.get(k) for k in range(6)}
    assert before == after
    assert before == {0: None, 1: 11, 2: 20, 3: 30, 4: 40, 5: None}


# --- Property-based tests ------------------------------------------------------------------------


@given(_KEYS, _VALUES)
def test_write_then_get_returns_the_value_written(key: int, value: int) -> None:
    """`lookup_write_self`: writing `(key, value)` makes it the immediate answer."""
    store: LSM[int, int] = LSM()
    store.write(key, value)
    assert store.get(key) == value


@given(_KEYS, _VALUES, _KEYS)
def test_write_does_not_change_lookup_of_a_different_key(key: int, value: int, other: int) -> None:
    """`lookup_write_other`: writing `key` never changes what an *unrelated* key looks up to."""
    store: LSM[int, int] = LSM()
    before = store.get(other)
    store.write(key, value)
    if key != other:
        assert store.get(other) == before


@given(_OPS)
def test_store_stays_valid_after_any_sequence_of_writes_deletes_compactions(
    ops: list[tuple[str, int | None, int | None]],
) -> None:
    """`runsSorted_write` (empirically, and across `flush` too, which Lean doesn't yet prove
    validity-preserving either): every run stays individually sorted no matter what sequence of
    operations produced it."""
    store, _ = _apply(ops)
    assert store.is_valid()


@_SHAPES
@given(data=st.data())
@settings(deadline=None)  # up to 120 operations and a deepcopy: time is not the property
def test_get_matches_dict_with_tombstone_reference(
    shape: tuple[int, int, int] | None,
    ops_strategy: st.SearchStrategy[list[tuple[str, int | None, int | None]]],
    data: st.DataObject,
) -> None:
    """The behavioral claim the Lean file's `lookup` is *stated* (not derived) to have: replaying
    the same writes/deletes/compactions against a plain `dict` (tombstones as key absence) agrees
    with the real store on every key, at every point along the way. At both shapes: the small one
    is where a tombstone kept above a deeper level is what hides the value below it."""
    ops = data.draw(ops_strategy)
    store, reference = _apply(ops, shape)
    for k in range(-50, 51):
        assert store.get(k) == reference.get(k)
        assert (k in store) == (k in reference)


@_SHAPES
@given(data=st.data())
@settings(deadline=None)  # up to 120 operations and a deepcopy: time is not the property
def test_compact_preserves_every_answer_a_client_can_get(
    shape: tuple[int, int, int] | None,
    ops_strategy: st.SearchStrategy[list[tuple[str, int | None, int | None]]],
    data: st.DataObject,
) -> None:
    """**`PreservesGet`**: a compaction may not change what a client can `get`. Lean proves it of
    each merge step (`preservesGet_compactAt`) and of this policy's flush and cascade
    (`Store.preservesGet_flush`). Checked across a `flush`, with the compaction it triggers,
    inserted after an arbitrary prefix of writes and deletes, against every key that could
    matter — every key mentioned in
    `ops`, plus a couple that never appear, to cover "absent either way".

    `lookup`'s three-way answer is preserved only *up to tombstone collection*: a merge reaching
    the deepest level drops a tombstone with nothing older left to shadow, so "written, then
    deleted" may become "never written". That direction and no other — the reverse would mean a
    deletion had been forgotten.
    """
    ops = data.draw(ops_strategy)
    store, _ = _apply(ops, shape)
    after = deepcopy(store)
    after.flush()

    keys = {key for _, key, _ in ops if key is not None} | {-999, 999}
    for k in keys:
        assert store.get(k) == after.get(k)
        before_answer, after_answer = store.lookup(k), after.lookup(k)
        if before_answer != after_answer:
            assert before_answer == (True, None), (k, before_answer, after_answer)
            assert after_answer == (False, None), (k, before_answer, after_answer)


@given(_OPS)
def test_the_levels_stay_within_their_budgets(
    ops: list[tuple[str, int | None, int | None]],
) -> None:
    """A sanity check on the mechanics, not a correctness claim from Lean: however the operations
    interleave, level 0 holds at most `level0_runs` runs, every deeper level but the last stays
    inside `capacity * ratio ** i`, and the oldest run below level 0 holds no tombstone. A small
    shape, so the
    cascade actually fires."""
    store: LSM[int, int] = LSM(capacity=2, ratio=2, level0_runs=3)
    for op, key, value in ops:
        if op == "write":
            assert key is not None and value is not None
            store.write(key, value)
        elif op == "delete":
            assert key is not None
            store.delete(key)
        else:
            store.flush()
        assert store.is_valid()


# --- The chapter's trace ---------------------------------------------------------------------
#
# The Search chapter walks a store with a three-entry list through six events and two trips.
# These two tests are that walk, run: the table after each trip, the four questions, and the
# compaction paragraph after them. If the library ever stops being able to tell this story, the
# chapter is describing a different structure from the one it ships.


def _two_trips() -> LSM[str, str]:
    store: LSM[str, str] = LSM(capacity=3)
    store.write("charger", "desk drawer")
    store.write("passport", "top shelf")
    store.write("scissors", "kitchen drawer")  # full: one trip, Page 1
    store.write("charger", "bedside table")
    store.delete("scissors")
    store.write("umbrella", "hallway hook")  # full: one trip, Page 2
    return store


def test_the_chapters_two_pages_are_two_sealed_runs() -> None:
    store = _two_trips()
    assert store.memtable_len() == 0
    (level0,) = store.levels()
    page_2, page_1 = level0  # newest first
    assert page_1 == (
        ("charger", "desk drawer"),
        ("passport", "top shelf"),
        ("scissors", "kitchen drawer"),
    ), "Page 1 is sealed: nobody went back to correct the charger"
    assert page_2 == (
        ("charger", "bedside table"),
        ("scissors", None),
        ("umbrella", "hallway hook"),
    ), "Page 2 records that the scissors are gone rather than erasing them"

    # The four questions, and the answers the chapter's table gives.
    assert store.lookup("charger") == (True, "bedside table")  # Page 2, Page 1 never consulted
    assert store.lookup("scissors") == (True, None)  # Page 2's tombstone stops the search
    assert store.lookup("passport") == (True, "top shelf")  # found only on Page 1
    assert store.lookup("bicycle pump") == (False, None)  # every page read, nothing anywhere
    assert store.is_valid()


def test_compaction_is_where_page_1s_stale_claim_dies() -> None:
    store = _two_trips()
    store.compact_fully()
    (level0,) = store.levels()
    (merged,) = level0
    # The desk drawer is not copied forward, and neither is the spent tombstone.
    assert merged == (
        ("charger", "bedside table"),
        ("passport", "top shelf"),
        ("umbrella", "hallway hook"),
    )
    assert store.lookup("scissors") == (False, None)
    assert store.get("scissors") is None


class _CountedKey:
    """An integer key that counts every comparison made on it, `<`, `==` and `>` alike, into one
    shared tally. A binary search compares with `<`; a linear scan is usually written with `==`,
    so counting only one of them would let the other through."""

    comparisons = 0

    __slots__ = ("value",)

    def __init__(self, value: int) -> None:
        self.value = value

    def __lt__(self, other: _CountedKey) -> bool:
        _CountedKey.comparisons += 1
        return bool(self.value < other.value)

    def __gt__(self, other: _CountedKey) -> bool:
        _CountedKey.comparisons += 1
        return bool(self.value > other.value)

    def __eq__(self, other: object) -> bool:
        _CountedKey.comparisons += 1
        return isinstance(other, _CountedKey) and self.value == other.value

    def __hash__(self) -> int:
        _CountedKey.comparisons += 1  # a hash is a read of the key too: `dict(run)` hashes all
        return hash(self.value)


class _CountedRun(tuple[tuple[_CountedKey, Any], ...]):
    """A run that counts the entries read out of it: one per index, one per entry iterated. A
    binary search reads about `log r` of them; copying the run -- into a dict, or into a list of
    its keys to bisect -- reads all `r`, on every call, even when the comparisons stay few."""

    reads = 0

    def __getitem__(self, index: Any) -> Any:
        _CountedRun.reads += 1
        return super().__getitem__(index)

    def __iter__(self) -> Iterator[tuple[_CountedKey, Any]]:
        for entry in super().__iter__():
            _CountedRun.reads += 1
            yield entry


def test_run_lookup_makes_logarithmic_comparisons() -> None:
    """A sorted run is read by binary search: at most `ceil(log2(r + 1)) + 1` key comparisons and
    `ceil(log2(r + 1)) + 3` entry reads for a run of `r` entries, hit or miss. A linear scan gives
    every answer right and costs up to `r` comparisons; copying the run per call (into a dict, or
    its keys into a list to bisect) keeps the comparisons down and still reads all `r` entries.
    Both are the read cost this structure exists to keep low. Probed at a run of 1024 entries, at every even key (a hit) and every odd one."""
    from algodesign.searching.lsm import run_lookup

    r = 1024
    run = _CountedRun((_CountedKey(2 * k), k) for k in range(r))
    bound = math.ceil(math.log2(r + 1)) + 1
    worst = worst_reads = 0
    for probe in range(-1, 2 * r + 1):
        key = _CountedKey(probe)
        _CountedKey.comparisons = _CountedRun.reads = 0
        found, value = run_lookup(run, key)
        assert (found, value) == ((True, probe // 2) if probe % 2 == 0 and 0 <= probe < 2 * r
                                  else (False, None)), probe
        worst = max(worst, _CountedKey.comparisons)
        worst_reads = max(worst_reads, _CountedRun.reads)
    assert worst <= bound, (worst, bound)
    assert worst_reads <= bound + 2, (worst_reads, bound + 2)


def test_a_store_lookup_reads_each_run_by_binary_search() -> None:
    """The same bound through the public door: `get` on a store of several levels and runs makes
    at most one binary search's comparisons and reads per run, plus the memtable's one hash probe.
    `lookup` bypassing `run_lookup` -- a `dict(run)` per run, say -- gives every answer and reads
    every entry of every run it passes."""
    store: LSM[_CountedKey, int] = LSM(capacity=4, ratio=2, level0_runs=3)
    for k in range(300):
        store.write(_CountedKey(k), k)
    store._levels = tuple(
        tuple(_CountedRun(run) for run in level) for level in store.levels()
    )
    runs = [run for level in store.levels() for run in level]
    assert len(runs) >= 3 and max(len(run) for run in runs) >= 128
    per_run = sum(math.ceil(math.log2(len(run) + 1)) + 1 for run in runs)
    for probe in [-1, 0, 7, 150, 299, 300]:
        _CountedKey.comparisons = _CountedRun.reads = 0
        assert store.get(_CountedKey(probe)) == (probe if 0 <= probe < 300 else None)
        assert _CountedKey.comparisons <= per_run + 3, (probe, _CountedKey.comparisons, per_run)
        assert _CountedRun.reads <= per_run + 2 * len(runs), (probe, _CountedRun.reads)


def test_len_does_not_sort() -> None:
    """`__len__` counts the live keys of the newest-wins fold and needs no order, so it sorts
    nothing -- no `sorted`, no `list.sort`, no heap, no `insort`, however reached; `items`, which must hand the keys
    back in order, is the one that sorts. A `len` built
    on `items` is `O(n log n)` for a count."""
    store: LSM[int, int] = LSM(capacity=4, ratio=2, level0_runs=3)
    for k in range(50):
        store.write(k, k)
    for k in range(0, 50, 3):
        store.delete(k)
    with sorts_during() as sorts:
        assert len(store) == 50 - len(range(0, 50, 3))
    assert sorts == []


def test_a_merge_that_cancels_out_leaves_its_level_empty() -> None:
    """Mirrors `a_merge_that_cancels_out_leaves_its_level_empty`. Write 1, then delete it, at one
    entry per flush and level 0 merged at two runs: the second flush merges the value and its
    tombstone into level 1, and the merge cancels out. The level is left *empty* -- a slot, not a
    run with nothing in it. The chapter's pages hold entries; an empty run, kept, became the
    "oldest run" and made "no tombstone in the oldest run" true of nothing. `delete(2)` is then
    filed in level 0 as it is, though nothing lies beneath it (a flush drops no tombstone), and
    the merge that carries it into level 1, with nothing below, drops it."""
    store: LSM[int, int] = LSM(capacity=1, ratio=2, level0_runs=2)
    store.write(1, 1)
    store.delete(1)
    assert store.levels() == ((), ())
    assert store.is_valid()
    store.delete(2)
    assert store.levels() == ((((2, None),),), ())
    assert store.lookup(2) == (True, None)
    assert store.get(1) is None and len(store) == 0
    assert store.is_valid()
    store.write(3, 3)
    assert store.levels() == ((), (((3, 3),),))
    assert store.lookup(2) == (False, None)
    store.write(4, 4)
    assert store.get(3) == 3 and store.is_valid()


def test_a_flush_into_an_empty_store_keeps_its_tombstones() -> None:
    """Mirrors `a_flush_into_an_empty_store_keeps_its_tombstones`. Neither LevelDB nor RocksDB
    drops a deletion on a flush, even with nothing older for it to shadow, and neither does this
    store: the tombstone waits in level 0, where `valid` allows it, for a merge with nothing
    below."""
    store: LSM[int, int] = LSM()
    store.delete(1)
    store.write(2, 2)
    store.flush()
    assert store.levels() == ((((1, None), (2, 2)),),)
    assert store.lookup(1) == (True, None)
    assert store.is_valid()


def test_level_0_merges_when_it_reaches_its_run_count() -> None:
    """Mirrors `level_0_merges_when_it_reaches_its_run_count`. The flush that brings level 0 to
    `level0_runs` runs merges them down, as LevelDB and RocksDB compact when level 0 *reaches*
    their trigger of four: three flushes wait side by side, and the fourth merges all four."""
    store: LSM[int, int] = LSM(capacity=1)
    for k in range(1, 4):
        store.write(k, k)
    assert store.level_count() == 1 and len(store.levels()[0]) == 3
    store.write(4, 4)
    assert store.levels() == ((), (((1, 1), (2, 2), (3, 3), (4, 4)),))
    assert store.is_valid()


def test_a_tombstone_above_an_emptied_level_is_dropped() -> None:
    """Mirrors `a_tombstone_above_an_emptied_level_is_dropped`. A tombstone is dropped when
    nothing older lies beneath it, which is not the same as its reaching the last level slot: a
    slot emptied by a merge that cancelled out holds nothing. Four writes reach level 2, four
    deletions cancel them there and empty it, and then a write of 5 and its deletion merge into
    level 1 above the empty slot. The tombstone must go, as it would at the bottom, rather than
    stand as the oldest thing in the store with nothing to shadow."""
    store: LSM[int, int] = LSM(capacity=1, ratio=2, level0_runs=2)
    for k in range(1, 5):
        store.write(k, k)
    assert store.level_count() == 3 and len(store.levels()[2][0]) == 4
    for k in range(1, 5):
        store.delete(k)
    assert all(level == () for level in store.levels())
    store.write(5, 5)
    store.delete(5)
    assert all(level == () for level in store.levels()), store.levels()
    assert store.lookup(5) == (False, None)
    assert store.is_valid()


def test_valid_rejects_an_empty_run() -> None:
    """`valid`'s first conjunct: every run holds an entry. An empty run at the bottom would make
    "no tombstone in the oldest run" true of nothing."""
    from algodesign.searching.lsm import Shape, is_valid

    assert is_valid(((), (((1, 1),),)), Shape(1, 2, 1))
    assert not is_valid(((), ((),)), Shape(1, 2, 1))
    assert not is_valid((((),),), Shape(1, 2, 1))


# --- `valid`, one conjunct at a time ------------------------------------------------------------
#
# Every other `is_valid` call in this file is on a store `write`, `delete` and `flush` built, and
# those are valid, so `valid` replaced by `lambda *_: True` would pass them. Each store below is
# the valid `_BASE` with one edit, which breaks exactly one of `valid`'s conjuncts, and must be
# rejected; the edits that stop just short of a conjunct's line must still be accepted. At
# `capacity=1, ratio=2` level 1 may hold 2 entries and level 2 may hold 4.

# Level 0: one sealed flush. Level 1: two entries, one of them a tombstone, which is fine above
# older data. Level 2, the deepest: two live entries.
_BASE: tuple[Any, ...] = ((((3, 3),),), (((1, 1), (2, None)),), (((1, 1), (2, 2)),))


def _store(levels: tuple[Any, ...], level0_runs: int = 1) -> LSM[int, int]:
    store: LSM[int, int] = LSM(capacity=1, ratio=2, level0_runs=level0_runs)
    store._levels = levels
    return store


_VALID_STORES = {
    "the base store": _store(_BASE),
    "level 0 at exactly its run cap": _store(((((3, 3),), ((4, 4),)), *_BASE[1:]), level0_runs=2),
    "level 1 at exactly its budget": _store(_BASE),
    "the deepest level over its budget, which no budget binds":
        _store((*_BASE[:2], (tuple((k, k) for k in range(1, 6)),))),
    "a tombstone in a run that is not the oldest": _store(_BASE),
    "a tombstone in level 0's oldest run, where a flush leaves it": _store(((((2, None),),),)),
    "no run at all": _store(((), (), ())),
}


@pytest.mark.parametrize("name", list(_VALID_STORES))
def test_valid_accepts_a_store_just_inside_each_line(name: str) -> None:
    assert _VALID_STORES[name].is_valid()


_BROKEN_STORES = {
    "a run out of order": _store(((((4, 4), (3, 3)),), *_BASE[1:])),
    "a key twice in one run": _store(((((3, 3), (3, 4)),), *_BASE[1:])),
    "an empty run in level 1": _store((_BASE[0], ((),), _BASE[2])),
    "level 0 over its run cap": _store(((((3, 3),), ((4, 4),)), *_BASE[1:])),
    "two runs in a deeper level": _store((_BASE[0], (((1, 1),), ((2, None),)), _BASE[2])),
    "level 1 over its budget": _store((_BASE[0], (((1, 1), (2, None), (4, 4)),), _BASE[2])),
    "a tombstone in the oldest run below level 0": _store((*_BASE[:2], (((1, 1), (2, None)),))),
}


@pytest.mark.parametrize("name", list(_BROKEN_STORES))
def test_valid_rejects_each_conjunct_broken_alone(name: str) -> None:
    assert not _BROKEN_STORES[name].is_valid()


def test_a_cascade_into_a_level_above_empty_slots_drops_its_tombstones() -> None:
    """The same rule one level deeper, where a push-down is a cascade rather than level 0's merge.
    Level 1's tombstone for 1 is kept on its way in, because level 2 below it holds 1's value;
    level 1 then runs over its budget and is pushed into level 2, and below level 2 there is only
    an empty slot -- so that merge, which is not into the last slot, drops the tombstone, and the
    value it shadowed with it."""
    from algodesign.searching.lsm import Shape, flush_into_levels

    levels = (
        (((10, 1),),),
        (((1, None), (2, 2)),),
        (((1, 1), (7, 7)),),
        (),
    )
    out = flush_into_levels(((20, 2),), levels, Shape(capacity=1, ratio=2, level0_runs=1))
    assert out == ((), (), (((2, 2), (7, 7), (10, 1), (20, 2)),), ())
