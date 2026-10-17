# SPDX-License-Identifier: Apache-2.0
"""The design project's bench: the cost model counts what it says, the promise check catches the
candidates it should, and the chapter's two trees pass it."""

from __future__ import annotations

import bisect

import pytest

from algodesign.searching.workbench import (
    BLOCK,
    HELD,
    Memory,
    Op,
    OrderedSet,
    Reference,
    btree_baseline,
    btree_t,
    check_promise,
    llrb_baseline,
    measure,
    outside_memory,
    timers,
)


def _ints(memory: Memory, ref: int) -> list[int]:
    """Block `ref`'s slots, which these candidates fill with integers only."""
    return [k for k in memory.load(ref) if isinstance(k, int)]


class _Pages:
    """A small correct candidate: sorted pages of keys, listed in one directory block. Holds at
    most `BLOCK` pages, enough for these tests."""

    def __init__(self, memory: Memory) -> None:
        self.memory = memory
        self.directory = memory.new()

    def _pages(self) -> list[int]:
        return _ints(self.memory, self.directory)

    def _page_for(self, pages: list[int], key: int) -> tuple[int, list[int]]:
        """The index of the page `key` belongs in, and that page's keys."""
        for i, ref in enumerate(pages):
            keys = _ints(self.memory, ref)
            if i == len(pages) - 1 or (keys and key <= keys[-1]):
                return i, keys
        raise AssertionError("unreachable")

    def insert(self, key: int) -> bool:
        pages = self._pages()
        if not pages:
            pages.append(self.memory.new([key]))
            self.memory.store(self.directory, pages)
            return True
        i, keys = self._page_for(pages, key)
        j = bisect.bisect_left(keys, key)
        if j < len(keys) and keys[j] == key:
            return False
        keys.insert(j, key)
        if len(keys) <= self.memory.block:
            self.memory.store(pages[i], keys)
        else:
            half = len(keys) // 2
            self.memory.store(pages[i], keys[:half])
            pages.insert(i + 1, self.memory.new(keys[half:]))
            self.memory.store(self.directory, pages)
        return True

    def delete(self, key: int) -> bool:
        pages = self._pages()
        if not pages:
            return False
        i, keys = self._page_for(pages, key)
        if key not in keys:
            return False
        keys.remove(key)
        self.memory.store(pages[i], keys)
        return True

    def contains(self, key: int) -> bool:
        pages = self._pages()
        return bool(pages) and key in self._page_for(pages, key)[1]

    def next_larger(self, key: int) -> int | None:
        for ref in self._pages():
            keys = _ints(self.memory, ref)
            j = bisect.bisect_right(keys, key)
            if j < len(keys):
                return keys[j]
        return None


class _LazyDelete(_Pages):
    """Deletes by marking: `contains` honours the mark, `next_larger` forgets it."""

    def __init__(self, memory: Memory) -> None:
        super().__init__(memory)
        self.gone = memory.new()

    def delete(self, key: int) -> bool:
        gone = list(self.memory.load(self.gone))
        if not super().contains(key) or key in gone:
            return False
        self.memory.store(self.gone, gone + [key])
        return True

    def insert(self, key: int) -> bool:
        gone = list(self.memory.load(self.gone))
        if key in gone:
            gone.remove(key)
            self.memory.store(self.gone, gone)
            return True
        return super().insert(key)

    def contains(self, key: int) -> bool:
        return super().contains(key) and key not in self.memory.load(self.gone)


class _KeepsAList:
    """Correct answers, but the keys live in a Python list beside the memory."""

    def __init__(self, memory: Memory) -> None:
        self.reference = Reference()

    def insert(self, key: int) -> bool:
        return self.reference.insert(key)

    def delete(self, key: int) -> bool:
        return self.reference.delete(key)

    def contains(self, key: int) -> bool:
        return self.reference.contains(key)

    def next_larger(self, key: int) -> int | None:
        return self.reference.next_larger(key)


def _small(seed: int) -> list[Op]:
    """A dense small workload: few keys, many writes, so deletes and "next larger" collide."""
    preload, ops = timers(seed, start=200, ops=3000, reads_per_write=2, span=500)
    return [("insert", k) for k in preload] + ops


def test_memory_counts_a_fetch_per_load_and_a_write_per_store() -> None:
    memory = Memory()
    ref = memory.new([1, 2])
    assert (memory.fetches, memory.writes) == (0, 1)
    slots = memory.load(ref)
    slots.append(3)
    assert memory.load(ref) == [1, 2]
    memory.store(ref, slots)
    assert (memory.fetches, memory.writes, memory.in_use()) == (2, 2, 1)
    memory.free(ref)
    assert memory.in_use() == 0


def test_a_block_holds_no_more_than_its_slots() -> None:
    memory = Memory(block=4)
    with pytest.raises(ValueError):
        memory.new(range(5))


def test_a_slot_holds_one_word_so_keys_cannot_be_packed() -> None:
    memory = Memory()
    with pytest.raises(ValueError):
        memory.new([sum(k << (40 * i) for i, k in enumerate(range(10)))])
    with pytest.raises(ValueError):
        memory.new(["a key"])
    with pytest.raises(ValueError):
        memory.new([(1, 2)] * 33)
    memory.new([(7,)] * 64)


def test_the_widest_btree_node_fits_a_block() -> None:
    t = btree_t()
    assert 4 * t - 1 <= BLOCK < 4 * (t + 1) - 1


@pytest.mark.parametrize("seed", range(5))
def test_the_reference_answers_like_a_python_set(seed: int) -> None:
    ref, keys = Reference(), set[int]()
    for name, key in _small(seed):
        if name == "insert":
            assert ref.insert(key) == (key not in keys)
            keys.add(key)
        elif name == "delete":
            assert ref.delete(key) == (key in keys)
            keys.discard(key)
        elif name == "contains":
            assert ref.contains(key) == (key in keys)
        else:
            assert ref.next_larger(key) == min((k for k in keys if k > key), default=None)


@pytest.mark.parametrize("seed", range(5))
def test_the_chapters_trees_keep_the_promise(seed: int) -> None:
    ops = _small(seed)
    assert check_promise(llrb_baseline, ops, trusted=True) is None
    assert check_promise(btree_baseline, ops, trusted=True) is None


def test_the_chapters_trees_are_trusted_without_being_told() -> None:
    """The bench knows its own baselines: run without `trusted=True` they keep the promise and
    are measured the same as with it."""
    ops = _small(0)
    for make in (llrb_baseline, btree_baseline):
        assert check_promise(make, ops) is None
        told = measure(make, [], ops, trusted=True)
        untold = measure(make, [], ops)
        assert (told.fetches, told.writes, told.blocks) == (untold.fetches, untold.writes,
                                                           untold.blocks)


@pytest.mark.parametrize("seed", range(5))
def test_a_correct_block_candidate_passes(seed: int) -> None:
    assert check_promise(_Pages, _small(seed)) is None


def test_a_lazy_delete_is_caught_by_next_larger() -> None:
    mismatch = check_promise(_LazyDelete, _small(0))
    assert mismatch is not None and mismatch.op[0] == "next_larger"


def test_keys_kept_outside_memory_are_caught() -> None:
    mismatch = check_promise(_KeepsAList, _small(0))
    assert mismatch is not None and "outside memory" in str(mismatch.got)
    assert outside_memory(_Pages(Memory()), Memory()) <= HELD


def test_the_workload_is_the_same_for_the_same_seed() -> None:
    assert timers(7, start=100, ops=500) == timers(7, start=100, ops=500)
    preload, ops = timers(7, start=1000, ops=5000, reads_per_write=50)
    writes = sum(name in ("insert", "delete") for name, _ in ops)
    assert len(set(preload)) == 1000 and 50 < writes < 150
    _, checks_only = timers(7, start=100, ops=500, next_share=0.0)
    assert all(name != "next_larger" for name, _ in checks_only)


def test_the_btree_fetches_far_fewer_blocks_than_the_llrb() -> None:
    preload, ops = timers(1, start=20_000, ops=2_000)
    llrb = measure(llrb_baseline, preload, ops, trusted=True)
    btree = measure(btree_baseline, preload, ops, trusted=True)
    assert btree.per_op()[0] * 3 < llrb.per_op()[0]
    assert btree.blocks * 10 < llrb.blocks


def test_measure_counts_the_candidates_own_loads() -> None:
    preload, ops = timers(2, start=300, ops=300, span=10_000)
    costs = measure(_Pages, preload, ops)
    assert sum(costs.ops.values()) == 300
    assert costs.per_op("contains")[0] >= 2
    assert costs.blocks >= 1 + 300 // BLOCK  # the directory and at least the pages it needs


def _protocol_check(candidate: OrderedSet) -> OrderedSet:
    return candidate


def test_the_baselines_are_ordered_sets() -> None:
    _protocol_check(llrb_baseline(Memory()))
    _protocol_check(btree_baseline(Memory()))
