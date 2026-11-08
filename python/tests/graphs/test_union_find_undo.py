# SPDX-License-Identifier: Apache-2.0
"""Union-find with undo: the links, ranks and count pinned, every rollback compared with the state
it returns to, the answers compared with the plain search, and the depth bound without
compression.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import UndoUnionFind, naive


@st.composite
def runs(draw: st.DrawFn) -> tuple[int, list[tuple[int, int]]]:
    n = draw(st.integers(1, 12))
    item = st.integers(0, n - 1)
    return n, draw(st.lists(st.tuples(item, item), max_size=20))


def state(u: UndoUnionFind) -> tuple[list[int], list[int], int]:
    return list(u.parent), list(u.rank), u.count()


def depth(u: UndoUnionFind) -> int:
    """The most links any item is from its root."""
    deepest = 0
    for i in range(len(u.parent)):
        d = 0
        while u.parent[i] != i:
            i = u.parent[i]
            d += 1
        deepest = max(deepest, d)
    return deepest


def test_every_item_starts_alone_with_an_empty_log() -> None:
    u = UndoUnionFind(4)
    assert state(u) == ([0, 1, 2, 3], [0, 0, 0, 0], 4)
    assert u.log == []
    assert not u.undo()
    assert state(u) == ([0, 1, 2, 3], [0, 0, 0, 0], 4)


def test_the_tie_rule_and_the_log() -> None:
    # Equal ranks: the second root goes under the first, whose rank rises. Lower rank: under the
    # higher, nothing rises.
    u = UndoUnionFind(4)
    assert u.union(0, 1)
    assert u.union(2, 3)
    assert u.union(3, 1)
    assert state(u) == ([2, 0, 2, 2], [1, 0, 2, 0], 1)
    assert u.log == [(1, True), (3, True), (0, True)]
    v = UndoUnionFind(3)
    v.union(0, 1)
    assert v.union(2, 1)
    assert state(v) == ([0, 0, 0], [1, 0, 0], 1)
    assert v.log == [(1, True), (2, False)]


def test_a_merge_of_two_already_together_takes_one_undo_step() -> None:
    u = UndoUnionFind(3)
    u.union(0, 1)
    after = state(u)
    assert not u.union(1, 0)
    assert u.log == [(1, True), None]
    assert u.undo()  # takes back the empty entry only
    assert state(u) == after
    assert u.undo()
    assert state(u) == ([0, 1, 2], [0, 0, 0], 3)
    assert not u.undo()


def test_find_changes_nothing() -> None:
    u = UndoUnionFind(4)
    for x, y in [(0, 1), (2, 3), (0, 2)]:
        u.union(x, y)
    before = state(u)
    assert [u.find(i) for i in range(4)] == [0, 0, 0, 0]
    assert state(u) == before


@pytest.mark.parametrize("x", [-1, 3])
def test_an_item_out_of_range_is_refused(x: int) -> None:
    u = UndoUnionFind(3)
    with pytest.raises(IndexError):
        u.find(x)
    with pytest.raises(IndexError):
        u.union(0, x)


def test_a_negative_size_is_refused() -> None:
    with pytest.raises(ValueError):
        UndoUnionFind(-1)


@given(runs())
def test_rollback_restores_every_earlier_state_exactly(run: tuple[int, list[tuple[int, int]]]) -> None:
    n, pairs = run
    u = UndoUnionFind(n)
    states = [state(u)]
    for x, y in pairs:
        u.union(x, y)
        states.append(state(u))
    assert len(u.log) == len(pairs)
    for earlier in reversed(states[:-1]):
        assert u.undo()
        assert state(u) == earlier
    assert not u.undo()


@given(runs(), st.data())
def test_answers_match_the_plain_search_after_a_partial_rollback(
    run: tuple[int, list[tuple[int, int]]], data: st.DataObject
) -> None:
    n, pairs = run
    u = UndoUnionFind(n)
    for x, y in pairs:
        u.union(x, y)
    back = data.draw(st.integers(0, len(pairs)))
    for _ in range(back):
        u.undo()
    label = naive.groups(n, pairs[: len(pairs) - back])
    assert u.count() == len(set(label))
    for x in range(n):
        for y in range(n):
            assert u.joined(x, y) == (label[x] == label[y])


@given(runs())
def test_no_lookup_is_deeper_than_log2_n(run: tuple[int, list[tuple[int, int]]]) -> None:
    n, pairs = run
    u = UndoUnionFind(n)
    for x, y in pairs:
        u.union(x, y)
        assert depth(u) <= n.bit_length() - 1


def test_pairing_equal_groups_reaches_exactly_log2_n_and_undoes_back() -> None:
    # Pass r joins groups of size 2^r in pairs: every union is a tie, and the depth grows by one.
    n = 1024
    u = UndoUnionFind(n)
    step = 1
    while step < n:
        for x in range(0, n, 2 * step):
            u.union(x, x + step)
        step *= 2
    assert depth(u) == 10
    assert u.count() == 1
    while u.undo():
        pass
    assert state(u) == (list(range(n)), [0] * n, n)
