# SPDX-License-Identifier: Apache-2.0
"""Union-find: the Lean's `Valid` after every operation, and the plain search's answers.

Mirrors the Rust's `union_find::tests` and the Lean's `UnionFind/` (`Valid`, `union_spec`,
`find_spec`, and the kernel-checked examples in `Union.lean`). The links and ranks are pinned
exactly, since every tie rule gives the same answers to `joined`.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import naive
from algodesign.graphs.union_find import UnionFind


def root_of(u: UnionFind, i: int) -> int:
    """Where following the links upward from `i` leads after `n` steps, without compressing
    anything (Lean `root`)."""
    for _ in range(len(u.parent)):
        i = u.parent[i]
    return i


def depth(u: UnionFind) -> int:
    """The most links any item is from its root, counted without compressing anything."""
    deepest = 0
    for i in range(len(u.parent)):
        d = 0
        while u.parent[i] != i:
            i = u.parent[i]
            d += 1
        deepest = max(deepest, d)
    return deepest


def unions(n: int, pairs: list[tuple[int, int]]) -> UnionFind:
    u = UnionFind(n)
    for x, y in pairs:
        u.union(x, y)
    return u


def test_every_item_starts_alone() -> None:
    # Lean: valid_init
    u = UnionFind(5)
    assert u.parent == [0, 1, 2, 3, 4]
    assert u.rank == [0] * 5
    assert u.count() == 5
    assert u.is_valid()
    assert UnionFind(0).is_valid()


def test_union_of_two_singles_keeps_the_first_as_root() -> None:
    # Lean: the `(init 2).union 0 1` example in Union.lean
    u = UnionFind(2)
    assert u.union(0, 1)
    assert u.parent[1] == 0
    assert u.rank[0] == 1
    assert u.count() == 1
    assert u.is_valid()


def test_union_inside_one_group_keeps_ranks_and_count() -> None:
    # Lean: the "merging two items already together" example in Union.lean
    u = unions(2, [(0, 1)])
    assert not u.union(1, 0)
    assert u.rank == [1, 0]
    assert u.count() == 1
    assert u.is_valid()


def self_unions_then_chain(n: int) -> list[tuple[int, int]]:
    """The 21-item run behind the same-root check: before each item joins the chain, it is merged
    with itself once more than the last."""
    ops = []
    for i in range(n - 1):
        ops += [(i + 1, i + 1)] * (i + 1)
        ops.append((i, i + 1))
    return ops


def test_repeated_unions_inside_one_group_keep_ranks_and_depth_bounded() -> None:
    n = 21
    # CLRS's FIND-SET and LINK, with the tie as here but no check for one root: a self-union
    # raises the root's rank with no new item, so each new item outranks the chain and goes on top.
    parent = list(range(n))
    rank = [0] * n

    def find_set(x: int) -> int:
        if parent[x] != x:
            parent[x] = find_set(parent[x])
        return parent[x]

    for x, y in self_unions_then_chain(n):
        rx, ry = find_set(x), find_set(y)
        if rank[rx] < rank[ry]:
            parent[rx] = ry
        else:
            parent[ry] = rx
            if rank[rx] == rank[ry]:
                rank[rx] += 1
    unguarded = UnionFind(n)
    unguarded.parent = parent
    assert depth(unguarded) == 20

    # With the check, every self-union answers no and changes nothing.
    u = UnionFind(n)
    for x, y in self_unions_then_chain(n):
        ranks = list(u.rank)
        assert u.union(x, y) == (x != y)
        if x == y:
            assert u.rank == ranks
    assert u.count() == 1
    assert u.is_valid()
    assert max(u.rank) <= 4  # log2 21 < 5
    assert depth(u) <= 4

    # Repeating unions of pairs already joined keeps ranks and the count.
    ranks = list(u.rank)
    for _ in range(3):
        for i in range(n - 1):
            assert not u.union(i, i + 1)
            assert not u.union(i + 1, i)
    assert u.rank == ranks
    assert u.count() == 1
    assert u.is_valid()
    assert depth(u) <= 4


def test_equal_ranks_raise_the_first_root() -> None:
    # Lean: the `(init 4).unions [(0, 1), (2, 3), (1, 3)]` example in Union.lean
    u = unions(4, [(0, 1), (2, 3), (1, 3)])
    assert u.is_valid()
    assert u.parent == [0, 0, 0, 2]
    assert u.rank == [2, 0, 1, 0]
    assert u.count() == 1
    assert u.joined(1, 2)


def test_five_item_run_ends_flat() -> None:
    # Lean: the `(init 5).unions [(0, 1), (2, 3), (1, 3), (4, 4), (3, 4), (0, 4)]` example in
    # Union.lean
    u = unions(5, [(0, 1), (2, 3), (1, 3), (4, 4), (3, 4), (0, 4)])
    assert u.is_valid()
    assert u.parent == [0, 0, 0, 0, 0]
    assert u.rank == [2, 0, 1, 0, 0]
    assert u.count() == 1


def test_a_long_chain_stays_within_log_n_only_with_the_rank_rule() -> None:
    n = 1024
    # Without ranks or compression, hanging x's root under y's along (0, 1), (1, 2), ... makes
    # one path through every item.
    parent = list(range(n))

    def top(i: int) -> int:
        while parent[i] != i:
            i = parent[i]
        return i

    for i in range(n - 1):
        parent[top(i)] = top(i + 1)
    plain = UnionFind(n)
    plain.parent = parent
    assert depth(plain) == n - 1

    # With ranks, the same chain stays shallow ...
    u = unions(n, [(i, i + 1) for i in range(n - 1)])
    assert u.is_valid()
    assert depth(u) <= 10  # log2 1024

    # ... and merging equal halves, stride by stride, reaches the largest rank the bound allows.
    halves = []
    step = 1
    while step < n:
        halves += [(i, i + step) for i in range(0, n, 2 * step)]
        step *= 2
    u = unions(n, halves)
    assert u.is_valid()
    assert u.rank[0] == 10
    assert depth(u) <= 10


@pytest.mark.parametrize("x", [-1, 3])
def test_an_item_out_of_range_raises(x: int) -> None:
    with pytest.raises(IndexError):
        UnionFind(3).find(x)
    with pytest.raises(IndexError):
        UnionFind(3).union(0, x)
    with pytest.raises(IndexError):
        UnionFind(3).joined(x, 0)


@st.composite
def runs(draw: st.DrawFn) -> tuple[int, list[tuple[int, int, int]]]:
    """A number of items up to 64, and operations on them: 0 a union, 1 a joined question, 2 a
    lookup. Items are drawn inside the range, so nothing is filtered."""
    n = draw(st.integers(1, 64))
    item = st.integers(0, n - 1)
    return n, draw(st.lists(st.tuples(st.integers(0, 2), item, item), max_size=120))


@given(runs())
def test_every_operation_keeps_valid_and_answers_as_the_plain_search(
    run: tuple[int, list[tuple[int, int, int]]],
) -> None:
    # Lean: valid_union, valid_find, valid_joined, union_spec, find_spec
    n, ops = run
    u = UnionFind(n)
    pairs: list[tuple[int, int]] = []
    for kind, x, y in ops:
        before = naive.groups(n, pairs)
        old_rank, old_count = list(u.rank), u.count()
        if kind == 0:
            merged = u.union(x, y)
            assert merged == (before[x] != before[y])
            if merged:
                assert u.count() + 1 == old_count
            else:
                assert (u.rank, u.count()) == (old_rank, old_count)
            pairs.append((x, y))
        elif kind == 1:
            assert u.joined(x, y) == (before[x] == before[y])
        else:
            expected = root_of(u, x)
            assert u.find(x) == expected
            assert (u.rank, u.count()) == (old_rank, old_count)
        assert u.is_valid()
        # The groups are the plain search's: one root per label, one label per root.
        after = naive.groups(n, pairs)
        roots = {after[i]: root_of(u, i) for i in range(n)}
        assert all(roots[after[i]] == root_of(u, i) for i in range(n))
        assert len(set(roots.values())) == len(roots) == u.count()


def deep8() -> UnionFind:
    """Eight items, one group with root 3 and the path 0 -> 1 -> 2 -> 3: ranks 0 to 3 up the
    path, items 4 to 7 straight under the root (Lean `deep8` in `AlgoDesignTests/Graphs.lean`)."""
    u = UnionFind(8)
    u.parent = [1, 2, 3, 3, 3, 3, 3, 3]
    u.rank = [0, 1, 2, 3, 0, 0, 0, 0]
    u._count = 1
    return u


def test_each_check_accepts_a_deep_valid_tree() -> None:
    assert deep8().check_valid() is None
    assert deep8().one_rank_per_item()


@pytest.mark.parametrize(
    "part,index,value,label",
    [
        ("parent", 4, 8, "invariant 1 (upward_ends_at_root)"),  # a link past the items
        ("parent", 3, 2, "invariant 1 (upward_ends_at_root)"),  # a loop that reaches no root
        ("rank", 1, 2, "invariant 2 (ranks_rise_upward)"),  # a rank equal to its parent's
        ("rank", 3, 4, "invariant 2 (root_rank_bounds_size)"),  # rank 4 over eight items
        ("rank", 3, 10**9, "invariant 2 (root_rank_bounds_size)"),  # no 2 ** rank is built
    ],
)
def test_each_check_rejects_its_own_breakage_and_names_it(
    part: str, index: int, value: int, label: str
) -> None:
    u = deep8()
    getattr(u, part)[index] = value
    assert u.check_valid() == label


def test_a_negative_link_is_named() -> None:
    # Item 4 links to -5, which Python's list would read as item 3, the root.
    u = deep8()
    u.parent[4] = -5
    assert u.check_valid() == "invariant 1 (upward_ends_at_root)"


def test_a_wrong_count_is_named() -> None:
    u = deep8()
    u._count = 2
    assert u.check_valid() == "not in the box (count_is_roots)"


def test_each_check_answers_on_any_stored_state() -> None:
    """Arrays of different lengths and links far out of range: every check answers."""
    u = UnionFind(0)
    u.parent, u.rank, u._count = [9, 0, 2], [200], 7
    assert not u.one_rank_per_item()
    assert not u.is_upward_ends_at_root()
    assert not u.is_ranks_rise_upward()
    assert u.is_root_rank_bounds_size()
    assert not u.is_count_is_roots()
    assert not u.is_valid()


def test_a_negative_number_of_items_is_refused() -> None:
    with pytest.raises(ValueError):
        UnionFind(-1)
