"""Breadth-first search: the fewest arrows, pinned on small graphs (the Rust walks the same rows in
the same order, so the previous vertices must match too) and judged by trying every path on
random small graphs."""

from __future__ import annotations

from itertools import pairwise

import pytest
from hypothesis import given

from algodesign.graphs import Digraph
from algodesign.paths import Network, naive
from algodesign.paths.bfs import bfs

from .strategies import network_and_vertex


def test_fewest_arrows_and_the_vertex_each_was_found_from() -> None:
    # 0 -> 1 -> 3 and 0 -> 2 -> 3: 3 is found first from 1, the earlier of the two in the queue.
    g = Digraph(5, [(0, 2), (0, 1), (1, 3), (2, 3), (3, 4)])
    d = bfs(g, 0)
    assert d.cost == [0, 1, 1, 2, 3]
    assert d.previous == [None, 0, 0, 1, 3]
    assert d.path_to(4) == [0, 1, 3, 4]


def test_a_vertex_is_marked_when_found() -> None:
    # 2 is found from 0 at one arrow; the arrow 1 -> 2 later finds it marked and changes nothing.
    g = Digraph(3, [(0, 1), (0, 2), (1, 2)])
    d = bfs(g, 0)
    assert d.cost == [0, 1, 1]
    assert d.previous == [None, 0, 0]


def test_loops_doubled_arrows_and_unreachable_vertices() -> None:
    g = Digraph(4, [(0, 0), (0, 1), (0, 1), (2, 3)])
    d = bfs(g, 0)
    assert d.cost == [0, 1, None, None]
    assert d.previous == [None, 0, None, None]
    assert d.path_to(3) is None


def test_the_start_must_be_a_vertex() -> None:
    with pytest.raises(IndexError):
        bfs(Digraph(2, []), 2)
    with pytest.raises(IndexError):
        bfs(Digraph(2, []), -1)
    with pytest.raises(IndexError):
        bfs(Digraph(0, []), 0)


@given(network_and_vertex())
def test_bfs_gives_the_fewest_arrows(case: tuple[Network, int]) -> None:
    network, start = case
    g = network.g
    d = bfs(g, start)
    assert d.cost == naive.cheapest(Network(g, [1] * len(g.arrows)), start)
    for v in range(g.n):
        path = d.path_to(v)
        assert (path is None) == (d.cost[v] is None)
        if path is not None:
            assert path[0] == start and path[-1] == v and len(path) - 1 == d.cost[v]
            assert len(set(path)) == len(path)
            assert all(any(w == b for w, _ in g.out[a]) for a, b in pairwise(path))
