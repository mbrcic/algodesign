# SPDX-License-Identifier: Apache-2.0
"""Graph storage: rows sorted by (neighbour, id) whatever order the arrows came in, every arrow
or link in its rows with its id, loops and doubled arrows kept, and endpoints outside the graph
refused.

Mirrors the kernel-checked examples in the Lean's `Graphs/Digraph.lean`.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Digraph, Graph


@st.composite
def edge_lists(draw: st.DrawFn) -> tuple[int, list[tuple[int, int]]]:
    n = draw(st.integers(0, 6))
    if n == 0:
        return 0, []
    vertex = st.integers(0, n - 1)
    return n, draw(st.lists(st.tuples(vertex, vertex), max_size=12))


def test_rows_are_sorted_by_neighbour_then_id() -> None:
    # Lean: the `Digraph.out` and `Digraph.into` examples in Digraph.lean
    g = Digraph(3, [(0, 2), (0, 1), (0, 2), (1, 0)])
    assert g.out[0] == [(1, 1), (2, 0), (2, 2)]
    assert g.into[2] == [(0, 0), (0, 2)]
    assert g.out[1] == [(0, 3)]
    assert g.into[0] == [(1, 3)]
    assert g.out[2] == [] and g.into[1] == [(0, 1)]
    assert g.arrows == [(0, 2), (0, 1), (0, 2), (1, 0)]


def test_a_link_is_in_both_rows_and_a_loop_twice_in_its_own() -> None:
    # Lean: the `Graph.adj` examples in Digraph.lean
    g = Graph(2, [(0, 1), (1, 1)])
    assert g.adj[1] == [(0, 0), (1, 1), (1, 1)]
    assert g.adj[0] == [(1, 0)]
    assert g.links == [(0, 1), (1, 1)]


def test_doubled_arrows_and_loops_are_kept() -> None:
    g = Digraph(2, [(0, 1), (1, 1), (0, 1)])
    assert g.out[0] == [(1, 0), (1, 2)]
    assert g.out[1] == [(1, 1)]
    assert g.into[1] == [(0, 0), (0, 2), (1, 1)]
    h = Graph(2, [(1, 0), (0, 1)])
    assert h.adj[0] == [(1, 0), (1, 1)]
    assert h.adj[1] == [(0, 0), (0, 1)]


@pytest.mark.parametrize("pairs", [[(0, 3)], [(3, 0)], [(-1, 0)], [(0, 1), (1, 5)]])
def test_an_end_outside_the_graph_is_refused(pairs: list[tuple[int, int]]) -> None:
    with pytest.raises(ValueError):
        Digraph(3, pairs)
    with pytest.raises(ValueError):
        Graph(3, pairs)


def test_a_negative_number_of_vertices_is_refused() -> None:
    with pytest.raises(ValueError):
        Digraph(-1, [])
    with pytest.raises(ValueError):
        Graph(-1, [])
    assert Digraph(0, []).out == [] and Graph(0, []).adj == []


@given(edge_lists())
def test_every_row_is_sorted_and_holds_exactly_its_arrows(
    case: tuple[int, list[tuple[int, int]]],
) -> None:
    n, pairs = case
    g = Digraph(n, pairs)
    h = Graph(n, pairs)
    for v in range(n):
        assert g.out[v] == sorted((w, i) for i, (a, w) in enumerate(pairs) if a == v)
        assert g.into[v] == sorted((a, i) for i, (a, w) in enumerate(pairs) if w == v)
        ends = [(b, i) for i, (a, b) in enumerate(pairs) if a == v]
        ends += [(a, i) for i, (a, b) in enumerate(pairs) if b == v]
        assert h.adj[v] == sorted(ends)
