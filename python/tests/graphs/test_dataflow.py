# SPDX-License-Identifier: Apache-2.0
"""Spreading news: the chapter's example, and the group-by-group run against the plain repeat over
all vertices on random small graphs.
"""

from __future__ import annotations

from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Digraph, naive, spread

AMARA, MATEO, OMAR = 0, 1, 2


def test_amara_and_mateo_pass_news_to_each_other_and_amara_to_omar() -> None:
    g = Digraph(3, [(AMARA, MATEO), (MATEO, AMARA), (AMARA, OMAR)])
    heard = [{"the table is at eight"}, set(), {"Omar is late"}]
    assert spread(g, heard) == [
        {"the table is at eight"},
        {"the table is at eight"},
        {"the table is at eight", "Omar is late"},
    ]
    assert heard == [{"the table is at eight"}, set(), {"Omar is late"}]  # left as it was


@st.composite
def graphs_with_news(draw: st.DrawFn) -> tuple[Digraph, list[set[int]]]:
    n = draw(st.integers(0, 7))
    if n == 0:
        return Digraph(0, []), []
    vertex = st.integers(0, n - 1)
    g = Digraph(n, draw(st.lists(st.tuples(vertex, vertex), max_size=14)))
    heard = draw(st.lists(st.sets(st.integers(0, 5), max_size=2), min_size=n, max_size=n))
    return g, heard


@given(graphs_with_news())
def test_group_by_group_reaches_the_plain_fixpoint(case: tuple[Digraph, list[set[int]]]) -> None:
    g, heard = case
    assert spread(g, heard) == naive.spread(g, heard)


@given(graphs_with_news())
def test_each_vertex_hears_what_starts_at_vertices_that_reach_it(
    case: tuple[Digraph, list[set[int]]],
) -> None:
    g, heard = case
    news = spread(g, heard)
    for v in range(g.n):
        sources = [u for u in range(g.n) if u == v or v in naive.reachable(g, [u])]
        assert news[v] == set().union(*(heard[u] for u in sources))
