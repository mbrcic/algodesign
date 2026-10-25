# SPDX-License-Identifier: Apache-2.0
"""Bridges, cut vertices and blocks: the walk pinned exactly on small graphs (the Rust walks the same
rows in the same order, so the arrays must match), the block-cut forest's shape, and both compared
with deletion oracles on random small multigraphs with loops and doubled links.
"""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import BlockCutForest, Blocks, Graph, naive
from algodesign.graphs.block_cut import Walk, blocks


@st.composite
def graphs(draw: st.DrawFn) -> Graph:
    n = draw(st.integers(1, 7))
    vertex = st.integers(0, n - 1)
    links = draw(st.lists(st.tuples(vertex, vertex), max_size=10))
    # Copy some links, ends swapped or not, so doubled links turn up often.
    copies = draw(st.lists(st.tuples(st.integers(0, 9), st.booleans()), max_size=3))
    for k, swap in copies:
        if k < len(links):
            a, b = links[k]
            links.append((b, a) if swap else (a, b))
    return Graph(n, links)


def as_sets(b: Blocks) -> set[tuple[frozenset[int], frozenset[int]]]:
    return {(frozenset(links), frozenset(vertices))
            for links, vertices in zip(b.blocks, b.block_vertices, strict=True)}


# a, b, c, d, e = 0 .. 4: two triangles through b.
BOWTIE = Graph(5, [(0, 1), (1, 2), (2, 0), (1, 3), (3, 4), (4, 1)])

# 0 = 1 doubled, a loop at 1, 1 - 2, and 3 with only a loop.
DOUBLED = Graph(4, [(0, 1), (1, 0), (1, 1), (1, 2), (3, 3)])


def test_the_bowtie() -> None:
    # The link 4 -> 1 climbs back to 1's entry number. With 1's climb-back number instead (1, from
    # the first triangle) the second triangle would seem to climb above 1, and 1 would be missed.
    b = blocks(BOWTIE)
    assert b.bridges == []
    assert b.cut_vertices == [1]
    assert b.block_of_link == [1, 1, 1, 0, 0, 0]
    assert b.blocks == [[5, 4, 3], [2, 1, 0]]
    assert b.block_vertices == [[1, 3, 4], [0, 1, 2]]
    f = BlockCutForest(BOWTIE, b)
    assert f.parent == [2, 1, 1]
    assert f.depth == [2, 0, 1]
    assert [f.node_of(p) for p in range(5)] == [1, 2, 1, 0, 0]
    assert f.separators(0, 4) == [1]
    assert f.separators(1, 4) == []
    assert f.separators(3, 4) == []


def test_a_doubled_link_a_loop_and_a_vertex_with_only_a_loop() -> None:
    b = blocks(DOUBLED)
    assert b.bridges == [3]
    assert b.cut_vertices == [1]
    assert b.block_of_link == [1, 1, None, 0, None]
    assert b.blocks == [[3], [1, 0], []]
    assert b.block_vertices == [[1, 2], [0, 1], [3]]
    f = BlockCutForest(DOUBLED, b)
    assert f.parent == [3, 1, 2, 1]
    assert f.depth == [2, 0, 0, 1]
    assert [f.node_of(p) for p in range(4)] == [1, 3, 0, 2]
    assert f.separators(0, 2) == [1]
    assert f.separators(2, 0) == [1]
    assert f.separators(0, 3) is None
    assert f.separators(3, 3) == []


def test_a_path() -> None:
    b = blocks(Graph(4, [(0, 1), (1, 2), (2, 3)]))
    assert b.bridges == [0, 1, 2]
    assert b.cut_vertices == [1, 2]
    assert b.blocks == [[2], [1], [0]]


def test_a_cycle() -> None:
    b = blocks(Graph(4, [(0, 1), (1, 2), (2, 3), (3, 0)]))
    assert b.bridges == []
    assert b.cut_vertices == []
    assert b.blocks == [[3, 2, 1, 0]]
    assert b.block_vertices == [[0, 1, 2, 3]]


def test_two_cycles_sharing_a_vertex() -> None:
    b = blocks(Graph(5, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2)]))
    assert b.bridges == []
    assert b.cut_vertices == [2]
    assert b.blocks == [[5, 4, 3], [2, 1, 0]]


def test_disconnected_pieces() -> None:
    g = Graph(5, [(0, 1), (2, 3), (3, 4), (4, 2)])
    b = blocks(g)
    assert b.bridges == [0]
    assert b.cut_vertices == []
    assert b.blocks == [[0], [3, 2, 1]]
    f = BlockCutForest(g, b)
    assert f.separators(0, 1) == []
    assert f.separators(1, 4) is None


def test_a_doubled_link_is_one_block_and_never_a_bridge() -> None:
    b = blocks(Graph(2, [(0, 1), (0, 1)]))
    assert b.bridges == []
    assert b.cut_vertices == []
    assert b.blocks == [[1, 0]]


def test_a_triple_link() -> None:
    b = blocks(Graph(2, [(0, 1), (1, 0), (0, 1)]))
    assert b.bridges == []
    assert b.blocks == [[2, 1, 0]]
    assert b.block_of_link == [0, 0, 0]


def test_a_doubled_link_inside_a_cycle() -> None:
    b = blocks(Graph(3, [(0, 1), (1, 2), (2, 0), (1, 2)]))
    assert b.bridges == []
    assert b.cut_vertices == []
    assert b.blocks == [[3, 2, 1, 0]]


def test_rows_listing_the_copies_in_opposite_orders() -> None:
    # Rows are sorted by neighbour, then id, so whichever end each copy names first, both rows
    # list id 0 before id 1 and the walk, and its answer, are the same.
    for links in ([(0, 1), (1, 0), (1, 2)], [(1, 0), (0, 1), (1, 2)]):
        b = blocks(Graph(3, links))
        assert b.bridges == [2]
        assert b.cut_vertices == [1]
        assert b.blocks == [[2], [1, 0]]


def test_a_loop_is_ignored() -> None:
    with_loop = blocks(Graph(3, [(0, 1), (1, 1), (1, 2)]))
    assert with_loop.bridges == [0, 2]
    assert with_loop.cut_vertices == [1]
    assert with_loop.block_of_link == [1, None, 0]
    assert with_loop.blocks == [[2], [0]]


def test_a_vertex_with_only_loops_is_its_own_block() -> None:
    b = blocks(Graph(2, [(0, 0), (0, 0), (1, 1)]))
    assert b.bridges == []
    assert b.cut_vertices == []
    assert b.block_of_link == [None, None, None]
    assert b.blocks == [[], []]
    assert b.block_vertices == [[0], [1]]
    assert blocks(Graph(1, [])).block_vertices == [[0]]


@pytest.mark.parametrize("vertex", [-1, 5])
def test_a_vertex_out_of_range_is_refused(vertex: int) -> None:
    f = BlockCutForest(BOWTIE, blocks(BOWTIE))
    with pytest.raises(IndexError):
        f.node_of(vertex)
    with pytest.raises(IndexError):
        f.separators(0, vertex)


@given(graphs())
def test_bridges_and_cut_vertices_match_deletion(g: Graph) -> None:
    b = blocks(g)
    assert b.bridges == naive.bridges(g)
    assert b.cut_vertices == naive.cut_vertices(g)


@given(graphs())
def test_blocks_match_common_cycles(g: Graph) -> None:
    b = blocks(g)
    assert as_sets(b) == naive.blocks(g)
    assert len(as_sets(b)) == len(b.blocks)
    for i, (x, y) in enumerate(g.links):
        k = b.block_of_link[i]
        assert (k is None) == (x == y)
        assert k is None or i in b.blocks[k]


@given(graphs())
def test_separators_match_deletion_for_every_pair(g: Graph) -> None:
    f = BlockCutForest(g, blocks(g))
    for u in range(g.n):
        for v in range(g.n):
            assert f.separators(u, v) == naive.separators(g, u, v), (u, v)


@given(graphs())
def test_the_forest_is_built_from_the_link_stacks_blocks(g: Graph) -> None:
    """The forest's block nodes are the blocks the link stack emitted, bridges and isolated
    vertices included: each vertex that is not a cut vertex lies in exactly one of them, each cut
    vertex's node is joined to exactly the blocks holding it, and each piece is one tree."""
    b = blocks(g)
    f = BlockCutForest(g, b)
    size = len(b.blocks) + len(b.cut_vertices)
    assert len(f.parent) == len(f.depth) == size
    for p in range(g.n):
        holding = [k for k, vertices in enumerate(b.block_vertices) if p in vertices]
        if p in b.cut_vertices:
            assert len(holding) >= 2
            x = f.node_of(p)
            joined = {y for y in range(size) if f.parent[y] == x and y != x}
            joined |= {f.parent[x]} if f.parent[x] != x else set()
            assert joined == set(holding)
        else:
            assert holding == [f.node_of(p)]
    for x in range(size):  # every node's depth is one more than its parent's
        assert f.depth[x] == (0 if f.parent[x] == x else f.depth[f.parent[x]] + 1)
    roots = {x for x in range(size) if f.parent[x] == x}
    assert len(roots) == naive.pieces(g.n, g.links)


def test_walk_states_name_their_broken_piece() -> None:
    # One link 0-1: the walk entered 0, took its row's one entry and went down to 1.
    g = Graph(2, [(0, 1)])
    good = Walk(entry=[1, 2], low=[1, 2], edges=[0], blocks=[], vertices=[], arrival=[None, 0],
                up=[0, 0], finished=[False, False], taken=[1, 0])
    assert good.check_valid(g) is None
    low = Walk(**{**good.__dict__, "low": [1, 1]})
    assert low.check_valid(g) == "invariant 1 (climb_back_is_earliest)"
    lost = Walk(**{**good.__dict__, "edges": []})
    assert lost.check_valid(g) == "invariant 2 (stack_holds_open_links)"
    # Both finished, the link popped as a block of its own: the end state.
    end = Walk(entry=[1, 2], low=[1, 2], edges=[], blocks=[[0]], vertices=[[0, 1]],
               arrival=[None, 0], up=[0, 0], finished=[True, True], taken=[1, 1])
    assert end.is_valid(g)
    alone = Walk(**{**end.__dict__, "blocks": [[0], []], "vertices": [[0, 1], [1]]})
    assert alone.check_valid(g) == "invariant 2 (stack_holds_open_links)"


@st.composite
def small_graphs(draw: st.DrawFn) -> Graph:
    # The state checks try every path, so the graphs stay small.
    n = draw(st.integers(1, 5))
    vertex = st.integers(0, n - 1)
    return Graph(n, draw(st.lists(st.tuples(vertex, vertex), max_size=7)))


@given(small_graphs())
def test_every_state_of_the_walk_is_valid(g: Graph) -> None:
    states = Walk.trace(g)
    for state in states:
        assert state.check_valid(g) is None
    b = blocks(g)  # the last state holds every block the walk returns, and nothing open
    assert states[-1].blocks == b.blocks and states[-1].vertices == b.block_vertices
    assert states[-1].edges == [] and all(states[-1].finished)


def test_every_state_on_the_bowtie_and_the_doubled_graph_is_valid() -> None:
    for g in (BOWTIE, DOUBLED):
        states = Walk.trace(g)
        assert all(state.check_valid(g) is None for state in states)
    # One state after the root is entered and after each of the 12 row entries taken, one after
    # each of the 4 vertices finishing under its parent, and one as the root finishes: 18.
    assert len(Walk.trace(BOWTIE)) == 18


def test_the_walk_goes_down_a_path_deeper_than_recursion_could() -> None:
    # The walk keeps its path in frames, not on Python's call stack (its limit is about 1,000).
    n = 100_000
    b = blocks(Graph(n, [(v, v + 1) for v in range(n - 1)]))
    assert b.bridges == list(range(n - 1)) and b.cut_vertices == list(range(1, n - 1))
    b = blocks(Graph(n, [(v, (v + 1) % n) for v in range(n)]))
    assert b.bridges == [] and b.cut_vertices == [] and len(b.blocks) == 1
