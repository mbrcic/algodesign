"""Kruskal's method: the answers pinned on the small networks the Lean's kernel checks in
`AlgoDesignTests/Paths.lean` (`triangle`, `twoPieces`, `loopAndDouble`, `islands`, `keptDear`);
judged by trying every set of links on random small networks; the Lean's `Valid` and `WellFormed`
after every step; and one broken state per piece, each named by its label. The Rust sorts and
breaks ties the same way, so the kept links and the links tried must match it.
"""

from __future__ import annotations

import copy
import importlib

import pytest
from hypothesis import given, settings

from algodesign.graphs import Graph, UnionFind
from algodesign.paths import LinkNetwork, kruskal_with_tried, naive
from algodesign.paths.kruskal import LABELS, State, kruskal

from .strategies import link_networks

# The package's `kruskal` is the function; the module is needed for the union-find it builds.
kruskal_module = importlib.import_module("algodesign.paths.kruskal")

# A triangle whose three links all cost 1, and the same with link 2 made dearer.
TRIANGLE = LinkNetwork(Graph(3, [(0, 1), (1, 2), (0, 2)]), [1, 1, 1])
DEAR = LinkNetwork(Graph(3, [(0, 1), (1, 2), (0, 2)]), [1, 1, 4])
# Two pieces, {0, 1} and {2, 3}.
TWO_PIECES = LinkNetwork(Graph(4, [(2, 3), (0, 1)]), [5, 2])
# A negative loop at 0, and two links between 0 and 1.
LOOP_AND_DOUBLE = LinkNetwork(Graph(2, [(0, 0), (0, 1), (0, 1)]), [-1, 4, 3])
# Two close pairs, {0, 1} and {2, 3}, far apart.
ISLANDS = LinkNetwork(Graph(4, [(0, 1), (2, 3), (1, 2), (0, 3)]), [1, 1, 5, 6])


def states(network: LinkNetwork) -> list[State]:
    """Every state of the walk, the start first, one more per step until it is done."""
    state = State.start(network)
    trail = [copy.deepcopy(state)]
    while not state.done():
        state.step(network)
        trail.append(copy.deepcopy(state))
    return trail


def merged(n: int, pairs: list[tuple[int, int]]) -> UnionFind:
    """A union-find over `n` items with `pairs` merged, in order."""
    uf = UnionFind(n)
    for a, b in pairs:
        uf.union(a, b)
    return uf


def test_on_equal_costs_the_tie_goes_by_id_and_the_walk_stops_at_one_group() -> None:
    assert State.start(TRIANGLE).rest == [0, 1, 2]
    assert naive.cheapest_forests(TRIANGLE) == [[0, 1], [0, 2], [1, 2]]
    # One group is left after two links, so link 2 is never tried.
    assert kruskal_with_tried(TRIANGLE) == ([0, 1], [0, 1])
    trail = states(TRIANGLE)
    assert len(trail) == 3 and trail[-1].rest == [2]
    cheapest = naive.cheapest_forests(TRIANGLE)
    assert all(state.check_valid(TRIANGLE, cheapest) is None for state in trail)


def test_a_graph_in_two_pieces_gets_a_spanning_forest() -> None:
    kept, tried = kruskal_with_tried(TWO_PIECES)
    assert kept == tried == [1, 0]
    assert TWO_PIECES.is_spanning_forest(kept)
    assert not TWO_PIECES.joins(kept, 0, 2)


def test_a_loop_is_skipped_and_of_two_doubled_links_the_cheaper_is_kept() -> None:
    assert State.start(LOOP_AND_DOUBLE).rest == [0, 2, 1]
    assert kruskal_with_tried(LOOP_AND_DOUBLE) == ([2], [0, 2])
    assert naive.cheapest_forests(LOOP_AND_DOUBLE) == [[2]]


def nearest_links(network: LinkNetwork) -> list[int]:
    """Each vertex's cheapest link, equal costs by id."""
    return sorted({min((network.cost[i], i) for _, i in row)[1]
                   for row in network.g.adj if row})


def test_nearest_neighbor_links_leave_islands_and_kruskal_joins_them() -> None:
    assert nearest_links(ISLANDS) == [0, 1]
    assert not ISLANDS.joins_what_graph_joins([0, 1])
    assert kruskal(ISLANDS) == [0, 1, 2]
    assert ISLANDS.joins_what_graph_joins(kruskal(ISLANDS))


def test_no_vertex_or_one_vertex_keeps_nothing() -> None:
    assert kruskal_with_tried(LinkNetwork(Graph(0, []), [])) == ([], [])
    # One vertex is one group from the start: its loop is never tried.
    assert kruskal_with_tried(LinkNetwork(Graph(1, [(0, 0)]), [3])) == ([], [])


def test_costs_below_zero_are_taken_first() -> None:
    network = LinkNetwork(Graph(3, [(0, 1), (1, 2), (0, 2)]), [2, -5, -1])
    assert kruskal(network) == [1, 2]
    assert network.total(kruskal(network)) == -6


def pieces(state: State, network: LinkNetwork) -> list[bool]:
    """Each piece of `Valid` and `WellFormed` on `state`, in the Lean order."""
    return [state.is_part_of_cheapest(naive.cheapest_forests(network)),
            state.is_groups_are_kept_joins(network), state.is_union_find_ready(network),
            state.is_kept_closes_no_cycle(network), state.is_rest_cheapest_first(network),
            state.is_passed_are_joined(network)]


def test_each_broken_state_names_its_piece() -> None:
    cases = [
        # Link 2 kept first: part of no cheapest tree (the Lean's `keptDear`).
        State([0, 1], [2], [2], merged(3, [(0, 2)])),
        # Link 0 kept, but the union-find still has every vertex alone.
        State([1, 2], [0], [0], UnionFind(3)),
        # A union-find over four items for a graph of three.
        State([0, 1, 2], [], [], UnionFind(4)),
        # Link 0 kept twice.
        State([1, 2], [0, 0], [0], merged(3, [(0, 1)])),
        # The dear link before the cheap one.
        State([0, 2, 1], [], [], UnionFind(3)),
        # Link 0 taken and skipped, though its ends were apart.
        State([1, 2], [], [0], UnionFind(3)),
    ]
    cheapest = naive.cheapest_forests(DEAR)
    for broken, state in enumerate(cases):
        assert pieces(state, DEAR) == [k != broken for k in range(6)], broken
        assert state.check_valid(DEAR, cheapest) == LABELS[broken]


def test_a_union_find_with_a_cycle_of_parents_gets_an_answer() -> None:
    # 0 and 1 point at each other: three steps up from 0 reach 1, and from 1 reach 0, so the two
    # read as apart, though link 0 is kept.
    looped = UnionFind(3)
    looped.parent = [1, 0, 2]
    state = State([1, 2], [0], [0], looped)
    assert not state.is_union_find_ready(DEAR)
    assert not state.is_groups_are_kept_joins(DEAR)
    assert state.check_valid(DEAR, naive.cheapest_forests(DEAR)) == LABELS[1]


def test_the_pieces_answer_on_parts_of_the_wrong_size() -> None:
    past = State([7, 0], [9], [9], UnionFind(1))
    cheapest = naive.cheapest_forests(DEAR)
    assert not past.is_part_of_cheapest(cheapest)
    assert not past.is_union_find_ready(DEAR)
    assert not past.is_kept_closes_no_cycle(DEAR)
    assert not past.is_rest_cheapest_first(DEAR)
    assert not past.is_passed_are_joined(DEAR)
    assert past.is_groups_are_kept_joins(DEAR)
    assert not past.is_valid(DEAR, [])


# Trying every set of links, up to 4096 of them, is slow on a busy runner: no deadline.
@settings(deadline=None)
@given(link_networks())
def test_the_kept_links_are_a_cheapest_spanning_forest(network: LinkNetwork) -> None:
    kept = kruskal(network)
    assert network.is_spanning_forest(kept)
    cheapest = naive.cheapest_forests(network)
    assert network.total(kept) == min(network.total(forest) for forest in cheapest)
    keys = [(network.cost[i], i) for i in kept]
    assert keys == sorted(set(keys))


@settings(deadline=None)
@given(link_networks())
def test_every_state_of_the_walk_is_valid(network: LinkNetwork) -> None:
    cheapest = naive.cheapest_forests(network)
    trail = states(network)
    assert all(state.check_valid(network, cheapest) is None for state in trail)
    last = trail[-1]
    assert (last.kept, last.tried) == kruskal_with_tried(network)
    assert kruskal(network) == last.kept
    # Each link given to the union-find at most once, in the order (Lean `kruskal_cost`).
    assert last.tried + last.rest == State.start(network).rest
    assert len(trail) == len(last.tried) + 1


def unions(network: LinkNetwork) -> list[tuple[int, int]]:
    """The ends of every link `kruskal` gives its union-find, in order."""
    given: list[tuple[int, int]] = []

    class Counted(UnionFind):
        def union(self, x: int, y: int) -> bool:
            given.append((x, y))
            return super().union(x, y)

    with pytest.MonkeyPatch.context() as m:
        m.setattr(kruskal_module, "UnionFind", Counted)
        kruskal(network)
    return given


def test_the_printed_loop_stops_at_one_group() -> None:
    # The triangle's third link is never given to the union-find: one group is left after two.
    assert unions(TRIANGLE) == [(0, 1), (1, 2)]


@settings(deadline=None)
@given(link_networks())
def test_the_printed_loop_gives_the_union_find_the_links_the_walk_tries(
        network: LinkNetwork) -> None:
    tried = kruskal_with_tried(network)[1]
    assert unions(network) == [network.g.links[i] for i in tried]
