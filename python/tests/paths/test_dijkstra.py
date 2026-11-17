"""Dijkstra's method: the answers pinned on small networks (the Rust walks the same rows and breaks
ties the same way, so the previous vertices and the settled order must match too), and judged by
trying every path on random small networks. The pins on `ROADS`, `TIE`, `LOOP` and the
three-vertex map `PROBE` are the examples the Lean's kernel checks in `AlgoDesignTests/Paths.lean`
(`roads`, `tie`, `loop`, `probe`).
"""

from __future__ import annotations

from functools import partial
from itertools import pairwise

import pytest
from hypothesis import given

from algodesign.graphs import Digraph
from algodesign.paths import Network, dijkstra_to, dijkstra_with_settled, naive
from algodesign.paths.bfs import bfs
from algodesign.paths.dijkstra import State, dijkstra

from .counting import ReadCosts, work
from .strategies import network_and_vertex

# A three-vertex map with one negative arrow: 0 -> 1 costs 1, 0 -> 2 costs 2, 2 -> 1 costs -2.
PROBE = Network(Digraph(3, [(0, 1), (0, 2), (2, 1)]), [1, 2, -2])
# Two arrows 0 -> 1 that cost differently, 1 -> 2, a dearer 0 -> 2, a loop at 2, and 3 unreached.
ROADS = Network(Digraph(4, [(0, 1), (0, 1), (1, 2), (0, 2), (2, 2)]), [3, 1, 2, 5, 0])
# Two vertices at the same cost: the lower id is settled first.
TIE = Network(Digraph(3, [(0, 2), (0, 1)]), [1, 1])
# One vertex and a loop.
LOOP = Network(Digraph(1, [(0, 0)]), [7])
# Both 1 and 2 cost 1 from 0, and both reach 3 at cost 2; 0's row lists 2 first.
DIAMOND = Network(Digraph(4, [(0, 2), (0, 1), (2, 3), (1, 3)]), [1, 1, 1, 1])


def path_costs(network: Network, path: list[int]) -> set[int]:
    """What the path's vertices cost, over every choice of arrow between two of them."""
    sums = {0}
    for a, b in pairwise(path):
        sums = {c + network.cost[i] for c in sums for w, i in network.g.out[a] if w == b}
    return sums


def test_the_cheaper_of_two_doubled_arrows_wins() -> None:
    d = dijkstra(ROADS, 0)
    assert d.cost == [0, 1, 3, None]
    assert d.previous == [None, 0, 1, None]
    assert d.path_to(2) == [0, 1, 2]
    assert d.path_to(3) is None
    assert dijkstra_with_settled(ROADS, 0) == (d, [0, 1, 2])


def test_ties_go_to_the_lower_vertex_id() -> None:
    assert dijkstra_with_settled(TIE, 0)[1] == [0, 1, 2]
    # Both 1 and 2 cost 1 from 0, and both reach 3 at cost 2: 3 keeps 1, settled first, as its
    # previous vertex, since a previous vertex changes only on a strict drop.
    d, settled = dijkstra_with_settled(DIAMOND, 0)
    assert settled == [0, 1, 2, 3]
    assert d.cost == [0, 1, 1, 2]
    assert d.previous == [None, 0, 0, 1]
    # The printed loop and the walk to the goal keep the same rule.
    assert dijkstra(DIAMOND, 0) == d
    assert dijkstra_to(DIAMOND, 0, 3) == d


def test_a_loop_changes_nothing() -> None:
    d = dijkstra(LOOP, 0)
    assert d.cost == [0]
    assert d.previous == [None]


def test_zero_cost_arrows() -> None:
    g = Digraph(3, [(0, 1), (1, 2), (0, 2)])
    d = dijkstra(Network(g, [0, 0, 0]), 0)
    assert d.cost == [0, 0, 0]
    assert d.previous == [None, 0, 0]


def test_an_arrow_below_zero_gives_a_wrong_cost() -> None:
    # The box's Assumes: vertex 1 is settled at cost 1 before 0 -> 2 -> 1 (cost 0) is seen, and
    # the arrow 2 -> 1 into it is never tried. Nothing checks the costs.
    d, settled = dijkstra_with_settled(PROBE, 0)
    assert d.cost == [0, 1, 2]
    assert d.previous == [None, 0, 0]
    assert settled == [0, 1, 2]
    assert naive.cheapest(PROBE, 0) == [0, 0, 2]
    assert dijkstra(PROBE, 0) == d


def test_the_walk_to_one_goal_stops_once_the_goal_is_settled() -> None:
    # 0 -> 1 -> 2 -> 3, each arrow costing 1: with goal 1, the walk stops before 1's arrow is
    # tried, so 2 is never reached.
    g = Digraph(4, [(0, 1), (1, 2), (2, 3)])
    network = Network(g, [1, 1, 1])
    d = dijkstra_to(network, 0, 1)
    assert d.cost == [0, 1, None, None]
    assert d.path_to(1) == [0, 1]
    assert dijkstra_to(network, 0, 3) == dijkstra(network, 0)
    # A goal that cannot be reached: the walk runs to its end.
    assert dijkstra_to(network, 2, 0) == dijkstra(network, 2)
    assert dijkstra_to(network, 2, 0).cost[0] is None
    # The goal is the start: nothing past it is tried.
    assert dijkstra_to(network, 0, 0).cost == [0, None, None, None]


def test_the_start_and_the_goal_must_be_vertices() -> None:
    with pytest.raises(IndexError):
        dijkstra(ROADS, 4)
    with pytest.raises(IndexError):
        dijkstra(ROADS, -1)
    with pytest.raises(IndexError):
        dijkstra_to(ROADS, 0, 4)
    with pytest.raises(IndexError):
        dijkstra_with_settled(ROADS, 4)
    with pytest.raises(IndexError):
        dijkstra(Network(Digraph(0, []), []), 0)


@given(network_and_vertex())
def test_every_cost_is_the_cheapest(case: tuple[Network, int]) -> None:
    network, start = case
    d = dijkstra(network, start)
    assert d.cost == naive.cheapest(network, start)
    for v in range(network.g.n):
        path = d.path_to(v)
        assert (path is None) == (d.cost[v] is None)
        if path is not None:
            assert path[0] == start and path[-1] == v and len(set(path)) == len(path)
            assert d.cost[v] in path_costs(network, path)


@given(network_and_vertex())
def test_the_three_entry_points_agree(case: tuple[Network, int]) -> None:
    network, start = case
    d, settled = dijkstra_with_settled(network, start)
    assert d == dijkstra(network, start)
    reached = [v for v in range(network.g.n) if d.cost[v] is not None]
    assert sorted(settled) == reached
    for goal in range(network.g.n):
        to = dijkstra_to(network, start, goal)
        if goal in settled:
            # Every vertex settled up to the goal has its final cost and previous vertex.
            for v in settled[:settled.index(goal) + 1]:
                assert (to.cost[v], to.previous[v]) == (d.cost[v], d.previous[v])
        else:
            assert to == d


@given(network_and_vertex())
def test_with_every_arrow_costing_one_the_costs_are_the_fewest_arrows(
        case: tuple[Network, int]) -> None:
    network, start = case
    g = network.g
    assert dijkstra(Network(g, [1] * len(g.arrows)), start).cost == bfs(g, start).cost


@given(network_and_vertex(low=-5, high=5))
def test_whatever_the_arrows_cost_the_paths_back_are_real(case: tuple[Network, int]) -> None:
    # Only the cheapest costs need the box's Assumes: an unreached vertex is reported, and each
    # path back is a path from the start that costs exactly the reported cost, negative or not.
    network, start = case
    d = dijkstra(network, start)
    cheapest = naive.cheapest(network, start)
    for v in range(network.g.n):
        assert (d.cost[v] is None) == (cheapest[v] is None)
        path = d.path_to(v)
        if path is not None:
            assert path[0] == start and path[-1] == v and len(set(path)) == len(path)
            assert d.cost[v] in path_costs(network, path)


def twin(network: Network, start: int, goal: int | None = None) -> tuple[list[int], int]:
    """The arrow ids whose costs `State`'s walk reads, in order, and how many entries it pushes
    after the start's, stopped as `dijkstra_to` stops when a goal is given."""
    counted = Network(network.g, network.cost)
    costs = ReadCosts(network.cost)
    counted.cost = costs
    state = State.start(counted, start)
    while state.queue:
        if state.queue[0][1] == goal and goal not in state.settled:
            break
        state.step(counted)
    return costs.read, state.pushed - 1


def test_an_old_entry_is_skipped_not_its_row_tried_again() -> None:
    # Two arrows 0 -> 1, the dearer listed first: 1 is pushed at 2, then at 1, and settled at 1.
    # Its old entry at 2 is skipped as it comes off the queue, so 1 -> 2 is tried once; three
    # entries are pushed, one per drop.
    doubled = Network(Digraph(3, [(1, 2), (0, 1), (0, 1)]), [1, 2, 1])
    assert work(lambda n: dijkstra(n, 0), doubled) == ([1, 2, 0], 3)
    assert work(lambda n: dijkstra_to(n, 0, 2), doubled) == ([1, 2, 0], 3)


@given(network_and_vertex())
def test_the_heap_loops_try_each_arrow_once_and_push_only_on_a_drop(
        case: tuple[Network, int]) -> None:
    # The same arrows tried in the same order as `State`'s walk, none twice, and one entry pushed
    # per strict drop of a known cost: an old entry is skipped, not its row tried again.
    network, start = case
    read, pushed = work(lambda n: dijkstra(n, start), network)
    assert (read, pushed) == twin(network, start)
    assert len(set(read)) == len(read)
    for goal in range(network.g.n):
        read, pushed = work(partial(dijkstra_to, start=start, goal=goal), network)
        assert (read, pushed) == twin(network, start, goal)
