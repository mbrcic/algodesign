"""Bellman-Ford's method: the answers pinned on small networks (the Rust walks the same rows in the
same order, so the previous vertices, the rounds and the cycles must match too), and judged on
random small networks with negative arrows against trying every path and every cycle.
"""

from __future__ import annotations

from itertools import pairwise

import pytest
from hypothesis import given

from algodesign.graphs import Digraph
from algodesign.paths import Distances, NegativeCycle, Network, bellman_ford_with_rounds, naive
from algodesign.paths.bellman_ford import bellman_ford
from algodesign.paths.dijkstra import dijkstra

from .strategies import network_and_vertex

# A three-vertex map with one negative arrow: 0 -> 1 costs 1, 0 -> 2 costs 2, 2 -> 1 costs -2.
PROBE = Network(Digraph(3, [(0, 1), (0, 2), (2, 1)]), [1, 2, -2])
# 0 -> 1 (1), 1 -> 2 (-3), 2 -> 1 (2): the cycle 1 -> 2 -> 1 totals -1.
LOOPED = Network(Digraph(3, [(0, 1), (1, 2), (2, 1)]), [1, -3, 2])


def network(n: int, arrows: list[tuple[int, int, int]]) -> Network:
    return Network(Digraph(n, [(a, b) for a, b, _ in arrows]), [c for _, _, c in arrows])


def cheapest_hops(net: Network, path: list[int]) -> int:
    """The cost of a path's vertices, taking the cheapest arrow of each hop."""
    return sum(min(net.cost[i] for w, i in net.g.out[a] if w == b) for a, b in pairwise(path))


def test_on_the_probe_vertex_1_costs_0_through_vertex_2() -> None:
    answer, rounds, tried = bellman_ford_with_rounds(PROBE, 0)
    assert answer == Distances([0, 0, 2], [None, 2, 0])
    assert (rounds, tried) == (2, 6)
    assert bellman_ford(PROBE, 0) == answer
    assert isinstance(answer, Distances) and answer.path_to(1) == [0, 2, 1]


def test_a_cost_lowered_earlier_in_the_round_is_used_later_in_it() -> None:
    # 1 gets its cost before its row is tried, so 2 is reached in the first round too.
    net = network(3, [(0, 1, 1), (1, 2, 1)])
    assert bellman_ford_with_rounds(net, 0) == (Distances([0, 1, 2], [None, 0, 1]), 2, 4)


def test_the_rounds_stop_after_the_first_that_lowers_nothing() -> None:
    net = network(5, [(0, 1, 5)])
    assert bellman_ford_with_rounds(net, 0) == (
        Distances([0, 5, None, None, None], [None, 0, None, None, None]), 2, 2)
    assert bellman_ford_with_rounds(network(2, []), 1)[1:] == (1, 0)


def test_an_equal_cost_keeps_the_previous_vertex() -> None:
    net = network(4, [(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)])
    assert bellman_ford(net, 0) == Distances([0, 1, 1, 2], [None, 0, 0, 1])


def test_of_two_arrows_between_the_same_vertices_the_cheaper_counts() -> None:
    for costs in ([5, -3], [-3, 5]):
        net = Network(Digraph(2, [(0, 1), (0, 1)]), costs)
        assert bellman_ford(net, 0) == Distances([0, -3], [None, 0])


def test_a_loop_below_zero_is_a_cycle_of_one_arrow() -> None:
    assert bellman_ford(network(2, [(0, 1, 1), (1, 1, -1)]), 0) == NegativeCycle([1, 1])
    assert bellman_ford(network(1, [(0, 0, -1)]), 0) == NegativeCycle([0, 0])
    assert bellman_ford(network(1, [(0, 0, 0)]), 0) == Distances([0], [None])


def test_a_cycle_below_zero_the_start_reaches_is_the_answer() -> None:
    assert bellman_ford_with_rounds(LOOPED, 0) == (NegativeCycle([2, 1, 2]), 3, 9)
    tail = network(4, [(0, 1, 1), (1, 2, -3), (2, 1, 2), (2, 3, 0)])
    answer = bellman_ford(tail, 0)
    assert isinstance(answer, NegativeCycle)
    assert naive.is_cycle_below_zero(tail, 0, answer.vertices)


def test_a_cycle_below_zero_the_start_does_not_reach_changes_nothing() -> None:
    net = network(4, [(0, 1, 1), (2, 3, -5), (3, 2, 1), (2, 0, 1)])
    assert not naive.reaches_cycle_below_zero(net, 0)
    assert bellman_ford(net, 0) == Distances([0, 1, None, None], [None, 0, None, None])
    assert isinstance(bellman_ford(net, 2), NegativeCycle)


def test_a_start_out_of_range_raises() -> None:
    with pytest.raises(IndexError, match="start 3 out of range"):
        bellman_ford(PROBE, 3)


@given(network_and_vertex(-4, 6))
def test_the_answer_is_the_cheapest_or_a_cycle_below_zero(case: tuple[Network, int]) -> None:
    net, start = case
    answer, rounds, tried = bellman_ford_with_rounds(net, start)
    assert rounds <= net.g.n and tried == rounds * len(net.g.arrows)
    if isinstance(answer, NegativeCycle):
        assert naive.reaches_cycle_below_zero(net, start)
        assert naive.is_cycle_below_zero(net, start, answer.vertices)
        return
    assert not naive.reaches_cycle_below_zero(net, start)
    assert answer.cost == naive.cheapest(net, start)
    for v in range(net.g.n):
        path = answer.path_to(v)
        if path is None:
            assert answer.cost[v] is None
            continue
        assert path[0] == start and len(set(path)) == len(path)
        assert cheapest_hops(net, path) == answer.cost[v]


@given(network_and_vertex(0, 3))
def test_with_no_arrow_below_zero_the_costs_are_dijkstras(case: tuple[Network, int]) -> None:
    net, start = case
    answer = bellman_ford(net, start)
    assert isinstance(answer, Distances)
    assert answer.cost == dijkstra(net, start).cost
