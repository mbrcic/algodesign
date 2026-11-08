"""Cheapest paths in a graph with no cycle: the answers pinned on the networks the Lean's kernel
checks in `AlgoDesignTests/Paths.lean` (`neg`, the doubled arrows, the loop, the cycle of two),
the walk's states ending at the answer, and the answers judged by trying every path on random
small graphs with no cycle, negative costs included.
"""

from __future__ import annotations

import copy

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Digraph, Stuck, topological_order
from algodesign.paths import Distances, Network, dag_paths, naive
from algodesign.paths.dag import State

from .strategies import network_and_vertex

# A negative arrow: the way round through 2 costs less than the direct arrow to 1.
NEG = Network(Digraph(4, [(0, 1), (0, 2), (2, 1), (1, 3)]), [5, 2, -4, 1])


def states(network: Network, start: int) -> list[State]:
    """Every state of the walk in Kahn's order, the start first, one more per vertex taken."""
    order = topological_order(network.g)
    assert not isinstance(order, Stuck)
    state = State.start(network, start, order)
    trail = [copy.deepcopy(state)]
    while state.todo:
        state.step(network)
        trail.append(copy.deepcopy(state))
    return trail


def test_a_negative_arrow_gives_the_cheaper_way_round() -> None:
    assert topological_order(NEG.g) == [0, 2, 1, 3]
    d = dag_paths(NEG, 0)
    assert d == Distances([0, -2, 2, -1], [None, 2, 0, 1])
    assert d.cost == naive.cheapest(NEG, 0)
    assert d.path_to(3) == [0, 2, 1, 3]
    # 1 is known at 5 from 0, then at -2 from 2.
    trail = states(NEG, 0)
    assert (trail[1].known[1], trail[2].known[1]) == (5, -2)


def test_the_walk_ends_at_the_answer() -> None:
    trail = states(NEG, 0)
    assert len(trail) == 5
    assert (trail[-1].done, trail[-1].todo) == ([0, 2, 1, 3], [])
    assert Distances(trail[-1].known, trail[-1].previous) == dag_paths(NEG, 0)


def test_a_vertex_that_cannot_be_reached_is_reported_and_its_row_is_not_tried() -> None:
    assert dag_paths(NEG, 2) == Distances([None, -4, 0, -3], [None, 2, None, 1])
    # 1 -> 2 is out of reach from 0: 1 is taken with no cost, and 2 stays unknown.
    d = dag_paths(Network(Digraph(3, [(1, 2)]), [1]), 0)
    assert isinstance(d, Distances) and d.cost == [0, None, None]


def test_of_two_arrows_between_the_same_vertices_the_cheaper_counts() -> None:
    d = dag_paths(Network(Digraph(2, [(0, 1), (0, 1)]), [5, 3]), 0)
    assert d == Distances([0, 3], [None, 0])


def test_an_equal_cost_keeps_the_previous_vertex() -> None:
    g = Digraph(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
    d = dag_paths(Network(g, [1, 1, 1, 1]), 0)
    assert isinstance(d, Distances) and d.previous == [None, 0, 0, 1]
    # The walk's states keep the same rule: 3 is reached from 1 first, and 2 only ties it.
    assert states(Network(g, [1, 1, 1, 1]), 0)[-1].previous == [None, 0, 0, 1]


def test_a_loop_or_a_cycle_gives_kahns_stuck_set() -> None:
    assert dag_paths(Network(Digraph(2, [(0, 1), (1, 1)]), [1, 1]), 0) == Stuck([1])
    cycle = Network(Digraph(3, [(0, 1), (1, 0), (1, 2)]), [1, 1, 1])
    assert dag_paths(cycle, 0) == Stuck([0, 1, 2])


def test_a_start_out_of_range_is_refused_before_the_order_is_sought() -> None:
    with pytest.raises(IndexError, match="start 2 out of range"):
        dag_paths(Network(Digraph(2, [(0, 1), (1, 0)]), [1, 1]), 2)


def test_every_vertex_and_every_arrow_is_looked_at_once() -> None:
    done = states(NEG, 0)[-1].done
    assert sum(len(NEG.g.out[v]) + 1 for v in done) == NEG.g.n + len(NEG.g.arrows)


@st.composite
def dags(draw: st.DrawFn) -> tuple[Network, int]:
    """A network with no cycle: every arrow from a lower position to a higher one of a shuffled
    order of the vertices, doubled arrows and negative costs included; and a start."""
    n = draw(st.integers(1, 6))
    rank = draw(st.permutations(range(n)))
    pairs = draw(st.lists(st.tuples(st.integers(0, n - 1), st.integers(0, n - 1)), max_size=10))
    arrows = [(rank[a], rank[b]) for a, b in pairs if a < b]
    cost = draw(st.lists(st.integers(-5, 5), min_size=len(arrows), max_size=len(arrows)))
    return Network(Digraph(n, arrows), cost), draw(st.integers(0, n - 1))


@given(dags())
def test_on_any_graph_with_no_cycle_the_costs_are_the_cheapest_and_the_walk_ends_there(
        case: tuple[Network, int]) -> None:
    network, start = case
    d = dag_paths(network, start)
    assert isinstance(d, Distances)
    assert d.cost == naive.cheapest(network, start)
    for v in range(network.g.n):
        path = d.path_to(v)
        assert (path is None) == (d.cost[v] is None)
    trail = states(network, start)
    assert (trail[-1].known, trail[-1].previous) == (d.cost, d.previous)


@given(network_and_vertex(-5, 5))
def test_on_any_graph_the_walk_answers_or_gives_kahns_stuck_set(case: tuple[Network, int]) -> None:
    network, start = case
    d, order = dag_paths(network, start), topological_order(network.g)
    if isinstance(order, Stuck):
        assert d == order
    else:
        assert isinstance(d, Distances) and d.cost == naive.cheapest(network, start)
