"""Dijkstra's walk, step by step: the Lean's `Valid` and `WellFormed` after every step on random
small networks with no negative arrow, the true cheapest costs taken from trying every path;
the states the Lean's kernel checks in `AlgoDesignTests/Paths.lean`, pinned; and one broken state
per piece, each named by its label.
"""

from __future__ import annotations

import copy

from hypothesis import given

from algodesign.graphs import Digraph
from algodesign.paths import Network, dijkstra_with_settled, naive
from algodesign.paths.dijkstra import State, dijkstra

from .strategies import network_and_vertex
from .test_dijkstra import LOOP, PROBE, ROADS, TIE


def states(network: Network, start: int) -> list[State]:
    """Every state of the walk, the start first, one more per step until the queue is empty."""
    state = State.start(network, start)
    trail = [copy.deepcopy(state)]
    while state.queue:
        state.step(network)
        trail.append(copy.deepcopy(state))
    return trail


def check(network: Network, start: int, state: State) -> str | None:
    """`check_valid` with the true cheapest costs, over all paths and through the settled."""
    return state.check_valid(network, start, naive.cheapest(network, start),
                             naive.cheapest_through(network, start, state.settled))


def tried(network: Network, state: State) -> list[int]:
    """The arrows the walk has tried: those out of each settled vertex, in its row's order (Lean
    `tried`)."""
    return [i for v in state.settled for _, i in network.g.out[v]]


@given(network_and_vertex())
def test_every_state_of_the_walk_is_valid(case: tuple[Network, int]) -> None:
    network, start = case
    trail = states(network, start)
    assert all(check(network, start, state) is None for state in trail)
    last = trail[-1]
    assert dijkstra_with_settled(network, start) == (dijkstra(network, start), last.settled)
    # The cost line (Lean `dijkstra_cost`): each arrow tried once, the queue given at most one
    # entry per arrow tried and one for the start; so at most one more than the arrows
    # (`pushed_final_le`), and no more steps than entries.
    assert len(set(tried(network, last))) == len(tried(network, last))
    assert last.pushed <= len(tried(network, last)) + 1
    assert last.pushed <= len(network.g.arrows) + 1
    assert len(trail) - 1 == last.pushed


def test_the_kernel_checked_states() -> None:
    roads = states(ROADS, 0)
    assert len(roads) == 6 and roads[-1].queue == []
    assert roads[-1].pushed == 5
    assert roads[-1].known == [0, 1, 3, None]
    assert roads[-1].previous == [None, 0, 1, None]
    assert tried(ROADS, roads[-1]) == [0, 1, 3, 2, 4]
    assert all(check(ROADS, 0, state) is None for state in roads)

    tie = states(TIE, 0)
    assert tie[1].queue == [(1, 1), (1, 2)]
    assert all(check(TIE, 0, state) is None for state in tie)

    loop = states(LOOP, 0)
    assert all(check(LOOP, 0, state) is None for state in loop)
    assert loop[-1].known == [0] and loop[-1].previous == [None]

    probe = states(PROBE, 0)
    assert probe[1].settled == [0]
    assert probe[1].queue == [(1, 1), (2, 2)]
    assert check(PROBE, 0, probe[0]) is None
    assert check(PROBE, 0, probe[1]) is None
    # Vertex 1 is settled at cost 1; its cheapest path costs 0.
    assert check(PROBE, 0, probe[2]) == "invariant 1 (settled_are_cheapest)"
    assert probe[-1].is_previous_leads_back(PROBE, 0)


def test_an_empty_queue_is_left_as_it_is() -> None:
    state = states(ROADS, 0)[-1]
    before = copy.deepcopy(state)
    state.step(ROADS)
    assert state == before


# 0 -> 1 costs 1, 1 -> 2 costs 1, 0 -> 2 costs 5; after the first step, 0 is settled, 1 and 2 are
# known at 1 and 5 from 0, and both are queued.
A = Network(Digraph(3, [(0, 1), (1, 2), (0, 2)]), [1, 1, 5])


def after_one_step() -> State:
    return State(settled=[0], known=[0, 1, 5], previous=[None, 0, 0], queue=[(1, 1), (5, 2)],
                pushed=3)


def test_each_broken_state_names_its_piece() -> None:
    assert states(A, 0)[1] == after_one_step()
    assert check(A, 0, after_one_step()) is None

    twice = after_one_step()
    twice.settled = [0, 0]
    assert check(A, 0, twice) == "invariant 1 (settled_are_cheapest)"

    # The start forgotten: nothing settled, and the start not known. Invariant 2 is the only
    # piece that sees it; every other piece reads only known costs.
    forgot = State(settled=[], known=[None, None, None], previous=[None, None, None], queue=[],
                  pushed=0)
    assert check(A, 0, forgot) == "invariant 2 (known_is_cheapest_through_settled)"

    # Both 0 and 1 settled at their cheapest, but 1 listed first.
    two = states(A, 0)[2]
    assert two.settled == [0, 1] and check(A, 0, two) is None
    two.settled = [1, 0]
    assert check(A, 0, two) == "not in the box (start_settled_first)"

    # 0 -> 2 and 2 -> 1 cost nothing, 1 -> 3 costs 1: with 0 and 1 settled at their cheapest, the
    # arrow 1 -> 3 was never tried, so 3 is not known. Invariant 2 still holds, since 1's only path
    # passes 2, which is not settled; the previous vertices break too, but later in the order.
    zero = Network(Digraph(4, [(0, 2), (2, 1), (1, 3)]), [0, 0, 1])
    untried = State(settled=[0, 1], known=[0, 0, 0, None], previous=[None, 2, 0, None],
                   queue=[(0, 2)], pushed=3)
    assert check(zero, 0, untried) == "not in the box (settled_rows_tried)"

    missing = after_one_step()
    missing.queue = [(1, 1)]
    assert check(A, 0, missing) == "not in the box (queue_holds_known)"
    unsorted = after_one_step()
    unsorted.queue = [(5, 2), (1, 1)]
    assert check(A, 0, unsorted) == "not in the box (queue_holds_known)"
    below = after_one_step()
    below.queue = [(0, 2), (1, 1), (5, 2)]
    assert check(A, 0, below) == "not in the box (queue_holds_known)"
    # An entry for a vertex past the graph, its cost recorded past the vertices: only the piece
    # that reads the entry's vertex against the graph sees it.
    past = after_one_step()
    past.known = [0, 1, 5, 9]
    past.queue = [(1, 1), (5, 2), (9, 3)]
    cheapest, through = naive.cheapest(A, 0), naive.cheapest_through(A, 0, past.settled)
    assert past.is_settled_are_cheapest(cheapest)
    assert past.is_known_is_cheapest_through_settled(A, through)
    assert past.is_start_settled_first(0)
    assert past.is_settled_rows_tried(A)
    assert not past.is_queue_holds_known(A)
    assert past.is_previous_leads_back(A, 0)

    # 2 records 1 as its previous vertex, but 1 is not settled.
    through_unsettled = after_one_step()
    through_unsettled.previous = [None, 0, 1]
    assert check(A, 0, through_unsettled) == "not in the box (previous_leads_back)"
    start_has_one = after_one_step()
    start_has_one.previous = [1, 0, 0]
    assert check(A, 0, start_has_one) == "not in the box (previous_leads_back)"


def test_each_piece_reads_any_state_without_failing() -> None:
    # Vertices outside the graph, in every list the pieces read.
    odd = State(settled=[7, -1], known=[0], previous=[9], queue=[(0, 8), (3, -2)], pushed=0)
    assert not odd.is_settled_are_cheapest([0, 1, 5])
    assert odd.is_known_is_cheapest_through_settled(A, [0, 1, 5]) is False
    assert not odd.is_start_settled_first(0)
    assert odd.is_settled_rows_tried(A)
    assert not odd.is_queue_holds_known(A)
    assert not odd.is_previous_leads_back(A, 0)
    assert not odd.is_valid(A, 0, [0, 1, 5], [0, 1, 5])
    looped = after_one_step()
    looped.previous = [None, 2, 1]
    assert not looped.is_previous_leads_back(A, 0)
