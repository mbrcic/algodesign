"""Bellman-Ford's rounds, in place: the Lean's `Valid` and `WellFormed` after every round on random
small networks with negative arrows, the answers about paths taken from `naive`; the rounds
against round by round on one network; and one broken state per piece, each failing that piece
alone.
"""

from __future__ import annotations

from hypothesis import given

from algodesign.graphs import Digraph
from algodesign.paths import Network, bellman_ford_with_rounds, naive
from algodesign.paths.bellman_ford import State

from .strategies import network_and_vertex
from .test_bellman_ford import PROBE, network

LABELS = ("invariant 1 (cost_is_walk_at_most_cheapest)", "not in the box (path_within_tries)",
          "not in the box (previous_arrow_fits)", "not in the box (recorded_cycles_below_zero)",
          "not in the box (no_previous_keeps_start)")


def states(net: Network, start: int) -> list[State]:
    """Every state of the rounds: the start, then one per round, until a round lowers nothing or
    one per vertex has run."""
    trail = [State.start(net, start)]
    while trail[-1].rounds < net.g.n:
        trail.append(trail[-1].round(net))
        if trail[-1].lowered is None:
            break
    return trail


def walks(net: Network, start: int, tried: int) -> list[set[int]]:
    """The costs of every path of at most `naive.walk_arrows_after` arrows, for `tried`."""
    return naive.walk_costs(net, start, naive.walk_arrows_after(net, tried))


def check(net: Network, start: int, state: State) -> str | None:
    """`check_valid` with the costs of the paths it needs, and the cheapest over paths of at most
    the rounds arrows."""
    return state.check_valid(net, start, walks(net, start, state.tried),
                             naive.walk_costs(net, start, state.tried),
                             naive.cheapest_walks(net, start, state.rounds)[state.rounds])


def failing(net: Network, start: int, state: State) -> list[str]:
    """The labels of every piece the state fails, not only the first."""
    cheapest = naive.cheapest_walks(net, start, state.rounds)[state.rounds]
    pieces = [state.is_cost_is_walk_at_most_cheapest(net, walks(net, start, state.tried),
                                                     cheapest),
              state.is_path_within_tries(net, naive.walk_costs(net, start, state.tried)),
              state.is_previous_arrow_fits(net), state.is_recorded_cycles_below_zero(net),
              state.is_no_previous_keeps_start(net, start)]
    return [label for label, ok in zip(LABELS, pieces) if not ok]


@given(network_and_vertex(-4, 6))
def test_every_state_of_the_rounds_is_valid(case: tuple[Network, int]) -> None:
    net, start = case
    trail = states(net, start)
    last = trail[-1]
    # The paths for the last state are the most any state needs; the check takes them for all.
    room = walks(net, start, last.tried)
    by_arrows = naive.cheapest_walks(net, start, last.rounds)
    for k, state in enumerate(trail):
        within = naive.walk_costs(net, start, state.tried)
        assert state.check_valid(net, start, room, within, by_arrows[k]) is None
        assert state.rounds == k
    assert bellman_ford_with_rounds(net, start)[1:] == (last.rounds, last.tried)
    assert last.tried == last.rounds * len(net.g.arrows)


def test_the_probe_in_place() -> None:
    trail = states(PROBE, 0)
    assert [s.cost for s in trail] == [[0, None, None], [0, 0, 2], [0, 0, 2]]
    assert [s.lowered for s in trail] == [None, 1, None]


def test_in_place_differs_from_round_by_round() -> None:
    # Round 1 tries 2 -> 1 with 2's new cost: 1 costs -1 after it, where a round reading only the
    # last round's costs would leave 4, the cheapest over paths of one arrow.
    net = network(4, [(0, 1, 4), (0, 2, 2), (2, 1, -3), (1, 3, 1), (2, 3, 5)])
    trail = states(net, 0)
    assert [s.cost for s in trail] == [[0, None, None, None], [0, -1, 2, 5], [0, -1, 2, 0],
                                       [0, -1, 2, 0]]
    assert naive.cheapest_walks(net, 0, 1)[1] == [0, 4, 2, None]
    assert (trail[-1].rounds, trail[-1].tried) == (3, 15)
    assert all(check(net, 0, s) is None for s in trail)


def test_a_loop_that_lowers_its_vertex_is_read_by_the_rest_of_its_row() -> None:
    net = network(2, [(0, 0, -1), (0, 1, 0)])
    assert states(net, 0)[1].cost == [-1, -1]


def test_each_broken_state_fails_its_piece_alone() -> None:
    net = network(3, [(0, 1, 1), (1, 2, 1), (0, 2, 5)])
    good = State([0, 1, 2], [None, 0, 1], 1, 2, 3)
    assert check(net, 0, good) is None
    assert states(net, 0)[1] == good
    # After two rounds 2 still at 5, though 0 -> 1 -> 2 costs 2.
    assert failing(net, 0, State([0, 1, 5], [None, 0, 0], 2, 2, 6)) == [LABELS[0]]
    # Before any round, 1 at 3, the cost of a path of one arrow, though no arrow has been tried.
    two = Network(Digraph(2, [(0, 1), (0, 1)]), [1, 3])
    assert failing(two, 0, State([0, 3], [None, 0], 0, None, 0)) == [LABELS[1]]
    assert check(two, 0, State([0, 3], [None, 0], 0, None, 1)) is None
    # 1 records 2, but no arrow leads from 2 to 1.
    assert failing(net, 0, State([0, 1, 5], [None, 2, 0], 1, 2, 3)) == [LABELS[2]]
    # 2 records 0, but 0's cost and the arrow 0 -> 2 make 5, more than 2's cost.
    assert failing(net, 0, State([0, 1, 2], [None, 0, 0], 2, 2, 6)) == [LABELS[2]]
    # 1 records itself round a loop of total zero.
    level = network(2, [(0, 1, 1), (1, 1, 0)])
    assert failing(level, 0, State([0, 1], [None, 1], 1, None, 2)) == [LABELS[3]]
    # 1 and 2 record each other round a cycle of total zero.
    level = network(3, [(0, 1, 1), (1, 2, -2), (2, 1, 2)])
    assert failing(level, 0, State([0, 1, -1], [None, 2, 1], 2, None, 6)) == [LABELS[3]]
    # 1 has a cost but records no previous vertex.
    assert failing(net, 0, State([0, 1, 5], [None, None, 0], 1, 2, 3)) == [LABELS[4]]


def test_a_cycle_the_records_close_below_zero_passes() -> None:
    net = network(3, [(0, 1, 1), (1, 2, -3), (2, 1, 2)])
    last = states(net, 0)[-1]
    assert last.previous == [None, 2, 1]
    assert last.is_recorded_cycles_below_zero(net)
    assert not last.is_recorded_cycles_below_zero(network(3, [(0, 1, 1), (1, 2, -3), (2, 1, 3)]))
    assert last.is_recorded_cycles_below_zero(
        network(3, [(0, 1, 1), (1, 2, -3), (2, 1, 3), (2, 1, 2)]))


def test_the_pieces_answer_on_parts_of_the_wrong_size() -> None:
    net = network(2, [(0, 1, 1)])
    short = State([0], [7], 1, None, 0)
    assert not short.is_cost_is_walk_at_most_cheapest(net, [], [])
    assert not short.is_path_within_tries(net, [])
    assert not short.is_previous_arrow_fits(net)
    assert short.is_recorded_cycles_below_zero(net)
    assert short.is_no_previous_keeps_start(net, 0)
    assert not short.is_valid(net, 0, [], [], [])
