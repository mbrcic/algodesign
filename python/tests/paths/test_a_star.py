"""A*: the examples the Lean's kernel checks in `AlgoDesignTests/Paths.lean` (the map `roads` with
the estimates `exact` and `overeager`, and the zero estimate), pinned; the search against
Dijkstra's walk to the goal and against trying every path on random small networks with consistent
estimates, the Lean's `Valid` and `WellFormed` after every step; one broken case per piece, each
named by its label.
"""

from __future__ import annotations

import copy
from itertools import pairwise

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Digraph
from algodesign.paths import Network, a_star_with_settled, dijkstra_to, naive
from algodesign.paths.a_star import (
    a_star,
    changed,
    check_valid,
    is_estimate_is_consistent,
    is_walk_is_cheapest_paths_on_changed_costs,
    shifted,
    start_state,
    step,
)
from algodesign.paths.dijkstra import State, dijkstra_with_settled

from .counting import ReadCosts, work
from .strategies import networks

# 0 -> 1 costs 1, 1 -> 2 costs 1, 0 -> 2 costs 3, 2 -> 3 costs 5, 0 -> 4 costs 1; the goal is 3.
ROADS = Network(Digraph(5, [(0, 1), (1, 2), (0, 2), (2, 3), (0, 4)]), [1, 1, 3, 5, 1])
# The cheapest cost still to go from each vertex, and 9 at 4, which reaches no goal.
EXACT = [7, 6, 5, 0, 9]
# Never above the cost still to go, but 1 -> 2 costs 1 while the estimate drops by 5.
OVEREAGER = [0, 5, 0, 0, 0]


def states(network: Network, start: int, goal: int, estimate: list[int]) -> list[State]:
    """Every state of the search, the start first, one more per step, until the goal is at the
    front of the queue unsettled or the queue is empty; the stopped state, its goal row untried, is
    not one."""
    state = start_state(network, estimate, start)
    trail = [copy.deepcopy(state)]
    while state.queue and not (state.queue[0][1] == goal and goal not in state.settled):
        step(network, estimate, state)
        trail.append(copy.deepcopy(state))
    return trail


def check(network: Network, start: int, goal: int, estimate: list[int], state: State) -> str | None:
    """`check_valid` with the true cheapest costs on the changed costs, over all paths and through
    the settled."""
    on = changed(network, estimate)
    return check_valid(network, start, goal, estimate, state, naive.cheapest(on, start),
                       naive.cheapest_through(on, start, state.settled))


def dijkstra_to_settled(network: Network, start: int, goal: int) -> list[int]:
    """The vertices Dijkstra's walk to `goal` settles: the whole walk's, up to the goal."""
    settled = dijkstra_with_settled(network, start)[1]
    return settled[:settled.index(goal) + 1] if goal in settled else settled


def test_with_a_consistent_estimate_the_search_settles_only_the_path() -> None:
    assert is_estimate_is_consistent(ROADS, 3, EXACT)
    d, settled = a_star_with_settled(ROADS, 0, 3, EXACT)
    assert d.cost[3] == 7 == naive.cheapest(ROADS, 0)[3]
    assert (d.previous[3], d.previous[2]) == (2, 1)
    assert d.path_to(3) == [0, 1, 2, 3]
    assert settled == [0, 1, 2, 3]
    assert a_star(ROADS, 0, 3, EXACT) == d
    # Dijkstra's walk to the goal settles 4 too.
    assert dijkstra_to_settled(ROADS, 0, 3) == [0, 1, 4, 2, 3]
    assert dijkstra_to(ROADS, 0, 3).cost[3] == 7


def test_every_state_of_the_search_on_the_map_is_valid() -> None:
    trail = states(ROADS, 0, 3, EXACT)
    assert len(trail) == 4
    assert all(check(ROADS, 0, 3, EXACT, state) is None for state in trail)
    last = trail[-1]
    assert last.settled == [0, 1, 2]
    assert last.known == [0, 1, 2, 7, 1]
    # Each key is the known cost plus the estimate: 3 at 7 + 0, 4 at 1 + 9.
    assert last.queue == [(7, 3), (8, 2), (10, 4)]
    assert last.pushed == 6


def test_an_estimate_that_never_overstates_but_is_not_consistent_gives_a_dearer_path() -> None:
    # The lesson of petgraph's issue #378.
    assert all(low <= exact for low, exact in zip(OVEREAGER[:4], EXACT[:4], strict=True))
    assert not is_estimate_is_consistent(ROADS, 3, OVEREAGER)
    # 2 is settled at 3 from the start before 1, and 1 -> 2 is never tried.
    d, settled = a_star_with_settled(ROADS, 0, 3, OVEREAGER)
    assert d.cost[3] == 8 and d.path_to(3) == [0, 2, 3]
    assert settled == [0, 4, 2, 1, 3]
    # The printed loop gives the same whole answer: 1 is not reopened, so 3 keeps 2 and cost 8.
    assert a_star(ROADS, 0, 3, OVEREAGER) == d
    assert naive.cheapest(ROADS, 0)[3] == 7
    first = states(ROADS, 0, 3, OVEREAGER)[0]
    assert check(ROADS, 0, 3, OVEREAGER, first) == "invariant 1 (estimate_is_consistent)"


def test_the_zero_estimate_is_dijkstras_walk_to_the_goal() -> None:
    for goal in range(5):
        d, settled = a_star_with_settled(ROADS, 0, goal, [0] * 5)
        assert d == dijkstra_to(ROADS, 0, goal)
        assert settled == dijkstra_to_settled(ROADS, 0, goal)


def test_an_old_entry_is_skipped_not_its_row_tried_again() -> None:
    # Two arrows 0 -> 1, the dearer listed first: 1 is pushed at 2, then at 1, and settled at 1.
    # Its old entry at 2 comes off the queue before the goal and is skipped, so 1 -> 2 is tried
    # once; three entries are pushed, one per drop.
    doubled = Network(Digraph(3, [(1, 2), (0, 1), (0, 1)]), [1, 2, 1])
    assert work(lambda n: a_star(n, 0, 2, [0] * 3), doubled) == ([1, 2, 0], 3)


def test_a_tie_on_cost_goes_to_the_smaller_vertex_number() -> None:
    # Both 1 and 2 cost 1 from 0, and both reach 3 at cost 2; 0's row lists 2 first. 1 is settled
    # first, and 3 keeps it as its previous vertex, since a previous vertex changes only on a
    # strict drop.
    diamond = Network(Digraph(4, [(0, 2), (0, 1), (2, 3), (1, 3)]), [1, 1, 1, 1])
    d, settled = a_star_with_settled(diamond, 0, 3, [0] * 4)
    assert settled == [0, 1, 2, 3]
    assert d.previous == [None, 0, 0, 1]
    assert a_star(diamond, 0, 3, [0] * 4) == d


def test_an_arrow_below_zero_is_fine_when_the_estimate_keeps_the_invariant() -> None:
    # 0 -> 1 costs -2, 1 -> 2 costs 5, 0 -> 2 costs 4; the estimate 3, 5, 0 drops by at most each
    # arrow, so the changed costs are 0, 0 and 1.
    network = Network(Digraph(3, [(0, 1), (1, 2), (0, 2)]), [-2, 5, 4])
    estimate = [3, 5, 0]
    assert is_estimate_is_consistent(network, 2, estimate)
    assert changed(network, estimate).cost == [0, 0, 1]
    d = a_star(network, 0, 2, estimate)
    assert d.cost[2] == 3 and d.path_to(2) == [0, 1, 2]
    assert all(check(network, 0, 2, estimate, state) is None
               for state in states(network, 0, 2, estimate))


def test_on_a_grid_a_good_estimate_settles_fewer_vertices() -> None:
    # Six by six, each step to a neighbor costs 1 both ways; from the top-left corner to the
    # top-right one, the estimate the steps left along the row and column.
    side = 6
    arrows = []
    for r in range(side):
        for c in range(side):
            if c + 1 < side:
                arrows += [(r * side + c, r * side + c + 1), (r * side + c + 1, r * side + c)]
            if r + 1 < side:
                arrows += [(r * side + c, (r + 1) * side + c), ((r + 1) * side + c, r * side + c)]
    network = Network(Digraph(side * side, arrows), [1] * len(arrows))
    goal = side - 1
    estimate = [v // side + (side - 1 - v % side) for v in range(side * side)]
    assert is_estimate_is_consistent(network, goal, estimate)
    d, settled = a_star_with_settled(network, 0, goal, estimate)
    assert d.cost[goal] == 5
    assert settled == [0, 1, 2, 3, 4, 5]
    # Dijkstra settles every vertex within four steps of the corner, fifteen, then the goal.
    assert len(dijkstra_to_settled(network, 0, goal)) == 16


def test_the_start_is_the_goal_and_a_goal_out_of_reach() -> None:
    d, settled = a_star_with_settled(ROADS, 0, 0, [0] * 5)
    assert settled == [0] and d.cost == [0, None, None, None, None]
    d, settled = a_star_with_settled(ROADS, 3, 0, [0] * 5)
    assert settled == [3] and d.cost[0] is None
    assert a_star(ROADS, 3, 0, [0] * 5) == d


def test_an_estimate_of_the_wrong_length_and_vertices_out_of_range() -> None:
    with pytest.raises(ValueError, match="4 estimates for 5 vertices"):
        a_star(ROADS, 0, 3, EXACT[:4])
    with pytest.raises(ValueError, match="6 estimates for 5 vertices"):
        a_star_with_settled(ROADS, 0, 3, [0] * 6)
    with pytest.raises(IndexError, match="goal 5 out of range"):
        a_star(ROADS, 0, 5, EXACT)
    with pytest.raises(IndexError, match="start 5 out of range"):
        a_star_with_settled(ROADS, 5, 3, EXACT)


def test_each_part_of_the_box_invariant_breaks_it_alone() -> None:
    assert not is_estimate_is_consistent(ROADS, 3, [7, 6, 5, 0, -1])
    assert not is_estimate_is_consistent(ROADS, 3, [7, 6, 5, 1, 9])
    assert not is_estimate_is_consistent(ROADS, 3, [8, 6, 5, 0, 9])
    # An estimate past the list counts as 0, as the Lean's; only the vertices' are read.
    assert is_estimate_is_consistent(ROADS, 3, [])
    assert is_estimate_is_consistent(ROADS, 3, [0, 0, 0, 0, 0, -1])


def test_a_broken_state_names_the_piece_not_in_the_box() -> None:
    last = states(ROADS, 0, 3, EXACT)[-1]
    # The key of 3 without its estimate is no longer the shifted walk's key.
    bad = copy.deepcopy(last)
    bad.queue = [(6, 3), (8, 2), (10, 4)]
    assert check(ROADS, 0, 3, EXACT, bad) == (
        "not in the box (walk_is_cheapest_paths_on_changed_costs)")
    on = changed(ROADS, EXACT)
    assert not is_walk_is_cheapest_paths_on_changed_costs(
        ROADS, 0, EXACT, bad, naive.cheapest(on, 0), naive.cheapest_through(on, 0, bad.settled))
    # A state with vertices past the lists is read without failing.
    odd = State(settled=[7], known=[0], previous=[9], queue=[(0, 8)], pushed=0)
    assert check(ROADS, 0, 3, EXACT, odd) == (
        "not in the box (walk_is_cheapest_paths_on_changed_costs)")


def test_the_shifted_state_is_dijkstras_on_the_changed_costs() -> None:
    on = changed(ROADS, EXACT)
    ours = [shifted(state, EXACT, EXACT[0]) for state in states(ROADS, 0, 3, EXACT)]
    walk = State.start(on, 0)
    theirs = [copy.deepcopy(walk)]
    for _ in ours[1:]:
        walk.step(on)
        theirs.append(copy.deepcopy(walk))
    assert ours == theirs
    assert a_star(ROADS, 0, 3, EXACT).previous == dijkstra_to(on, 0, 3).previous


@st.composite
def searches(draw: st.DrawFn) -> tuple[Network, int, int, list[int]]:
    """A network with no negative arrow, a start, a goal and a consistent estimate: the
    cheapest cost still to go scaled by p / 4 and rounded down, and one shared value, at least every
    other, where the goal is out of reach."""
    network = draw(networks(0, 3))
    start = draw(st.integers(0, network.g.n - 1))
    goal = draw(st.integers(0, network.g.n - 1))
    p, far = draw(st.integers(0, 4)), draw(st.integers(0, 2))
    to = naive.cheapest_to(network, goal)
    top = max((d * p // 4 for d in to if d is not None), default=0)
    estimate = [top + far if d is None else d * p // 4 for d in to]
    return network, start, goal, estimate


@given(searches())
def test_on_any_network_the_goal_gets_its_cheapest_cost(
        case: tuple[Network, int, int, list[int]]) -> None:
    network, start, goal, estimate = case
    assert is_estimate_is_consistent(network, goal, estimate)
    d, settled = a_star_with_settled(network, start, goal, estimate)
    assert a_star(network, start, goal, estimate) == d
    assert d.cost[goal] == naive.cheapest(network, start)[goal]
    path = d.path_to(goal)
    if path is not None:
        assert path[0] == start and settled[-1] == goal
        total = sum(min(network.cost[i] for w, i in network.g.out[a] if w == b)
                    for a, b in pairwise(path))
        assert total == d.cost[goal]
    assert len(set(settled)) == len(settled)


@given(searches())
def test_on_any_network_every_state_of_the_search_is_valid(
        case: tuple[Network, int, int, list[int]]) -> None:
    network, start, goal, estimate = case
    trail = states(network, start, goal, estimate)
    assert all(check(network, start, goal, estimate, state) is None for state in trail)
    tried = [i for v in trail[-1].settled for _, i in network.g.out[v]]
    assert len(set(tried)) == len(tried)
    assert trail[-1].pushed <= len(tried) + 1


@given(searches())
def test_on_any_network_the_zero_estimate_settles_as_dijkstras_walk_to_the_goal(
        case: tuple[Network, int, int, list[int]]) -> None:
    network, start, goal, _ = case
    d, settled = a_star_with_settled(network, start, goal, [0] * network.g.n)
    assert d == dijkstra_to(network, start, goal)
    assert settled == dijkstra_to_settled(network, start, goal)


@st.composite
def any_estimates(draw: st.DrawFn) -> tuple[Network, int, int, list[int]]:
    """A network, a start, a goal and any estimate from 0 to 9 per vertex, consistent or not."""
    network = draw(networks())
    n = network.g.n
    vertex = st.integers(0, n - 1)
    estimate = draw(st.lists(st.integers(0, 9), min_size=n, max_size=n))
    return network, draw(vertex), draw(vertex), estimate


def twin(network: Network, start: int, goal: int, estimate: list[int]) -> tuple[list[int], int]:
    """The arrow ids whose costs `step`'s search reads, in order, and how many entries it pushes
    after the start's, stopped as `a_star` stops."""
    counted = Network(network.g, network.cost)
    costs = ReadCosts(network.cost)
    counted.cost = costs
    state = start_state(counted, estimate, start)
    while state.queue and not (state.queue[0][1] == goal and goal not in state.settled):
        step(counted, estimate, state)
    return costs.read, state.pushed - 1


@given(any_estimates())
def test_with_any_estimate_the_printed_loop_is_the_search(
        case: tuple[Network, int, int, list[int]]) -> None:
    # Consistent or not, the heap loop gives `step`'s whole answer, tries the same arrows in the
    # same order, none twice, and pushes one entry per strict drop: a settled vertex is never
    # reopened, and an old entry is skipped, not its row tried again.
    network, start, goal, estimate = case
    assert a_star(network, start, goal, estimate) == a_star_with_settled(
        network, start, goal, estimate)[0]
    read, pushed = work(lambda n: a_star(n, start, goal, estimate), network)
    assert (read, pushed) == twin(network, start, goal, estimate)
    assert len(set(read)) == len(read)
