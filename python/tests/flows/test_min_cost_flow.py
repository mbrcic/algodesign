"""The cheapest flow of a given amount: the chapter's vehicles round by round with the paths,
heights and settled counts the Rust's tests pin, the ties, the shortfall and the refusals; and on
random tiny networks every answer checked against the contract and the cheapest cost found by trying
every flow."""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.flows import (
    MinCostFlow,
    MinCostRound,
    Network,
    Residual,
    min_cost_flow_with_rounds,
    naive,
)
from algodesign.flows.max_flow import max_flow, value_of
from algodesign.flows.min_cost_flow import min_cost_flow


def priced(
    n: int, arrows: list[tuple[int, int, int, int]], source: int, sink: int
) -> tuple[Network, list[int]]:
    """A network and its costs from arrows `(tail, head, capacity, cost)`."""
    network = Network(n, [(a, b) for a, b, _, _ in arrows], [c for _, _, c, _ in arrows], source, sink)
    return network, [k for _, _, _, k in arrows]


# The chapter's vehicles: the source 0; the flats Juan 1, Tomás 2, Anita 3, Daniel 4; the van 5, the
# car 6; the sink 7. Arrows 0-3 lead from the source to each flat (1 each, free); arrows 4-11 from
# each flat to the van, then the car (1 each): Juan 1 and 100, Tomás 1 and 100, Anita 3 and 2,
# Daniel 10 and 5; arrow 12 is the van to the sink (3), arrow 13 the car (1), both free.
VEHICLES, VEHICLE_COSTS = priced(8, [
    (0, 1, 1, 0), (0, 2, 1, 0), (0, 3, 1, 0), (0, 4, 1, 0),
    (1, 5, 1, 1), (1, 6, 1, 100), (2, 5, 1, 1), (2, 6, 1, 100),
    (3, 5, 1, 3), (3, 6, 1, 2), (4, 5, 1, 10), (4, 6, 1, 5),
    (5, 7, 3, 0), (6, 7, 1, 0),
], 0, 7)


def breaks(
    network: Network, cost: list[int], amount: int, answer: MinCostFlow, rounds: list[MinCostRound]
) -> str | None:
    """The first part of the contract the answer and its rounds break, in words; `None` if none."""
    s, t = network.source, network.sink
    # Lean: Valid, WellFormed, Ops.SendsAFlow, Ops.CheapestForItsAmount, Ops.HeightsFit,
    # Ops.ShortOnlyAtACut
    cheapest = naive.cheapest_cost(network, cost, value_of(network, answer.flow))
    if (broken := answer.check_valid(network, cost, amount, cheapest)) is not None:
        return broken
    if answer.value != value_of(network, answer.flow):
        return "value"
    if answer.value != min(amount, max_flow(network).value):
        return "the amount is not the requested one or the largest"
    if answer.cost != sum(k * x for k, x in zip(cost, answer.flow, strict=True)):
        return "cost"
    # Lean: Ops.RoundsAtMostAmount
    if len(rounds) > amount:
        return "more rounds than the amount"
    # Lean: Ops.walks, Ops.roundsKeep (invariant 3 after every round)
    r = Residual(network)
    heights = [0] * network.n
    for k, round in enumerate(rounds):
        path, sent = round.sent
        at = s
        for e in path:
            if r.tail(e) != at or sent > r.residual_capacity[e]:
                return f"round {k}: {path} is no augmenting path for {sent}"
            at = r.head[e]
        if at != t or sent < 1:
            return f"round {k}: {path} does not take {sent} to the sink"
        for e in path:
            r.send(e, sent)
        state = MinCostFlow(0, 0, r.flow(), round.heights, [])
        if not state.is_heights_fit_everywhere(network, cost):
            return f"round {k}: the heights after it do not fit"
        heights = round.heights
    if r.flow() != answer.flow or heights != answer.heights:
        return "the rounds do not lead to the answer"
    return None


def checked(network: Network, cost: list[int], amount: int) -> tuple[MinCostFlow, list[MinCostRound]]:
    """The answer and rounds, checked against the contract and the cheapest cost by trying every
    flow."""
    answer, rounds, searches = min_cost_flow_with_rounds(network, cost, amount)
    assert breaks(network, cost, amount, answer, rounds) is None
    # every round's search, and one more that missed the sink only when the amount was not met
    assert searches[:len(rounds)] == [round.settled for round in rounds]
    assert len(searches) == len(rounds) + (answer.value < amount)
    # Lean: Ops.CheapestForItsAmount
    assert naive.cheapest_cost(network, cost, answer.value) == answer.cost
    assert min_cost_flow(network, cost, amount) == answer
    return answer, rounds


def test_the_vehicles_take_the_four_cheapest_steps_and_the_last_moves_anita_back_to_the_van() -> None:
    # Lean: Ops.steps, Ops.heightsAfter, Ops.walks
    answer, rounds = checked(VEHICLES, VEHICLE_COSTS, 4)
    assert [round.sent for round in rounds] == [
        ([0, 8, 24], 1),  # Juan -> van
        ([2, 12, 24], 1),  # Tomás -> van
        ([4, 18, 26], 1),  # Anita -> car
        ([6, 22, 19, 16, 24], 1),  # Daniel -> car, Anita back from the car to the van
    ]
    assert [round.heights for round in rounds] == [
        [0, 0, 0, 0, 0, 1, 1, 1],
        [0, 0, 0, 0, 0, 1, 1, 1],
        [0, 1, 1, 0, 0, 2, 2, 2],
        [0, 5, 5, 3, 0, 6, 5, 6],
    ]
    assert (answer.value, answer.cost) == (4, 10)
    assert answer.flow == [1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 3, 1]
    assert answer.heights == rounds[-1].heights


def test_the_search_stops_as_soon_as_the_sink_is_settled() -> None:
    # Round 3 settles 5 vertices; run until its queue is empty, the search would settle 8.
    _, rounds = checked(VEHICLES, VEHICLE_COSTS, 4)
    assert [round.settled for round in rounds] == [7, 7, 5, 8]
    # the run stops when the amount is sent: no fifth search
    assert min_cost_flow_with_rounds(VEHICLES, VEHICLE_COSTS, 4)[2] == [7, 7, 5, 8]


def test_a_network_that_cannot_carry_the_amount_sends_the_most_with_a_cut_that_proves_it() -> None:
    # Lean: Ops.ShortOnlyAtACut
    answer, rounds = checked(VEHICLES, VEHICLE_COSTS, 5)
    assert (answer.value, answer.cost, len(rounds)) == (4, 10, 4)
    assert answer.heights == rounds[-1].heights
    assert answer.side == [True] + [False] * 7
    # Lean: settledEach. The fifth search settles the source alone and misses the sink.
    assert min_cost_flow_with_rounds(VEHICLES, VEHICLE_COSTS, 5)[2] == [7, 7, 5, 8, 1]
    network, cost = priced(3, [(0, 1, 2, 1), (2, 1, 2, 1)], 0, 2)
    answer, rounds = checked(network, cost, 3)
    assert (answer.value, answer.cost, rounds) == (0, 0, [])
    assert (answer.side, answer.heights) == ([True, True, False], [0, 0, 0])


def test_on_a_tie_the_first_vertex_labeled_keeps_the_arrow_that_labeled_it() -> None:
    network, cost = priced(4, [(0, 1, 1, 1), (0, 2, 1, 0), (2, 1, 1, 1), (1, 3, 1, 0)], 0, 3)
    assert checked(network, cost, 1)[1][0].sent == ([0, 6], 1)
    network, cost = priced(2, [(0, 1, 1, 2), (0, 1, 1, 2)], 0, 1)
    assert checked(network, cost, 1)[1][0].sent == ([0], 1)


def test_the_queue_breaks_a_tie_of_distances_by_vertex_id() -> None:
    network, cost = priced(4, [(0, 2, 1, 0), (0, 1, 1, 0), (2, 3, 1, 0), (1, 3, 1, 0)], 0, 3)
    assert checked(network, cost, 1)[1][0].sent == ([2, 6], 1)


def test_a_step_sends_its_bottleneck_or_what_is_still_requested_if_less() -> None:
    network, cost = priced(3, [(0, 1, 10, 1), (1, 2, 7, 1), (0, 2, 4, 3)], 0, 2)
    answer, rounds = checked(network, cost, 9)
    assert [round.sent for round in rounds] == [([0, 2], 7), ([4], 2)]
    assert (answer.value, answer.cost) == (9, 20)
    answer, rounds = checked(network, cost, 0)
    assert (answer.value, answer.cost, answer.heights, rounds) == (0, 0, [0, 0, 0], [])


def test_a_cost_count_mismatch_and_a_negative_cost_are_refused() -> None:
    # Lean: Problem.WellFormed, Problem.NoArrowBelowZero
    network, _ = priced(2, [(0, 1, 1, 0), (0, 1, 1, 0)], 0, 1)
    with pytest.raises(ValueError, match="1 costs for 2 arrows"):
        min_cost_flow(network, [1], 1)
    with pytest.raises(ValueError, match="arrow 1 costs -3"):
        min_cost_flow(network, [0, -3], 1)


def test_check_valid_names_each_broken_piece_alone() -> None:
    network, cost = priced(3, [(0, 1, 10, 1), (1, 2, 7, 1), (0, 2, 4, 3)], 0, 2)
    good = min_cost_flow(network, cost, 9)
    # Changed costs 0, -1 and 0: arrow 0 partly loaded, arrow 1 full, arrow 2 partly loaded.
    assert (good.flow, good.heights, good.side) == ([7, 7, 2], [0, 1, 3], [True] * 3)
    assert good.check_valid(network, cost, 9, 20) is None and good.is_valid(network, cost, 9, 20)

    def answer(flow: list[int], heights: list[int], side: list[bool]) -> MinCostFlow:
        return MinCostFlow(0, 0, flow, heights, side)

    def cheapest(a: MinCostFlow) -> int | None:
        return naive.cheapest_cost(network, cost, value_of(network, a.flow))

    cases = [
        # Lean: FlowRespected; arrow 2 carries 5 over its 4, full, so its changed cost 0 fits.
        (answer([7, 7, 5], [0, 1, 3], [True] * 3), 12, "invariant 1 (flow_respected)"),
        # Lean: FlowRespected; vertex 1 takes in 8 and lets out 7.
        (answer([8, 7, 2], [0, 1, 3], [True] * 3), 10, "invariant 1 (flow_respected)"),
        # Lean: CheapestForAmount; 9 sent at cost 22, where 20 is the cheapest for 9.
        (answer([5, 5, 4], [0, 1, 3], [True] * 3), 9, "invariant 2 (cheapest_for_amount)"),
        # Lean: HeightsFitEverywhere; arrow 2's changed cost 1 on a partly loaded arrow.
        (answer([7, 7, 2], [0, 1, 2], [True] * 3), 9, "invariant 3 (heights_fit_everywhere)"),
        # Lean: WellFormed; a height or an amount too many.
        (answer([7, 7, 2], [0, 1, 3, 0], [True] * 3), 9, "not in the box (well_formed)"),
        (answer([7, 7, 2, 0], [0, 1, 3], [True] * 3), 9, "not in the box (well_formed)"),
        # Lean: Ops.SendsAFlow; 9 sent where 8 were requested.
        (answer([7, 7, 2], [0, 1, 3], [True] * 3), 8, "promise (sends_a_flow)"),
        # Lean: Ops.ShortOnlyAtACut; 9 sent of 10, and the side holds the sink or marks too few.
        (answer([7, 7, 2], [0, 1, 3], [True] * 3), 10, "promise (short_only_at_a_cut)"),
        (answer([7, 7, 2], [0, 1, 3], [True]), 10, "promise (short_only_at_a_cut)"),
    ]
    for a, amount, label in cases:
        assert a.check_valid(network, cost, amount, cheapest(a)) == label, (a, amount)
        assert not a.is_valid(network, cost, amount, cheapest(a))
    # A short flow whose side is a cut of its amount passes.
    short = min_cost_flow(network, cost, 12)
    assert (short.value, short.side) == (11, [True, True, False])
    assert short.check_valid(network, cost, 12, cheapest(short)) is None


def test_cheapest_for_amount_compares_the_flows_cost_with_the_cheapest_given() -> None:
    # Lean: CheapestForAmount; arrows 0 -> 1 costing 1 and 3, each carrying up to 1.
    network, cost = priced(2, [(0, 1, 1, 1), (0, 1, 1, 3)], 0, 1)
    assert naive.cheapest_cost(network, cost, 1) == 1
    assert MinCostFlow(0, 0, [1, 0], [], []).is_cheapest_for_amount(network, cost, 1)
    assert not MinCostFlow(0, 0, [0, 1], [], []).is_cheapest_for_amount(network, cost, 1)
    # No flow sends 3, so no flow of that amount is cheaper; a missing amount reads as 0.
    assert naive.cheapest_cost(network, cost, 3) is None
    assert MinCostFlow(0, 0, [2, 1], [], []).is_cheapest_for_amount(network, cost, None)
    assert MinCostFlow(0, 0, [1], [], []).is_cheapest_for_amount(network, cost, 1)


def test_the_heights_fit_by_the_rule_per_arrow() -> None:
    # One arrow 0 -> 1 of capacity 2 and cost 0; its changed cost is h(0) - h(1).
    network, cost = priced(2, [(0, 1, 2, 0)], 0, 1)
    fits = {
        (changed, x): MinCostFlow(0, 0, [x], [changed, 0], []).is_heights_fit_everywhere(
            network, cost)
        for changed in (-1, 0, 1) for x in (0, 1, 2)
    }
    # Empty: at least zero; partly loaded: zero; full: at most zero.
    assert fits == {
        (-1, 0): False, (-1, 1): False, (-1, 2): True,
        (0, 0): True, (0, 1): True, (0, 2): True,
        (1, 0): True, (1, 1): False, (1, 2): False,
    }
    # An arrow of capacity 0 has no residual capacity either way, so any heights fit it.
    network, cost = priced(2, [(0, 1, 0, 0)], 0, 1)
    assert all(MinCostFlow(0, 0, [0], [h, 0], []).is_heights_fit_everywhere(network, cost)
               for h in (-5, 0, 5))


@st.composite
def tiny(draw: st.DrawFn) -> tuple[Network, list[int], int]:
    """A network of two to five vertices and up to six arrows carrying up to 2, costing up to 5,
    and an amount up to 5: trying every flow stays quick."""
    n = draw(st.integers(2, 5))
    vertex = st.integers(0, n - 1)
    arrows = draw(st.lists(
        st.tuples(vertex, vertex, st.integers(0, 2), st.integers(0, 5)), max_size=6
    ))
    source = draw(vertex)
    network, cost = priced(n, arrows, source, (source + draw(st.integers(1, n - 1))) % n)
    return network, cost, draw(st.integers(0, 5))


@given(tiny())
def test_on_any_tiny_network_the_answer_is_the_cheapest_for_its_amount(
    problem: tuple[Network, list[int], int],
) -> None:
    # Lean: Contract.promise, Ops.RoundsAtMostAmount
    checked(*problem)


def test_on_the_tie_network_the_first_arrow_to_reach_the_sink_wins() -> None:
    # The source 0, a 1, b 2, the sink 3; 0 -> a, 0 -> b, a -> 3 twice, b -> 3; each carries 1 and
    # costs 1. a and b both offer the sink at 2; a, the lower id, comes off first.
    network, cost = priced(
        4, [(0, 1, 1, 1), (0, 2, 1, 1), (1, 3, 1, 1), (1, 3, 1, 1), (2, 3, 1, 1)], 0, 3
    )
    answer, rounds = checked(network, cost, 2)
    assert [round.sent for round in rounds] == [([0, 4], 1), ([2, 8], 1)]
    assert rounds[0].heights == [0, 1, 1, 2]
    assert (answer.value, answer.cost) == (2, 4)
