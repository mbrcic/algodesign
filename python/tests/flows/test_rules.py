"""The three path rules, each on the small networks the Rust's tests pin: Edmonds-Karp's first
labeled vertex keeping its label, Dinic's sweep starting again from the source (counted by its
steps) and its dead ends on the sink's layer, and capacity scaling's first threshold."""

from __future__ import annotations

from hypothesis import given

from algodesign.flows import (
    CapacityScaling,
    Dinic,
    EdmondsKarp,
    Network,
    Residual,
    max_flow_with_rounds,
)
from algodesign.flows.max_flow import max_flow

from .strategies import networks


def test_the_first_vertex_labeled_keeps_the_arrow_that_labeled_it() -> None:
    # 0 -> 1 -> 3 and 0 -> 2 -> 3, then 3 -> 4: 3 is labeled from 1 first, and the arrow from 2
    # does not take the label over.
    network = Network(5, [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)], [1, 1, 1, 1, 2], 0, 4)
    answer, rounds = max_flow_with_rounds(network, EdmondsKarp())
    assert rounds == [[([0, 4, 8], 1)], [([2, 6, 8], 1)]]
    assert answer.value == 2


def test_a_later_path_takes_back_part_of_what_an_earlier_one_sent() -> None:
    # 0 -> 1 -> 2 -> 3 first; then 0 -> 4 -> 2, back against 1 -> 2, and 1 -> 5 -> 3.
    network = Network(
        6, [(0, 1), (1, 2), (2, 3), (0, 4), (4, 2), (1, 5), (5, 3)], [1] * 7, 0, 3
    )
    answer, rounds = max_flow_with_rounds(network, EdmondsKarp())
    assert rounds == [[([0, 2, 4], 1)], [([6, 8, 3, 10, 12], 1)]]
    assert answer.flow == [1, 0, 1, 1, 1, 1, 1]


def test_after_each_path_the_sweep_starts_again_from_the_source() -> None:
    # Lean: dinicSweepSteps
    # 0 -> 1 carries 2; 1 -> 2 -> 4 and 1 -> 3 -> 4 carry 1. The first path fills 1 -> 2.
    network = Network(5, [(0, 1), (1, 2), (1, 3), (2, 4), (3, 4)], [2, 1, 1, 1, 1], 0, 4)
    rule = Dinic()
    _, rounds = max_flow_with_rounds(network, rule)
    assert rounds == [[([0, 2, 6], 1), ([0, 4, 8], 1)]]
    # Along 0 -> 1, past 1's back arrow, along 1 -> 2, past 2's back arrow, along 2 -> 4, send
    # (6); again from the source, along 0 -> 1, past the full 1 -> 2, along 1 -> 3, past 3's back
    # arrow, along 3 -> 4, send (12); past the full 0 -> 1 (13); the source a dead end (14).
    # Resuming at 1 would count 13.
    assert rule.sweep_steps == [14]


def test_a_vertex_on_the_sinks_layer_is_a_dead_end_at_once() -> None:
    # 0 -> 1 -> 3 -> 4 and 0 -> 2 -> 4: the search labels 3 on the sink's layer before the sink.
    network = Network(5, [(0, 1), (0, 2), (1, 3), (2, 4), (3, 4)], [1] * 5, 0, 4)
    rule = Dinic()
    _, rounds = max_flow_with_rounds(network, rule)
    assert rounds == [[([2, 6], 1)], [([0, 4, 8], 1)]]
    # Phase 1: along 0 -> 1, past 1's back arrow, along 1 -> 3; 3 a dead end at once (4); 1 a
    # dead end (5); along 0 -> 2, past 2's back arrow, along 2 -> 4, send (9); past the full
    # 0 -> 2 (10); the source a dead end (11). Phase 2: along, past, along, past, along, send
    # (6), past two full arrows (8), the source a dead end (9).
    assert rule.sweep_steps == [11, 9]
    # The same rule on another network counts that network's phases alone.
    max_flow(Network(2, [(0, 1)], [3], 0, 1), rule)
    # Along 0 -> 1, send, past the full 0 -> 1, the source a dead end.
    assert rule.sweep_steps == [4]


def test_one_phase_sends_a_blocking_flow_and_the_next_finds_longer_paths() -> None:
    # Lean: Ops.RoundsAtMostN
    network = Network(
        6, [(0, 1), (1, 5), (0, 2), (2, 5), (0, 3), (3, 4), (4, 5)], [1] * 7, 0, 5
    )
    _, rounds = max_flow_with_rounds(network, Dinic())
    assert rounds == [[([0, 2], 1), ([4, 6], 1)], [([8, 10, 12], 1)]]


def test_the_first_threshold_is_the_largest_power_of_two_below_the_largest_capacity() -> None:
    # The largest capacity, 12, is not on an arrow out of the source, whose largest is 3.
    r = Residual(Network(3, [(0, 1), (1, 2)], [3, 12], 0, 2))
    rule = CapacityScaling()
    rule.start(r)
    assert rule.threshold == 8
    # Round 1: 8 and 4 find nothing; 2 finds 0 -> 1 -> 2 and sends its bottleneck.
    assert rule.round(r) == [([0, 2], 3)]
    assert rule.threshold == 2
    # Round 2: 2 and 1 find nothing, and the round sends nothing.
    assert rule.round(r) == []
    assert rule.threshold == 0


def test_with_every_capacity_zero_the_threshold_is_zero_and_nothing_is_sent() -> None:
    answer, rounds = max_flow_with_rounds(Network(2, [(0, 1)], [0], 0, 1), CapacityScaling())
    assert (answer.value, rounds) == (0, [])


@given(networks())
def test_every_scaling_path_carries_at_least_the_threshold_it_was_found_at(
    network: Network,
) -> None:
    r = Residual(network)
    rule = CapacityScaling()
    rule.start(r)
    while sent := rule.round(r):
        assert len(sent) == 1
        assert sent[0][1] >= rule.threshold >= 1
    assert rule.threshold == 0
