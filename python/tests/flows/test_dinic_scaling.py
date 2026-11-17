"""Dinic with scaling: its first threshold, its rounds on the chapter's network, Dinic's rounds
when every capacity is 1, and on random small networks a largest flow whose every path carries at
least the threshold it was found at."""

from __future__ import annotations

from hypothesis import given

from algodesign.flows import (
    Dinic,
    DinicScaling,
    MaxFlow,
    Network,
    Residual,
    max_flow_with_rounds,
    naive,
)
from algodesign.flows.max_flow import max_flow

from .strategies import ONE_AND_THOUSAND, networks
from .test_max_flow import replays


def test_the_first_threshold_is_the_largest_power_of_two_below_the_largest_capacity() -> None:
    # The largest capacity, 12, is not on an arrow out of the source, whose largest is 3.
    r = Residual(Network(3, [(0, 1), (1, 2)], [3, 12], 0, 2))
    rule = DinicScaling()
    rule.start(r)
    assert rule.threshold == 8
    # Round 1: the layers at 8 and at 4 miss the sink; at 2 the walk sends 0 -> 1 -> 2.
    assert rule.round(r) == [([0, 2], 3)]
    assert rule.threshold == 2
    # Round 2: the layers at 2 and at 1 miss the sink, and the round sends nothing.
    assert rule.round(r) == []
    assert rule.threshold == 0


def test_on_the_one_and_thousand_network_the_middle_arrow_is_below_the_threshold() -> None:
    answer, rounds = max_flow_with_rounds(ONE_AND_THOUSAND, DinicScaling())
    assert rounds == [[([0, 6], 1000), ([2, 8], 1000)]]
    assert answer == MaxFlow(2000, [1000, 1000, 0, 1000, 1000], [True, False, False, False])


def test_with_every_capacity_one_it_runs_dinic_s_rounds() -> None:
    network = Network(
        6, [(0, 1), (1, 5), (0, 2), (2, 5), (0, 3), (3, 4), (4, 5)], [1] * 7, 0, 5
    )
    assert max_flow_with_rounds(network, DinicScaling()) == max_flow_with_rounds(network, Dinic())


def test_with_every_capacity_zero_the_threshold_is_zero_and_nothing_is_sent() -> None:
    answer, rounds = max_flow_with_rounds(Network(2, [(0, 1)], [0], 0, 1), DinicScaling())
    assert (answer.value, rounds) == (0, [])


@given(networks())
def test_a_largest_flow_whose_every_path_carries_at_least_its_threshold(network: Network) -> None:
    answer, rounds = max_flow_with_rounds(network, DinicScaling())
    assert naive.check(network, answer) is None
    assert replays(network, answer, rounds) is None
    expected = max_flow(network)
    assert (answer.value, answer.side) == (expected.value, expected.side)
    r = Residual(network)
    rule = DinicScaling()
    rule.start(r)
    while sent := rule.round(r):
        assert all(amount >= rule.threshold >= 1 for _, amount in sent)
    assert rule.threshold == 0
