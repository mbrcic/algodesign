"""Push-relabel: every answer passes max flow's checks and has Dinic's amount, on the chapter's
networks with the flows and step counts the Rust's tests pin, on random small networks against the
smallest cut found by trying every one, and on 300 larger drawn networks against Dinic."""

from __future__ import annotations

from hypothesis import given

from algodesign._rng import SplitMix64
from algodesign.flows import MaxFlow, Network, naive
from algodesign.flows.max_flow import max_flow
from algodesign.flows.push_relabel import Counts, push_relabel, push_relabel_with_counts

from .strategies import ONE_AND_THOUSAND, networks


def checked(network: Network) -> tuple[MaxFlow, Counts]:
    """Push-relabel's answer and counts on `network`, after checking that it passes max flow's
    checks, that no loop carries anything, and that its amount is Dinic's."""
    answer, counts = push_relabel_with_counts(network)
    # Lean: PushRelabel.PassesChecks, so PushRelabel.largest_of_passesChecks
    assert naive.check(network, answer) is None
    assert all(x == 0 for (a, b), x in zip(network.arrows, answer.flow, strict=True) if a == b)
    assert answer.value == max_flow(network).value
    assert push_relabel(network) == answer
    return answer, counts


def test_on_the_one_and_thousand_network_the_excess_runs_straight_down() -> None:
    answer, counts = checked(ONE_AND_THOUSAND)
    assert answer == MaxFlow(2000, [1000, 1000, 0, 1000, 1000], [True, False, False, False])
    assert answer.flow == max_flow(ONE_AND_THOUSAND).flow
    assert counts == Counts(pushes=2, relabels=0, gaps=0, global_relabels=1)


def test_stranded_excess_goes_back_to_the_source_in_the_second_phase() -> None:
    # 0 -> 1 -> 2 -> 3 carrying 5, 2, 1: two gap steps in the first phase, then the excess on 1
    # and 2 goes back.
    answer, counts = checked(Network(4, [(0, 1), (1, 2), (2, 3)], [5, 2, 1], 0, 3))
    assert answer == MaxFlow(1, [1, 1, 1], [True, True, True, False])
    assert counts == Counts(pushes=4, relabels=4, gaps=2, global_relabels=1)


def test_doubled_and_opposite_arrows_stay_separate_arrows() -> None:
    answer, _ = checked(Network(3, [(0, 1), (0, 1), (1, 0), (1, 2)], [2, 3, 4, 10], 0, 2))
    assert answer == MaxFlow(5, [2, 3, 0, 5], [True, False, False])
    answer, _ = checked(Network(3, [(0, 1), (1, 1), (2, 1), (1, 2)], [7, 9, 4, 6], 0, 2))
    assert answer == MaxFlow(6, [6, 0, 0, 6], [True, True, False])
    # A loop at the source is not filled.
    assert checked(Network(2, [(0, 0), (0, 1)], [9, 4], 0, 1))[0].flow == [0, 4]


def test_a_sink_out_of_reach_gets_nothing_and_the_side_is_what_the_source_reaches() -> None:
    answer, _ = checked(Network(4, [(0, 1), (2, 3), (3, 0)], [5, 5, 5], 0, 3))
    assert answer == MaxFlow(0, [0, 0, 0], [True, True, False, False])
    assert push_relabel(Network(2, [], [], 0, 1)).side == [True, False]
    answer, counts = checked(Network(2, [(0, 1), (0, 1)], [0, 0], 0, 1))
    assert (answer.value, counts) == (0, Counts(global_relabels=1))


@given(networks())
def test_on_any_small_network_the_amount_is_the_smallest_cut(network: Network) -> None:
    # Lean: PushRelabel.PushRelabelPromise, by trying every cut
    assert checked(network)[0].value == naive.min_cut(network)


def test_on_larger_networks_the_amount_is_dinics_and_every_step_is_exercised() -> None:
    # The Rust's 300 networks, drawn from the same seed in the same order.
    r = SplitMix64(11)
    positive, total = 0, Counts()
    for _ in range(300):
        n = 2 + r.next_u64() % 39
        m = r.next_u64() % 161
        scale = [4, 100, 1 << 20][r.next_u64() % 3]
        arrows, capacity = [], []
        for _ in range(m):
            a, b = r.next_u64() % n, r.next_u64() % n
            arrows.append((a, b))
            capacity.append(r.next_u64() % scale)
        s = r.next_u64() % n
        t = (s + 1 + r.next_u64() % (n - 1)) % n
        answer, counts = checked(Network(n, arrows, capacity, s, t))
        positive += answer.value > 0
        total.pushes += counts.pushes
        total.relabels += counts.relabels
        total.gaps += counts.gaps
        total.global_relabels += counts.global_relabels
    assert positive > 100
    # Gap steps fire, and 30 global relabels run after the 300 at the start; the Rust's test pins
    # the same totals, step for step.
    assert total == Counts(pushes=6869, relabels=2910, gaps=170, global_relabels=330)
