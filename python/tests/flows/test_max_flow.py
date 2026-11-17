"""The loop around a path rule: every rule's answer checked against the contract and its rounds
replayed, on the chapter's networks with the paths the Rust's tests pin, and on random small
networks against the smallest cut found by trying every one."""

from __future__ import annotations

from hypothesis import given

from algodesign.flows import (
    Augmentation,
    CapacityScaling,
    Dinic,
    EdmondsKarp,
    MaxFlow,
    Network,
    PathRule,
    Residual,
    max_flow_with_rounds,
    naive,
)
from algodesign.flows.max_flow import max_flow

from .strategies import ONE_AND_THOUSAND, networks

Rounds = list[list[Augmentation]]


def every_rule(network: Network) -> list[tuple[str, MaxFlow, Rounds]]:
    """Each of the three rules by name, with its answer and its rounds."""
    rules: list[tuple[str, PathRule]] = [
        ("Dinic", Dinic()), ("Edmonds-Karp", EdmondsKarp()), ("capacity scaling", CapacityScaling()),
    ]
    return [(name, *max_flow_with_rounds(network, rule)) for name, rule in rules]


def replays(network: Network, answer: MaxFlow, rounds: Rounds) -> str | None:
    """What goes wrong replaying `rounds` from the zero flow, in words; `None` if each path is
    augmenting in its turn, carries at least 1 within the residual capacity of every arrow on it, no
    round is empty, and together they give the answer's flow."""
    r = Residual(network)
    for k, sent in enumerate(rounds):
        if not sent:
            return f"round {k} is listed and sent nothing"
        for path, amount in sent:
            # Lean: IsAugmentingPath, FitInTurn, PathRule.AddsAtLeastOne
            at, passed = network.source, [network.source]
            for e in path:
                if r.tail(e) != at or r.head[e] in passed or amount > r.residual_capacity[e]:
                    return f"round {k}: {path} is no augmenting path for {amount}"
                at = r.head[e]
                passed.append(at)
            if at != network.sink or amount < 1:
                return f"round {k}: {path} does not take {amount} to the sink"
            for e in path:
                r.send(e, amount)
    # Lean: Ops.walks
    return None if r.flow() == answer.flow else "the rounds do not add up to the answer's flow"


def every_rule_meets_the_contract(network: Network) -> int:
    """Check every rule on `network` and return the amount they agree on."""
    n, m = network.n, len(network.arrows)
    runs = every_rule(network)
    for name, answer, rounds in runs:
        # Lean: Ops.ReturnsAFlow, Ops.CutMatchesFlow
        assert naive.check(network, answer) is None, name
        assert replays(network, answer, rounds) is None, name
        assert answer.value == runs[0][1].value, name
        assert answer.side == runs[0][1].side, name
        # Lean: Ops.FinishesWithIntegers
        assert sum(map(len, rounds)) <= answer.value, name
    # Lean: Ops.RoundsAtMostN
    assert len(runs[0][2]) <= n
    # Lean: Ops.AugmentationsAtMostNM
    assert sum(map(len, runs[1][2])) <= n * m
    assert all(len(sent) == 1 for _, _, rounds in runs[1:] for sent in rounds)
    assert max_flow(network) == runs[0][1]
    return runs[0][1].value


def test_on_the_one_and_thousand_network_no_rule_touches_the_middle_arrow() -> None:
    # Lean: Ops.walks, Ops.rounds
    assert every_rule_meets_the_contract(ONE_AND_THOUSAND) == 2000
    (_, dinic, dinic_rounds), (_, ek, ek_rounds), (_, scaling, scaling_rounds) = every_rule(
        ONE_AND_THOUSAND
    )
    assert dinic_rounds == [[([0, 6], 1000), ([2, 8], 1000)]]
    assert ek_rounds == [[([0, 6], 1000)], [([2, 8], 1000)]]
    assert scaling_rounds == ek_rounds
    for answer in (dinic, ek, scaling):
        assert answer == MaxFlow(2000, [1000, 1000, 0, 1000, 1000], [True, False, False, False])


def test_doubled_and_opposite_arrows_stay_separate_arrows() -> None:
    network = Network(3, [(0, 1), (0, 1), (1, 0), (1, 2)], [2, 3, 4, 10], 0, 2)
    assert every_rule_meets_the_contract(network) == 5
    assert all(a.flow == [2, 3, 0, 5] for _, a, _ in every_rule(network))
    network = Network(3, [(0, 1), (1, 1), (2, 1), (1, 2)], [7, 9, 4, 6], 0, 2)
    assert every_rule_meets_the_contract(network) == 6
    assert all(a.flow == [6, 0, 0, 6] and a.side == [True, True, False]
               for _, a, _ in every_rule(network))


def test_a_sink_out_of_reach_gets_nothing_and_the_side_is_what_the_source_reaches() -> None:
    # Lean: PathRule.NoneOnlyWhenDone, reached
    network = Network(4, [(0, 1), (2, 3), (3, 0)], [5, 5, 5], 0, 3)
    for name, answer, rounds in every_rule(network):
        assert answer == MaxFlow(0, [0, 0, 0], [True, True, False, False]), name
        assert rounds == [], name
    assert max_flow(Network(2, [], [], 0, 1)).side == [True, False]
    assert every_rule_meets_the_contract(Network(2, [(0, 1), (0, 1)], [0, 0], 0, 1)) == 0


class Stopping:
    """Edmonds-Karp's rule for one round, then nothing: a rule that breaks its promise."""

    def __init__(self) -> None:
        self.asked = 0

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        self.asked += 1
        return EdmondsKarp().round(residual) if self.asked == 1 else []


def test_the_loop_ends_at_the_first_round_that_sends_nothing() -> None:
    # Lean: PathRule.runRounds
    rule = Stopping()
    answer, rounds = max_flow_with_rounds(ONE_AND_THOUSAND, rule)
    assert rule.asked == 2
    assert rounds == [[([0, 6], 1000)]]
    # The flow so far; the sink is still reached, so the side is no cut.
    assert answer.value == 1000
    assert answer.side == [True, True, True, True]
    assert naive.check(ONE_AND_THOUSAND, answer) == "promise (cut_matches_flow)"


class Longest:
    """A rule of the reader's own: each round sends along the longest augmenting path, found by
    trying every one. It keeps the promise and is slow on purpose."""

    def __init__(self) -> None:
        self.rounds = 0

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        self.rounds += 1

        def paths(path: list[int], at: int, passed: list[int]) -> list[list[int]]:
            if at == residual.sink:
                return [path]
            return [p for e in residual.out[at]
                    if residual.residual_capacity[e] > 0 and residual.head[e] not in passed
                    for p in paths(path + [e], residual.head[e], passed + [residual.head[e]])]

        found = paths([], residual.source, [residual.source])
        if not found:
            return []
        longest = max(found, key=len)
        return [(longest, residual.augment(longest))]


def test_a_rule_that_takes_the_long_way_needs_two_thousand_rounds() -> None:
    # Every path of three arrows crosses the middle arrow, one way and then back, one unit each.
    rule = Longest()
    answer = max_flow(ONE_AND_THOUSAND, rule)
    assert answer.value == 2000
    assert rule.rounds == 2001
    assert naive.check(ONE_AND_THOUSAND, answer) is None
    assert answer == max_flow(ONE_AND_THOUSAND)


def test_check_valid_names_each_broken_piece_alone() -> None:
    # The library's answer on the chapter's network, then one piece broken at a time.
    good = max_flow(ONE_AND_THOUSAND)
    assert good.check_valid(ONE_AND_THOUSAND) is None and good.is_valid(ONE_AND_THOUSAND)
    cases = [
        # Lean: WithinCapacity; the middle arrow carries 2 over its 1, or -1, and the arrows
        # after it make up the difference.
        (MaxFlow(2000, [1000, 1000, 2, 998, 1002], good.side), "invariant 1 (within_capacity)"),
        (MaxFlow(2000, [1000, 1000, -1, 1001, 999], good.side), "invariant 1 (within_capacity)"),
        # Lean: Conserved; vertex 1 takes in 1000 and lets out 999.
        (MaxFlow(1999, [1000, 1000, 0, 999, 1000], good.side), "invariant 2 (conserved)"),
        # Lean: WellFormed; one amount too many, a zero on no arrow.
        (MaxFlow(2000, [*good.flow, 0], good.side), "not in the box (well_formed)"),
        # Lean: Ops.CutMatchesFlow; the side holds the sink, misses the source, has the wrong
        # capacity, or marks too few vertices.
        (MaxFlow(2000, good.flow, [True] * 4), "promise (cut_matches_flow)"),
        (MaxFlow(2000, good.flow, [False] * 4), "promise (cut_matches_flow)"),
        (MaxFlow(2000, good.flow, [True, True, False, False]), "promise (cut_matches_flow)"),
        (MaxFlow(2000, good.flow, [True]), "promise (cut_matches_flow)"),
    ]
    for answer, label in cases:
        assert answer.check_valid(ONE_AND_THOUSAND) == label, answer
        assert not answer.is_valid(ONE_AND_THOUSAND)
    # A short flow list breaks only `WellFormed`: a missing amount reads as 0.
    zero = MaxFlow(0, [0, 0, 0, 0], [True, False, False, False])
    zero_network = Network(4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)], [0] * 5, 0, 3)
    assert zero.check_valid(zero_network) == "not in the box (well_formed)"
    # The reported amount has no piece; the test helper checks it.
    wrong_value = MaxFlow(1999, good.flow, good.side)
    assert wrong_value.check_valid(ONE_AND_THOUSAND) is None
    assert naive.check(ONE_AND_THOUSAND, wrong_value) == "value"


@given(networks())
def test_on_any_small_network_every_rule_keeps_the_promise_and_finds_the_smallest_cut(
    network: Network,
) -> None:
    # Lean: PathRule.Promise, Contract.promise, Ops.Largest
    assert every_rule_meets_the_contract(network) == naive.min_cut(network)
