# SPDX-License-Identifier: Apache-2.0
"""The design project's bench: the library's three rules keep the contract on any small network,
each broken piece is caught by its own check (a rule that stops early, one whose rounds lie, one
that sends what it does not report, one that never stops, one that raises), a candidate that
cannot be made or read fails alone, the speed menu counts what it says, code size counts code only
and counts inherited code, and the frontier keeps exactly what nothing beats."""

from __future__ import annotations

from hypothesis import given, settings

from algodesign import flows
from algodesign.flows import (
    Augmentation,
    CapacityScaling,
    Dinic,
    EdmondsKarp,
    Network,
    Residual,
    naive,
)
from algodesign.flows import workbench as wb
from algodesign.flows.dinic import layers
from algodesign.flows.edmonds_karp import path_back, shortest_path

from .strategies import ONE_AND_THOUSAND, networks


class StopsEarly:
    """Edmonds-Karp's rule for one round, then nothing: it breaks the promise."""

    def __init__(self) -> None:
        self.asked = 0

    def start(self, residual: Residual) -> None:
        self.asked = 0

    def round(self, residual: Residual) -> list[Augmentation]:
        self.asked += 1
        if self.asked > 1:
            return []
        path = shortest_path(residual, 1)
        return [] if path is None else [(path, residual.augment(path))]


class OneUnit:
    """One unit along a path of fewest arrows each round: it keeps the promise, slowly."""

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        path = shortest_path(residual, 1)
        if path is None:
            return []
        for e in path:
            residual.send(e, 1)
        return [(path, 1)]


class Lies:
    """Dinic's rounds, reported as one path along every arrow they used: the flow is right, the
    count is not."""

    def __init__(self) -> None:
        self.dinic = Dinic()

    def start(self, residual: Residual) -> None:
        self.dinic.start(residual)

    def round(self, residual: Residual) -> list[Augmentation]:
        sent = self.dinic.round(residual)
        return [([e for path, _ in sent for e in path], 1)] if sent else []


class Hides:
    """Edmonds-Karp's rule, sending one more unit than it reports along each path."""

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        path = shortest_path(residual, 2)
        if path is None:
            return []
        for e in path:
            residual.send(e, 2)
        return [(path, 1)]


class NeverStops:
    """Reports a path of nothing every round and sends nothing."""

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        return [([], 0)]


class Raises:
    """Fails at its first round."""

    def start(self, residual: Residual) -> None:
        pass

    def round(self, residual: Residual) -> list[Augmentation]:
        raise RuntimeError("no idea")


class NeedsAParameter(EdmondsKarp):
    """Cannot be made without an argument the bench does not give."""

    def __init__(self) -> None:
        raise ValueError("needs a parameter")


class Mine(Dinic):
    pass


class MineByAttribute(flows.Dinic):
    pass


def failure_of(rule: type, network: Network, speed: wb.Speed | None = None) -> str | None:
    """The bench's verdict on one rule and one network."""
    (result,) = wb.bench([wb.Entry(rule.__name__, rule)], [network], speed, repeat=1)
    return result.failure()


@settings(max_examples=60)
@given(networks())
def test_the_library_rules_keep_the_contract_on_any_small_network(network: Network) -> None:
    # Lean: contract_of_promise, largestOn_of_cut
    results = wb.bench(wb.BUILT_IN, [network], repeat=1)
    assert [r.failure() for r in results] == [None, None, None]
    for entry in wb.BUILT_IN:
        flow, rounds = wb.run(network, entry.make())
        assert wb.value_of(network, flow) == naive.min_cut(network)
        assert wb.adds_along_augmenting_paths(network, rounds)
    dinic, ek = wb.run(network, Dinic())[1], wb.run(network, EdmondsKarp())[1]
    assert wb.rounds_at_most_n(network, dinic)
    assert wb.augmentations_at_most_nm(network, ek)


def test_on_the_one_and_thousand_network_the_lean_s_decided_pieces_hold() -> None:
    # Lean: the examples deciding ReturnsAFlowOn, CutMatchesFlowOn, AddsAlongAugmentingPathsOn
    flow, rounds = wb.run(ONE_AND_THOUSAND, EdmondsKarp())
    assert rounds == [[([0, 6], 1000)], [([2, 8], 1000)]]
    assert wb.check(ONE_AND_THOUSAND, flow, rounds, wb.augmentations_at_most_nm) is None
    assert wb.check(ONE_AND_THOUSAND, flow, rounds, wb.bounded_by(lambda n, m: 1)) == (
        "the speed requirement bounded_by(<lambda>)")
    assert wb.check(ONE_AND_THOUSAND, *wb.run(ONE_AND_THOUSAND, Dinic()),
                    wb.rounds_at_most_n) is None


def test_a_rule_that_stops_early_leaves_no_cut() -> None:
    flow, rounds = wb.run(ONE_AND_THOUSAND, StopsEarly())
    assert rounds == [[([0, 6], 1000)]]
    assert wb.is_flow(ONE_AND_THOUSAND, flow) and wb.adds_along_augmenting_paths(
        ONE_AND_THOUSAND, rounds)
    assert failure_of(StopsEarly, ONE_AND_THOUSAND) == (
        "network 0: a cut of the same amount: an augmenting path was left")


def test_a_slow_rule_keeps_the_contract_and_fails_the_speed_requirement() -> None:
    assert failure_of(OneUnit, ONE_AND_THOUSAND) is None
    assert failure_of(OneUnit, ONE_AND_THOUSAND, wb.augmentations_at_most_nm) == (
        "network 0: the speed requirement augmentations_at_most_nm")
    assert failure_of(OneUnit, ONE_AND_THOUSAND, wb.bounded_by(lambda n, m: 2000)) is None


def test_rounds_that_lie_about_their_paths_are_caught() -> None:
    assert failure_of(Lies, ONE_AND_THOUSAND) == (
        "network 0: along augmenting paths: a path was no augmenting path in its turn")


def test_a_rule_that_sends_what_it_does_not_report_is_caught() -> None:
    assert failure_of(Hides, ONE_AND_THOUSAND) == (
        "network 0: the rounds do not add up to the flow the rule left")


def test_a_rule_that_never_stops_ends_at_the_total_capacity_plus_one() -> None:
    network = Network(2, [(0, 1)], [3], 0, 1)
    _, rounds = wb.run(network, NeverStops())
    assert len(rounds) == 4
    assert failure_of(NeverStops, network) == (
        "network 0: along augmenting paths: a path was no augmenting path in its turn")


def test_a_rule_that_raises_fails_its_verdict() -> None:
    assert failure_of(Raises, ONE_AND_THOUSAND) == "network 0: raised RuntimeError: no idea"


def test_code_lines_count_code_only() -> None:
    source = '''
    def f(x):
        """A docstring
        over two lines."""
        # a comment

        y = (x +
             1)  # a trailing comment
        return y
    '''
    assert wb.code_lines(source) == 4


def test_code_size_counts_the_helpers_a_rule_reaches_and_not_the_bench_s_own() -> None:
    assert wb.counted_objects(EdmondsKarp) == [EdmondsKarp, shortest_path, path_back]
    assert set(map(id, wb.counted_objects(CapacityScaling))) == {
        id(CapacityScaling), id(shortest_path), id(path_back)}
    assert Residual not in wb.counted_objects(Dinic)
    ek, dinic, scaling = (wb.lines_of(r) for r in (EdmondsKarp, Dinic, CapacityScaling))
    assert ek < scaling < dinic


def test_code_size_counts_inherited_code() -> None:
    assert wb.counted_objects(Mine) == [Mine, Dinic, layers]
    assert wb.counted_objects(MineByAttribute) == [MineByAttribute, Dinic, layers]
    assert wb.lines_of(Mine) == 2 + wb.lines_of(Dinic)
    assert wb.lines_of(MineByAttribute) == 2 + wb.lines_of(Dinic)


def test_a_candidate_that_cannot_be_made_fails_alone() -> None:
    results = wb.bench([wb.Entry("good", EdmondsKarp), wb.Entry("bad", NeedsAParameter)],
                       [ONE_AND_THOUSAND], repeat=1)
    assert [r.failure() for r in results] == [
        None, "making it raised ValueError: needs a parameter"]
    assert (results[0].networks[0].rounds, results[0].networks[0].added) == (2, 2)
    assert results[1].networks == []
    assert [r.name for r in wb.frontier(results)] == ["good"]
    assert "not run: making it raised ValueError: needs a parameter" in wb.table(results)


def test_a_candidate_whose_source_cannot_be_read_fails_as_that() -> None:
    piped = type("Piped", (EdmondsKarp,), {})
    (result,) = wb.bench([wb.Entry("piped", piped)], [ONE_AND_THOUSAND], repeat=1)
    failure = result.failure()
    assert failure is not None and failure.startswith("its source cannot be read: ")
    assert result.networks == []
    assert "not run: its source cannot be read" in wb.table([result])


def made(name: str, lines: int, seconds: float, failure: str | None = None) -> wb.Result:
    return wb.Result(name, lines, [wb.NetworkResult(1, 1, seconds, failure)])


def test_the_frontier_keeps_what_nothing_beats_on_both() -> None:
    results = [
        made("short and slow", 30, 9.0), made("long and fast", 90, 1.0),
        made("beaten on both", 95, 2.0), made("tie on lines, slower", 30, 9.5),
        made("equal twin", 90, 1.0), made("fast but wrong", 10, 0.1, "a flow"),
    ]
    assert [r.name for r in wb.frontier(results)] == [
        "short and slow", "long and fast", "equal twin"]
    text = wb.table(results)
    assert "* short and slow" in text and "  beaten on both" in text
    assert "fails on network 0: a flow" in text


def test_the_bench_prints_the_library_rules() -> None:
    results = wb.bench(wb.BUILT_IN, [ONE_AND_THOUSAND], wb.rounds_at_most_n, repeat=1)
    assert [r.name for r in results] == ["Edmonds-Karp", "Dinic", "capacity scaling"]
    assert [r.failure() for r in results] == [None, None, None]
    assert [(r.networks[0].rounds, r.networks[0].added) for r in results] == [
        (2, 2), (1, 2), (2, 2)]
    assert wb.frontier(results)
    assert "on the Pareto frontier" in wb.table(results)
