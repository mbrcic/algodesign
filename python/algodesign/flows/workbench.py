# SPDX-License-Identifier: Apache-2.0
"""The Flow chapter's design project: a bench for choosing a path rule on your own networks.

The reader states the requirements (max flow's contract, and a speed requirement from the menu),
asks an AI for several path rules, and runs them here on their own networks. The bench checks
every answer, counts rounds and added paths, measures time and code size, and keeps the rules no
other beats on both code size and time: the Pareto frontier, chapter 1's term.

- A candidate is a path rule, the protocol of `algodesign.flows.max_flow`: an object with
  `start(residual)` and `round(residual)`. `Entry` names it and says how to make a fresh one.
- `run`, the loop: the bench's own, as the Lean `PathRule.run` runs it. It starts from the zero
  flow, asks for one round at a time, and stops at the first round that sends nothing, or after
  as many rounds as the total capacity plus one: a round that adds at least one unit never needs
  more.
- `check`, the verdict on one network: the rule's rounds are replayed from the zero flow on a
  residual graph of the bench's own, never the rule's. Each path must be augmenting when its turn
  comes and carry at least one unit within the residual capacity of every arrow on it
  (`adds_along_augmenting_paths`), and together they must give the flow the rule left (`replay`).
  That flow must be a flow (`is_flow`), and the vertices the replayed residual graph reaches a cut
  of the same amount (`is_cut_of_flow`): so it is the largest, since no flow exceeds any cut. Then
  the speed requirement, if one is given: `rounds_at_most_n`, `augmentations_at_most_nm`, or
  `bounded_by(b)` for a bound `b(n, m)` the reader states.
- `bench`, the run: every candidate on every network, `repeat` times, each answer checked. Time is
  the best of the repeats, in Python seconds on the machine that runs the bench, for the loop
  around the rule: a Python measure, not the Rust's. Code size is the non-blank lines of the
  candidate's source that are neither comments nor docstrings (`code_lines`): its class, the
  classes it inherits from, and every class and function of its own package or of this library
  that these reach by name (`counted_objects`), less the bench's own `Network`, `Residual` and
  loop. A subclass of a library rule counts the rule's code too.
- A candidate that cannot be made, or whose source cannot be read, fails with the reason and is
  not run; the others' results stand.
- `frontier`, the choice: among the candidates that kept the contract on every network, those no
  other beats on both code size and time; `table` prints it all in plain words.
- `BUILT_IN`, the library's three rules as candidates: Edmonds–Karp, Dinic and capacity scaling.

What the bench cannot see. The cut certifies the largest flow on the networks it is given, and no
more: a rule may fail on a network the reader did not bring. "Some bound set by size" speaks of
every network, so the bench checks only a bound the reader states. A rule that never returns from
a round stops the bench; a rule that edits the bench's state, or reaches through the interpreter,
is not caught; code it imports from a package other than its own and this library is not counted.
Code size reads the candidate's source, so a candidate must live in a `.py` file, not in a
notebook cell or a script piped to the interpreter. Reading the candidate is the reader's part.

The promise comes first, in Lean: `lean/AlgoDesign/Flows/Workbench/Spec.lean` states what every
candidate owes (`Contract`), and `Workbench/Decide.lean` decides each piece on one network. Each
check below names its Lean piece.

The Rust differs here: there is no Rust bench. This is a Python tool for the chapter's project,
not a structure the chapter teaches.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/Workbench/`: an answer beside a
cut of the same amount is the largest, `largestOn_of_cut`; each piece of the contract is its
one-network piece on every network, `returnsAFlow_iff`, `cutMatchesFlow_iff`,
`Ops.addsAlongAugmentingPaths_iff`, `roundsAtMostN_iff`, `augmentationsAtMostNM_iff`,
`boundSetBySize_iff`; a rule that keeps its promise keeps the contract, `contract_of_promise`.
"""

from __future__ import annotations

import ast
import inspect
import io
import sys
import textwrap
import time
import tokenize
import types
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import TypeGuard

from .capacity_scaling import CapacityScaling
from .dinic import Dinic
from .edmonds_karp import EdmondsKarp
from .max_flow import PathRule
from .network import Network
from .residual import Augmentation, Residual

Rounds = list[list[Augmentation]]
"""The paths each round sent, in order; a round that sent nothing is not listed."""

Speed = Callable[[Network, Rounds], bool]
"""A speed requirement on one network: whether the rounds keep it."""


# --- The speed menu ----------------------------------------------------------------------------


def rounds_at_most_n(network: Network, rounds: Rounds) -> bool:
    """At most n rounds, for n vertices. The Lean `RoundsAtMostNOn`."""
    return len(rounds) <= network.n


def augmentations_at_most_nm(network: Network, rounds: Rounds) -> bool:
    """At most n·m added paths, for n vertices and m arrows. The Lean `AugmentationsAtMostNMOn`."""
    return sum(map(len, rounds)) <= network.n * len(network.arrows)


def bounded_by(b: Callable[[int, int], int]) -> Speed:
    """At most `b(n, m)` added paths, for a bound `b` the reader states. The Lean `BoundOn`."""

    def within(network: Network, rounds: Rounds) -> bool:
        return sum(map(len, rounds)) <= b(network.n, len(network.arrows))

    within.__name__ = f"bounded_by({getattr(b, '__name__', 'b')})"
    return within


# --- The loop ----------------------------------------------------------------------------------


def run(network: Network, rule: PathRule) -> tuple[list[int], Rounds]:
    """The flow the rule leaves and its rounds: one round at a time from the zero flow, until a
    round sends nothing, at most the total capacity plus one rounds. The Lean `PathRule.run`."""
    residual = Residual(network)
    rule.start(residual)
    rounds: Rounds = []
    fuel = sum(network.capacity) + 1
    while len(rounds) < fuel and (sent := rule.round(residual)):
        rounds.append(sent)
    return residual.flow(), rounds


# --- The contract, piece by piece --------------------------------------------------------------


def replay(network: Network, rounds: Rounds) -> Residual | None:
    """The residual graph after sending every path of `rounds` in order from the zero flow,
    on the bench's own copy; `None` if a path is not augmenting when its turn comes (from the
    source to the sink along arrows of the network, no vertex twice) or its amount is below 1 or
    above the residual capacity of an arrow on it. The Lean `FitInTurn` and `applyAll`."""
    residual = Residual(network)
    arrows = 2 * len(network.arrows)
    for sent in rounds:
        for path, amount in sent:
            at, passed = network.source, {network.source}
            for e in path:
                if not (type(e) is int and 0 <= e < arrows and residual.tail(e) == at
                        and residual.head[e] not in passed
                        and amount <= residual.residual_capacity[e]):
                    return None
                at = residual.head[e]
                passed.add(at)
            if at != network.sink or type(amount) is not int or amount < 1:
                return None
            for e in path:
                residual.send(e, amount)
    return residual


def adds_along_augmenting_paths(network: Network, rounds: Rounds) -> bool:
    """Every path the rounds added was augmenting when its turn came, its amount fitting every
    arrow on it, and carried at least one unit. The Lean `AddsAlongAugmentingPathsOn`."""
    return replay(network, rounds) is not None


def value_of(network: Network, flow: list[int]) -> int:
    """What leaves the source less what comes back into it. The Lean `value`."""
    s = network.source
    return (sum(x for (a, _), x in zip(network.arrows, flow, strict=True) if a == s)
            - sum(x for (_, b), x in zip(network.arrows, flow, strict=True) if b == s))


def is_flow(network: Network, flow: list[int]) -> bool:
    """One amount per arrow, none below 0 or above its capacity, and at every vertex but the
    source and the sink what comes in goes out. The Lean `ReturnsAFlowOn`, `IsFlow`."""
    if len(flow) != len(network.arrows):
        return False
    if any(not 0 <= x <= c for x, c in zip(flow, network.capacity, strict=True)):
        return False
    net_out = [0] * network.n
    for (a, b), x in zip(network.arrows, flow, strict=True):
        net_out[a] += x
        net_out[b] -= x
    return all(net_out[v] == 0 for v in range(network.n) if v not in (network.source, network.sink))


def is_cut_of_flow(network: Network, flow: list[int], side: list[bool]) -> bool:
    """The source on the side, the sink not, and the capacities of the arrows leaving the side
    add up to the flow amount. The Lean `CutMatchesFlowOn`."""
    cut = sum(c for (a, b), c in zip(network.arrows, network.capacity, strict=True)
              if side[a] and not side[b])
    return side[network.source] and not side[network.sink] and cut == value_of(network, flow)


def check(network: Network, flow: list[int], rounds: Rounds,
          speed: Speed | None = None) -> str | None:
    """The first piece of the contract the run breaks on `network`, in words, or `None`. The cut
    is the vertices the replayed residual graph reaches, as the Lean loop's `reached`."""
    replayed = replay(network, rounds)
    if replayed is None:
        return "along augmenting paths: a path was no augmenting path in its turn"
    if replayed.flow() != flow:
        return "the rounds do not add up to the flow the rule left"  # the Lean `Ops.walks`
    if not is_flow(network, flow):
        return "a flow"
    if not is_cut_of_flow(network, flow, replayed.reached()):
        return "a cut of the same amount: an augmenting path was left"
    if speed is not None and not speed(network, rounds):
        return f"the speed requirement {getattr(speed, '__name__', 'stated')}"
    return None


# --- Code size ---------------------------------------------------------------------------------

_GIVEN = frozenset({"algodesign.flows.residual", "algodesign.flows.network",
                    "algodesign.flows.max_flow", __name__})
Code = type | types.FunctionType
"""What code size counts: a class or a function."""

_LAYOUT = frozenset({tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
                     tokenize.DEDENT, tokenize.ENDMARKER})


def code_lines(source: str) -> int:
    """The lines of `source` that hold code: not blank, not only a comment, not in a docstring."""
    source = textwrap.dedent(source)
    docs: set[int] = set()
    for node in ast.walk(ast.parse(source)):
        body = getattr(node, "body", None)
        first = body[0] if isinstance(body, list) and body else None
        if (isinstance(first, ast.Expr) and isinstance(first.value, ast.Constant)
                and isinstance(first.value.value, str)):
            docs.update(range(first.lineno, (first.end_lineno or first.lineno) + 1))
    lines: set[int] = set()
    for tok in tokenize.generate_tokens(io.StringIO(source).readline):
        if tok.type not in _LAYOUT:
            lines.update(range(tok.start[0], tok.end[0] + 1))
    return len(lines - docs)


def counted_objects(cls: type) -> list[Code]:
    """The candidate's class, and every class and function of its own package or of this library
    that it reaches by name or by inheritance, one after another, leaving out the bench's
    `Network`, `Residual` and loop."""
    packages = {cls.__module__.split(".")[0], __name__.split(".")[0]}

    def counted(v: object) -> TypeGuard[Code]:
        return (isinstance(v, (type, types.FunctionType))
                and v.__module__.split(".")[0] in packages and v.__module__ not in _GIVEN)

    seen: list[Code] = []
    todo: list[Code] = [cls]
    while todo:
        obj = todo.pop()
        if any(obj is s for s in seen):
            continue
        seen.append(obj)
        tree = ast.parse(textwrap.dedent(inspect.getsource(obj)))
        names = sorted({n.id for n in ast.walk(tree) if isinstance(n, ast.Name)})
        space = vars(sys.modules[obj.__module__])
        todo += [v for v in map(space.get, names) if counted(v)]
        if isinstance(obj, type):
            todo += [base for base in obj.__mro__[1:] if counted(base)]
    return seen


def lines_of(cls: type) -> int:
    """The candidate's code size: the code lines of every object `counted_objects` finds."""
    return sum(code_lines(inspect.getsource(obj)) for obj in counted_objects(cls))


# --- The bench ---------------------------------------------------------------------------------


@dataclass(frozen=True)
class Entry:
    """A candidate: its name, and how to make a fresh rule of it."""
    name: str
    make: Callable[[], PathRule]


BUILT_IN = (Entry("Edmonds-Karp", EdmondsKarp), Entry("Dinic", Dinic),
            Entry("capacity scaling", CapacityScaling))
"""The library's three rules, as candidates."""


@dataclass
class NetworkResult:
    """One candidate on one network: its rounds and added paths, its best time, and the first
    piece of the contract it broke, if any."""
    rounds: int = 0
    added: int = 0
    seconds: float = 0.0
    failure: str | None = None


@dataclass
class Result:
    """One candidate on every network, or why it was not run."""
    name: str
    lines: int = 0
    networks: list[NetworkResult] = field(default_factory=list)
    not_run: str | None = None

    def failure(self) -> str | None:
        """Why the candidate was not run, or its first failure with the network's place in the
        list, or `None`."""
        if self.not_run is not None:
            return self.not_run
        return next((f"network {i}: {r.failure}" for i, r in enumerate(self.networks)
                     if r.failure is not None), None)

    def seconds(self) -> float:
        """The best times, added over the networks."""
        return sum(r.seconds for r in self.networks)


def bench(entries: Sequence[Entry], networks: Sequence[Network], speed: Speed | None = None,
          repeat: int = 3) -> list[Result]:
    """Every candidate on every network, `repeat` times, a fresh rule each time; every answer
    checked against the contract and, if given, the speed requirement."""
    results = []
    for entry in entries:
        result = Result(entry.name)
        results.append(result)
        try:
            made = type(entry.make())
        except Exception as e:  # noqa: BLE001 -- a candidate that cannot be made is not run
            result.not_run = f"making it raised {type(e).__name__}: {e}"
            continue
        try:
            result.lines = lines_of(made)
        except (OSError, TypeError) as e:
            result.not_run = f"its source cannot be read: {e}"
            continue
        for network in networks:
            out = NetworkResult(seconds=float("inf"))
            result.networks.append(out)
            for _ in range(repeat):
                try:
                    rule = entry.make()
                    begin = time.perf_counter()
                    flow, rounds = run(network, rule)
                    out.seconds = min(out.seconds, time.perf_counter() - begin)
                    out.failure = out.failure or check(network, flow, rounds, speed)
                except Exception as e:  # noqa: BLE001 -- a candidate that raises fails its verdict
                    out.failure = f"raised {type(e).__name__}: {e}"
                    break
                out.rounds, out.added = len(rounds), sum(map(len, rounds))
    return results


def frontier(results: Sequence[Result]) -> list[Result]:
    """The candidates that kept the contract on every network and that no other such candidate
    beats on both code size and time: no worse on both and better on one."""
    kept = [r for r in results if r.failure() is None]

    def beats(a: Result, b: Result) -> bool:
        return (a.lines <= b.lines and a.seconds() <= b.seconds()
                and (a.lines < b.lines or a.seconds() < b.seconds()))

    return [r for r in kept if not any(beats(q, r) for q in kept)]


def table(results: Sequence[Result]) -> str:
    """Every candidate, one line each: on the frontier or not, its code lines, its Python time in
    milliseconds, its rounds and added paths over all networks, and the first failure if it broke
    the contract."""
    front = {id(r) for r in frontier(results)}
    rows = [f"{'':2}{'candidate':<20}{'lines':>7}{'Python ms':>11}{'rounds':>9}{'paths':>9}"
            "  verdict"]
    for r in results:
        failure = r.failure()
        mark = "* " if id(r) in front else "  "
        verdict = ("keeps the contract" if failure is None
                   else f"not run: {failure}" if r.not_run is not None else f"fails on {failure}")
        rows.append(f"{mark}{r.name:<20}{r.lines:>7}{1000 * r.seconds():>11.3f}"
                    f"{sum(n.rounds for n in r.networks):>9}{sum(n.added for n in r.networks):>9}"
                    f"  {verdict}")
    rows.append("* on the Pareto frontier of code lines and time")
    return "\n".join(rows)
