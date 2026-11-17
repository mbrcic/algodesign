# SPDX-License-Identifier: Apache-2.0
"""Max flow: one loop around an open choice, the path rule.

The loop starts from the zero flow and asks the rule for one round at a time. A round sends more
along augmenting paths of the residual graph and returns them, each as its residual arrows from
the source and the amount sent; the first round that returns none ends the loop. The answer is the
flow and the source's side of a cut: the vertices the residual graph still reaches from the
source. Its capacity equals the flow amount, and no flow exceeds any cut, so the flow is the
largest (Ford and Fulkerson, "Maximal flow through a network", 1956).

A rule is any object with `start(residual)`, called once before the first round, and
`round(residual)`. It must keep the promise every rule keeps: send only along augmenting paths,
each path carrying at least one unit, and send nothing only when no augmenting path is left.
`Dinic` is the default; `EdmondsKarp` and `CapacityScaling` are the others.

`max_flow_with_rounds` also gives the paths each round sent, in order.

The Rust differs here: its rule returns only whether it sent anything, and records its paths
only in test builds; and its loop is generic over the capacity type.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/MaxFlow/`: the loop's answer is
the flow its rounds add, `PathRule.run_walks`; no flow exceeds a cut, `value_le_cutCapacity`; the
last search's cut has the flow amount, `reached_cut`; every rule keeping its promise meets the
contract, `PathRule.contract`; the library's loop around Dinic's rule meets it, `contract`.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from .dinic import Dinic
from .network import Network
from .residual import Augmentation, Residual


class PathRule(Protocol):
    """How one round of the loop chooses the paths it sends along."""

    def start(self, residual: Residual) -> None:
        """Get ready for the zero flow of a new network."""

    def round(self, residual: Residual) -> list[Augmentation]:
        """Send along the paths the rule chooses, and return them in order."""
        ...


@dataclass
class MaxFlow:
    """The flow amount, the amount on each arrow by id, and the source's side of a cut.

    `check_valid` judges an answer on its network, anyone's, piece by piece: the box's invariants
    on the flow, one amount per arrow, and the cut beside it. The promise's third part, that the
    flow is the largest, needs no check of its own: no flow exceeds any cut (Lean
    `value_le_cutCapacity`), so a cut of the flow's amount makes it the largest. The reported
    `value` has no piece of its own; the cut is measured against what the flow itself sends."""

    value: int
    flow: list[int]
    side: list[bool]

    def _on(self, i: int) -> int:
        """The amount on arrow `i`, read as 0 past the end of the list."""
        return self.flow[i] if i < len(self.flow) else 0

    def is_within_capacity(self, network: Network) -> bool:
        """Box invariant 1: no arrow carries more than its capacity, or a negative amount (Lean
        `WithinCapacity`)."""
        return all(0 <= self._on(i) <= c for i, c in enumerate(network.capacity))

    def is_conserved(self, network: Network) -> bool:
        """Box invariant 2: at every vertex except the source and the sink, what comes in goes out
        (Lean `Conserved`)."""
        net_out = [0] * network.n
        for i, (a, b) in enumerate(network.arrows):
            net_out[a] += self._on(i)
            net_out[b] -= self._on(i)
        return all(net_out[v] == 0 for v in range(network.n)
                   if v not in (network.source, network.sink))

    def is_well_formed(self, network: Network) -> bool:
        """Not in the box: the flow lists one amount per arrow (Lean `WellFormed`)."""
        return len(self.flow) == len(network.arrows)

    def is_cut_matches_flow(self, network: Network) -> bool:
        """The promise's cut: the source on one side, the sink on the other, and the capacities of
        arrows leaving the source's side add up to the flow amount; `side` marks every vertex
        (Lean `Ops.CutMatchesFlow`)."""
        side = self.side
        return (len(side) == network.n and side[network.source] and not side[network.sink]
                and cut_capacity(network, side) == value_of(network, self.flow))

    def check_valid(self, network: Network) -> str | None:
        """The first piece the answer breaks on `network`, or `None`."""
        if not self.is_within_capacity(network):
            return "invariant 1 (within_capacity)"
        if not self.is_conserved(network):
            return "invariant 2 (conserved)"
        # Invariant 3, an integer on every arrow, holds by the type.
        if not self.is_well_formed(network):
            return "not in the box (well_formed)"
        if not self.is_cut_matches_flow(network):
            return "promise (cut_matches_flow)"
        return None

    def is_valid(self, network: Network) -> bool:
        """The Lean `Valid` and `WellFormed` on the flow, and `Ops.CutMatchesFlow` on the cut."""
        return self.check_valid(network) is None


def max_flow_with_rounds(
    network: Network, rule: PathRule | None = None
) -> tuple[MaxFlow, list[list[Augmentation]]]:
    """A largest flow and a cut of the same amount, and the paths each round sent."""
    rule = Dinic() if rule is None else rule
    residual = Residual(network)
    rule.start(residual)
    rounds: list[list[Augmentation]] = []
    while sent := rule.round(residual):
        rounds.append(sent)
    return answer(network, residual), rounds


def max_flow(network: Network, rule: PathRule | None = None) -> MaxFlow:
    """A largest flow from the source to the sink, and the source's side of a cut of the same
    amount; by Dinic's rule unless another is given."""
    rule = Dinic() if rule is None else rule
    residual = Residual(network)
    rule.start(residual)
    while rule.round(residual):
        pass
    return answer(network, residual)


def answer(network: Network, residual: Residual) -> MaxFlow:
    """The flow, its amount (what leaves the source less what comes back; loops count on neither
    side), and the vertices the residual graph reaches."""
    flow = residual.flow()
    s = network.source
    leaving = sum(flow[i] for i, (a, b) in enumerate(network.arrows) if a == s and b != s)
    entering = sum(flow[i] for i, (a, b) in enumerate(network.arrows) if b == s and a != s)
    return MaxFlow(leaving - entering, flow, residual.reached())


def value_of(network: Network, flow: list[int]) -> int:
    """What leaves the source along `flow`, less what comes back into it; an arrow past the end of
    the list carries 0 (Lean `value`)."""
    s = network.source
    out = sum(x for (a, _), x in zip(network.arrows, flow, strict=False) if a == s)
    back = sum(x for (_, b), x in zip(network.arrows, flow, strict=False) if b == s)
    return out - back


def cut_capacity(network: Network, side: list[bool]) -> int:
    """The capacities of the arrows leaving the vertices marked in `side`, one mark per vertex
    (Lean `cutCapacity`)."""
    return sum(
        c for (a, b), c in zip(network.arrows, network.capacity, strict=True)
        if side[a] and not side[b]
    )
