# SPDX-License-Identifier: Apache-2.0
"""The cheapest flow of a given amount: max flow's loop with the path rule "cheapest", stopped at
the requested amount.

Each arrow has a cost per unit; residual arrow `2i`, along arrow `i`, costs `cost[i]`, and its
reverse arrow `2i + 1` refunds it, so it costs `-cost[i]`. Every vertex has a height, all zero at
the start. A round is Dijkstra's search from the source over the unsaturated residual arrows, each
row in input order, on changed costs: an arrow's cost plus the height at its start minus the height
at its end. The queue is a binary heap (`heapq`) of entries `(distance, vertex)`, so ties go to the
lower vertex id, as chapter 6's Dijkstra; a vertex's distance and the arrow that reached it change
only when the distance strictly drops, so the first vertex labeled wins. The search stops as soon as
the sink is settled. The path back from the sink is sent its bottleneck, or the amount still
requested if that is less. Then every settled vertex adds its distance to its height and every other
vertex adds the sink's. The rounds stop when the amount is sent, or when the search never settles
the sink; then the side, the vertices arrows with residual capacity still reach from the source, is
a cut whose capacity is the smaller amount sent.

Under the heights every unsaturated arrow has a changed cost of zero or more, so the search finds a
cheapest path to add, and the heights prove the flow is the cheapest for its amount (successive
shortest paths: Edmonds and Karp, 1972, for the first heights all zero; Ahuja, Magnanti and Orlin,
*Network Flows*, §9.7, p. 320, and the height update of a search stopped at the sink,
pp. 322–323, there with the opposite sign).

A cost list of the wrong length, or a cost below zero, raises `ValueError`: the zero heights fit
only when no arrow costs less than nothing.

Each round is one search and sends at least one unit, so there are at most as many rounds as the
requested amount. `min_cost_flow_with_rounds` also gives every round (its path and amount, the
heights after it, and how many vertices its search settled) and how many vertices every search
settled, a last one that missed the sink included.

The Rust differs here: its search's arrays and queue are kept from round to round, it sends along
the arrows that reached each vertex without building the path, and it records the rounds only in
test builds; its capacities are generic, and the amount still requested is converted to them.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/MinCostFlow/`: the library's
rounds meet the contract, `contract`.
"""

from __future__ import annotations

import heapq
from dataclasses import dataclass

from .max_flow import MaxFlow, value_of
from .network import Network
from .residual import Augmentation, Residual


@dataclass
class MinCostFlow:
    """The amount sent, its total cost, the amount on each arrow by id, the height of each vertex,
    and for each vertex whether arrows with residual capacity reach it from the source.

    `check_valid` judges an answer on its problem, anyone's, piece by piece: the box's three
    invariants on the flow and the heights, one amount per arrow and one height per vertex, and
    the promise's amount and cut. Invariant 2, the flow cheapest for its amount, is judged against
    `cheapest`, the smallest cost of any flow of the amount the flow sends, found elsewhere (for a
    small network, by `naive.cheapest_cost`); heights that fit a flow also prove it (Lean
    `cheapest_of_heightsFit`). The reported `value` and `cost` have no piece of their own; the
    amount and the cost are measured on the flow itself."""

    value: int
    cost: int
    flow: list[int]
    heights: list[int]
    side: list[bool]

    def _as_max_flow(self) -> MaxFlow:
        """The flow and the side as a max flow's answer, to read max flow's pieces on."""
        return MaxFlow(self.value, self.flow, self.side)

    def is_flow_respected(self, network: Network) -> bool:
        """Box invariant 1: max flow's invariants 1-3, no arrow over its capacity or below zero and
        nothing lost at any vertex but the source and the sink (Lean `FlowRespected`)."""
        f = self._as_max_flow()
        return f.is_within_capacity(network) and f.is_conserved(network)

    def is_cheapest_for_amount(self, network: Network, cost: list[int],
                               cheapest: int | None) -> bool:
        """Box invariant 2: the current flow is the cheapest for its current amount (Lean
        `CheapestForAmount`). `cheapest` is the smallest cost of any flow of the amount this flow
        sends, `None` when no flow sends it, and then no flow is cheaper. A missing amount or cost
        reads as 0."""
        def at(xs: list[int], i: int) -> int:
            return xs[i] if i < len(xs) else 0

        own = sum(at(cost, i) * at(self.flow, i) for i in range(len(network.arrows)))
        return cheapest is None or own <= cheapest

    def is_heights_fit_everywhere(self, network: Network, cost: list[int]) -> bool:
        """Box invariant 3: under the heights, every unsaturated arrow has a changed cost of at
        least zero (Lean `HeightsFitEverywhere`). Arrow `i` from `a` to `b` has the changed cost
        `cost[i] + h(a) - h(b)` if it has residual capacity left, and its reverse arrow the negative
        of that if it carries something. On a flow within capacity this is the rule per arrow: at
        least zero on an empty arrow, zero on a partly loaded one, at most zero on a full one, and
        nothing on an arrow of capacity zero. A missing amount, cost or height reads as 0."""
        def at(xs: list[int], i: int) -> int:
            return xs[i] if i < len(xs) else 0

        def fits(i: int, a: int, b: int) -> bool:
            x = at(self.flow, i)
            changed = at(cost, i) + at(self.heights, a) - at(self.heights, b)
            return (x >= network.capacity[i] or changed >= 0) and (x <= 0 or changed <= 0)

        return all(fits(i, a, b) for i, (a, b) in enumerate(network.arrows))

    def is_well_formed(self, network: Network) -> bool:
        """Not in the box: one amount per arrow and one height per vertex (Lean `WellFormed`)."""
        return len(self.flow) == len(network.arrows) and len(self.heights) == network.n

    def is_sends_a_flow(self, network: Network, amount: int) -> bool:
        """The promise's flow: a flow, carrying at most the requested amount (Lean
        `Ops.SendsAFlow`). That it is a flow is invariant 1 with one amount per arrow, checked
        before it; this piece checks the amount."""
        return value_of(network, self.flow) <= amount

    def is_short_only_at_a_cut(self, network: Network, amount: int) -> bool:
        """The promise's cut: when less than the requested amount is sent, the source is on the
        side, the sink is not, and the capacities of the arrows leaving the side add up to the
        amount sent (Lean `Ops.ShortOnlyAtACut`)."""
        return (value_of(network, self.flow) >= amount
                or self._as_max_flow().is_cut_matches_flow(network))

    def check_valid(self, network: Network, cost: list[int], amount: int,
                    cheapest: int | None) -> str | None:
        """The first piece the answer breaks on the problem, or `None`; `cheapest` as for
        `is_cheapest_for_amount`."""
        if not self.is_flow_respected(network):
            return "invariant 1 (flow_respected)"
        if not self.is_cheapest_for_amount(network, cost, cheapest):
            return "invariant 2 (cheapest_for_amount)"
        if not self.is_heights_fit_everywhere(network, cost):
            return "invariant 3 (heights_fit_everywhere)"
        if not self.is_well_formed(network):
            return "not in the box (well_formed)"
        if not self.is_sends_a_flow(network, amount):
            return "promise (sends_a_flow)"
        if not self.is_short_only_at_a_cut(network, amount):
            return "promise (short_only_at_a_cut)"
        return None

    def is_valid(self, network: Network, cost: list[int], amount: int,
                 cheapest: int | None) -> bool:
        """The Lean `Valid` and `WellFormed` on the flow and the heights, and `Ops.SendsAFlow` and
        `Ops.ShortOnlyAtACut`."""
        return self.check_valid(network, cost, amount, cheapest) is None


@dataclass
class MinCostRound:
    """One round: the path it added with its amount, the heights after it, the vertices settled."""

    sent: Augmentation
    heights: list[int]
    settled: int


def changed_cost(residual: Residual, cost: list[int], heights: list[int], e: int) -> int:
    """The cost of residual arrow `e`, plus the height at its start, minus the height at its end."""
    own = cost[e // 2] if e % 2 == 0 else -cost[e // 2]
    return own + heights[residual.tail(e)] - heights[residual.head[e]]


def cheapest_path(
    residual: Residual, cost: list[int], heights: list[int]
) -> tuple[list[int] | None, list[int | None], list[bool]]:
    """Dijkstra's search on changed costs, stopped when the sink is settled: the path from the
    source (`None` if the sink is never settled), each vertex's distance, and which vertices are
    settled."""
    known: list[int | None] = [None] * residual.n
    came_by: list[int | None] = [None] * residual.n  # the arrow that last lowered each distance
    settled = [False] * residual.n
    known[residual.source] = 0
    queue = [(0, residual.source)]
    while queue:
        du, u = heapq.heappop(queue)
        # an old entry: u was settled at a smaller distance
        if settled[u]:
            continue
        settled[u] = True
        if u == residual.sink:
            return path_back(residual, came_by), known, settled
        for e in residual.out[u]:
            w = residual.head[e]
            if residual.residual_capacity[e] == 0 or settled[w]:
                continue
            dw = du + changed_cost(residual, cost, heights, e)
            if (kw := known[w]) is None or dw < kw:
                known[w] = dw
                came_by[w] = e
                heapq.heappush(queue, (dw, w))
    return None, known, settled


def path_back(residual: Residual, came_by: list[int | None]) -> list[int]:
    """The arrows that reached the vertices from the source to the sink, source first."""
    path: list[int] = []
    v = residual.sink
    while (e := came_by[v]) is not None:
        path.append(e)
        v = residual.tail(e)
    path.reverse()
    return path


def min_cost_flow_with_rounds(
    network: Network, cost: list[int], amount: int
) -> tuple[MinCostFlow, list[MinCostRound], list[int]]:
    """The cheapest flow of `amount`, or of the most the network carries; every round; and
    how many vertices every search settled, a last one that missed the sink included."""
    if len(cost) != len(network.arrows):
        raise ValueError(f"{len(cost)} costs for {len(network.arrows)} arrows")
    for i, c in enumerate(cost):
        if c < 0:
            raise ValueError(f"arrow {i} costs {c}, less than nothing")
    residual = Residual(network)
    heights = [0] * network.n
    sent = 0
    rounds: list[MinCostRound] = []
    searches: list[int] = []
    while sent < amount:
        path, known, settled = cheapest_path(residual, cost, heights)
        searches.append(sum(settled))
        if path is None:
            break
        bottleneck = min(residual.residual_capacity[e] for e in path)
        round_amount = min(bottleneck, amount - sent)
        for e in path:
            residual.send(e, round_amount)
        sent += round_amount
        to_sink = known[network.sink]
        assert to_sink is not None
        heights = [
            h + (d if is_settled and d is not None else to_sink)
            for h, d, is_settled in zip(heights, known, settled, strict=True)
        ]
        rounds.append(MinCostRound((path, round_amount), heights, sum(settled)))
    flow = residual.flow()
    total = sum(c * x for c, x in zip(cost, flow, strict=True))
    return MinCostFlow(sent, total, flow, heights, residual.reached()), rounds, searches


def min_cost_flow(network: Network, cost: list[int], amount: int) -> MinCostFlow:
    """The cheapest flow of `amount` from the source to the sink, arrow `i` costing `cost[i]` per
    unit; if the network cannot carry `amount`, the most it can, cheapest for it, with a cut that
    proves it."""
    return min_cost_flow_with_rounds(network, cost, amount)[0]
