# SPDX-License-Identifier: Apache-2.0
"""Slow references that are correct by inspection, for the tests to compare the real rules
against: the smallest cut found by trying every set of vertices with the source and without the
sink, a check of an answer against the contract, and the cheapest cost of a flow of a given amount,
found by trying every flow. The rules themselves never use them. Twenty vertices make a quarter of
a million sets, so `min_cut` is for networks of a handful of vertices, and `cheapest_cost` for a
handful of small arrows. `cheapest_assignment` tries every order of the objects, so it is for
tables of a handful of people.
"""

from __future__ import annotations

from itertools import permutations, product

from .max_flow import MaxFlow, cut_capacity, value_of
from .network import Network


def min_cut(network: Network) -> int:
    """The smallest capacity of a cut, by trying every set with the source and without the sink."""
    s, t = network.source, network.sink
    others = [v for v in range(network.n) if v not in (s, t)]
    cuts = []
    for choice in product([False, True], repeat=len(others)):
        side = [False] * network.n
        side[s] = True
        for v, inside in zip(others, choice, strict=True):
            side[v] = inside
        cuts.append(cut_capacity(network, side))
    return min(cuts)


def check(network: Network, answer: MaxFlow) -> str | None:
    """The first part of the contract `answer` breaks on `network`; `None` if none: the label
    `MaxFlow.check_valid` gives, then "value" when the reported amount is not what the flow
    sends."""
    if (broken := answer.check_valid(network)) is not None:
        return broken
    if answer.value != value_of(network, answer.flow):
        return "value"
    return None


def cheapest_cost(network: Network, cost: list[int], value: int) -> int | None:
    """The smallest cost of a flow of amount `value`, by trying every integer amount on every arrow;
    `None` if no flow has that amount."""
    s, t = network.source, network.sink
    best: int | None = None
    for flow in product(*(range(c + 1) for c in network.capacity)):
        net_out = [0] * network.n
        for (a, b), x in zip(network.arrows, flow, strict=True):
            net_out[a] += x
            net_out[b] -= x
        conserved = all(net_out[v] == 0 for v in range(network.n) if v not in (s, t))
        if conserved and net_out[s] == value:
            total = sum(c * x for c, x in zip(cost, flow, strict=True))
            best = total if best is None else min(best, total)
    return best


def cheapest_assignment(cost: list[list[int]]) -> int:
    """The smallest total cost of an assignment of the square table `cost`, by trying every order
    of the objects."""
    n = len(cost)
    return min(sum(cost[p][obj[p]] for p in range(n)) for obj in permutations(range(n)))
