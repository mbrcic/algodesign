# SPDX-License-Identifier: Apache-2.0
"""Push-relabel: a largest flow by heights and excess, highest vertex first, with the gap step and
global relabels.

Max flow's loop keeps a flow from the start and stops when no augmenting path is left; push-relabel
keeps a cut's promise from the start and makes the flow legal at the end. It begins by filling every
arrow from the source to another vertex, so the vertices those arrows reach hold more than they pass
on, an excess. Each vertex has a height: the sink stands at 0, the source at `n`, and no arrow with
residual capacity drops by more than one, so a height never overstates how many arrows with residual
capacity lead to the sink. A vertex with an excess pushes along an arrow with residual capacity that
goes exactly one down, as much as its excess and the residual capacity allow; when no such arrow is
left, it is relabeled one above the lowest other vertex its arrows with residual capacity reach
(Goldberg and Tarjan, "A new approach to the maximum-flow problem", 1988; Cherkassky and Goldberg,
"On implementing the push-relabel method for the maximum flow problem", 1997; Ahuja, Magnanti and
Orlin, *Network Flows*, ch. 7).

- Highest first: each height keeps a stack of the vertices with an excess standing there, and the
  next vertex is the last one put on the highest stack that holds one. It pushes from its current
  arrow on, in its row's input order, until its excess is gone, or relabels when its row runs out;
  after a relabel its current arrow is the first of its row again.
- The gap step: when a relabel leaves a height below `n` with no vertex, no vertex above it can
  reach the sink any more, and all of them go up to `n` at once.
- Global relabels: a first-in first-out search backward from the sink over the arrows with residual
  capacity, each row in input order, gives every vertex its exact count of arrows to the sink, and
  `n` to the source and to every vertex that cannot reach the sink. One runs at the start, on the
  filled source arrows, and again after every `n` relabels.
- Two phases: the first works only on vertices below `n` and ends with the largest amount in the
  sink, some excess stranded where the sink is out of reach. The second runs the same pushes and
  relabels, highest first, without the gap step or global relabels, until the stranded excess is
  back in the source, along arrows that carry flow only (Ahuja, Magnanti and Orlin, Exercise
  7.11(d)): excess goes back the way flow brought it. The answer is then a flow.

The answer is max flow's: the amount, the flow by arrow id, and the source's side of a minimum cut,
the vertices the final residual graph reaches from the source. `push_relabel_with_counts` also
counts the pushes (after the source's arrows are filled), the relabels, the gap steps and the
global relabels (the first one included).

The Rust differs here: its lists of the vertices at each height and its stacks are linked through
arrays where here they are sets and lists, its gap step visits only the heights that hold a vertex,
and it counts the steps only in test builds.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/PushRelabel.lean`: the promise
is argued, not proved, and has max flow's shape, `promise_iff`; an answer that passes max flow's
checks is a largest flow, `largest_of_passesChecks`; checks passed on every network give the whole
promise, `promise_of_passesChecks`.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .max_flow import MaxFlow
from .network import Network
from .residual import Residual


@dataclass
class Counts:
    """How often each step ran."""

    pushes: int = 0
    relabels: int = 0
    gaps: int = 0
    global_relabels: int = 0


class PushRelabel:
    """One run: the residual graph, each vertex's height, excess and current arrow, the vertices
    at each height below `n`, and a stack of vertices with an excess for each height."""

    def __init__(self, network: Network) -> None:
        """Fill every arrow from the source to another vertex, then the first global relabel."""
        self.r = Residual(network)
        self.n, self.s, self.t = network.n, network.source, network.sink
        self.height = [0] * self.n
        self.excess = [0] * self.n
        self.current = [0] * self.n  # each vertex's current arrow, as a place in its row
        self.at_height: list[set[int]] = []
        self.active: list[list[int]] = []
        self.level = 0  # at least the highest height whose stack is not empty
        self.relabels_since = 0
        self.counts = Counts()
        for e in self.r.out[self.s]:
            v = self.r.head[e]
            if v != self.s and self.r.residual_capacity[e] > 0:
                self.excess[v] += self.r.residual_capacity[e]
                self.r.send(e, self.r.residual_capacity[e])
        self.global_relabel()

    def global_relabel(self) -> None:
        """Exact heights by a search backward from the sink; `n` for the source and every vertex
        that cannot reach the sink. Then the sets, the stacks and the current arrows start again."""
        n, s, t, r = self.n, self.s, self.t, self.r
        self.height = [n] * n
        self.height[t] = 0
        queue = deque([t])
        while queue:
            v = queue.popleft()
            for e in r.out[v]:
                u = r.head[e]  # the reverse arrow `e ^ 1` leads from u into v
                if u != s and self.height[u] == n and r.residual_capacity[e ^ 1] > 0:
                    self.height[u] = self.height[v] + 1
                    queue.append(u)
        self.at_height = [set() for _ in range(n)]
        self.active = [[] for _ in range(2 * n)]
        self.level = 0
        self.current = [0] * n
        for v in range(n):
            if v != s and self.height[v] < n:
                self.at_height[self.height[v]].add(v)
                if v != t and self.excess[v] > 0:
                    self.activate(v)
        self.relabels_since = 0
        self.counts.global_relabels += 1

    def activate(self, v: int) -> None:
        """Put `v` on the stack of its height."""
        self.active[self.height[v]].append(v)
        self.level = max(self.level, self.height[v])

    def highest_active(self) -> int | None:
        """The vertex with an excess on the highest stack, taken off it; an entry whose vertex has
        moved to another height or lost its excess is dropped on the way."""
        while True:
            stack = self.active[self.level]
            while stack:
                v = stack.pop()
                if self.height[v] == self.level and self.excess[v] > 0:
                    return v
            if self.level == 0:
                return None
            self.level -= 1

    def discharge(self, u: int, first_phase: bool) -> None:
        """Push from `u` along its current arrow on until its excess is gone; when its row runs
        out, relabel it."""
        row = self.r.out[u]
        while self.current[u] < len(row):
            e = row[self.current[u]]
            v = self.r.head[e]
            if (self.r.residual_capacity[e] > 0 and usable(e, first_phase)
                    and self.height[u] == self.height[v] + 1):
                amount = min(self.excess[u], self.r.residual_capacity[e])
                self.r.send(e, amount)
                self.counts.pushes += 1
                self.excess[u] -= amount
                if self.excess[v] == 0 and v not in (self.s, self.t):
                    self.activate(v)
                self.excess[v] += amount
                if self.excess[u] == 0:
                    return  # the arrow may still have residual capacity: it stays the current one
            self.current[u] += 1
        self.relabel(u, first_phase)

    def relabel(self, u: int, first_phase: bool) -> None:
        """Lift `u` one above the lowest other vertex its arrows with residual capacity reach. In
        the first phase no higher than `n`, with the gap step when its old height is left empty, and
        back on a stack only below `n`."""
        lowest = min(self.height[self.r.head[e]] for e in self.r.out[u]
                     if self.r.residual_capacity[e] > 0 and self.r.head[e] != u
                     and usable(e, first_phase))
        self.current[u] = 0
        self.relabels_since += 1
        self.counts.relabels += 1
        if not first_phase:
            self.height[u] = lowest + 1
            self.activate(u)
            self.level = self.height[u]
            return
        old = self.height[u]
        self.at_height[old].discard(u)
        self.height[u] = min(lowest + 1, self.n)
        if self.height[u] < self.n:
            self.at_height[self.height[u]].add(u)
        if not self.at_height[old]:
            self.gap(old)
        if self.height[u] < self.n:
            self.activate(u)
            self.level = self.height[u]

    def gap(self, empty: int) -> None:
        """No vertex is left at height `empty`: every vertex above it goes up to `n`."""
        self.counts.gaps += 1
        for h in range(empty + 1, self.n):
            for v in self.at_height[h]:
                self.height[v] = self.n
            self.at_height[h] = set()

    def first_phase(self) -> None:
        """Vertices below `n`, highest first, with a global relabel after every `n` relabels."""
        while True:
            if self.relabels_since >= self.n:
                self.global_relabel()
            u = self.highest_active()
            if u is None:
                return
            self.discharge(u, True)

    def second_phase(self) -> None:
        """Every vertex still holding an excess, highest first, until it is all back in the
        source, along arrows that carry flow only."""
        self.active = [[] for _ in range(2 * self.n)]
        self.level = 0
        self.current = [0] * self.n
        for v in range(self.n):
            if v not in (self.s, self.t) and self.excess[v] > 0:
                self.activate(v)
        while (u := self.highest_active()) is not None:
            self.discharge(u, False)

    def answer(self) -> MaxFlow:
        """The amount in the sink, the flow, and the vertices the residual graph reaches."""
        return MaxFlow(self.excess[self.t], self.r.flow(), self.r.reached())


def usable(e: int, first_phase: bool) -> bool:
    """Every residual arrow in the first phase; in the second only a reverse arrow, its residual
    capacity that arrow's flow, so excess returns along the flow that brought it."""
    return first_phase or e % 2 == 1


def push_relabel_with_counts(network: Network) -> tuple[MaxFlow, Counts]:
    """A largest flow and a cut of the same amount by push-relabel, and how often each step ran."""
    run = PushRelabel(network)
    run.first_phase()
    run.second_phase()
    return run.answer(), run.counts


def push_relabel(network: Network) -> MaxFlow:
    """A largest flow from the source to the sink, and the source's side of a cut of the same
    amount, by push-relabel."""
    return push_relabel_with_counts(network)[0]
