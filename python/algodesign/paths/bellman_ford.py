# SPDX-License-Identifier: Apache-2.0
"""Bellman-Ford's method: the cheapest path from one start to every vertex when some arrows are
negative, or a negative cycle that the start reaches.

The method runs in rounds, and each round tries every arrow once (Kleinberg and Tardos,
*Algorithm Design*, §6.8, pp. 292-297). It works in place, on one list of costs: a round goes
through the vertices by increasing id, and each vertex's row in order; an arrow out of `u` to `w`
is tried against `u`'s cost as it is now, and when it gives `w` less than its cost (or `w` has none
yet), `w` gets that cost at once and records `u` as its previous vertex. A cost lowered earlier in
a round is used later in the same round. So after `k` rounds every cost is the cost of some path,
and no more than the cheapest over paths of at most `k` arrows: "after i rounds of updates the
value M[v] is no larger than the length of the shortest path from v to t using at most i edges"
(Kleinberg and Tardos, (6.26), pp. 295-296). The rounds are dynamic programming over the number
of arrows used, sped up: a cost may already be the cheapest over longer paths.

The rounds stop after the first that lowers nothing (Kleinberg and Tardos, p. 297): that round is
the check, and its costs are the answer. At most one round per vertex runs. A cheapest path passes
no vertex twice, so it has fewer arrows than there are vertices; if the last round still lowers a
cost, the start reaches a negative cycle. The previous vertices, written in any order, close
only negative cycles (Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, 4th
ed., Lemma 22.16 and its proof, pp. 636-637). The answer is then one such cycle: from the last
vertex that round lowered, follow the previous vertices back `n` steps, which lands on the cycle,
and then on until that vertex comes back (cp-algorithms, "Bellman-Ford algorithm",
`bellman_ford.md` l. 154). A cycle the start does not reach changes nothing.

A previous vertex changes only when a cost strictly drops. The work is at most the vertices times
the arrows; `bellman_ford_with_rounds` also gives the rounds run and the arrows tried.

`State` is the state after some rounds, as the Lean's `State`: each vertex's cost and previous
vertex, the rounds run, the last vertex the last round lowered, and the arrows tried. Its `start`
and `round` are the Lean's, and `bellman_ford` runs them. Its five checks are the pieces of the
Lean's `Valid` and `WellFormed`; the first is the box's invariant, and it and the second speak of
paths, which the state cannot see, so the tests pass in those paths' costs from `naive`. Each piece
answers on any state, broken or not.

The Rust differs here: it keeps one array and writes in place, where the Python's `round` builds
the next state's lists, and counts the tries only when asked.

The Lean definitions behind this module, in `lean/AlgoDesign/Paths/BellmanFord/`: `start`,
`round`, `cycleFrom`, `Valid`, `WellFormed`, `CycleBelowZero`, `Contract`. The Lean statements
behind this module, in `lean/AlgoDesign/Paths/BellmanFord/`: `contract`, `valid_start`,
`valid_round`, `bellmanFord_cheapest`, `bellmanFord_error`, `bellmanFord_cycle_exists`,
`bellmanFord_cost`.
"""

from __future__ import annotations

from dataclasses import dataclass

from .distances import Distances
from .network import Network


@dataclass(frozen=True)
class NegativeCycle:
    """A negative cycle that the start reaches: v0, v1, ..., v0, each vertex with an arrow to
    the next, the arrows with a negative total."""

    vertices: list[int]


def bellman_ford(network: Network, start: int) -> Distances | NegativeCycle:
    """The cheapest cost from `start` to each vertex and the vertex each was last reached from;
    or, when the start reaches a cycle whose arrows have a negative total, one such cycle."""
    return bellman_ford_with_rounds(network, start)[0]


def bellman_ford_with_rounds(network: Network,
                             start: int) -> tuple[Distances | NegativeCycle, int, int]:
    """The answer of `bellman_ford`, the rounds run and the arrows tried: at most one round per
    vertex, each trying every arrow."""
    n = network.g.n
    state = State.start(network, start)
    while True:
        state = state.round(network)
        if state.lowered is None:
            answer = Distances(state.cost, state.previous)
            return answer, state.rounds, state.tried
        if state.rounds == n:
            cycle = cycle_from(state.previous, n,
                               state.lowered)
            return (NegativeCycle(cycle),
                    state.rounds, state.tried)


def cycle_from(previous: list[int | None], n: int, x: int) -> list[int]:
    """The cycle a round that still lowers a cost shows: from `x`, the last vertex it lowered,
    follow the previous vertices back `n` steps to a vertex `y` (a vertex that records none stays
    put), then on from `y` until `y` comes back, at most `n` steps; and turn the list around, so
    each vertex is followed by the one its arrow points to."""

    def back(v: int) -> int:
        u = previous[v]
        return v if u is None else u

    y = x
    for _ in range(n):
        y = back(y)
    cycle = [y]
    for _ in range(n):
        cycle.append(back(cycle[-1]))
        if cycle[-1] == y:
            break
    cycle.reverse()
    return cycle


@dataclass
class State:
    """The state after some rounds: each vertex's cost (`None` while no path has reached it) and
    previous vertex, how many rounds have run, the last vertex the last round lowered (`None` when
    it lowered nothing), and how many arrows the rounds have tried. A vertex past the lists has no
    cost and no previous vertex.

    The checks are for tests on small networks."""

    cost: list[int | None]
    previous: list[int | None]
    rounds: int
    lowered: int | None
    tried: int

    @staticmethod
    def start(network: Network, start: int) -> State:
        """No rounds run: only the start has a cost, 0, and no vertex a previous one."""
        n = network.g.n
        if not 0 <= start < n:
            raise IndexError(f"start {start} out of range 0..{n}")
        cost: list[int | None] = [None] * n
        cost[start] = 0
        return State(cost, [None] * n, 0, None, 0)

    def round(self, network: Network) -> State:
        """One round, the vertices by increasing id and each row in order: every arrow tried
        against its vertex's cost as it is now, `cost[u]`, in the list the round writes, so a cost
        lowered earlier in the round is used later in it. The lists start as this state's."""
        cost, previous = list(self.cost), list(self.previous)
        lowered, tried = None, self.tried
        for u in range(network.g.n):
            for w, i in network.g.out[u]:
                tried += 1
                du = cost[u]
                if du is not None and (
                        (dw := cost[w]) is None
                        or du + network.cost[i] < dw):
                    cost[w] = du + network.cost[i]
                    previous[w] = u
                    lowered = w
        return State(cost, previous, self.rounds + 1,
                     lowered, tried)

    def _cost(self, v: int) -> int | None:
        return self.cost[v] if 0 <= v < len(self.cost) else None

    def _previous(self, v: int) -> int | None:
        return self.previous[v] if 0 <= v < len(self.previous) else None

    def is_cost_is_walk_at_most_cheapest(self, network: Network, walks: list[set[int]],
                                         cheapest: list[int | None]) -> bool:
        """Box invariant 1: after any number of rounds, every vertex's cost is the cost of some
        path to it (a path may pass a vertex more than once), and no more than the cheapest over
        paths with at most that many arrows. `walks[v]` holds costs of paths from the start to `v`
        that count as that path (the tests take every path of at most `naive.walk_arrows_after`
        arrows, which the tries cannot outgrow); `cheapest[v]` is the cheapest over paths to `v` of
        at most the rounds arrows, `None` when there is none (Lean `CostIsWalkAtMostCheapest`)."""
        for v in range(network.g.n):
            d = self._cost(v)
            if d is not None and (v >= len(walks) or d not in walks[v]):
                return False
            if v >= len(cheapest):
                return False
            c = cheapest[v]
            if c is not None and (d is None or d > c):
                return False
        return True

    def is_path_within_tries(self, network: Network, within: list[set[int]]) -> bool:
        """Not in the box: the path a cost is the cost of has at most as many arrows as arrows
        have been tried. `within[v]` holds the costs of every path from the start to `v` of at
        most the tried arrows (Lean `PathWithinTries`)."""
        return all((d := self._cost(v)) is None or (v < len(within) and d in within[v])
                   for v in range(network.g.n))

    def is_previous_arrow_fits(self, network: Network) -> bool:
        """Not in the box: an arrow leads from each vertex's previous vertex to it, and the
        previous vertex's cost plus the arrow's is at most the vertex's cost (Lean
        `PreviousArrowFits`)."""
        g, cost = network.g, network.cost
        for v in range(g.n):
            u = self._previous(v)
            if u is None:
                continue
            du, dv = self._cost(u), self._cost(v)
            if not 0 <= u < g.n or du is None or dv is None:
                return False
            if not any(w == v and du + cost[i] <= dv for w, i in g.out[u]):
                return False
        return True

    def _recorded_cycle(self, v: int, n: int) -> list[int] | None:
        """The cycle the previous vertices reach from `v`, if they never stop within `n` steps
        back: its vertices, each the previous vertex of the one before, the last's previous the
        first."""
        for _ in range(n):
            u = self._previous(v)
            if u is None:
                return None
            v = u
        cycle = [v]
        while (u := self._previous(cycle[-1])) != cycle[0]:
            if u is None or len(cycle) == n:
                return None
            cycle.append(u)
        return cycle

    def is_recorded_cycles_below_zero(self, network: Network) -> bool:
        """Not in the box: every cycle the previous vertices close has arrows with a negative
        total. Each recorded step, from a vertex's previous vertex to it, is taken by its cheapest
        arrow; a step with no arrow fails (Lean `RecordedCyclesBelowZero`)."""
        g, cost = network.g, network.cost
        for v in range(g.n):
            cycle = self._recorded_cycle(v, g.n)
            if cycle is None:
                continue
            total = 0
            for y in cycle:
                u = self._previous(y)
                arrows = ([cost[i] for w, i in g.out[u] if w == y]
                          if u is not None and 0 <= u < g.n else [])
                if not arrows:
                    return False
                total += min(arrows)
            if total >= 0:
                return False
        return True

    def is_no_previous_keeps_start(self, network: Network, start: int) -> bool:
        """Not in the box: a vertex that records no previous vertex keeps its first cost, 0 for
        the start and none for every other vertex (Lean `NoPreviousKeepsStart`)."""
        return all(self._cost(v) == (0 if v == start else None)
                   for v in range(network.g.n) if self._previous(v) is None)

    def check_valid(self, network: Network, start: int, walks: list[set[int]],
                    within: list[set[int]], cheapest: list[int | None]) -> str | None:
        """The first piece of the Lean `Valid` and `WellFormed` the state breaks, or `None`.
        `walks` and `cheapest` are as the first check takes them, `within` as the second."""
        if not self.is_cost_is_walk_at_most_cheapest(network, walks, cheapest):
            return "invariant 1 (cost_is_walk_at_most_cheapest)"
        if not self.is_path_within_tries(network, within):
            return "not in the box (path_within_tries)"
        if not self.is_previous_arrow_fits(network):
            return "not in the box (previous_arrow_fits)"
        if not self.is_recorded_cycles_below_zero(network):
            return "not in the box (recorded_cycles_below_zero)"
        if not self.is_no_previous_keeps_start(network, start):
            return "not in the box (no_previous_keeps_start)"
        return None

    def is_valid(self, network: Network, start: int, walks: list[set[int]],
                 within: list[set[int]], cheapest: list[int | None]) -> bool:
        """The Lean `Valid` and `WellFormed`: their five pieces."""
        return self.check_valid(network, start, walks, within, cheapest) is None
