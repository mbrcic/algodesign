# SPDX-License-Identifier: Apache-2.0
"""A*: the cheapest path from one start to one goal, Dijkstra's walk with each queue entry's key the
known cost plus an estimate of the cost still to go.

The estimate is one number per vertex, given by the caller. The walk is Dijkstra's, entry for
entry: the smallest (key, vertex) comes off the queue, a settled vertex is skipped and never tried
again (no reopening), and the vertex taken off is settled at its key less its estimate, which is
its known cost. The start is queued with its own estimate. The walk stops the moment the goal comes
off the queue, before its arrows are tried (Hart, Nilsson and Raphael, "A Formal Basis for the
Heuristic Determination of Minimum Cost Paths", IEEE Trans. SSC 4 (1968), p. 102).

Why it works: give arrow `a -> b` the changed cost, its cost plus the estimate at `b` minus the
estimate at `a`. Along a path the changes cancel but for the two ends, so the cheapest paths stay
the cheapest, and on the changed costs the search is Dijkstra's walk to the goal, every key moved by
the estimate at the start (Sanders, Mehlhorn, Dietzfelbinger and Dementiev, *Sequential and Parallel
Algorithms and Data Structures*, §10.8.1, pp. 323–324). Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, 4th ed., §23.3, eq. (23.10), p. 663, reweight by `w + h(u) - h(v)`:
the same change with `h` the negated estimate.

The box's invariant is on the estimate: at least zero, zero at the goal, and along any arrow it
drops by no more than the arrow costs (it is consistent). Then no changed cost is negative, and
Dijkstra's walk is right on them. No arrow itself needs to cost at least zero. Nothing checks
the estimate; the box assumes it. An estimate that never overstates the cost to go but breaks the
invariant can give a dearer path: on the map in the tests, 8 where the cheapest is 7 (the lesson of
petgraph's issue #378).

`a_star` is the search with a heap (`heapq`) of lazy entries, as `dijkstra_to`.
`a_star_with_settled` also gives the vertices in the order they were settled, and runs `start_state`
and `step`, the Lean's `start` and `step`, on Dijkstra's walk state `State`, whose queue is a list
kept in order; the search's state is Dijkstra's, with the keys moved by the estimate (the Lean's
carries the estimate and the goal too). Its pieces are `is_estimate_is_consistent`, the box's
invariant, and `is_walk_is_cheapest_paths_on_changed_costs`, not in the box: the state read on the
changed costs (`changed`, `shifted`) passes Dijkstra's checks, whose true cheapest costs, on the
changed costs, the tests pass in from `naive`.

The Rust differs here: it asserts the invariant in debug builds, and an estimate list of the wrong
length is an `Err` there, a `ValueError` here. Its search is Dijkstra's keyed walk, the one its
`dijkstra_to` runs, where this module writes its own loop, and its `a_star_with_settled` runs that
heap walk too, where this one runs `start_state` and `step`. The Lean reads a missing estimate as
0, so it takes an estimate list of any length, where both refuse one of the wrong length.

The Lean statements behind this module, in `lean/AlgoDesign/Paths/AStar/`: `contract`,
`valid_start`, `valid_step`, `astar_goal`, `astar_previous`, `astar_unreached`, `shifted_step`,
`final_counted`.
"""

from __future__ import annotations

import heapq
from bisect import insort

from .dijkstra import State
from .distances import Distances
from .network import Network


def _check(network: Network, start: int, goal: int, estimate: list[int]) -> None:
    """One estimate per vertex, and the start and the goal vertices of the network."""
    n = network.g.n
    if len(estimate) != n:
        raise ValueError(f"{len(estimate)} estimates for {n} vertices: one estimate per vertex")
    if not 0 <= start < n:
        raise IndexError(f"start {start} out of range 0..{n}")
    if not 0 <= goal < n:
        raise IndexError(f"goal {goal} out of range 0..{n}")


def a_star(network: Network, start: int, goal: int, estimate: list[int]) -> Distances:
    """The cheapest cost from `start` to `goal`, and the vertex each reached vertex was last reached
    from; correct when the estimate keeps the box's invariant. Only the goal's cost, and the costs
    of the vertices settled before it, are final."""
    _check(network, start, goal, estimate)
    g, cost = network.g, network.cost
    known: list[int | None] = [None] * g.n
    previous: list[int | None] = [None] * g.n
    settled = [False] * g.n
    known[start] = 0
    queue = [(estimate[start], start)]
    while queue:
        key, u = heapq.heappop(queue)
        # an old entry: u was settled at a smaller key
        if settled[u]:
            continue
        settled[u] = True
        if u == goal:
            break
        du = key - estimate[u]
        for w, i in g.out[u]:
            if settled[w]:
                continue
            dw = du + cost[i]
            if (kw := known[w]) is None or dw < kw:
                known[w] = dw
                previous[w] = u
                heapq.heappush(queue, (dw + estimate[w], w))
    return Distances(known, previous)


def a_star_with_settled(network: Network, start: int, goal: int,
                        estimate: list[int]) -> tuple[Distances, list[int]]:
    """The answer of `a_star`, and the vertices in the order they were settled, the goal last if it
    is reached; run through `start_state` and `step`, whose list queue and settled list make each
    step cost up to the number of vertices."""
    _check(network, start, goal, estimate)
    state = start_state(network, estimate, start)
    while state.queue:
        _, u = state.queue[0]
        if u == goal and u not in state.settled:
            state.queue.pop(0)
            state.settled.append(u)
            break
        step(network, estimate, state)
    return Distances(state.known, state.previous), state.settled


def _at(estimate: list[int], v: int) -> int:
    """The estimate at `v`; 0 past the list, as the Lean reads it."""
    return estimate[v] if 0 <= v < len(estimate) else 0


def start_state(network: Network, estimate: list[int], start: int) -> State:
    """The search's start: nothing settled; only the start known, at cost 0, and queued with its
    estimate (Lean `AStar.start`)."""
    n = network.g.n
    if not 0 <= start < n:
        raise IndexError(f"start {start} out of range 0..{n}")
    known: list[int | None] = [None] * n
    known[start] = 0
    return State([], known, [None] * n, [(_at(estimate, start), start)], 1)


def step(network: Network, estimate: list[int], state: State) -> None:
    """Take the smallest entry off the queue; skip its vertex if it is settled, else settle it and
    try every arrow out of it, in its row's order, from its key less its estimate (Lean
    `AStar.step`). An empty queue is left as it is."""
    if not state.queue:
        return
    key, u = state.queue.pop(0)
    if u in state.settled:
        return
    state.settled.append(u)
    du = key - _at(estimate, u)
    for w, i in network.g.out[u]:
        if w in state.settled:
            continue
        dw = du + network.cost[i]
        if (kw := state.known[w]) is None or dw < kw:
            state.known[w] = dw
            state.previous[w] = u
            insort(state.queue, (dw + _at(estimate, w), w))
            state.pushed += 1


def changed(network: Network, estimate: list[int]) -> Network:
    """The changed costs: arrow `a -> b` costs its cost plus the estimate at `b` minus the estimate
    at `a`, on the same graph (Lean `AStar.changed`)."""
    return Network(network.g, [c + _at(estimate, b) - _at(estimate, a)
                               for (a, b), c in zip(network.g.arrows, network.cost, strict=True)])


def shifted(state: State, estimate: list[int], h0: int) -> State:
    """The search's state read on the changed costs: each known cost plus the estimate at its
    vertex, and each queue key, less `h0`, the estimate at the start (Lean `AStar.shifted`)."""
    known = [None if d is None else d + _at(estimate, v) - h0 for v, d in enumerate(state.known)]
    queue = [(key - h0, v) for key, v in state.queue]
    return State(list(state.settled), known, list(state.previous), queue, state.pushed)


def is_estimate_is_consistent(network: Network, goal: int, estimate: list[int]) -> bool:
    """Box invariant 1: the estimate is at least zero, is zero at the goal, and along any arrow
    drops by no more than the arrow costs; an estimate past the list counts as 0 (Lean
    `EstimateIsConsistent`)."""
    g = network.g
    return (all(_at(estimate, v) >= 0 for v in range(g.n))
            and _at(estimate, goal) == 0
            and all(_at(estimate, a) <= c + _at(estimate, b)
                    for (a, b), c in zip(g.arrows, network.cost, strict=True)))


def is_walk_is_cheapest_paths_on_changed_costs(network: Network, start: int, estimate: list[int],
                                               state: State, cheapest: list[int | None],
                                               through: list[int | None]) -> bool:
    """Not in the box: read on the changed costs, the search's state is a legal state of
    Dijkstra's walk from `start`. `cheapest` and `through` are the true cheapest costs Dijkstra's
    checks take, on the changed costs: over all paths, and over paths through the settled vertices
    (Lean `WalkIsCheapestPathsOnChangedCosts`)."""
    on = shifted(state, estimate, _at(estimate, start))
    return on.is_valid(changed(network, estimate), start, cheapest, through)


def check_valid(network: Network, start: int, goal: int, estimate: list[int], state: State,
                cheapest: list[int | None], through: list[int | None]) -> str | None:
    """The first piece of the Lean `Valid` and `WellFormed` the search breaks, or `None`.
    `cheapest` and `through` are the true cheapest costs on the changed costs."""
    if not is_estimate_is_consistent(network, goal, estimate):
        return "invariant 1 (estimate_is_consistent)"
    if not is_walk_is_cheapest_paths_on_changed_costs(network, start, estimate, state, cheapest,
                                                      through):
        return "not in the box (walk_is_cheapest_paths_on_changed_costs)"
    return None


def is_valid(network: Network, start: int, goal: int, estimate: list[int], state: State,
             cheapest: list[int | None], through: list[int | None]) -> bool:
    """The Lean `Valid` and `WellFormed`: their two pieces."""
    return check_valid(network, start, goal, estimate, state, cheapest, through) is None
