# SPDX-License-Identifier: Apache-2.0
"""Strong components: the groups of vertices that all reach each other, numbered so that every
arrow between two groups goes from a smaller number to a larger one.

`strong_components` is Tarjan and Zwick's Algorithm T (2024, arXiv 2201.07197v3, Fig. 2, p. 12),
walked without recursion as their Implementation V (§6.1): the path is a stack of frames
`[vertex, next position in its row]`, and a second stack F, the open list, holds the vertices that
have finished while their group has not. A vertex's entry number counts the vertices entered so far,
from 1; its climb-back number `low` starts as its entry number and drops to a smaller one when an
arrow the walk comes back over leads to a vertex with a smaller `low`. `low` 0 means not entered,
and a vertex whose group is out gets `g.n + 1`, larger than every entry number. A vertex that
finishes with its `lead` mark still on leads a group: it and the vertices above the first open
vertex with a smaller `low` on F (F's bottom is a guard with `low` 0, so that loop needs no
emptiness test). The walk stops when done (TZ p. 12): once every vertex is entered and the current
vertex climbs back to its root, everything still open is one group. The condition is tested where
a climb-back number drops, as TZ give it, in the Rust as here. Groups come out sinks first,
members in the order they finished; group number = count - 1 - the order it came out, so the
numbering is topological (AtCoder `internal_scc.hpp`, l. 56-58).

`kosaraju_sharir` is the second method (CLRS 4th ed., §20.5, p. 577): a depth-first walk on the
arrows records the finishing order, and a walk on the arrows turned around, started from vertices in
decreasing finishing order, finds one group per start. Groups come out in topological order and
are numbered so; members in the order the second walk enters them.

`condensation` shrinks each group to one vertex (TZ §3.3, p. 10): arrows between groups taken from
the original arrows, a loop dropped, one copy of each doubled arrow, with a mark per group and a
pass that clears the marks. `check_components` checks a grouping it did not compute: every vertex
in exactly one group, each group strongly connected, and the graph of groups, derived from the
arrows, without a cycle.

`Walk` is a state of Algorithm T's walk, as the Lean's `Scc.Walk` holds what its invariants read.
Its `is_followers_in_finish_order`, `is_climb_back_is_earliest` and `is_done_iff_group_out` are
the Lean `AlgorithmT.Valid`'s three pieces; each answers on any state, broken or not.
`Walk.trace` gives every state of the walk, one per step, for tests to judge.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .digraph import Digraph
from .naive import reachable
from .topo import Stuck, topological_order


def _quiet(*parts: object) -> None:
    """Does nothing: the walks call this with their own lists after each step."""


_watch: Callable[..., None] = _quiet
"""Called by `strong_components` with its `low`, `F`, `groups` and `path` after each step;
`Walk.trace` puts a recorder here for one walk."""


@dataclass(frozen=True)
class Components:
    """The groups: `group_of[v]` is v's group, `groups[c]` the members of group c."""

    group_of: list[int]
    groups: list[list[int]]


def _numbered(group_of: list[int], groups: list[list[int]]) -> Components:
    """Number groups that came out sinks first in topological order instead."""
    k = len(groups)
    return Components([k - 1 - c for c in group_of], groups[::-1])


def strong_components(g: Digraph) -> Components:
    """Algorithm T: the strong components, numbered in topological order. Linear in vertices plus
    arrows."""
    guard = g.n
    done = g.n + 1  # the `low` of a vertex whose group is out
    low = [0] * (g.n + 1)  # climb-back numbers; the guard's stays 0
    lead = [False] * g.n
    group_of = [0] * g.n
    groups: list[list[int]] = []  # in the order they come out
    F = [guard]  # the open list
    entered = 0

    def come_out(members: list[int]) -> None:
        for x in members:
            group_of[x] = len(groups)
            low[x] = done
        groups.append(members)

    for root in range(g.n):
        if low[root] != 0:
            continue
        entered += 1
        low[root], lead[root] = entered, True
        path = [[root, 0]]  # frames [vertex, next position in its row]
        while path:
            _watch(low, F, groups, path)
            frame = path[-1]
            v, i = frame
            if i < len(g.out[v]):
                frame[1] = i + 1
                w, _ = g.out[v][i]
                if low[w] == 0:  # w not entered: walk down to it
                    entered += 1
                    low[w], lead[w] = entered, True
                    path.append([w, 0])
                    continue
            else:  # every arrow of v walked: v finishes
                path.pop()
                if lead[v]:
                    members = []
                    while low[F[-1]] >= low[v]:
                        members.append(F.pop())
                    members.reverse()
                    come_out(members + [v])
                else:
                    F.append(v)
                if not path:
                    break
                w, v = v, path[-1][0]  # back over the arrow v -> w
            if low[w] < low[v]:  # climb back through w
                low[v], lead[v] = low[w], False
                if entered == g.n and low[v] == low[root]:  # stop when done
                    on_path = [x for x, _ in reversed(path)]
                    come_out(F[1:] + on_path)
                    _watch(low, F, groups, path)
                    return _numbered(group_of, groups)
        _watch(low, F, groups, path)
    return _numbered(group_of, groups)


def _mutual(g: Digraph, u: int, v: int) -> bool:
    """`u` and `v` reach each other; a vertex reaches itself."""
    return u == v or (0 <= u < g.n and 0 <= v < g.n and v in reachable(g, [u])
                      and u in reachable(g, [v]))


@dataclass
class Walk:
    """A state of Algorithm T's walk: each vertex's climb-back number (0 not entered, `g.n + 1`
    once its group is out); the open list F, top first, the guard `g.n` at its bottom; the groups
    out so far, in the order they came out, each in postorder. Then what only the invariants read:
    each vertex's entry number (0 if not entered), the vertices in the order they finished, and the
    arrows the walk has come back over, in order, as (from, to). Past the end of a list, a number
    reads 0.

    The checks are for tests on small graphs: deciding which vertices reach each other takes a
    search for every pair, so `check_valid` costs about n⁴ steps. They use `naive.reachable`, the
    tests' slow reference; the walk itself does not."""

    low: list[int]
    followers: list[int]
    groups: list[list[int]]
    pre: list[int]
    finished: list[int]
    retreats: list[tuple[int, int]]

    def _low(self, v: int) -> int:
        return self.low[v] if v < len(self.low) else 0

    def _pre(self, v: int) -> int:
        return self.pre[v] if v < len(self.pre) else 0

    def _out(self, v: int) -> bool:
        return any(v in m for m in self.groups)

    def _leader_out(self, g: Digraph, v: int) -> bool:
        """The leader of `v`'s strong component, its first-entered member, has finished."""
        return any(_mutual(g, u, v) and u in self.finished
                   and all(not _mutual(g, x, v) or self._pre(x) == 0 or self._pre(u) <= self._pre(x)
                           for x in range(g.n))
                   for u in range(g.n))

    def _climb_back(self, g: Digraph, v: int) -> int:
        """The least entry number `v` reaches along a retreating path inside its component, every
        arrow of which the walk has come back over: taking the retreats in order, the arrow x -> y
        lets x reach whatever y reached by the retreats before it."""
        reach = [{x} for x in range(g.n)]
        for x, y in self.retreats:
            if x < g.n and y < g.n and _mutual(g, x, y):
                reach[x] = reach[x] | reach[y]
        return min([self._pre(v)] + [self._pre(x) for x in reach[v]])

    def is_followers_in_finish_order(self, g: Digraph) -> bool:
        """Box invariant 1: the open list holds the finished vertices whose group has not come out
        yet; formally, exactly those, in the order they finished. F, above the guard, holds exactly
        the finished vertices whose group is not out, most recently finished on top (Lean
        `FollowersInFinishOrder`)."""
        waiting = [v for v in reversed(self.finished) if not self._out(v)]
        return self.followers == waiting + [g.n]

    def is_climb_back_is_earliest(self, g: Digraph) -> bool:
        """Box invariant 2: each vertex's climb-back number is the earliest entry number it can get
        back to within its group; formally, along arrows the walk has already come back over, from
        its entry until its leader finishes (Lean `ClimbBackIsEarliest`)."""
        return all(self._low(v) == self._climb_back(g, v) for v in range(g.n)
                   if self._pre(v) != 0 and not self._leader_out(g, v))

    def _done_iff_out(self, g: Digraph, v: int) -> bool:
        """`v` is done, and in a group out, exactly when its leader has finished."""
        leader_out = self._leader_out(g, v)
        return (self._low(v) == g.n + 1) == leader_out and self._out(v) == leader_out

    def is_done_iff_group_out(self, g: Digraph) -> bool:
        """Box invariant 3: every group that has come out is whole; formally, a vertex is marked
        done exactly when its group is out: exactly when the leader of its component has finished;
        and each group out is a whole strong component (Lean `DoneIffGroupOut`)."""
        return (all(self._done_iff_out(g, v) for v in range(g.n))
                and all((x in m) == _mutual(g, x, u)
                        for m in self.groups for u in m for x in range(g.n)))

    def check_valid(self, g: Digraph) -> str | None:
        """The first piece of the Lean `Valid` the state breaks, or `None`."""
        if not self.is_followers_in_finish_order(g):
            return "invariant 1 (followers_in_finish_order)"
        if not self.is_climb_back_is_earliest(g):
            return "invariant 2 (climb_back_is_earliest)"
        if not self.is_done_iff_group_out(g):
            return "invariant 3 (done_iff_group_out)"
        return None

    def is_valid(self, g: Digraph) -> bool:
        """The Lean `Valid`: its three pieces."""
        return self.check_valid(g) is None

    @staticmethod
    def trace(g: Digraph) -> list[Walk]:
        """Every state of `strong_components`' walk on `g`, one per step: after each root is
        entered, each walk down, each look at an entered vertex and each finish below a root (with
        the climb back it ends in), and each root's finish. What only the invariants read is taken
        from the path between two states: a vertex's entry number is its `low` when it is first
        seen, a frame gone from the top finished, and a look along an arrow, or a finish below a
        parent, comes back over that arrow. A climb back that stops the walk when done leaves the
        path unfinished and F as it was; its state is the walk's end as the Lean's walk reaches it:
        the path finished top down, and F holding the guard alone."""
        global _watch
        n = g.n
        pre = [0] * n
        finished: list[int] = []
        retreats: list[tuple[int, int]] = []
        states: list[Walk] = []
        before: list[tuple[int, int]] = []

        def record(low: list[int], F: list[int], groups: list[list[int]],
                   path: list[list[int]]) -> None:
            nonlocal before
            now = [(v, i) for v, i in path]
            followers = F[::-1]
            if len(now) == len(before) + 1:  # a root entered, or a walk down
                v = now[-1][0]
                pre[v] = low[v]
            elif len(now) + 1 == len(before):  # the top finished
                finished.append(before[-1][0])
                if now:
                    retreats.append((now[-1][0], before[-1][0]))
            else:  # a look along an arrow to an entered vertex
                v, i = before[-1]
                retreats.append((v, g.out[v][i][0]))
            if now and low[now[-1][0]] == n + 1:  # the stop: the path's vertices are out
                finished.extend(v for v, _ in reversed(now))
                followers = [n]
            states.append(Walk(low=low[:n], followers=followers,
                               groups=[list(m) for m in groups], pre=list(pre),
                               finished=list(finished), retreats=list(retreats)))
            before = now

        _watch = record
        try:
            strong_components(g)
        finally:
            _watch = _quiet
        return states


def _finishing_order(g: Digraph) -> list[int]:
    """The vertices in the order a depth-first walk on the arrows finishes them."""
    entered = [False] * g.n
    finished: list[int] = []
    for root in range(g.n):
        if entered[root]:
            continue
        entered[root] = True
        path = [[root, 0]]
        while path:
            frame = path[-1]
            v, i = frame
            if i == len(g.out[v]):
                path.pop()
                finished.append(v)
                continue
            frame[1] = i + 1
            w, _ = g.out[v][i]
            if not entered[w]:
                entered[w] = True
                path.append([w, 0])
    return finished


def kosaraju_sharir(g: Digraph) -> Components:
    """Kosaraju-Sharir: the strong components, numbered in topological order. Linear in vertices
    plus arrows."""
    group_of = [-1] * g.n
    groups: list[list[int]] = []
    for root in reversed(_finishing_order(g)):
        if group_of[root] != -1:
            continue
        c = len(groups)
        members = [root]
        group_of[root] = c
        path = [[root, 0]]  # the same walk on the rows `into`
        while path:
            frame = path[-1]
            v, i = frame
            if i == len(g.into[v]):
                path.pop()
                continue
            frame[1] = i + 1
            w, _ = g.into[v][i]
            if group_of[w] == -1:
                group_of[w] = c
                members.append(w)
                path.append([w, 0])
        groups.append(members)
    return Components(group_of, groups)


def condensation(g: Digraph, comps: Components) -> Digraph:
    """The graph of groups: one arrow c -> d for each pair of groups an arrow joins, no loops.
    Linear in vertices plus arrows."""
    marked = [False] * len(comps.groups)
    arrows: list[tuple[int, int]] = []
    for c, members in enumerate(comps.groups):
        first = len(arrows)
        for v in members:
            for w, _ in g.out[v]:
                d = comps.group_of[w]
                if d != c and not marked[d]:
                    marked[d] = True
                    arrows.append((c, d))
        for _, d in arrows[first:]:  # clear the marks this group set
            marked[d] = False
    return Digraph(len(comps.groups), arrows)


def _reaches_all(
    rows: list[list[tuple[int, int]]], group_of: list[int], members: list[int]
) -> bool:
    """Does a search from the first member, along `rows` inside the group, reach them all?"""
    c = group_of[members[0]]
    seen = {members[0]}
    stack = [members[0]]
    while stack:
        v = stack.pop()
        for w, _ in rows[v]:
            if group_of[w] == c and w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(members)


def check_components(g: Digraph, group_of: list[int]) -> str | None:
    """None if `group_of` is the strong components of `g`, numbered in any order; else the name of
    the first check it fails: "partition", "strongly connected" or "acyclic". Linear in vertices
    plus arrows."""
    if len(group_of) != g.n or any(not 0 <= c < g.n for c in group_of):
        return "partition"
    k = max(group_of, default=-1) + 1
    groups: list[list[int]] = [[] for _ in range(k)]
    for v, c in enumerate(group_of):
        groups[c].append(v)
    if any(not members for members in groups):
        return "partition"
    for members in groups:
        both_ways = (_reaches_all(g.out, group_of, members)
                     and _reaches_all(g.into, group_of, members))
        if not both_ways:
            return "strongly connected"
    of_groups = condensation(g, Components(group_of, groups))
    if isinstance(topological_order(of_groups), Stuck):
        return "acyclic"
    return None
