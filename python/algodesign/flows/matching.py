# SPDX-License-Identifier: Apache-2.0
"""Matching people with objects: a reduction to max flow, with König's cover and Hall's blocked
group read from its last search.

The matching network has the source at vertex 0, person `p` at `1 + p`, object `o` at
`1 + people + o`, and the sink last. Its arrows come in three blocks, each in order: the source to
every person, one arrow per acceptable pair in input order, and every object to the sink; every
arrow carries 1. Max flow (Dinic's rule) runs on it; with an integer flow every arrow carries 0
or 1, and the pairs whose arrows carry 1 are a matching, listed in input order. The vertices the
last search reached give the rest: the people it did not reach and the objects it reached are a
cover, as many as there are pairs, with every acceptable pair incident to one of them, so no
matching is larger (König, 1931); when someone stays unmatched, the people it reached accept
between them fewer objects than there are of them (Hall, 1935).

A pair naming a person or an object outside the problem raises `ValueError`.

Every added path carries one unit out of one person, so max flow adds at most as many paths as
there are people. `max_matching_with_rounds` also gives the paths each round of max flow sent.

`State` is a flow on a problem's matching network, the state those rounds change; its
`check_valid` judges it by the box's one invariant, max flow's invariants on that network.

The Rust differs here: it also refuses a problem whose network would have more vertices or arrows
than a network may have, and gives the rounds only in test builds; its `State` refuses a problem
when it is built, where this one raises when it is judged.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/Matching/`: the pairs that carry
the unit are a matching, `carried_isMatching`; no matching is larger than a cover,
`matching_le_cover`; the people not reached and the objects reached are a cover, `isCover_read`,
no larger than the matching, `cover_le_carried`; the people reached are blocked when someone is
unmatched, `isBlocked_read`; the library's matching meets its contract, `contract`.
"""

from __future__ import annotations

from dataclasses import dataclass

from .max_flow import MaxFlow, max_flow_with_rounds
from .network import Network
from .residual import Augmentation


@dataclass
class BlockedGroup:
    """Some people, and every object one of them accepts, fewer than the people."""

    people: list[int]
    objects: list[int]


@dataclass
class Matching:
    """The matched pairs in input order, the cover's people and objects, and a blocked group when
    someone stays unmatched.

    `check_valid` judges an answer on its problem, anyone's, by the promise's three parts. That no
    matching is larger needs no check of its own: no matching is larger than a cover (Lean
    `matching_le_cover`), so a cover as large as the matching makes it a maximum one. The box's
    invariant, max flow's on the matching network, is about the flow, which the answer does not
    carry, so it is no piece here: `State` checks it on a flow, and the Lean proves that every
    round keeps it (`Ops.roundsKeep`)."""

    pairs: list[tuple[int, int]]
    cover_people: list[int]
    cover_objects: list[int]
    blocked: BlockedGroup | None

    def is_maximum_matching(self, pairs: list[tuple[int, int]]) -> bool:
        """The promise's matching: acceptable pairs, each person in at most one and each object in
        at most one (Lean `Ops.MaximumMatching`, its `IsMatching`)."""
        people = [p for p, _ in self.pairs]
        objects = [o for _, o in self.pairs]
        return (all(e in pairs for e in self.pairs)
                and len(set(people)) == len(people) and len(set(objects)) == len(objects))

    def is_cover_as_large(self, people: int, objects: int, pairs: list[tuple[int, int]]) -> bool:
        """The promise's cover: as many people and objects as there are pairs, none listed twice,
        with every acceptable pair incident to one of them (Lean `Ops.CoverAsLarge`)."""
        cp, co = self.cover_people, self.cover_objects
        return (len(set(cp)) == len(cp) and len(set(co)) == len(co)
                and all(0 <= p < people for p in cp) and all(0 <= o < objects for o in co)
                and all(p in cp or o in co for p, o in pairs)
                and len(cp) + len(co) == len(self.pairs))

    def is_blocked_group_when_short(self, people: int, pairs: list[tuple[int, int]]) -> bool:
        """The promise's blocked group: if some person stays unmatched, some people, none listed
        twice, beside exactly the objects they accept between them, fewer of those than there are
        people (Lean `Ops.BlockedGroupWhenShort`, its `IsBlocked`)."""
        if len(self.pairs) >= people:
            return True
        g = self.blocked
        if g is None:
            return False
        accepted = {o for p, o in pairs if p in g.people}
        return (len(set(g.people)) == len(g.people) and all(0 <= p < people for p in g.people)
                and len(set(g.objects)) == len(g.objects) and set(g.objects) == accepted
                and len(g.objects) < len(g.people))

    def check_valid(self, people: int, objects: int, pairs: list[tuple[int, int]]) -> str | None:
        """The first part of the promise the answer breaks on the problem, or `None`."""
        if not self.is_maximum_matching(pairs):
            return "promise (maximum_matching)"
        if not self.is_cover_as_large(people, objects, pairs):
            return "promise (cover_as_large)"
        if not self.is_blocked_group_when_short(people, pairs):
            return "promise (blocked_group_when_short)"
        return None

    def is_valid(self, people: int, objects: int, pairs: list[tuple[int, int]]) -> bool:
        """The promise's three parts, `Ops.MaximumMatching`, `Ops.CoverAsLarge` and
        `Ops.BlockedGroupWhenShort`."""
        return self.check_valid(people, objects, pairs) is None


@dataclass
class State:
    """A flow on a problem's matching network, the state the rounds of max flow change: the
    problem, and the amount on each arrow of its matching network by id.

    `check_valid` judges it by the box's one invariant, max flow's invariants on the matching
    network. Judging a state whose problem has a pair outside it raises `ValueError`, as
    `matching_network` does."""

    people: int
    objects: int
    pairs: list[tuple[int, int]]
    flow: list[int]

    def is_flow_respected(self) -> bool:
        """Box invariant 1: those of max flow, on this network; no arrow carries more than its
        capacity or a negative amount, and at every vertex but the source and the sink what comes
        in goes out (Lean `FlowRespected`)."""
        network = matching_network(self.people, self.objects, self.pairs)
        flow = MaxFlow(0, self.flow, [])
        return flow.is_within_capacity(network) and flow.is_conserved(network)

    def check_valid(self) -> str | None:
        """The first piece the state breaks, or `None`."""
        if not self.is_flow_respected():
            return "invariant 1 (flow_respected)"
        return None

    def is_valid(self) -> bool:
        """The Lean `Valid`: `FlowRespected`."""
        return self.check_valid() is None


def matching_network(people: int, objects: int, pairs: list[tuple[int, int]]) -> Network:
    """One unit from the source to every person, on every pair, and from every object to the
    sink, in that order; raise `ValueError` for a pair outside the problem."""
    for i, (p, o) in enumerate(pairs):
        if not (0 <= p < people and 0 <= o < objects):
            raise ValueError(f"pair {i} = ({p}, {o}) names someone outside the problem")
    sink = 1 + people + objects
    arrows = (
        [(0, 1 + p) for p in range(people)]
        + [(1 + p, 1 + people + o) for p, o in pairs]
        + [(1 + people + o, sink) for o in range(objects)]
    )
    return Network(sink + 1, arrows, [1] * len(arrows), 0, sink)


def max_matching_with_rounds(
    people: int, objects: int, pairs: list[tuple[int, int]]
) -> tuple[Matching, list[list[Augmentation]]]:
    """A maximum matching, a cover as large, and a blocked group when someone stays unmatched; and
    the paths each round of max flow sent."""
    answer, rounds = max_flow_with_rounds(matching_network(people, objects, pairs))
    side = answer.side
    matched = [e for e, x in zip(pairs, answer.flow[people:people + len(pairs)], strict=True) if x]
    cover_people = [p for p in range(people) if not side[1 + p]]
    cover_objects = [o for o in range(objects) if side[1 + people + o]]
    blocked = None
    if len(matched) < people:
        group = [p for p in range(people) if side[1 + p]]
        accepted = {o for p, o in pairs if side[1 + p]}
        blocked = BlockedGroup(group, sorted(accepted))
    return Matching(matched, cover_people, cover_objects, blocked), rounds


def max_matching(people: int, objects: int, pairs: list[tuple[int, int]]) -> Matching:
    """A maximum matching, a cover as large, and a blocked group when someone stays unmatched."""
    return max_matching_with_rounds(people, objects, pairs)[0]
