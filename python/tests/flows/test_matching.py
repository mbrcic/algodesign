"""Matching by max flow: the chapter's rooms with the answer the Rust's tests pin, and small random
problems against the largest matching found by trying every set of pairs, every answer checked
against the contract: a matching, a cover as large touching every pair, and a blocked group exactly
when someone stays unmatched."""

from __future__ import annotations

import random
from itertools import combinations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.flows import BlockedGroup, Dinic, Matching, max_flow_with_rounds, max_matching
from algodesign.flows.matching import State, matching_network, max_matching_with_rounds

Pairs = list[tuple[int, int]]

# A variant of the chapter's rooms in which Anita (0) also accepts room 2: Daniel (1) accepts
# room 1, Tomás (2) rooms 1 and 2, Juan (3) rooms 3 and 4; room r is object r - 1.
ROOMS: Pairs = [(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 2), (3, 3)]

# The chapter's quiet rooms, the people in the order of its hand run: Tomás (0) accepts rooms 1
# and 2, Daniel (1) and Anita (2) room 1, Juan (3) rooms 3 and 4.
BOOK_ROOMS: Pairs = [(0, 0), (0, 1), (1, 0), (2, 0), (3, 2), (3, 3)]


def distinct(xs: list[int]) -> bool:
    return len(set(xs)) == len(xs)


def check(people: int, objects: int, pairs: Pairs, m: Matching) -> str | None:
    """What breaks in `m` as an answer: the label `check_valid` gives, then the library's own
    choices, no group beside a matching of everyone and the lists in increasing order; `None` if
    nothing."""
    # Lean: Ops.MaximumMatching, Ops.CoverAsLarge, Ops.BlockedGroupWhenShort
    if (broken := m.check_valid(people, objects, pairs)) is not None:
        return broken
    if m.blocked is not None and len(m.pairs) == people:
        return "a blocked group beside a matching of everyone"
    lists = [m.cover_people, m.cover_objects]
    if m.blocked is not None:
        lists += [m.blocked.people, m.blocked.objects]
    if any(xs != sorted(xs) for xs in lists):
        return "a list out of order"
    return None


def brute_force(pairs: Pairs) -> int:
    """The size of a largest matching, by trying every set of pairs, largest first."""
    for k in range(len(pairs), 0, -1):
        for chosen in combinations(pairs, k):
            if distinct([p for p, _ in chosen]) and distinct([o for _, o in chosen]):
                return k
    return 0


def paths_added(people: int, objects: int, pairs: Pairs) -> int:
    """How many paths max flow added on the matching network."""
    _, rounds = max_flow_with_rounds(matching_network(people, objects, pairs), Dinic())
    return sum(len(r) for r in rounds)


def test_the_rooms_match_three_and_name_the_cover_and_the_blocked_group() -> None:
    m = max_matching(4, 4, ROOMS)
    assert m.pairs == [(0, 0), (2, 1), (3, 2)]
    # the cover: Juan, room 1, room 2
    assert (m.cover_people, m.cover_objects) == ([3], [0, 1])
    # Anita, Daniel and Tomás accept only rooms 1 and 2
    assert m.blocked == BlockedGroup([0, 1, 2], [0, 1])
    assert check(4, 4, ROOMS, m) is None


def test_the_chapters_rooms_give_its_answer() -> None:
    m = max_matching(4, 4, BOOK_ROOMS)
    # Tomás moves to room 2, Daniel takes room 1, Juan room 3; Anita stays out, as in the hand run
    assert m.pairs == [(0, 1), (1, 0), (3, 2)]
    # the cover: Tomás, Juan, room 1
    assert (m.cover_people, m.cover_objects) == ([0, 3], [0])
    # Daniel and Anita accept only room 1
    assert m.blocked == BlockedGroup([1, 2], [0])
    assert check(4, 4, BOOK_ROOMS, m) is None


def test_check_valid_names_each_broken_part_alone() -> None:
    good = max_matching(4, 4, ROOMS)
    assert good.check_valid(4, 4, ROOMS) is None and good.is_valid(4, 4, ROOMS)
    cover, group = (good.cover_people, good.cover_objects), good.blocked
    cases = [
        # Lean: IsMatching; a pair nobody accepts, a person twice, an object twice. Each keeps the
        # cover's size equal to the number of pairs, the cover touching every acceptable pair.
        (Matching([(0, 0), (2, 1), (3, 0)], *cover, group), "promise (maximum_matching)"),
        (Matching([(0, 0), (0, 1), (3, 2)], *cover, group), "promise (maximum_matching)"),
        (Matching([(0, 0), (2, 0), (3, 2)], *cover, group), "promise (maximum_matching)"),
        # Lean: Ops.CoverAsLarge; a pair it misses (Juan's (3, 2)), someone twice, someone outside
        # the problem, and a cover one larger than the matching.
        (Matching(good.pairs, [0], [0, 1], group), "promise (cover_as_large)"),
        (Matching(good.pairs, [3], [0, 0], group), "promise (cover_as_large)"),
        (Matching(good.pairs, [4], [0, 1], group), "promise (cover_as_large)"),
        (Matching(good.pairs, [3, 0], [0, 1], group), "promise (cover_as_large)"),
        # Lean: Ops.BlockedGroupWhenShort; no group, a person twice, a person outside the problem,
        # an object nobody of them accepts, one they accept missing, and as many objects as people.
        (Matching(good.pairs, *cover, None), "promise (blocked_group_when_short)"),
        (Matching(good.pairs, *cover, BlockedGroup([0, 0, 1], [0, 1])),
         "promise (blocked_group_when_short)"),
        (Matching(good.pairs, *cover, BlockedGroup([0, 1, 4], [0, 1])),
         "promise (blocked_group_when_short)"),
        (Matching(good.pairs, *cover, BlockedGroup([0, 1, 2], [0, 1, 2])),
         "promise (blocked_group_when_short)"),
        (Matching(good.pairs, *cover, BlockedGroup([0, 1, 2], [0])),
         "promise (blocked_group_when_short)"),
        (Matching(good.pairs, *cover, BlockedGroup([0, 2], [0, 1])),
         "promise (blocked_group_when_short)"),
    ]
    for m, label in cases:
        assert m.check_valid(4, 4, ROOMS) == label, m
        assert not m.is_valid(4, 4, ROOMS)
    # When everyone is matched no group is asked for, and any group passes.
    full = max_matching(1, 1, [(0, 0)])
    assert Matching(full.pairs, [0], [], BlockedGroup([], [])).check_valid(1, 1, [(0, 0)]) is None


def test_everyone_matched_means_no_blocked_group() -> None:
    m = max_matching(2, 3, [(0, 0), (0, 1), (1, 1), (1, 2)])
    assert m.pairs == [(0, 0), (1, 1)]
    assert m.blocked is None
    assert (m.cover_people, m.cover_objects) == ([0, 1], [])


def test_no_people_or_no_pairs() -> None:
    m = max_matching(0, 0, [])
    assert m.pairs == [] and m.blocked is None
    # nobody accepts anything: together they accept nothing
    assert max_matching(2, 1, []).blocked == BlockedGroup([0, 1], [])


def test_a_doubled_pair_still_matches_once() -> None:
    m = max_matching(1, 1, [(0, 0), (0, 0)])
    assert m.pairs == [(0, 0)]
    assert check(1, 1, [(0, 0), (0, 0)], m) is None


def test_a_pair_outside_the_problem_is_refused() -> None:
    with pytest.raises(ValueError, match="pair 1"):
        max_matching(2, 2, [(0, 1), (2, 0)])
    with pytest.raises(ValueError):
        max_matching(2, 2, [(0, 2)])


def test_the_network_has_three_blocks_of_unit_arrows() -> None:
    net = matching_network(2, 2, [(1, 0), (0, 1)])
    assert net.arrows == [(0, 1), (0, 2), (2, 3), (1, 4), (3, 5), (4, 5)]
    assert net.capacity == [1] * 6
    assert (net.source, net.sink) == (0, 5)


@st.composite
def problems(draw: st.DrawFn) -> tuple[int, int, Pairs]:
    """Up to five people and objects and ten pairs, doubled pairs included."""
    people = draw(st.integers(0, 5))
    objects = draw(st.integers(1, 5))
    if people == 0:
        return people, objects, []
    pair = st.tuples(st.integers(0, people - 1), st.integers(0, objects - 1))
    return people, objects, draw(st.lists(pair, max_size=10))


@given(problems())
def test_on_small_problems_the_answer_is_largest_with_its_cover_and_group(
    problem: tuple[int, int, Pairs],
) -> None:
    people, objects, pairs = problem
    m = max_matching(people, objects, pairs)
    assert check(people, objects, pairs, m) is None
    assert len(m.pairs) == brute_force(pairs)
    # Lean: Ops.StepsAtMostPeople
    assert paths_added(people, objects, pairs) <= people


def test_on_larger_problems_the_cover_proves_the_matching_largest() -> None:
    r = random.Random(11)
    for _ in range(100):
        people, objects = r.randint(1, 40), r.randint(1, 40)
        pairs = [(r.randrange(people), r.randrange(objects)) for _ in range(r.randrange(200))]
        assert check(people, objects, pairs, max_matching(people, objects, pairs)) is None
        assert paths_added(people, objects, pairs) <= people


def flows_of_rounds(people: int, objects: int, pairs: Pairs) -> list[list[int]]:
    """The zero flow on the matching network, then the flow after every round of its max flow."""
    _, rounds = max_matching_with_rounds(people, objects, pairs)
    flow = [0] * (people + len(pairs) + objects)
    out = [list(flow)]
    for sent in rounds:
        for path, amount in sent:
            for e in path:
                flow[e // 2] += amount if e % 2 == 0 else -amount
        out.append(list(flow))
    return out


@given(problems())
def test_every_flow_of_the_rounds_keeps_the_invariant(problem: tuple[int, int, Pairs]) -> None:
    # Lean: Matching.Ops.startValid, Matching.Ops.roundsKeep
    people, objects, pairs = problem
    for flow in flows_of_rounds(people, objects, pairs):
        state = State(people, objects, pairs, flow)
        assert state.check_valid() is None and state.is_valid()


def test_state_names_a_flow_that_breaks_max_flows_invariants() -> None:
    # Lean: Matching.FlowRespected, on the network 0 -> person -> object -> sink
    assert State(1, 1, [(0, 0)], [1, 1, 1]).is_flow_respected()
    # an amount past the arrows is read by no piece: the Lean state has no `WellFormed`
    assert State(1, 1, [(0, 0)], [1, 1, 1, 5]).is_valid()
    for flow in ([2, 2, 2], [1, 1, 0], [0, 1, 1]):
        state = State(1, 1, [(0, 0)], flow)
        assert state.check_valid() == "invariant 1 (flow_respected)", flow
        assert not state.is_flow_respected() and not state.is_valid()
    with pytest.raises(ValueError):
        State(1, 1, [(0, 1)], [0, 0, 0]).is_valid()
