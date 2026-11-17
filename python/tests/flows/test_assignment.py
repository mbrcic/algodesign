"""The assignment: the three-by-three table and the rent with the labels, steps and prices the
Rust's tests pin, the three tie rules, the edges and the refusal; on random small tables every
answer checked against the contract and the cheapest cost found by trying every order of the
objects; and on larger drawn tables every answer certified by its labels."""

from __future__ import annotations

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign._rng import SplitMix64
from algodesign.flows import Assignment, AssignmentStep, assignment_with_steps, naive
from algodesign.flows.assignment import assignment


def labels_break(
    cost: list[list[int]], people: int, obj: list[int], u: list[int], v: list[int]
) -> str | None:
    """Whether the labels fit every pair of the people `0..people` and meet every chosen pair of
    them exactly; the first that fails, in words, or `None`."""
    for i in range(people):
        for j, c in enumerate(cost[i]):
            if u[i] + v[j] > c:
                return f"LabelsFit at ({i}, {j})"
        if u[i] + v[obj[i]] != cost[i][obj[i]]:
            return f"ExactOnChosen at ({i}, {obj[i]})"
    return None


def breaks(
    cost: list[list[int]], answer: Assignment, steps: list[AssignmentStep], oracle: bool
) -> str | None:
    """The first part of the contract the answer and its steps break, in words; `None` if none."""
    n = len(cost)
    obj, u, v = answer.obj, answer.person_label, answer.object_label
    # Lean: IsAssignmentOf
    if sorted(obj) != list(range(n)) or len(u) != n or len(v) != n:
        return "no assignment"
    if answer.cost != sum(cost[i][obj[i]] for i in range(n)):
        return "cost"
    # Lean: Ops.LabelsFit, Ops.ExactOnChosen
    if (wrong := labels_break(cost, n, obj, u, v)) is not None:
        return wrong
    # Adding the labels up proves that no assignment costs less.
    if sum(u) + sum(v) != answer.cost:
        return "the labels do not add up to the cost"
    # Lean: Ops.FavoriteAfterPrice
    for i in range(n):
        if any(cost[i][obj[i]] - v[obj[i]] > cost[i][j] - v[j] for j in range(n)):
            return f"person {i} prefers another object after price"
    # Lean: Ops.OneSearchPerPerson, Ops.stepsKeep, Ops.walks
    if len(steps) != n:
        return "one step per person"
    placed = [0] * n
    holder: list[int | None] = [None] * n
    for k, step in enumerate(steps):
        free = step.path[-1]
        if step.settled[-1] != free or holder[free] is not None:
            return f"step {k}: the search does not end at a free object"
        if any(j not in step.settled for j in step.path):
            return f"step {k}: the path leaves the settled objects"
        movers = [k] + [holder[j] for j in step.path[:-1]]
        for p, j in zip(movers, step.path, strict=True):
            assert p is not None
            placed[p] = j
            holder[j] = p
        if (wrong := labels_break(cost, k + 1, placed, step.person_label, step.object_label)):
            return f"step {k}: {wrong}"
    if steps and (placed != obj or (steps[-1].person_label, steps[-1].object_label) != (u, v)):
        return "the steps do not lead to the answer"
    # Lean: Ops.LeastCost
    if oracle and naive.cheapest_assignment(cost) != answer.cost:
        return "a cheaper assignment exists"
    return None


def checked(cost: list[list[int]], oracle: bool = True) -> tuple[Assignment, list[AssignmentStep]]:
    """The answer and steps for `cost`, checked against the contract."""
    answer, steps = assignment_with_steps(cost)
    assert breaks(cost, answer, steps, oracle) is None
    assert assignment(cost) == answer
    return answer, steps


def test_the_three_by_three_table_costs_twelve_and_its_labels_prove_it() -> None:
    # P1 (1, 3, 6), P2 (2, 8, 9), P3 (5, 4, 9). By hand, u = (6, 7, 7), v = (-5, -3, 0): every
    # pair fits, each chosen pair is exact, and the labels add up to 12, the cost.
    answer, steps = checked([[1, 3, 6], [2, 8, 9], [5, 4, 9]])
    assert answer == Assignment([2, 0, 1], [6, 7, 7], [-5, -3, 0], 12)
    assert [s.settled for s in steps] == [[0], [0, 1], [1, 0, 2]]
    assert [s.path for s in steps] == [[0], [0, 1], [1, 2]]
    assert (steps[1].person_label, steps[1].object_label) == ([3, 4, 0], [-2, 0, 0])


def test_the_rent_gives_every_tenant_their_favorite_room_after_price() -> None:
    # Values, larger is better; costs are 900 - value. Rows: Juan, Anita, Daniel, Tomás.
    values = [[550, 400, 700, 350], [700, 650, 400, 250], [900, 550, 300, 250],
              [650, 700, 400, 250]]
    answer, steps = checked([[900 - x for x in row] for row in values])
    # Juan room 3, Anita room 4, Daniel room 1, Tomás room 2.
    assert answer.obj == [2, 3, 0, 1]
    assert sum(values[i][answer.obj[i]] for i in range(4)) == 2_550
    assert (answer.person_label, answer.object_label) == ([350, 650, 450, 600],
                                                          [-450, -400, -150, 0])
    # Prices are minus the room labels, 450, 400, 150, 0, each raised by 250 to sum to 2,000.
    raw = [-label for label in answer.object_label]
    shift = (2_000 - sum(raw)) // 4
    assert [p + shift for p in raw] == [700, 650, 400, 250]
    # Daniel wants Anita's room 1, and she moves to room 2; Tomás reaches room 4 through her row.
    assert (steps[2].settled, steps[2].path) == ([0, 1], [0, 1])
    assert (steps[3].settled, steps[3].path) == ([1, 0, 2, 3], [1, 3])


def test_on_a_tie_a_free_object_comes_before_a_held_one_of_lower_index() -> None:
    # The lowest index alone would settle object 0 first and move person 0 to object 1.
    answer, steps = checked([[0, 0], [0, 0]])
    assert steps[1].settled == [1]
    assert answer.obj == [0, 1]
    # Lean's tie table: person 0 takes object 0 at 1; person 1 then takes the free object 1.
    answer, steps = checked([[1, 1], [0, 0]])
    assert [s.settled for s in steps] == [[0], [1]]
    assert answer.obj == [0, 1]


def test_on_a_tie_of_free_objects_the_lowest_index_wins() -> None:
    answer, steps = checked([[5, 1, 1], [0, 9, 9], [9, 9, 0]])
    assert steps[0].settled == [1]
    assert answer.obj == [1, 0, 2]


def test_on_a_tie_of_held_objects_the_lowest_index_wins() -> None:
    answer, steps = checked([[0, 9, 9], [9, 0, 9], [1, 1, 5]])
    assert (steps[2].settled, steps[2].path) == ([0, 1, 2], [2])
    assert answer.obj == [0, 1, 2]


def test_an_empty_table_one_person_and_costs_below_zero() -> None:
    assert checked([]) == (Assignment([], [], [], 0), [])
    assert checked([[-5]])[0] == Assignment([0], [-5], [0], -5)
    # -3 - 7 - 9.
    assert checked([[-3, 4, -8], [0, -7, 2], [-1, -1, -9]])[0].cost == -19


def test_a_table_that_is_not_square_is_refused() -> None:
    with pytest.raises(ValueError, match="row 1 has 1 costs for 2 people"):
        assignment([[1, 2], [3]])
    with pytest.raises(ValueError, match="row 0 has 2 costs for 1 people"):
        assignment([[1, 2]])


@st.composite
def tables(draw: st.DrawFn, low: int, high: int) -> list[list[int]]:
    """A square table of up to seven people with costs from `low` to `high`."""
    n = draw(st.integers(0, 7))
    cost = st.integers(low, high)
    return [draw(st.lists(cost, min_size=n, max_size=n)) for _ in range(n)]


@given(tables(-20, 19))
def test_on_any_small_table_the_answer_is_the_cheapest(cost: list[list[int]]) -> None:
    # Lean: Contract.promise, Ops.OneSearchPerPerson
    answer, steps = assignment_with_steps(cost)
    assert breaks(cost, answer, steps, oracle=True) is None


@given(tables(0, 2))
def test_on_any_small_table_of_many_ties_the_answer_is_the_cheapest(cost: list[list[int]]) -> None:
    answer, steps = assignment_with_steps(cost)
    assert breaks(cost, answer, steps, oracle=True) is None


def drawn(r: SplitMix64, low: int, span: int) -> list[list[int]]:
    """A square table of 1 to 60 people with costs drawn from `low` to `low + span - 1`."""
    n = 1 + r.next_u64() % 60
    return [[low + r.next_u64() % span for _ in range(n)] for _ in range(n)]


def test_on_larger_tables_the_labels_certify_every_answer() -> None:
    # The Rust's tables: the same seed, the same draws.
    r = SplitMix64(7)
    for k in range(200):
        cost = drawn(r, -1_000, 2_001) if k % 2 == 0 else drawn(r, 0, 5)
        checked(cost, oracle=False)
