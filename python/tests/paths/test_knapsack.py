"""Knapsack as a longest path: the answers pinned on the cases the Lean's kernel checks in
`AlgoDesignTests/Paths.lean` (the cargo box, a tie between taking and skipping, a tie between two
ends, an item weighing nothing, one worth less than nothing, no items, no room), the walk's layers
and the arrows it tries, and the answers judged by trying every set of items.
"""

from __future__ import annotations

import copy

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.paths import Packing, naive
from algodesign.paths.knapsack import State, knapsack

# The cargo box: 10 kg, one order of 6 kg for 30 and two of 5 kg for 20 each.
WEIGHTS, VALUES = [6, 5, 5], [30, 20, 20]


def states(weights: list[int], values: list[int], capacity: int) -> list[State]:
    """Every state of the walk, the start first, one more per item decided."""
    state = State.start(capacity)
    trail = [copy.deepcopy(state)]
    for _ in weights:
        state.step(weights, values)
        trail.append(copy.deepcopy(state))
    return trail


def test_the_cargo_box_takes_the_two_lighter_orders_where_greedy_takes_one() -> None:
    assert knapsack(WEIGHTS, VALUES, 10) == Packing(40, [1, 2])
    assert naive.best_value(WEIGHTS, VALUES, 10) == 40
    # Greedy by value per kilo takes the 6 kg order (5 a kilo against 4); then nothing fits: 30.
    room, greedy = 10, 0
    for k in sorted(range(3), key=lambda k: -VALUES[k] / WEIGHTS[k]):
        if WEIGHTS[k] <= room:
            room, greedy = room - WEIGHTS[k], greedy + VALUES[k]
    assert greedy == 30


def test_the_walk_fills_one_layer_per_item() -> None:
    trail = states(WEIGHTS, VALUES, 10)
    assert len(trail) == 4
    # A state no path reaches holds None.
    assert (trail[-1].best[3][4], trail[-1].best[3][5]) == (None, 20)


def test_at_most_two_arrows_are_tried_out_of_each_state_before_the_last_layer() -> None:
    tried = states(WEIGHTS, VALUES, 10)[-1].tried
    assert tried <= 2 * 3 * 11
    # Layer 0: (0, 0) skips and takes. Layer 1: 0 and 6 skip, 0 takes. Layer 2: 0, 5 and 6 skip,
    # 0 and 5 take.
    assert tried == 2 + 3 + 5


def test_a_tie_between_taking_and_skipping_takes_the_item() -> None:
    assert knapsack([2, 2], [5, 5], 2) == Packing(5, [1])


def test_two_weights_tie_in_the_last_layer_the_lighter_one_wins() -> None:
    assert knapsack([1, 2], [3, 3], 2) == Packing(3, [0])


def test_an_item_weighing_nothing_is_taken_when_it_is_worth_something() -> None:
    assert knapsack([0, 3], [4, 2], 2) == Packing(4, [0])
    # Worth nothing: a tie, so it is taken; worth less: left out.
    assert knapsack([0], [0], 0) == Packing(0, [0])
    assert knapsack([0], [-1], 0) == Packing(0, [])


def test_an_item_worth_less_than_nothing_is_left_out() -> None:
    assert knapsack([1], [-3], 5) == Packing(0, [])


def test_no_items_or_no_room() -> None:
    assert knapsack([], [], 5) == Packing(0, [])
    assert knapsack(WEIGHTS, VALUES, 0) == Packing(0, [])


def test_lists_of_different_lengths_and_weights_below_zero_are_refused() -> None:
    with pytest.raises(ValueError, match="2 weights for 1 values"):
        knapsack([1, 2], [3], 5)
    with pytest.raises(ValueError, match="below zero"):
        knapsack([-1], [3], 5)
    with pytest.raises(ValueError, match="below zero"):
        knapsack([1], [3], -1)


@st.composite
def items(draw: st.DrawFn) -> tuple[list[int], list[int], int]:
    """Up to ten items, weights 0 to 6 and values -3 to 9, and a box of 0 to 12."""
    pairs = draw(st.lists(st.tuples(st.integers(0, 6), st.integers(-3, 9)), max_size=10))
    return [w for w, _ in pairs], [v for _, v in pairs], draw(st.integers(0, 12))


@given(items())
def test_on_any_items_the_value_is_the_best_and_the_items_give_it(
        case: tuple[list[int], list[int], int]) -> None:
    weights, values, capacity = case
    p = knapsack(weights, values, capacity)
    assert p.value == naive.best_value(weights, values, capacity)
    assert p.items == sorted(set(p.items)) and all(0 <= k < len(weights) for k in p.items)
    assert sum(weights[k] for k in p.items) <= capacity
    assert sum(values[k] for k in p.items) == p.value


@given(items())
def test_on_any_items_the_walk_tries_at_most_two_arrows_out_of_each_state(
        case: tuple[list[int], list[int], int]) -> None:
    weights, values, capacity = case
    trail = states(weights, values, capacity)
    assert trail[-1].tried <= 2 * len(weights) * (capacity + 1)
