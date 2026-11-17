# SPDX-License-Identifier: Apache-2.0
from hypothesis import given
from hypothesis import strategies as st

from algodesign.searching.sequential_search import build, contains, contains_with_checks


@given(st.lists(st.integers()), st.integers())
def test_contains_agrees_with_in_operator(items: list[int], target: int) -> None:
    """`contains` must agree with Python's own `in` operator on every input, present or absent."""
    assert contains(items, target) == (target in items)


@given(st.lists(st.integers()), st.integers())
def test_contains_agrees_with_naive_scan(items: list[int], target: int) -> None:
    """`contains` must agree with the most naive possible linear scan, written independently."""
    found = False
    for item in items:
        if item == target:
            found = True
            break
    assert contains(items, target) == found


def test_contains_empty_list() -> None:
    assert contains([], 42) is False


def test_contains_finds_present_element() -> None:
    assert contains([1, 2, 3], 2) is True


def test_contains_misses_absent_element() -> None:
    assert contains([1, 2, 3], 99) is False


@given(st.lists(st.integers()))
def test_build_has_no_duplicates(keys: list[int]) -> None:
    """`build` must never produce a list with duplicate elements, even with duplicate input keys."""
    result = build(keys)
    assert len(result) == len(set(result))


@given(st.lists(st.integers()))
def test_build_contains_same_elements_as_input(keys: list[int]) -> None:
    """`build`'s output, as a set, must match the input's set of distinct keys exactly."""
    result = build(keys)
    assert set(result) == set(keys)


@given(st.lists(st.integers()))
def test_build_preserves_first_occurrence_order(keys: list[int]) -> None:
    """Each key in the output should appear in the order of its first occurrence in the input."""
    result = build(keys)
    expected_order: list[int] = []
    seen: set[int] = set()
    for key in keys:
        if key not in seen:
            expected_order.append(key)
            seen.add(key)
    assert result == expected_order


def test_build_empty_input() -> None:
    assert build([]) == []


def test_build_drops_duplicates() -> None:
    assert build([1, 2, 1, 3, 2, 2]) == [1, 2, 3]


def test_build_with_no_duplicates_returns_same_order() -> None:
    assert build([3, 1, 4, 1, 5, 9, 2, 6]) == [3, 1, 4, 5, 9, 2, 6]


class _Unordered:
    """A key with equality and no order at all: comparing two of them with `<` raises."""

    def __init__(self, label: str) -> None:
        self.label = label

    def __eq__(self, other: object) -> bool:
        return isinstance(other, _Unordered) and self.label == other.label

    def __hash__(self) -> int:
        return hash(self.label)


def test_keys_need_equality_and_no_order() -> None:
    """Sequential search exploits no order, so its keys need `==` and nothing else. At run time
    `<` is never asked for; and because `mypy --strict` checks this file, a signature that
    demanded `<` (a `SupportsLT` bound) fails type-checking on the two calls below."""
    keys = [_Unordered("b"), _Unordered("a"), _Unordered("b"), _Unordered("c")]
    assert [k.label for k in build(keys)] == ["b", "a", "c"]
    assert contains(keys, _Unordered("c")) and not contains(keys, _Unordered("z"))


@given(st.lists(st.integers(0, 20)), st.integers(0, 20))
def test_checks_are_every_key_on_a_miss(items: list[int], target: int) -> None:
    found, checks = contains_with_checks(items, target)
    assert found == contains(items, target)
    assert checks == (items.index(target) + 1 if target in items else len(items))
