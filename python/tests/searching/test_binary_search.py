# SPDX-License-Identifier: Apache-2.0
from hypothesis import given
from hypothesis import strategies as st

from algodesign.searching.binary_search import search, search_with_glances


@given(st.lists(st.integers()), st.integers())
def test_search_finds_a_valid_index_iff_present(sorted_source: list[int], target: int) -> None:
    """On any sorted list, `search` returns an index holding `target` iff `target` is present,
    and `None` iff it's absent."""
    sorted_items = sorted(sorted_source)
    result = search(sorted_items, target)
    if target in sorted_items:
        assert result is not None
        assert sorted_items[result] == target
    else:
        assert result is None


def test_search_empty_list() -> None:
    assert search([], 5) is None


def test_search_single_element_present() -> None:
    assert search([5], 5) == 0


def test_search_single_element_absent() -> None:
    assert search([5], 3) is None


def test_search_target_at_start() -> None:
    assert search([1, 2, 3, 4, 5], 1) == 0


def test_search_target_at_middle() -> None:
    assert search([1, 2, 3, 4, 5], 3) == 2


def test_search_target_at_end() -> None:
    assert search([1, 2, 3, 4, 5], 5) == 4


def test_search_target_below_min() -> None:
    assert search([10, 20, 30], 5) is None


def test_search_target_above_max() -> None:
    assert search([10, 20, 30], 40) is None


def test_search_target_in_gap() -> None:
    assert search([10, 20, 30], 25) is None


def test_search_even_length_list() -> None:
    sorted_items = [1, 2, 3, 4, 5, 6]
    for target in sorted_items:
        assert search(sorted_items, target) == sorted_items.index(target)


def test_search_uses_the_closed_stretch_midpoint() -> None:
    """The stretch is Sedgewick's closed `[0, n - 1]`, so the first probe of four equal keys is
    index 1, as in the Rust and the Lean. A half-open `[0, n)` would probe index 2 first."""
    assert search([2, 2, 2, 2], 2) == 1


@given(st.lists(st.integers()), st.integers())
def test_glances_stay_within_the_chapter_bound(source: list[int], target: int) -> None:
    """The counted search answers as `search` does, in at most `ceil(log2(n + 1))` glances."""
    row = sorted(source)
    found, glances = search_with_glances(row, target)
    assert found == search(row, target)
    assert glances <= len(row).bit_length()  # ceil(log2(n + 1))


def test_the_chapters_row_of_fifteen_takes_four_glances() -> None:
    row = [3 * i + 2 for i in range(15)]  # 2, 5, 8, ..., 44
    assert search_with_glances(row, 38) == (12, 4)
    for k in range(1, 12):
        full = [2 * i + 1 for i in range(2**k - 1)]
        assert search_with_glances(full, 0) == (None, k)
