# SPDX-License-Identifier: Apache-2.0
"""The ball-weighing solver finds the odd ball, and never takes more than `ceil(log3 n)` weighings.

Both are checked for every placement of the odd ball, for every `n` up to 81.
"""

from __future__ import annotations

import pytest

from algodesign.contracts.ball_weighing import find_heavier, min_weighings


@pytest.mark.parametrize("n", list(range(1, 82)))
def test_finds_the_odd_ball_within_the_bound(n: int) -> None:
    bound = min_weighings(n)
    for odd in range(n):
        found, used = find_heavier(n, odd)
        assert found == odd, f"n={n} odd={odd}: found {found}"
        assert used <= bound, f"n={n} odd={odd}: used {used} > bound {bound}"


def test_the_bound_is_the_smallest_power_of_three_that_reaches_n() -> None:
    assert [min_weighings(n) for n in (1, 2, 3, 4, 9, 10, 27, 28)] == [0, 1, 1, 2, 2, 3, 3, 4]


def test_the_bound_is_reached() -> None:
    """The bound is not only respected but met: some placement needs every weighing."""
    for n in range(2, 82):
        assert max(find_heavier(n, odd)[1] for odd in range(n)) == min_weighings(n)


def test_an_odd_index_out_of_range_is_rejected() -> None:
    with pytest.raises(ValueError):
        find_heavier(5, 5)
