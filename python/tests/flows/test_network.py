"""The network and the residual graph: what a network refuses, each vertex's row in input
order, and sending along residual arrows."""

from __future__ import annotations

import re

import pytest

from algodesign.flows import Network, Residual


def test_a_network_keeps_its_arrows_capacities_source_and_sink() -> None:
    network = Network(3, [(0, 1), (1, 2), (0, 1)], [4, 2, 7], 0, 2)
    assert (network.n, network.source, network.sink) == (3, 0, 2)
    assert network.arrows == [(0, 1), (1, 2), (0, 1)]
    assert network.capacity == [4, 2, 7]


@pytest.mark.parametrize(
    ("n", "arrows", "capacity", "source", "sink", "message"),
    [
        (2, [(0, 2)], [1], 0, 1, "arrow 0 = (0, 2) has an end outside 0..2"),
        (2, [(0, 1)], [], 0, 1, "0 capacities for 1 arrows"),
        (2, [(0, 1)], [1, 2], 0, 1, "2 capacities for 1 arrows"),
        (2, [(0, 1)], [-1], 0, 1, "arrow 0 has capacity -1, below zero"),
        (2, [(0, 1)], [1], 2, 1, "the source 2 is outside 0..2"),
        (2, [(0, 1)], [1], 0, 5, "the sink 5 is outside 0..2"),
        (2, [(0, 1)], [1], 1, 1, "vertex 1 is both the source and the sink"),
    ],
)
def test_a_network_that_is_not_one_is_refused_by_name(
    n: int, arrows: list[tuple[int, int]], capacity: list[int], source: int, sink: int,
    message: str,
) -> None:
    with pytest.raises(ValueError, match=re.escape(message)):
        Network(n, arrows, capacity, source, sink)


def test_each_row_lists_along_at_the_tail_and_back_at_the_head_in_input_order() -> None:
    # Lean: ResidualArrow.tail, ResidualArrow.head; 2i is `along i`, 2i + 1 is `back i`.
    # Arrow 0: 1 -> 0, arrow 1: 0 -> 1 (opposite), arrow 2: 0 -> 1 (doubled), arrow 3: a loop at 2,
    # arrow 4: 2 -> 0. The same rows as the Rust's test.
    network = Network(3, [(1, 0), (0, 1), (0, 1), (2, 2), (2, 0)], [1, 2, 3, 4, 5], 0, 1)
    r = Residual(network)
    assert r.out == [[1, 2, 4, 9], [0, 3, 5], [6, 7, 8]]
    assert all(r.tail(e) == r.head[e ^ 1] and e in r.out[r.tail(e)] for e in range(10))
    assert r.residual_capacity == [1, 0, 2, 0, 3, 0, 4, 0, 5, 0]
    assert r.flow() == [0] * 5


def test_sending_moves_residual_capacity_to_the_reverse_arrow_and_the_flow_is_its_residual_capacity() -> None:
    # Lean: sendOne, Augmentation.apply
    r = Residual(Network(3, [(0, 1), (1, 2)], [5, 3], 0, 2))
    assert r.augment([0, 2]) == 3
    assert r.residual_capacity == [2, 3, 0, 3]
    assert r.flow() == [3, 3]
    r.send(1, 1)  # arrow 0's reverse arrow takes 1 off it
    assert r.flow() == [2, 3]
    with pytest.raises(AssertionError):
        r.send(2, 1)


def test_the_reached_vertices_are_those_arrows_with_residual_capacity_lead_to() -> None:
    # Lean: reached
    r = Residual(Network(5, [(0, 1), (1, 2), (2, 3), (4, 0)], [3, 2, 9, 1], 0, 3))
    assert r.reached() == [True, True, True, True, False]
    r.augment([0, 2, 4])
    assert r.reached() == [True, True, False, False, False]
