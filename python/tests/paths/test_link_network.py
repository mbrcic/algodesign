"""The link network (a `Graph` and one cost per link) and the Lean's definitions on it: joining,
the total, closing no cycle, a spanning forest; the examples of `LinkNetwork.lean`."""

from __future__ import annotations

import pytest

from algodesign.graphs import Graph
from algodesign.paths import LinkNetwork


def test_one_cost_per_link_by_id() -> None:
    g = Graph(2, [(0, 1), (0, 1)])
    network = LinkNetwork(g, [5, 3])
    assert network.g is g
    assert network.cost == [5, 3]
    with pytest.raises(ValueError, match="1 costs for 2 links"):
        LinkNetwork(g, [5])


def test_two_links_between_the_same_vertices_and_a_loop() -> None:
    double = LinkNetwork(Graph(2, [(0, 1), (0, 1)]), [5, 3])
    assert double.is_spanning_forest([1]) and double.is_spanning_forest([0])
    assert not double.closes_no_cycle([0, 1])
    assert double.total([0, 1]) == 8
    loop = LinkNetwork(Graph(2, [(1, 1)]), [0])
    assert not loop.closes_no_cycle([0])
    assert loop.is_spanning_forest([])


def test_joining_is_a_chain_of_links_read_either_way() -> None:
    path = LinkNetwork(Graph(4, [(1, 0), (1, 2), (3, 3)]), [1, 1, 1])
    assert path.joins([0, 1], 0, 2) and path.joins([0, 1], 2, 0)
    assert not path.joins([0], 0, 2)
    assert path.joins([], 3, 3)
    assert not path.joins([0, 1, 2], 0, 3)
    assert path.joins_what_graph_joins([0, 1])
    assert not path.joins_what_graph_joins([1])


def test_ids_past_the_links_read_as_a_loop_at_0_that_costs_nothing() -> None:
    path = LinkNetwork(Graph(3, [(0, 1), (1, 2)]), [2, 3])
    assert path.ends(9) == (0, 0) and path.link_cost(9) == 0
    assert path.total([0, 9]) == 2
    assert not path.joins([9], 1, 2)
    assert path.joins([9], 7, 7)
    assert not path.joins([0, 1], 0, 7)
    assert not path.closes_no_cycle([0, 0])
    assert not path.closes_no_cycle([9])
    assert not path.is_spanning_forest([0, 1, 9])
    assert path.is_spanning_forest([1, 0])
