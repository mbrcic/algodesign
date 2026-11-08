"""The network (a `Digraph` and one cost per arrow) and the answer of a search, `Distances`, with
the path it reads back."""

from __future__ import annotations

import pytest

from algodesign.graphs import Digraph
from algodesign.paths import Distances, Network


def test_one_cost_per_arrow_by_id() -> None:
    g = Digraph(2, [(0, 1), (0, 1)])
    network = Network(g, [5, 3])
    assert network.g is g
    assert network.cost == [5, 3]


def test_a_cost_list_of_the_wrong_length_is_refused() -> None:
    g = Digraph(2, [(0, 1), (0, 1)])
    with pytest.raises(ValueError):
        Network(g, [5])
    with pytest.raises(ValueError):
        Network(g, [5, 3, 1])
    assert Network(Digraph(3, []), []).cost == []


def test_the_path_back_runs_from_the_start() -> None:
    d = Distances(cost=[0, 1, 3, None], previous=[None, 0, 1, None])
    assert d.path_to(0) == [0]
    assert d.path_to(1) == [0, 1]
    assert d.path_to(2) == [0, 1, 2]
    assert d.path_to(3) is None


def test_a_vertex_outside_the_graph_has_no_path() -> None:
    d = Distances(cost=[0, 1], previous=[None, 0])
    with pytest.raises(IndexError):
        d.path_to(2)
    with pytest.raises(IndexError):
        d.path_to(-1)
