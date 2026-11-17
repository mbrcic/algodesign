"""Prim's method: the answers pinned on small networks (the Rust walks the same rows and breaks
ties the same way, so the order of the links added must match too), and judged against Kruskal and
by trying every set of links on random small networks."""

from __future__ import annotations

import importlib
import random

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.graphs import Graph
from algodesign.paths import LinkNetwork, naive
from algodesign.paths.kruskal import kruskal
from algodesign.paths.prim import prim

from .strategies import link_networks

# The package's `prim` is the function; the module is needed for the `heapq` it pushes with.
prim_module = importlib.import_module("algodesign.paths.prim")


def test_the_tree_grows_from_vertex_0_by_the_cheapest_link_out() -> None:
    five = LinkNetwork(Graph(4, [(0, 1), (0, 2), (2, 1), (1, 3), (2, 3)]), [4, 1, 2, 1, 5])
    assert prim(five) == [1, 2, 3]
    assert kruskal(five) == [1, 3, 2]


def test_equal_costs_go_by_link_id() -> None:
    assert prim(LinkNetwork(Graph(3, [(0, 1), (1, 2), (0, 2)]), [1, 1, 1])) == [0, 1]
    assert prim(LinkNetwork(Graph(2, [(0, 1), (1, 0)]), [3, 3])) == [0]


def test_each_piece_gets_its_own_tree_from_its_lowest_vertex() -> None:
    pieces = LinkNetwork(Graph(5, [(2, 1), (3, 0), (4, 4)]), [7, 2, 0])
    assert prim(pieces) == [1, 0]
    assert pieces.is_spanning_forest(prim(pieces))
    assert prim(LinkNetwork(Graph(0, []), [])) == []


def pushed(network: LinkNetwork, monkeypatch: pytest.MonkeyPatch) -> int:
    """How many entries `prim` pushes on its queue, counted at `heapq.heappush`."""
    count = 0
    push = prim_module.heapq.heappush

    def counted(queue: list[tuple[int, int, int]], entry: tuple[int, int, int]) -> None:
        nonlocal count
        count += 1
        push(queue, entry)

    with monkeypatch.context() as m:
        m.setattr(prim_module.heapq, "heappush", counted)
        prim(network)
    return count


def test_a_link_is_pushed_only_when_cheaper_than_every_link_pushed_towards_its_vertex(
        monkeypatch: pytest.MonkeyPatch) -> None:
    # From 0, links 0 and 1 reach 1 and 2 at cost 1; from 1, link 2 reaches 2 at cost 5, dearer
    # than link 1, so it is not pushed.
    dear = LinkNetwork(Graph(3, [(0, 1), (0, 2), (1, 2)]), [1, 1, 5])
    assert prim(dear) == [0, 1]
    assert pushed(dear, monkeypatch) == 2
    # Link 2 at cost 1 ties link 1 on cost and has the larger id: not pushed either.
    tie = LinkNetwork(Graph(3, [(0, 1), (0, 2), (1, 2)]), [1, 1, 1])
    assert prim(tie) == [0, 1]
    assert pushed(tie, monkeypatch) == 2
    # Link 2 at cost 0 is cheaper than link 1: pushed, and taken.
    cheap = LinkNetwork(Graph(3, [(0, 1), (0, 2), (1, 2)]), [1, 1, 0])
    assert prim(cheap) == [0, 2]
    assert pushed(cheap, monkeypatch) == 3


def test_nearest_neighbor_islands_are_joined() -> None:
    islands = LinkNetwork(Graph(4, [(0, 1), (2, 3), (1, 2), (0, 3)]), [1, 1, 5, 6])
    assert prim(islands) == [0, 2, 1]


# Trying every set of links, up to 4096 of them, is slow on a busy runner: no deadline.
@settings(deadline=None)
@given(link_networks())
def test_prim_gives_a_cheapest_spanning_forest(network: LinkNetwork) -> None:
    added = prim(network)
    assert network.is_spanning_forest(added)
    least = min(network.total(forest) for forest in naive.cheapest_forests(network))
    assert network.total(added) == least == network.total(kruskal(network))
    # Both take the cheapest link by (cost, id), so the set is Kruskal's, ties or not.
    assert sorted(added) == sorted(kruskal(network))


@settings(deadline=None)
@given(link_networks(), st.randoms(use_true_random=False))
def test_on_distinct_costs_prim_keeps_kruskals_links(network: LinkNetwork,
                                                     rng: random.Random) -> None:
    cost = list(range(-3, len(network.cost) - 3))
    rng.shuffle(cost)
    distinct = LinkNetwork(network.g, cost)
    assert sorted(prim(distinct)) == sorted(kruskal(distinct))
