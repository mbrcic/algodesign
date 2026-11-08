"""Random small networks for the Paths tests: up to six vertices and ten arrows, doubled arrows and
loops included, so that trying every path stays quick; and random small link networks."""

from __future__ import annotations

from hypothesis import strategies as st

from algodesign.graphs import Digraph, Graph
from algodesign.paths import LinkNetwork, Network


@st.composite
def networks(draw: st.DrawFn, low: int = 0, high: int = 9) -> Network:
    """A network of one to six vertices whose arrows cost from `low` to `high`."""
    n = draw(st.integers(1, 6))
    vertex = st.integers(0, n - 1)
    arrows = draw(st.lists(st.tuples(vertex, vertex), max_size=10))
    cost = draw(st.lists(st.integers(low, high), min_size=len(arrows), max_size=len(arrows)))
    return Network(Digraph(n, arrows), cost)


@st.composite
def network_and_vertex(draw: st.DrawFn, low: int = 0, high: int = 9) -> tuple[Network, int]:
    """A network and one of its vertices."""
    network = draw(networks(low, high))
    return network, draw(st.integers(0, network.g.n - 1))


@st.composite
def link_networks(draw: st.DrawFn, low: int = -2, high: int = 3) -> LinkNetwork:
    """A link network of one to seven vertices and up to twelve links costing from `low` to
    `high`: few enough that trying every set of links stays quick, loops, doubled links, pieces and
    equal costs common."""
    n = draw(st.integers(1, 7))
    vertex = st.integers(0, n - 1)
    links = draw(st.lists(st.tuples(vertex, vertex), max_size=12))
    cost = draw(st.lists(st.integers(low, high), min_size=len(links), max_size=len(links)))
    return LinkNetwork(Graph(n, links), cost)
