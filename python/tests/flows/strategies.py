"""Random small networks for the Flows tests: two to seven vertices and up to fourteen arrows, loops,
doubled and opposite arrows and zero capacities included, so that trying every cut stays quick;
and the chapter's networks the tests pin."""

from __future__ import annotations

from hypothesis import strategies as st

from algodesign.flows import Network


@st.composite
def networks(draw: st.DrawFn) -> Network:
    """A network of two to seven vertices whose arrows carry from 0 to 5."""
    n = draw(st.integers(2, 7))
    vertex = st.integers(0, n - 1)
    arrows = draw(st.lists(st.tuples(vertex, vertex), max_size=14))
    capacity = draw(st.lists(st.integers(0, 5), min_size=len(arrows), max_size=len(arrows)))
    source = draw(vertex)
    sink = (source + draw(st.integers(1, n - 1))) % n
    return Network(n, arrows, capacity, source, sink)


# The chapter's network: 0 -> 1 and 0 -> 2 carry 1000, 1 -> 3 and 2 -> 3 carry 1000, and the
# middle arrow 1 -> 2 carries 1.
ONE_AND_THOUSAND = Network(
    4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)], [1000, 1000, 1, 1000, 1000], 0, 3
)
