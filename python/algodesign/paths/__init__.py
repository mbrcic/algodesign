"""The Paths chapter: `network`, the Graphs chapter's `Digraph` with one integer cost per arrow;
`distances`, the answer of a search from one start (each vertex's cost and previous vertex, and the
path back); `bfs`, the fewest arrows by breadth-first search; `dijkstra`, the cheapest paths when no
arrow is negative, to every vertex or to one goal, with the walk's state and its checks
(`algodesign.paths.dijkstra.State`); `a_star`, the cheapest path to one goal, its keys moved by an
estimate of the cost still to go, with its checks in `algodesign.paths.a_star`; `bellman_ford`, the
cheapest paths when some arrows are negative, or a negative cycle that the start reaches, with the
state after some rounds and its checks (`algodesign.paths.bellman_ford.State`); `dag`, the cheapest
paths in a graph with no cycle, each vertex's row tried in Kahn's order, any arrow costs allowed
(its state `algodesign.paths.dag.State`); `knapsack`, the best packing of a box as a longest path
through the states (items decided, weight used), filled one layer at a time (its state
`algodesign.paths.knapsack.State`); `link_network`, the Graphs chapter's `Graph` with one integer
cost per link; `kruskal`, the cheapest spanning forest by taking the links cheapest first, with the
walk's state and its checks (`algodesign.paths.kruskal.State`); `prim`, the same forest grown by
Dijkstra's walk with the key the link alone. The seven methods named after their modules are reached
through them, as the Search chapter's are: `dijkstra.dijkstra(network, start)`, or `from
algodesign.paths.dijkstra import dijkstra`. `naive` holds the slow references the tests compare
against; import it as `algodesign.paths.naive`. `workbench` is the chapter's design project's bench,
not a structure; import it as `algodesign.paths.workbench`.
"""

from __future__ import annotations

from . import a_star, bellman_ford, bfs, dijkstra, knapsack, kruskal, prim
from .a_star import a_star_with_settled
from .bellman_ford import NegativeCycle, bellman_ford_with_rounds
from .dag import dag_paths
from .dijkstra import dijkstra_to, dijkstra_with_settled
from .distances import Distances
from .knapsack import Packing
from .kruskal import kruskal_with_tried
from .link_network import LinkNetwork
from .network import Network

__all__ = [
    "NegativeCycle", "bellman_ford", "bellman_ford_with_rounds",
    "Distances", "Network", "a_star", "a_star_with_settled", "bfs", "dijkstra", "dijkstra_to",
    "dijkstra_with_settled", "dag_paths", "Packing", "knapsack", "LinkNetwork", "kruskal",
    "kruskal_with_tried", "prim",
]
