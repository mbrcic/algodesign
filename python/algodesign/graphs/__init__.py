"""The Graphs chapter: `union_find`, the groups of items joined so far; `digraph`, directed and
undirected graphs stored as sorted rows; `topo`, a topological order by Kahn's method or by a
depth-first walk, with the vertices that cannot be ordered or a cycle when there is none; `scc`, the
strong components by Algorithm T and by Kosaraju-Sharir, the graph of groups, and a checker for a
grouping computed elsewhere; `satisfiability`, 2-SAT through the strong components (`two_sat`);
`block_cut`, the bridges, cut vertices and blocks of an undirected graph by one walk (`blocks`),
and the block-cut forest that names the vertices separating two others; `union_find_undo`,
union-find that takes back its merges, last first; `dataflow`, news spread along the arrows, group
by group. `workbench` is the chapter's design project's bench, not a structure; import it as
`algodesign.graphs.workbench`.

The package gives the functions `blocks` and `two_sat`, the names the chapter prints; their
modules are named for their topics, so a module never hides behind a function of its name.
"""

from __future__ import annotations

from .block_cut import BlockCutForest, Blocks, blocks
from .dataflow import spread
from .digraph import Digraph, Graph
from .satisfiability import Unsat, two_sat
from .scc import Components, check_components, condensation, kosaraju_sharir, strong_components
from .topo import Cycle, Stuck, dfs_order, topological_order
from .union_find import UnionFind
from .union_find_undo import UndoUnionFind

__all__ = [
    "BlockCutForest", "Blocks", "Components", "Cycle", "Digraph", "Graph", "Stuck",
    "UndoUnionFind", "UnionFind", "Unsat", "blocks", "check_components", "condensation",
    "dfs_order", "kosaraju_sharir", "spread", "strong_components", "topological_order", "two_sat",
]
