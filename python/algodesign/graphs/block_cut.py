# SPDX-License-Identifier: Apache-2.0
"""Single failures in an undirected graph: the bridges, the cut vertices, the blocks, and the
block-cut forest that answers which vertices separate two others.

`blocks` is the low-link walk with a link stack (Drozdek, *Data Structures and Algorithms in
C++*, 4th ed., §8.6.1, pp. 416-418; Hopcroft and Tarjan 1973). The walk keeps its path as explicit
frames `[vertex, arrival link id, next position in its row]`, starts at vertices 0 upward, and gives
each vertex an entry number from 1 in the order vertices are first entered. Its climb-back number
`low` starts as its entry number. Walking the row of the top vertex v, an entry (w, e):

- is skipped when it is a loop (w is v), or when e is the link v arrived by: the walk skips the
  link, by its id, not the vertex it came from (cp-algorithms, "Finding bridges", "pass to dfs the
  index of the edge used to enter the vertex"), so the second copy of a doubled link climbs back;
- when w was not entered: e goes on the link stack and the walk descends to w;
- when w was entered earlier than v: e goes on the link stack and low[v] takes w's entry number if
  that is smaller (the neighbour's entry number, not its climb-back number);
- when w was entered later than v: skipped, since w is below v and pushed e already.

When a child c finishes under v, having arrived by link e: low[v] takes low[c] if that is smaller;
if low[c] >= entry[v], the link stack is popped down to and including e, and those links are one
block; if low[c] > entry[v], e is a bridge. A vertex other than a root with such a child is a cut
vertex; a root is a cut vertex when it has two or more children. A vertex with no link except loops
is an isolated vertex: a block of its own with no links, emitted when it finishes as its own root.

`BlockCutForest` joins every block to the cut vertices it holds (Diestel, *Graph Theory*, §3.1): one
tree per piece of the graph. Two vertices in one piece are separated by exactly the cut vertices on
the forest path between their nodes.

Loops are in no block. A query vertex outside `0 .. n-1` raises `IndexError`.

`Walk` is a state of the walk, as the Lean's `Blocks.Walk` holds what its invariants read. Its
`is_climb_back_is_earliest` and `is_stack_holds_open_links` are the Lean `Valid`'s two pieces
(`Blocks.Walk.Valid`); each answers on any state, broken or not. `Walk.trace` gives every state
of the walk, one per step, for tests to judge.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from itertools import pairwise

from .digraph import Graph
from .naive import on_common_cycle


def _quiet(*parts: object) -> None:
    """Does nothing: the walk calls this with its own lists after each step."""


_watch: Callable[..., None] = _quiet
"""Called by `blocks` with its `entry`, `low`, `link_stack`, `found`, `found_vertices` and `path`
after each step; `Walk.trace` puts a recorder here for one walk."""


@dataclass(frozen=True)
class Blocks:
    """What the walk finds.

    `bridges`: the link ids of the bridges, increasing. `cut_vertices`: increasing. `block_of_link`:
    each link's block, `None` for a loop. `blocks`: each block's links in the order the link stack
    popped them, the blocks in the order they were emitted. `block_vertices`: each block's vertices,
    increasing (an isolated vertex's block holds that vertex alone).
    """

    bridges: list[int]
    cut_vertices: list[int]
    block_of_link: list[int | None]
    blocks: list[list[int]]
    block_vertices: list[list[int]]


def blocks(g: Graph) -> Blocks:
    """The bridges, cut vertices and blocks of `g`, by one low-link walk with a link stack. Linear
    in vertices plus links."""
    entry = [0] * g.n  # 0: not entered yet
    low = [0] * g.n
    time = 0
    link_stack: list[int] = []
    is_cut = [False] * g.n
    bridges: list[int] = []
    found: list[list[int]] = []
    found_vertices: list[list[int]] = []

    def pop_block(e: int) -> None:
        """Pop the link stack down to and including `e`: one block."""
        links: list[int] = []
        while not links or links[-1] != e:
            links.append(link_stack.pop())
        found.append(links)
        ends = {p for i in links for p in g.links[i]}
        found_vertices.append(sorted(ends))

    for root in range(g.n):
        if entry[root] != 0:
            continue
        time += 1
        entry[root] = low[root] = time
        children = 0  # the root's children in the walk
        path = [[root, -1, 0]]  # frames [vertex, arrival link id, next position]; a root has -1
        while path:
            _watch(entry, low, link_stack, found, found_vertices, path)
            frame = path[-1]
            v, arrival, i = frame
            if i < len(g.adj[v]):
                frame[2] = i + 1
                w, e = g.adj[v][i]
                if w == v or e == arrival:
                    continue
                if entry[w] == 0:
                    link_stack.append(e)
                    time += 1
                    entry[w] = low[w] = time
                    if v == root:
                        children += 1
                    path.append([w, e, 0])
                elif entry[w] < entry[v]:
                    link_stack.append(e)
                    low[v] = min(low[v], entry[w])
                continue
            path.pop()  # every entry of v walked: v finishes
            if not path:
                continue
            u = path[-1][0]  # v finishes under u, having arrived by link `arrival`
            low[u] = min(low[u], low[v])
            if low[v] >= entry[u]:
                pop_block(arrival)
                if u != root:
                    is_cut[u] = True
            if low[v] > entry[u]:
                bridges.append(arrival)
        if children >= 2:
            is_cut[root] = True
        if children == 0:  # no link but loops: an isolated vertex
            found.append([])
            found_vertices.append([root])
        _watch(entry, low, link_stack, found, found_vertices, path)

    block_of_link: list[int | None] = [None] * len(g.links)
    for k, links in enumerate(found):
        for i in links:
            block_of_link[i] = k
    return Blocks(
        bridges=sorted(bridges),
        cut_vertices=[v for v in range(g.n) if is_cut[v]],
        block_of_link=block_of_link,
        blocks=found,
        block_vertices=found_vertices,
    )


def _not_loop(g: Graph, i: int) -> bool:
    """`i` is a link of `g` and not a loop."""
    return 0 <= i < len(g.links) and g.links[i][0] != g.links[i][1]


def _same_block(g: Graph, e: int, f: int) -> bool:
    """One block: two links that are not loops, the same or on one cycle through distinct
    vertices."""
    return _not_loop(g, e) and _not_loop(g, f) and (e == f or on_common_cycle(g, e, f))


def _isolated(g: Graph, v: int) -> bool:
    """An isolated vertex: every link at it is a loop."""
    return 0 <= v < g.n and all(a == b for a, b in g.links if v in (a, b))


@dataclass
class Walk:
    """A state of the walk: each vertex's entry number (0 if not entered) and climb-back number;
    the link stack, top first; the blocks out so far, each with its links in pop order, and each
    block's vertices. Then what only the invariants read: the link each vertex was entered by (None
    for a root or a vertex not entered), the vertex it was entered from, whether it has finished,
    and how many entries of its row the walk has taken. Past the end of a list, an entry number,
    climb-back number or count reads 0, a link None, a vertex itself, a flag False and a block's
    vertices none.

    The checks are for tests on small graphs: whether two links share a block is decided by
    `naive.on_common_cycle`, the tests' slow reference, which tries every path, so `check_valid`
    takes time exponential in the number of vertices. The walk itself does not use it."""

    entry: list[int]
    low: list[int]
    edges: list[int]
    blocks: list[list[int]]
    vertices: list[list[int]]
    arrival: list[int | None]
    up: list[int]
    finished: list[bool]
    taken: list[int]

    def _entry(self, v: int) -> int:
        return self.entry[v] if v < len(self.entry) else 0

    def _low(self, v: int) -> int:
        return self.low[v] if v < len(self.low) else 0

    def _vertices(self, k: int) -> list[int]:
        return self.vertices[k] if k < len(self.vertices) else []

    def _arrival(self, v: int) -> int | None:
        return self.arrival[v] if v < len(self.arrival) else None

    def _up(self, v: int) -> int:
        return self.up[v] if v < len(self.up) else v

    def _finished(self, v: int) -> bool:
        return self.finished[v] if v < len(self.finished) else False

    def _looked(self, g: Graph, x: int) -> list[tuple[int, int]]:
        """The entries of `x`'s row the walk has taken."""
        return g.adj[x][:self.taken[x] if x < len(self.taken) else 0]

    def _chain(self, x: int, k: int) -> list[int]:
        """`x` and the vertices above it in the walk's tree, at most `k + 1` of them."""
        if k == 0 or self._arrival(x) is None:
            return [x]
        return [x] + self._chain(self._up(x), k - 1)

    def _explored(self, g: Graph, v: int, x: int) -> bool:
        """`x` is `v`, or lies under a finished child of `v`."""
        return x == v or any(self._finished(y) and self._arrival(y) is not None
                             and self._up(y) == v for y in self._chain(x, g.n))

    def _climb(self, g: Graph, v: int) -> int:
        """The earliest entry number `v`'s explored subtree reaches by one taken row entry, never
        the link the vertex taking it arrived by; at most `v`'s own."""
        return min([self._entry(v)] + [self._entry(w) for x in range(g.n) if self._explored(g, v, x)
                                       for w, i in self._looked(g, x) if i != self._arrival(x)])

    def is_climb_back_is_earliest(self, g: Graph) -> bool:
        """Box invariant 1: each vertex's climb-back number is the earliest entry number the part
        of the walk below it can reach, without the link it arrived by; formally, through tree
        links and at most one other link, never the very link it arrived by (Lean
        `ClimbBackIsEarliest`)."""
        return all(self._low(v) == self._climb(g, v) for v in range(g.n) if self._entry(v) != 0)

    def is_stack_holds_open_links(self, g: Graph) -> bool:
        """Box invariant 2: the link stack holds the explored links whose block has not come off
        yet, and every block that has come off is whole; formally, exactly those links, each once;
        every finished block is a whole block of the network, and a finished block without links
        is an isolated vertex (Lean `StackHoldsOpenLinks`)."""
        m = len(g.links)
        taken = {i for x in range(g.n) for _, i in self._looked(g, x) if _not_loop(g, i)}
        out = {i for b in self.blocks for i in b}
        return (len(set(self.edges)) == len(self.edges)
                and all((f in self.edges) == (f in taken and f not in out) for f in range(m))
                and all((f in b) == _same_block(g, e, f)
                        for b in self.blocks for e in b for f in range(m))
                and all(len(self._vertices(k)) == 1 and _isolated(g, self._vertices(k)[0])
                        for k, b in enumerate(self.blocks) if not b))

    def check_valid(self, g: Graph) -> str | None:
        """The first piece of the Lean `Valid` the state breaks, or `None`."""
        if not self.is_climb_back_is_earliest(g):
            return "invariant 1 (climb_back_is_earliest)"
        if not self.is_stack_holds_open_links(g):
            return "invariant 2 (stack_holds_open_links)"
        return None

    def is_valid(self, g: Graph) -> bool:
        """The Lean `Valid`: its two pieces."""
        return self.check_valid(g) is None

    @staticmethod
    def trace(g: Graph) -> list[Walk]:
        """Every state of `blocks`' walk on `g`, one per step: after each root is entered, each
        row entry is taken (a skipped one too), each vertex finishes under its parent, and each
        root finishes. What only the invariants read is taken from the path: a frame's link and
        the frame below it give a vertex's arrival link and the vertex it was entered from, a
        vertex entered and off the path has finished and taken its whole row, and a frame's
        position is what its row has taken."""
        global _watch
        n = g.n
        arrival: list[int | None] = [None] * n
        up = list(range(n))
        states: list[Walk] = []

        def record(entry: list[int], low: list[int], link_stack: list[int],
                   found: list[list[int]], found_vertices: list[list[int]],
                   path: list[list[int]]) -> None:
            for below, (v, e, _) in pairwise(path):
                arrival[v], up[v] = e, below[0]
            on_path = {v: i for v, _, i in path}
            states.append(Walk(
                entry=list(entry), low=list(low), edges=link_stack[::-1],
                blocks=[list(b) for b in found], vertices=[list(b) for b in found_vertices],
                arrival=list(arrival), up=list(up),
                finished=[entry[v] != 0 and v not in on_path for v in range(n)],
                taken=[on_path[v] if v in on_path else len(g.adj[v]) if entry[v] != 0 else 0
                       for v in range(n)]))

        _watch = record
        try:
            blocks(g)
        finally:
            _watch = _quiet
        return states


class BlockCutForest:
    """The block-cut forest: nodes `0 .. len(blocks)-1` are the blocks, then one node per cut
    vertex in increasing vertex order; a cut vertex's node is joined to every block holding it.

    Each piece's tree is rooted at the node of the piece's smallest vertex. `parent[x]` is the
    node above x (a root is its own parent) and `depth[x]` the number of steps up to the root.
    """

    def __init__(self, g: Graph, b: Blocks) -> None:
        """Join every cut vertex's node to its blocks, then root each tree. Linear in vertices plus
        blocks."""
        self.n = g.n
        self.n_blocks = len(b.blocks)
        self.cut_vertices = b.cut_vertices
        size = self.n_blocks + len(b.cut_vertices)
        node_of_cut = {c: self.n_blocks + k for k, c in enumerate(b.cut_vertices)}
        self._node_of = [-1] * g.n
        around: list[list[int]] = [[] for _ in range(size)]
        for k, vertices in enumerate(b.block_vertices):
            for p in vertices:
                if p in node_of_cut:
                    around[k].append(node_of_cut[p])
                    around[node_of_cut[p]].append(k)
                else:
                    self._node_of[p] = k  # a vertex that is no cut vertex is in one block
        for c, x in node_of_cut.items():
            self._node_of[c] = x
        self.parent = [-1] * size
        self.depth = [0] * size
        for p in range(g.n):  # the smallest vertex of each piece roots its tree
            top = self._node_of[p]
            if self.parent[top] != -1:
                continue
            self.parent[top] = top
            stack = [top]
            while stack:
                x = stack.pop()
                for y in around[x]:
                    if self.parent[y] == -1:
                        self.parent[y] = x
                        self.depth[y] = self.depth[x] + 1
                        stack.append(y)

    def node_of(self, vertex: int) -> int:
        """A cut vertex's own node; for any other vertex, the one block holding it."""
        if not 0 <= vertex < self.n:
            raise IndexError(f"vertex {vertex} out of range 0..{self.n}")
        return self._node_of[vertex]

    def separators(self, u: int, v: int) -> list[int] | None:
        """The vertices whose failure alone separates `u` from `v`, increasing: the cut vertices
        strictly between their nodes on the forest path. `None` when they are in different
        pieces. Linear in the length of that path."""
        ends = (self.node_of(u), self.node_of(v))
        x, y = ends
        passed: set[int] = set()  # the nodes stepped onto from either end
        while x != y:
            if self.depth[x] < self.depth[y]:
                x, y = y, x  # step up from the deeper end
            if self.parent[x] == x:
                return None  # two different roots: two pieces
            x = self.parent[x]
            passed.add(x)
        cuts = [z - self.n_blocks for z in passed
                if z >= self.n_blocks and z not in ends]
        return sorted(self.cut_vertices[c] for c in cuts)
