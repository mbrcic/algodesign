# SPDX-License-Identifier: Apache-2.0
"""Slow references that are correct by inspection, for the tests to compare the real structures
against. The state checks of `scc.Walk` and `block_cut.Walk` also use `reachable` and
`on_common_cycle`; the algorithms themselves never do.
"""

from __future__ import annotations

from itertools import pairwise, product

from .digraph import Digraph, Graph


def groups(n: int, pairs: list[tuple[int, int]]) -> list[int]:
    """The group of every item after the unions in `pairs`: each item is labelled with the
    smallest item it is joined to, found by a depth-first search over the pairs as undirected
    links. O(n + len(pairs))."""
    links: list[list[int]] = [[] for _ in range(n)]
    for x, y in pairs:
        links[x].append(y)
        links[y].append(x)
    label = [-1] * n
    for start in range(n):
        if label[start] != -1:
            continue
        label[start] = start
        stack = [start]
        while stack:
            i = stack.pop()
            for j in links[i]:
                if label[j] == -1:
                    label[j] = start
                    stack.append(j)
    return label


def is_order(g: Digraph, order: list[int]) -> bool:
    """Is `order` every vertex once, with every arrow from an earlier vertex to a later one? A loop
    never is."""
    if sorted(order) != list(range(g.n)):
        return False
    position = {v: k for k, v in enumerate(order)}
    return all(position[v] < position[w] for v, w in g.arrows)


def is_stuck_set(g: Digraph, vertices: list[int]) -> bool:
    """Is `vertices` a set of vertices no order can begin with? It must be nonempty and increasing,
    every member must have an arrow into it from a member, and the vertices outside it, with the
    arrows among them, must have an order: peeled off one at a time, each with no arrow into it
    from a vertex not yet peeled."""
    if not vertices or vertices != sorted(set(vertices)) or not all(0 <= v < g.n for v in vertices):
        return False
    inside = set(vertices)
    if not all(any(v in inside for v, _ in g.into[w]) for w in vertices):
        return False
    left = set(range(g.n)) - inside
    while left:
        free = [w for w in left if not any(v in left for v, _ in g.into[w])]
        if not free:
            return False
        left -= set(free)
    return True


def is_cycle(g: Digraph, vertices: list[int]) -> bool:
    """Is `vertices` a cycle w, ..., v, w: closed, each vertex with an arrow to the next, and no
    vertex twice before the closing one?"""
    if len(vertices) < 2 or vertices[0] != vertices[-1]:
        return False
    if len(set(vertices[:-1])) != len(vertices) - 1:
        return False
    return all(any(w == b for w, _ in g.out[a]) for a, b in pairwise(vertices))


def reachable(g: Digraph, starts: list[int]) -> set[int]:
    """Every vertex one or more arrows lead to from some vertex of `starts`, by a plain search."""
    seen: set[int] = set()
    stack = [w for v in starts for w, _ in g.out[v]]
    while stack:
        v = stack.pop()
        if v not in seen:
            seen.add(v)
            stack.extend(w for w, _ in g.out[v])
    return seen


def has_cycle(g: Digraph) -> bool:
    """Does some vertex reach itself by one or more arrows? O(n * (n + m))."""
    return any(v in reachable(g, [v]) for v in range(g.n))


def stuck_vertices(g: Digraph) -> list[int]:
    """The vertices no order of Kahn's can reach, increasing: those on a cycle and those a cycle
    leads to. O(n * (n + m))."""
    on_cycle = [v for v in range(g.n) if v in reachable(g, [v])]
    return sorted(reachable(g, on_cycle))


def mutual_groups(g: Digraph) -> list[int]:
    """Each vertex labelled with the smallest vertex it and that vertex reach each other from (a
    vertex reaches itself by no arrows), by a plain search from every vertex. O(n * (n + m))."""
    reach = [reachable(g, [v]) | {v} for v in range(g.n)]
    return [min(w for w in reach[v] if v in reach[w]) for v in range(g.n)]


def same_partition(a: list[int], b: list[int]) -> bool:
    """Do the labellings `a` and `b` put the same vertices together, whatever the labels are?"""
    return len(a) == len(b) and len(set(zip(a, b))) == len(set(a)) == len(set(b))


def postorder(g: Digraph) -> list[int]:
    """The vertices in the order a depth-first walk finishes them: roots 0 upward, rows in order."""
    finished: list[int] = []
    entered = [False] * g.n

    def walk(v: int) -> None:
        entered[v] = True
        for w, _ in g.out[v]:
            if not entered[w]:
                walk(w)
        finished.append(v)

    for v in range(g.n):
        if not entered[v]:
            walk(v)
    return finished


def satisfies(values: list[bool], clauses: list[tuple[int, int]]) -> bool:
    """Does every clause (a or b) hold, literal 2i being xᵢ and 2i + 1 not-xᵢ?"""

    def holds(lit: int) -> bool:
        return values[lit // 2] != (lit % 2 == 1)

    return all(holds(a) or holds(b) for a, b in clauses)


def two_sat(n_vars: int, clauses: list[tuple[int, int]]) -> list[bool] | None:
    """The first assignment, in the order of `itertools.product`, that satisfies every clause, or
    None. O(2^n_vars * len(clauses))."""
    for values in product([False, True], repeat=n_vars):
        if satisfies(list(values), clauses):
            return list(values)
    return None


def spread[T](g: Digraph, heard: list[set[T]]) -> list[set[T]]:
    """What each vertex has heard: every vertex takes in its predecessors' news, over and over,
    until a whole pass over all vertices changes nothing."""
    news = [set(s) for s in heard]
    changed = True
    while changed:
        changed = False
        for v in range(g.n):
            for u, _ in g.into[v]:
                if not news[u] <= news[v]:
                    news[v] |= news[u]
                    changed = True
    return news


def pieces(n: int, links: list[tuple[int, int]], gone: int | None = None) -> int:
    """The number of pieces of the graph on the vertices `0 .. n-1` with `links`, when the vertex
    `gone` (if any) is deleted with every link at it."""
    kept = [(a, b) for a, b in links if gone not in (a, b)]
    return len(set(groups(n, kept))) - (gone is not None)


def bridges(g: Graph) -> list[int]:
    """The links whose deletion alone leaves more pieces, by deleting each one in turn."""
    whole = pieces(g.n, g.links)
    return [i for i in range(len(g.links))
            if pieces(g.n, g.links[:i] + g.links[i + 1:]) > whole]


def cut_vertices(g: Graph) -> list[int]:
    """The vertices whose deletion alone leaves more pieces, by deleting each one in turn."""
    whole = pieces(g.n, g.links)
    return [v for v in range(g.n) if pieces(g.n, g.links, gone=v) > whole]


def on_common_cycle(g: Graph, e: int, f: int) -> bool:
    """Do the links `e` and `f` lie on one cycle with distinct vertices? Such a cycle through e =
    {a, b} is e with a path from b back to a that uses another link and repeats no vertex; every
    such path is tried. A doubled link and its copy make a cycle of two."""
    a, b = g.links[e]

    def path_uses_f(v: int, seen: set[int], used_f: bool) -> bool:
        if v == a:
            return used_f
        return any(path_uses_f(w, seen | {w}, used_f or i == f)
                   for w, i in g.adj[v] if i != e and w not in seen)

    return a != b and path_uses_f(b, {b}, False)


def blocks(g: Graph) -> set[tuple[frozenset[int], frozenset[int]]]:
    """The blocks as the book defines them, each as (its links, its vertices): two links other than
    loops are in one block when they are equal or on a common cycle with distinct vertices; loops
    are in none; a vertex with no link but loops is a block on its own with no links. Each class
    is read off one link's partners, so a relation that failed to group the links into classes
    would give overlapping blocks. Exponential: for small graphs only."""
    links = [i for i, (a, b) in enumerate(g.links) if a != b]
    found: set[tuple[frozenset[int], frozenset[int]]] = set()
    for e in links:
        block = frozenset(f for f in links if f == e or on_common_cycle(g, e, f))
        found.add((block, frozenset(p for i in block for p in g.links[i])))
    touched = {p for i in links for p in g.links[i]}
    found |= {(frozenset(), frozenset([v])) for v in range(g.n) if v not in touched}
    return found


def separators(g: Graph, u: int, v: int) -> list[int] | None:
    """The vertices other than `u` and `v` whose deletion alone leaves `v` out of `u`'s reach, by
    deleting each in turn; `None` when `v` is out of reach to begin with."""
    if groups(g.n, g.links)[u] != groups(g.n, g.links)[v]:
        return None

    def apart_without(w: int) -> bool:
        label = groups(g.n, [(a, b) for a, b in g.links if w not in (a, b)])
        return label[u] != label[v]

    return [w for w in range(g.n) if w not in (u, v) and apart_without(w)]
