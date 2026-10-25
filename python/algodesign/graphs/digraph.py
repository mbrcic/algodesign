# SPDX-License-Identifier: Apache-2.0
"""Directed and undirected graphs on the vertices `0 .. n-1`, stored as rows.

A `Digraph` holds its arrows by id (an arrow's id is its position in the list it was built from).
Each vertex's row `out[v]` lists the arrows leaving `v` as `(neighbour, id)` pairs, sorted by
neighbour and then by id; `into[v]` is the same for the arrows entering `v`. A `Graph` holds its
links by id the same way, and a vertex's row `adj[v]` has one entry per end of a link at `v`: a link
between two vertices is in both rows with one id, and a loop is twice in its own vertex's row
(Ahuja, Magnanti and Orlin, *Network Flows*, §2.3, p. 38: "we will store each arc (i, j) of an
undirected network twice").

Loops and doubled arrows or links are accepted; each algorithm says what it does with them. The
rows equal `Digraph.out`, `Digraph.into` and `Graph.adj` in the Lean's `Graphs/Digraph.lean`.
Every algorithm of the chapter walks a row in this order and starts its outer loop at vertex 0, so
the Python and the Rust give the same answers, not just equally correct ones.

An endpoint outside `0 .. n-1`, or a negative number of vertices, raises `ValueError`.
"""

from __future__ import annotations


def _check(n: int, pairs: list[tuple[int, int]], what: str) -> None:
    """Refuse a negative `n` and any endpoint outside `0 .. n-1`."""
    if n < 0:
        raise ValueError(f"the number of vertices must be nonnegative, not {n}")
    for i, (a, b) in enumerate(pairs):
        if not (0 <= a < n and 0 <= b < n):
            raise ValueError(f"{what} {i} = ({a}, {b}) has an end outside 0..{n}")


class Digraph:
    """A directed graph: vertices `0 .. n-1` and arrows `(from, to)`, each with its id."""

    def __init__(self, n: int, arrows: list[tuple[int, int]]) -> None:
        """Build the rows: every arrow in its tail's `out` row and its head's `into` row."""
        _check(n, arrows, "arrow")
        self.n = n
        self.arrows = list(arrows)  # by id
        self.out: list[list[tuple[int, int]]] = [[] for _ in range(n)]
        self.into: list[list[tuple[int, int]]] = [[] for _ in range(n)]
        for i, (v, w) in enumerate(arrows):
            self.out[v].append((w, i))
            self.into[w].append((v, i))
        for row in self.out + self.into:
            row.sort()  # by neighbour, then id


class Graph:
    """An undirected graph: vertices `0 .. n-1` and links `{a, b}`, each with its id."""

    def __init__(self, n: int, links: list[tuple[int, int]]) -> None:
        """Build the rows: every link in both its ends' rows, a loop twice in its own."""
        _check(n, links, "link")
        self.n = n
        self.links = list(links)  # by id
        self.adj: list[list[tuple[int, int]]] = [[] for _ in range(n)]
        for i, (a, b) in enumerate(links):
            self.adj[a].append((b, i))
            self.adj[b].append((a, i))
        for row in self.adj:
            row.sort()  # by neighbour, then id
