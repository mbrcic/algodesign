# SPDX-License-Identifier: Apache-2.0
"""Spreading news: news passes along the arrows "can pass a message to", and nobody forgets what
they heard, so in the end each vertex holds what it started with and everything that can flow to it.

The groups are taken in topological order, so a group starts only after every group that can pass
it news is settled (Nielson and Nielson, *Principles of Program Analysis*, Fig. 4.18, pp. 70-71).
Inside a group the arrows go round in circles, so every member is re-run, its set becoming its own
united with its predecessors', until a whole pass over the group changes nothing (their Teaser
4.26: the whole group, not only the members whose predecessors changed). Repeating stops because
sets only grow, and only finitely many things can be heard.

The module is `dataflow`, its one function `spread`, and the chapter calls it spreading news: three
names for one thing.
"""

from __future__ import annotations

from .digraph import Digraph
from .scc import strong_components


def spread[T](g: Digraph, heard: list[set[T]]) -> list[set[T]]:
    """What each vertex has heard once all news has flowed; `heard` is left as it was. Each pass
    over a group walks its members' arrows in; a pass that changes something adds at least one
    thing to some member, so a group of s members, among which k things can be heard, takes at
    most k * s + 1 passes."""
    news = [set(s) for s in heard]
    for members in strong_components(g).groups:
        changed = True
        while changed:
            changed = False
            for v in members:
                incoming = (news[u] for u, _ in g.into[v])
                now = news[v].union(*incoming)
                if now != news[v]:
                    news[v] = now
                    changed = True
    return news
