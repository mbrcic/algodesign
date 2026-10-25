# SPDX-License-Identifier: Apache-2.0
"""2-SAT: give each variable true or false so that every clause (a or b) holds, or show that no
choice can.

The method is Aspvall, Plass and Tarjan's (1979, p. 122). Literal 2i is xᵢ and 2i + 1 is not-xᵢ,
so `a ^ 1` is the negation of `a`. A clause (a or b) gives two arrows "if this is false, then that
must be true": not-a -> b and not-b -> a. A clause (x or x) gives two copies of one arrow, and
(x or not-x) two loops. The formula has no answer exactly when some xᵢ and not-xᵢ are in one strong
component; otherwise xᵢ is true when its group comes after not-xᵢ's in topological order (the
parity cp-algorithms uses), that is `group_of[2i] > group_of[2i + 1]`.
"""

from __future__ import annotations

from dataclasses import dataclass

from .digraph import Digraph
from .scc import strong_components


@dataclass(frozen=True)
class Unsat:
    """No answer: xᵢ and not-xᵢ, for i = `var` (the smallest such), are in one group."""

    var: int


def two_sat(n_vars: int, clauses: list[tuple[int, int]]) -> list[bool] | Unsat:
    """A value for each variable that makes every clause true, or the variable that rules it out.

    Raises `ValueError` naming the first clause with a literal not below `2 * n_vars`."""
    for k, (a, b) in enumerate(clauses):
        for literal in (a, b):
            if not 0 <= literal < 2 * n_vars:
                raise ValueError(
                    f"clause {k} names literal {literal}, out of range 0..{2 * n_vars}"
                )
    arrows = []
    for a, b in clauses:
        arrows += [(a ^ 1, b), (b ^ 1, a)]
    implications = Digraph(2 * n_vars, arrows)
    group_of = strong_components(implications).group_of
    for i in range(n_vars):
        if group_of[2 * i] == group_of[2 * i + 1]:
            return Unsat(i)
    return [group_of[2 * i] > group_of[2 * i + 1]
            for i in range(n_vars)]
