# SPDX-License-Identifier: Apache-2.0
"""2-SAT: every formula with at most 3 variables and at most 4 clauses against brute force, and
the clause shapes the chapter names.

A clause is an unordered pair of literals, repeats allowed (21 of them on 3 variables), and a
formula a multiset of at most 4 clauses: 12,650 formulas on 3 variables. Clause order does not
matter: two different clauses never give the same arrow, so reordering them only renumbers arrow
ids, never changes a row.
"""

from __future__ import annotations

from itertools import combinations_with_replacement

import pytest

from algodesign.graphs import Digraph, Unsat, naive, two_sat


def implication_graph(n_vars: int, clauses: list[tuple[int, int]]) -> Digraph:
    return Digraph(2 * n_vars, [arrow for a, b in clauses for arrow in ((a ^ 1, b), (b ^ 1, a))])


def test_every_small_formula_against_brute_force() -> None:
    on_three = 0
    for n_vars in range(4):
        all_clauses = list(combinations_with_replacement(range(2 * n_vars), 2))
        for size in range(5):
            for formula in combinations_with_replacement(all_clauses, size):
                on_three += n_vars == 3
                clauses = list(formula)
                answer = two_sat(n_vars, clauses)
                if isinstance(answer, Unsat):
                    assert naive.two_sat(n_vars, clauses) is None
                    together = naive.mutual_groups(implication_graph(n_vars, clauses))
                    stuck = [i for i in range(n_vars) if together[2 * i] == together[2 * i + 1]]
                    assert answer.var == stuck[0]
                else:
                    assert naive.satisfies(answer, clauses)
    assert len(all_clauses) == 21
    assert on_three == 12650


def test_x_or_x_gives_two_copies_of_one_arrow() -> None:
    assert two_sat(1, [(0, 0)]) == [True]
    assert two_sat(1, [(1, 1)]) == [False]


def test_x_or_not_x_gives_two_loops() -> None:
    assert two_sat(1, [(0, 1)]) == [True]


def test_no_clauses() -> None:
    assert two_sat(0, []) == []
    assert two_sat(2, []) == [True, True]


def test_no_answer_names_the_smallest_variable_ruled_out() -> None:
    assert two_sat(1, [(0, 0), (1, 1)]) == Unsat(0)
    # x0 is free; x1 and not-x1 are both forced.
    assert two_sat(2, [(2, 2), (3, 3), (0, 1)]) == Unsat(1)
    # (x0 or x1), (x0 or not-x1), (not-x0 or x1), (not-x0 or not-x1): all four excluded together.
    assert two_sat(2, [(0, 2), (0, 3), (1, 2), (1, 3)]) == Unsat(0)


def test_a_literal_out_of_range_names_its_clause() -> None:
    with pytest.raises(ValueError, match=r"clause 1 names literal 5, out of range 0\.\.4"):
        two_sat(2, [(0, 1), (0, 5)])


def test_the_package_gives_the_printed_functions() -> None:
    # The chapter prints `two_sat(...)` and `blocks(g)`; importing either name from the package
    # gives the function, not its module.
    from algodesign.graphs import Graph, blocks  # noqa: PLC0415

    assert two_sat(1, [(0, 0)]) == [True]
    assert blocks(Graph(2, [(0, 1)])).bridges == [0]
