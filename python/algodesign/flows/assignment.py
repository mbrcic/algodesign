# SPDX-License-Identifier: Apache-2.0
"""The assignment: every person one object, every object one person, at the least total cost, with
a label on every person and every object that proves no assignment costs less.

The table is square, row `i` for person `i` and column `j` for object `j`. The people are placed
one at a time, in row order, with every label zero at the start. Placing person `i` is one
best-first search over the objects on changed costs: the cost of a pair minus the label of its
person minus the label of its object, with the labels as they stand when the search starts. A list
holds each object's distance from person `i`, the cheapest changed cost of a path to it through the
people reached so far, and the object it came through. Each pick settles the unsettled object with
the smallest distance; on a tie a free object first, then the lowest index. If the picked object is
free, the search stops; otherwise the person holding it is reached, and their row may lower the
distances (only a strict drop changes a distance and the object it came through). Then the labels
move once, as the cheapest flow's heights: with `top` the free object's distance, person `i` gains
`top`, and every settled object loses `top` less its own distance while its holder gains it. Then
the people along the path move one object on, and person `i` takes the path's first object.

This is shortest augmenting paths with heights, one person at a time (Ahuja, Magnanti and Orlin,
*Network Flows*, 1993, §12.4, p. 471): the cheapest flow on the matching network, its heights read
as labels on both sides. The labels fit every pair, `person_label[i] + object_label[j] <=
cost[i][j]`, and meet every chosen pair exactly, so they add up to the answer's cost, and every
assignment costs at least that. Read as prices, `-object_label[j]`, every person's object is their
favorite after price.

A table that is not square raises `ValueError`. Costs may be below zero: a search starts at the
person being placed, whose label is not yet held to fit, so the first arrows of the search may have
any changed cost; every later arrow leaves a placed person, whose labels fit, so its changed cost is
zero or more and the search stays safe. One search per person,
each of at most `n` picks, each pick a pass over the objects: the work grows like `n**3`.
`assignment_with_steps` also gives every person's step: the objects the search settled in order,
the path's objects, and the labels after it.

The Rust differs here: its search's arrays are kept from person to person, one pass over a reached
person's row both lowers the distances and finds the next pick, and it follows the path back through
the arrays without building it; it records the steps only in test builds; and it also
offers the same procedure on decimals, `assignment_f64`, with a stated tolerance for the labels.

This module has no `check_valid`. The Lean `Valid`, `CheapestForThesePeople` and
`LabelsFitAndExact`, is checked in its tests on the state after every person: the labels fit every
pair of the people placed so far and are exact on their chosen pairs, which makes those people's
objects the cheapest for them.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/Assignment/`: the library's
steps meet the contract, `contract`.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass
class Assignment:
    """Every person's object, the label of every person and every object, and the total cost."""

    obj: list[int]
    person_label: list[int]
    object_label: list[int]
    cost: int


@dataclass
class AssignmentStep:
    """One person's step: the objects the search settled in order (the free one last), the path's
    objects (the one the new person takes first), and the labels after it."""

    settled: list[int]
    path: list[int]
    person_label: list[int]
    object_label: list[int]


def place(
    i: int, cost: list[list[int]], holder: list[int | None], u: list[int], v: list[int]
) -> tuple[list[int], list[int]]:
    """Person `i`'s search, then the labels `u` and `v` moved once: the objects settled in order,
    and the path's objects from the one person `i` takes to a free one."""
    n = len(cost)
    dist = [cost[i][j] - u[i] - v[j] for j in range(n)]  # on the labels as the search starts
    came_from: list[int | None] = [None] * n  # the object before it on its path
    settled: list[int] = []
    unsettled = list(range(n))
    while True:
        # smallest distance, then a free object first, then the lowest index
        picked = min(unsettled, key=lambda j: (dist[j], holder[j] is not None, j))
        settled.append(picked)
        unsettled.remove(picked)
        r = holder[picked]
        if r is None:
            break
        for j in unsettled:
            through = dist[picked] + cost[r][j] - u[r] - v[j]
            if through < dist[j]:
                dist[j] = through
                came_from[j] = picked
    # the labels move once, as the cheapest flow's heights
    top = dist[picked]
    u[i] += top
    for j in settled:
        holder_j = holder[j]
        v[j] -= top - dist[j]
        if holder_j is not None:
            u[holder_j] += top - dist[j]
    path = [picked]
    while (before := came_from[path[-1]]) is not None:
        path.append(before)
    path.reverse()
    return settled, path


def assignment_with_steps(cost: list[list[int]]) -> tuple[Assignment, list[AssignmentStep]]:
    """A least-cost assignment of the square table `cost` with its labels, and every person's
    step."""
    n = len(cost)
    for row, costs in enumerate(cost):
        if len(costs) != n:
            raise ValueError(f"row {row} has {len(costs)} costs for {n} people")
    u = [0] * n
    v = [0] * n
    obj = [0] * n
    holder: list[int | None] = [None] * n
    steps = []
    for i in range(n):
        settled, path = place(i, cost, holder, u, v)
        # person i takes the first object, each holder along the path the next one
        movers = [i] + [holder[j] for j in path[:-1]]
        for p, j in zip(movers, path, strict=True):
            assert p is not None
            obj[p] = j
            holder[j] = p
        steps.append(AssignmentStep(settled, path, u.copy(), v.copy()))
    total = sum(cost[p][obj[p]] for p in range(n))
    return Assignment(obj, u, v, total), steps


def assignment(cost: list[list[int]]) -> Assignment:
    """A least-cost assignment of the square table `cost`, row `i` for person `i`, with a label on
    every person and every object: on every pair the two labels add up to at most its cost,
    and on every chosen pair exactly to it."""
    return assignment_with_steps(cost)[0]
