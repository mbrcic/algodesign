# SPDX-License-Identifier: Apache-2.0
"""Knapsack as a longest path: the most value a box of capacity `C` can hold, and the items that
give it.

A state `(i, w)` says the first `i` items are decided and they use weight `w`. Two arrows leave
it: skip item `i`, to `(i + 1, w)`, gaining nothing; or take it, to `(i + 1, w + weight)`, gaining
its value, when that weight still fits. Every arrow decides one more item, so the graph has no
cycle, and each path from `(0, 0)` to the last layer is one packing that fits, worth what the path
gains (Ahuja, Magnanti and Orlin, *Network Flows*, Fig. 4.3, pp. 101-102). The states are never
built as a graph: `best[i][w]` holds the most a path into `(i, w)` gains, `None` while no arrow
has reached it, and the table is filled one layer at a time, which is a topological order. From
each reached state of a layer, by increasing weight, the skip is tried, then the take; an arrow
raises its end's gain when it gains more, or reaches it first. That is at most two arrows out of
each of the `n (C + 1)` states before the last layer.

The answer is the best gain in the last layer, the least weight on a tie. The items come from
walking back from there through the table: item `i - 1` was taken when taking it fits and gains at
least as much as skipping it, a tie taking it (Roughgarden, *Algorithms Illuminated*, Part 3,
§16.5, p. 131). The walk back is recursive, one call per item, so a list of about a thousand items
meets Python's `RecursionError`. A weight or a capacity below zero raises `ValueError`, as does a
list of weights that is not as long as the list of values.

`State` is the walk's state, as the Lean's `State`: how many items are decided, the layers filled,
and how many arrows were tried. Its `step` is the Lean's `step`.

The Rust differs here: it keeps only the layer it reads and the layer it fills, and one bit per
state saying whether the walk back takes the item there, set while the layers are filled; the
answer and the items are the same. It walks back by a loop over the bits, and it has no `State`.

The Lean statements behind this module, in `lean/AlgoDesign/Paths/Knapsack/`: `valid_start`,
`valid_step`, `knapsack_spec`, `chosen_spec`, `knapsack_cost`, `paths_are_packings`, `no_cycle`.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass
class Packing:
    """The best value, and the items that give it, by index in increasing order."""

    value: int
    items: list[int]


def knapsack(weights: list[int], values: list[int], capacity: int) -> Packing:
    """The most value that fits in a box of `capacity`, item `i` weighing `weights[i]` and worth
    `values[i]`, and the items that give it."""
    if len(weights) != len(values):
        raise ValueError(f"{len(weights)} weights for {len(values)} values")
    if capacity < 0 or any(weight < 0 for weight in weights):
        raise ValueError("a weight or the capacity is below zero")
    best: list[list[int | None]] = [[None] * (capacity + 1)]  # layer 0: nothing decided
    best[0][0] = 0  # the start, (0, 0)
    for weight, value in zip(weights, values):
        best.append(next_layer(best[-1], weight, value))
    gain = max(b for b in best[-1] if b is not None)  # (n, 0) is always reached
    w = best[-1].index(gain)  # the least weight on a tie
    return Packing(gain, chosen(best, weights, values, len(weights), w))


def next_layer(layer: list[int | None], weight: int, value: int) -> list[int | None]:
    """The layer after deciding one more item: from each reached state, the two arrows out."""
    capacity = len(layer) - 1
    nxt: list[int | None] = [None] * len(layer)
    for w, b in enumerate(layer):
        if b is None:
            continue  # no path reaches (i, w)
        relax(nxt, w, b)  # skip the item
        if w + weight <= capacity:
            relax(nxt, w + weight, b + value)  # take it
    return nxt


def relax(layer: list[int | None], w: int, gain: int) -> None:
    """Keep `gain` at weight `w` if nothing has reached it yet, or `gain` is more."""
    if (b := layer[w]) is None or b < gain:
        layer[w] = gain


def chosen(best: list[list[int | None]], weights: list[int], values: list[int],
           i: int, w: int) -> list[int]:
    """The items taken on a best path into `(i, w)`, walking back: item `i - 1` is taken when
    taking it fits and gains at least as much as skipping it."""
    if i == 0:
        return []
    weight, value = weights[i - 1], values[i - 1]
    took = best[i - 1][w - weight] if weight <= w else None
    skipped = best[i - 1][w]
    if took is not None and (skipped is None
                             or skipped <= took + value):
        return chosen(best, weights, values,
                      i - 1, w - weight) + [i - 1]
    return chosen(best, weights, values, i - 1, w)


@dataclass
class State:
    """A state of the walk: how many items are decided, the layers of the table filled so far
    (`best[i][w]`, `None` where no arrow has reached `(i, w)`), and how many arrows were tried."""

    decided: int
    best: list[list[int | None]]
    tried: int

    @staticmethod
    def start(capacity: int) -> State:
        """Nothing decided; only `(0, 0)` reached, with gain 0."""
        layer: list[int | None] = [None] * (capacity + 1)
        layer[0] = 0
        return State(0, [layer], 0)

    def step(self, weights: list[int], values: list[int]) -> None:
        """Fill the next layer from the last one filled, counting the arrows tried: the skip out of
        every reached state, and the take where it fits. With every item decided, the state is
        left as it is."""
        if self.decided >= len(weights):
            return
        layer, weight = self.best[self.decided], weights[self.decided]
        self.best.append(next_layer(layer, weight, values[self.decided]))
        capacity = len(layer) - 1
        self.tried += sum(1 if w + weight > capacity else 2
                          for w, b in enumerate(layer) if b is not None)
        self.decided += 1
