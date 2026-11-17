"""Counting the work of the heap loops the book prints: which arrows' costs a walk reads, and how
many entries it pushes on its queue. The `State` twins count their own pushes; these counts hold
the printed loops to the same procedure."""

from __future__ import annotations

import heapq
from collections.abc import Callable
from typing import Any, SupportsIndex, overload

import pytest

from algodesign.paths import Network


class ReadCosts(list[int]):
    """A cost list that records the arrow id of every cost read from it."""

    def __init__(self, cost: list[int]) -> None:
        super().__init__(cost)
        self.read: list[int] = []

    @overload
    def __getitem__(self, i: SupportsIndex) -> int: ...

    @overload
    def __getitem__(self, i: slice) -> list[int]: ...

    def __getitem__(self, i: SupportsIndex | slice) -> int | list[int]:
        if isinstance(i, slice):
            return super().__getitem__(i)
        self.read.append(int(i))
        return super().__getitem__(i)


def work(walk: Callable[[Network], Any], network: Network) -> tuple[list[int], int]:
    """The arrow ids whose costs `walk` reads, in order, and how many entries it pushes, counted
    at `heapq.heappush`; on a copy of `network` whose costs record their reads."""
    counted = Network(network.g, network.cost)
    costs = ReadCosts(network.cost)
    counted.cost = costs
    count = 0
    push = heapq.heappush

    def pushing(queue: list[tuple[int, int]], entry: tuple[int, int]) -> None:
        nonlocal count
        count += 1
        push(queue, entry)

    with pytest.MonkeyPatch.context() as m:
        m.setattr(heapq, "heappush", pushing)
        walk(counted)
    return costs.read, count
