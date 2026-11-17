# SPDX-License-Identifier: Apache-2.0
"""Test-only: did the code under test sort anything, by any of Python's ready-made means?

Shadowing the name `sorted` in a module catches one spelling of a comparison sort and misses the
rest. `sorts_during` watches every call made while its block runs, through `sys.setprofile`, and
records each call of:

- the builtin `sorted`, or a list's `sort` method, however reached;
- anything in `heapq` -- `heapify`, `heappush`, `heappop`, `nsmallest`, `merge` and the rest,
  which order by comparison as surely as a sort does (a heap drained is a heap sort);
- `bisect.insort` and its variants, which build a sorted list one insertion at a time.

`bisect.bisect_left` and `bisect_right` are not on the list: a binary search into a list that is
already sorted is what the library is supposed to do.
"""

from __future__ import annotations

import sys
from collections.abc import Iterator
from contextlib import contextmanager
from types import FrameType
from typing import Any

_SORTING_NAMES = {"sorted", "insort", "insort_left", "insort_right"}


@contextmanager
def sorts_during() -> Iterator[list[str]]:
    """Yield a list that, when the block ends, holds one entry per sorting call made inside it."""
    calls: list[str] = []
    previous = sys.getprofile()

    def watch(frame: FrameType, event: str, arg: Any) -> None:
        if event == "call":
            # A Python-level function of `heapq` (`nsmallest`, `merge`, ...).
            if frame.f_globals.get("__name__") == "heapq":
                calls.append(f"heapq.{frame.f_code.co_name}")
            return
        if event != "c_call":
            return
        name = getattr(arg, "__name__", None)
        owner = getattr(arg, "__self__", None)
        module = getattr(arg, "__module__", None) or getattr(owner, "__name__", None)
        if name in _SORTING_NAMES or (name == "sort" and isinstance(owner, list)):
            calls.append(f"{name} from {frame.f_code.co_name}")
        elif module in ("_heapq", "heapq"):
            calls.append(f"heapq.{name} from {frame.f_code.co_name}")

    sys.setprofile(watch)
    try:
        yield calls
    finally:
        sys.setprofile(previous)
