# SPDX-License-Identifier: Apache-2.0
"""Test-only: what a property test's inputs actually reach.

A property test is only as good as its inputs reach: a test that never reaches a case cannot fail
on it, and stays green. Short FM-index texts, query positions past the end of the input, and
suffix-array texts too short to need a third doubling round are the misses this guards against.
Inspecting the strategy objects is not enough: the test could be switched to another strategy, or
the strategy could draw texts of the right length over one symbol.

`inputs_reaching` therefore runs the **`@given` test itself**, on a fixed set of random byte
buffers (Hypothesis' `fuzz_one_input`, so the run is the same every time), and records what the
library was handed while it ran: whatever the strategy is, and whichever strategy the test uses.
"""

from __future__ import annotations

import random
from collections.abc import Callable
from typing import Any, TypeVar
from unittest import mock

T = TypeVar("T")


def inputs_reaching(
    test: Any, target: Any, name: str, record: Callable[..., T], runs: int = 100
) -> list[T]:
    """Run the Hypothesis test `test` on `runs` fixed random buffers, with `target.name` wrapped
    so that every call to it first appends `record(*args, **kwargs)` to the answer."""
    seen: list[T] = []
    original = getattr(target, name)

    def spy(*args: Any, **kwargs: Any) -> Any:
        seen.append(record(*args, **kwargs))
        return original(*args, **kwargs)

    with mock.patch.object(target, name, spy):
        for run in range(runs):
            test.hypothesis.fuzz_one_input(random.Random(run).randbytes(8000))
    return seen
