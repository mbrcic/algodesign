# SPDX-License-Identifier: Apache-2.0
"""Capacity scaling: each round sends along one augmenting path whose every arrow has residual
capacity at least a threshold, which the rule keeps from one round to the next.

The threshold starts at the largest power of two not above the largest capacity of any arrow. A
round runs Edmonds–Karp's search over the arrows with residual capacity at least the threshold and
sends the path it finds its bottleneck. When the search misses the sink, the round halves the
threshold and searches again. An arrow always needs some residual capacity, so a threshold of 0
searches as 1 does; when the search at 1 misses the sink, the threshold drops to 0 and the round
sends nothing (Ahuja and Orlin; Ahuja, Magnanti and Orlin, *Network Flows*, §7.3; Cormen, Leiserson,
Rivest and Stein, *Introduction to Algorithms*, 4th ed., Problem 24-5; one path per round).

Each threshold sends at most `2m` paths for `m` arrows, so the run takes `O(m^2 log U)` for the
largest capacity `U`.

The Rust differs here: its search keeps its labels and queue in arrays from round to round, and
it sends along the labels without building the path.

The Lean statements behind this module, in `lean/AlgoDesign/Flows/MaxFlow/CapacityScaling.lean`:
the rule's promise, `capacityScaling_promise`.
"""

from __future__ import annotations

from .edmonds_karp import shortest_path
from .residual import Augmentation, Residual


class CapacityScaling:
    """One round, one path whose every arrow has residual capacity at least the threshold."""

    def __init__(self) -> None:
        """The threshold is set by `start`, from the network."""
        self.threshold = 0

    def start(self, residual: Residual) -> None:
        """The largest power of two not above the largest capacity of any arrow; 0 if none."""
        largest = max(residual.residual_capacity, default=0)
        self.threshold = 1 << (largest.bit_length() - 1) if largest > 0 else 0

    def round(self, residual: Residual) -> list[Augmentation]:
        """Send along one path at the largest threshold that still has one."""
        while True:
            path = shortest_path(residual, max(self.threshold, 1))
            if path is not None:
                return [(path, residual.augment(path))]
            if self.threshold <= 1:
                self.threshold = 0
                return []
            self.threshold //= 2
