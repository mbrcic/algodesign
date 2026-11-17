# SPDX-License-Identifier: Apache-2.0
"""Dinic with scaling: each round is a round of Dinic's over the arrows whose residual capacity is
at least a threshold, which the rule keeps from one round to the next, as capacity scaling keeps it.

The threshold starts at the largest power of two not above the largest capacity of any arrow. A
round runs Dinic's round, its layers and its one walk, over the arrows with residual capacity at
least the threshold only, so every path it sends carries at least the threshold. When the layers
miss the sink, the round halves the threshold and tries again. An arrow always needs some residual
capacity, so a threshold of 0 searches as 1 does; when the layers at 1 miss the sink, the threshold
drops to 0 and the round sends nothing (capacity scaling with the shortest augmenting path algorithm
as its subroutine: Ahuja, Magnanti and Orlin, *Network Flows*, §7.4, p. 220, "Application to
Capacity Scaling Algorithm"; Dinic's rounds as that subroutine, with the threshold in the search and
in the walk, are this library's choice; KACTL's `Dinic.h` keeps it in the search only).

Each threshold takes at most `n` rounds for `n` vertices, so the run takes `O(n² m log U)` for
`m` arrows and the largest capacity `U`.

The rule is not taught: it has no Lean statement, and the workbench leaves it out.
"""

from __future__ import annotations

from .dinic import Dinic
from .residual import Augmentation, Residual


class DinicScaling(Dinic):
    """One round, one round of Dinic's over the arrows with residual capacity at least the
    threshold."""

    def __init__(self) -> None:
        """The threshold is set by `start`, from the network."""
        super().__init__()
        self.threshold = 0

    def start(self, residual: Residual) -> None:
        """The largest power of two not above the largest capacity of any arrow; 0 if none."""
        super().start(residual)
        largest = max(residual.residual_capacity, default=0)
        self.threshold = 1 << (largest.bit_length() - 1) if largest > 0 else 0

    def round(self, residual: Residual, at_least: int = 1) -> list[Augmentation]:
        """Dinic's round at the largest threshold whose layers still reach the sink."""
        while True:
            sent = super().round(residual, max(self.threshold, at_least))
            if sent:
                return sent
            if self.threshold <= 1:
                self.threshold = 0
                return []
            self.threshold //= 2
