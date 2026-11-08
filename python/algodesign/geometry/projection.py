# SPDX-License-Identifier: Apache-2.0
"""Random projection: multiply by a k x d matrix of independent Gaussian entries, variance 1/k
(Dasgupta-Gupta 2003; BHK §2.9; Wright-Ma Thm 3.19).

The Johnson-Lindenstrauss lemma: with k = O(log n / eps**2), every pairwise distance among n
points survives within a factor 1 +- eps, with high probability. Each output coordinate is one dot
product, so the map is linear. The matrix comes from the shared generator, in the Rust's order (row
by row), so a seed gives the Rust's matrix.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/LSH/Families.lean`:
`dot_add`.
The JL bound itself is not proved there; a seeded statistical test holds it.
"""

from __future__ import annotations

import math
from collections.abc import Sequence

from ._rng import SplitMix64
from .point import check_query, dot


class GaussianProjection:
    """A seeded projection from `d_in` to `k` dimensions."""

    def __init__(self, d_in: int, k: int, seed: int) -> None:
        if d_in < 1 or k < 1:
            raise ValueError(f"a projection needs d_in >= 1 and k >= 1, got {d_in} and {k}")
        rng = SplitMix64(seed)
        scale = 1.0 / math.sqrt(k)
        self.matrix = [[rng.standard_normal() * scale for _ in range(d_in)] for _ in range(k)]

    def project(self, v: Sequence[float]) -> list[float]:
        """The image of `v`: one dot product per row."""
        check_query(self.matrix, v)
        return [dot(row, v) for row in self.matrix]
