# SPDX-License-Identifier: Apache-2.0
"""RaBitQ: store each vector as one bit per coordinate, and estimate distances from the bits
without bias (Gao and Long 2024, §3; Algorithm 1 builds the codes, Algorithm 2 answers a query).

**The codes** (Algorithm 1):
- Every vector is normalized around the centroid `c`: `o = (o_r - c) / ||o_r - c||` (§3.1.1).
- A seeded random rotation `P` (modified Gram-Schmidt, run twice, on Gaussian rows) is applied,
  and the code is the sign of each rotated coordinate: `x_bar = (2 x_b - 1) / sqrt(D)` (§3.1.3).
- Two numbers per vector are kept: `||o_r - c||` and `<o_bar, o> = <x_bar, P^T o>`.

**The estimate** (Algorithm 2). The query is normalized and rotated the same way, `q'`. Then
`<o, q>` is estimated by `<x_bar, q'> / <o_bar, o>` (Eq. 13), which is unbiased (Theorem 3.2), and
the squared distance follows by Eq. 2:
`||o_r - q_r||^2 = ||o_r - c||^2 + ||q_r - c||^2 - 2 ||o_r - c|| ||q_r - c|| <o, q>`.

**The query's quantization is a black box here.** Gao and Long also quantize the query, to a few
bits per coordinate, so that `<x_bar, q'>` becomes bitwise ANDs and population counts (§3.3);
that is where the speed comes from, and the Rust does it, at 4 bits
(`rust/crates/algodesign/src/geometry/rabitq.rs`). This rendering calls `quantize_query`, which
returns `q'` unchanged, and computes `<x_bar, q'>` as an ordinary dot product. So its estimates,
and the walk they steer, may differ from the Rust's.

**On the graph index the combination is the book's, not the paper's.** The paper runs RaBitQ in
an inverted-file index and leaves graphs to future work. `search_quantized` uses one centroid for
the whole set, lets the HNSW walk rank nodes by the estimate, and re-checks every candidate left
in the final `ef` with its exact distance. The answer's distances and order are therefore exact
among those candidates; whether the true nearest points are among them is not guaranteed, and the
paper's re-ranking guarantee does not transfer.

`SignCodes` is the baseline RaBitQ's recall and speed on the graph are measured against: the
signs of `o - c` with no rotation, and `<o, q>` estimated by `<x_bar, q>` with no correction,
which is biased.

The Rust differs here: it quantizes the query to `B_Q` bits, so its estimates and the walk they
steer differ from these.

No Lean theorem stands behind this module: the error bound of Theorem 3.2 is probabilistic and is
not proved there. Seeded statistical tests hold the unbiasedness instead.
"""

from __future__ import annotations

import math
from collections.abc import Sequence
from dataclasses import dataclass
from typing import Protocol

from . import scan
from ._rng import SplitMix64
from .hnsw import HNSW, Found
from .point import check_query, copy_points, dot


def random_orthogonal(d: int, seed: int) -> list[list[float]]:
    """A seeded random orthogonal `d x d` matrix, as rows: modified Gram-Schmidt run twice on
    Gaussian rows, a row that collapses (probability 0) drawn again. The Rust draws the same."""
    rng = SplitMix64(seed)
    rows: list[list[float]] = []
    while len(rows) < d:
        v = [rng.standard_normal() for _ in range(d)]
        for _ in range(2):
            for r in rows:
                proj = dot(r, v)
                v = [x - proj * y for x, y in zip(v, r, strict=True)]
        length = math.sqrt(dot(v, v))
        if length > 1e-6:
            rows.append([x / length for x in v])
    return rows


@dataclass
class PreparedQuery:
    """A query prepared for estimation: its normalized, rotated (and here unquantized) vector, and
    its distance to the centroid."""

    q: list[float]
    norm: float


class Codes:
    """One bit per coordinate, and the two numbers each vector keeps."""

    def __init__(
        self, points: Sequence[Sequence[float]], rotation: list[list[float]] | None, corrected: bool
    ) -> None:
        pts = copy_points(points)
        if not pts:
            raise ValueError("RaBitQ needs at least one point")
        self.dim = len(pts[0])
        self.centroid = [0.0] * self.dim
        for p in pts:
            for j, x in enumerate(p):
                self.centroid[j] += x
        self.centroid = [c / len(pts) for c in self.centroid]
        self.rotation = rotation
        self.corrected = corrected
        self.bits: list[list[int]] = []  # bit j is 1 iff rotated coordinate j is >= 0
        self.norms: list[float] = []  # ||o_r - c||
        self.dots: list[float] = []  # <o_bar, o>; 1 for a point at the centroid, never read
        for p in pts:
            y, norm = self.normalize(p)
            self.bits.append([1 if v >= 0 else 0 for v in y])
            self.norms.append(norm)
            ob_o = 0.0
            for v in y:
                ob_o += abs(v)
            self.dots.append(ob_o / math.sqrt(self.dim) if norm > 0 else 1.0)

    def normalize(self, v: Sequence[float]) -> tuple[list[float], float]:
        """`(P^T (v - c) / ||v - c||, ||v - c||)`; the zero vector and 0 when `v` is `c`."""
        diff = [x - c for x, c in zip(v, self.centroid, strict=True)]
        norm = math.sqrt(dot(diff, diff))
        if norm == 0:
            return [0.0] * self.dim, 0.0
        unit = [x / norm for x in diff]
        if self.rotation is None:
            return unit, norm
        return [dot(row, unit) for row in self.rotation], norm

    def quantize_query(self, q_rotated: list[float]) -> list[float]:
        """Algorithm 2, line 2, as a black box: here it returns the query unchanged. The Rust
        quantizes it to 4 bits per coordinate (Gao-Long §3.3.1) and estimates by popcount."""
        return q_rotated

    def prepare(self, q: Sequence[float]) -> PreparedQuery:
        """Algorithm 2, lines 1-2: normalize and rotate the query, then quantize it."""
        check_query([self.centroid], q)
        rotated, norm = self.normalize(q)
        return PreparedQuery(self.quantize_query(rotated), norm)

    def estimate_inner(self, query: PreparedQuery, i: int) -> float:
        """`<x_bar, q'>`, divided by `<o_bar, o>` when corrected (Eq. 13)."""
        x_dot_q = 0.0
        for b, v in zip(self.bits[i], query.q, strict=True):
            x_dot_q += v if b else -v
        x_dot_q /= math.sqrt(self.dim)
        return x_dot_q / self.dots[i] if self.corrected else x_dot_q

    def estimate_sq_dist(self, query: PreparedQuery, i: int) -> float:
        """Eq. 2, with the estimated inner product."""
        o, q = self.norms[i], query.norm
        return o * o + q * q - 2 * o * q * self.estimate_inner(query, i)


class RaBitQ(Codes):
    """One-bit codes with RaBitQ's rotation and unbiased estimator."""

    def __init__(self, points: Sequence[Sequence[float]], seed: int) -> None:
        dim = len(points[0]) if points else 0
        super().__init__(points, random_orthogonal(dim, seed) if dim else None, corrected=True)


class SignCodes(Codes):
    """One-bit codes with no rotation and no correction: the biased baseline."""

    def __init__(self, points: Sequence[Sequence[float]]) -> None:
        super().__init__(points, None, corrected=False)


class Estimator(Protocol):
    norms: list[float]

    def prepare(self, q: Sequence[float]) -> PreparedQuery: ...

    def estimate_sq_dist(self, query: PreparedQuery, i: int) -> float: ...


def search_quantized(h: HNSW, q: Sequence[float], k: int, ef: int, codes: Estimator) -> Found:
    """The `min(k, n)` nearest of the candidates the HNSW walk keeps when it ranks nodes by the
    estimated distance: a cheap filter, then an exact check of every candidate in the final `ef`.
    """
    check_query(h.points, q)
    if len(codes.norms) != len(h.points):
        encoded, graph = len(codes.norms), len(h.points)
        raise ValueError(f"the codes encode {encoded} points but the graph has {graph}")
    if k < 0:
        raise ValueError(f"k must be at least 0, got {k}")
    if k == 0:
        return []
    query = codes.prepare(q)
    walked = h.search_by(lambda i: codes.estimate_sq_dist(query, i), max(ef, k))
    return scan.k_nearest_among(h.points, [i for _, i in walked], q, k)
