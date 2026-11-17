# SPDX-License-Identifier: Apache-2.0
"""Locality-sensitive hashing: hash every point into several tables, and answer a query by
re-ranking, exactly, the points that share its key in some table (MMDS Ch. 3: k hash values make
one key, L tables). Any hash family fits: the answer is the nearest candidate, and if the true
nearest point is a candidate, it is the answer. The chapter's two families, drawn from the shared
generator in the Rust's order: **SimHash** (Charikar 2002 §3), a bit per random hyperplane, which
side a point lies on; and **p-stable LSH** (Datar et al. 2004 §3.2), cells of width `w` along a
random direction. The index keeps the Lean `LSH.Valid`, box invariant 1, `is_in_its_bucket`, and
`LSH.WellFormed`, not in the box, `is_one_bucket_per_key` and `is_each_point_once_per_table`. An
answer keeps box invariant 2, `is_measured_exactly`. Seeded statistical tests hold the collision
probabilities.
The box's K, the hash values a key is made of, is `bits` in `SimHash` and `k` in `PStable`; its L
is `tables` in both.

The Rust differs here: only in flat arrays; the same seed gives the same hyperplanes.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/LSH/`: `valid_build`,
`measuredExactly_nearest`, `measuredExactly_kNearest`, `nearest_eq_lshQuery`,
`nearest_eq_scanNearest`, `lshQuery_le_candidates`, `lshQuery_eq_scanNearest`, `simBit_eq_orient`,
`pStableKey_eq`.
"""

from __future__ import annotations

import math
from collections import Counter
from collections.abc import Hashable, Sequence
from typing import Protocol

from . import scan
from ._rng import SplitMix64
from .point import check_query, copy_points, dot, sq_dist


class HashFamily(Protocol):
    """`tables` hash functions over points of dimension `dim`."""

    @property
    def dim(self) -> int: ...

    @property
    def tables(self) -> int: ...

    def key(self, table: int, v: Sequence[float]) -> Hashable: ...


def sim_bit(r: Sequence[float], p: Sequence[float]) -> bool:
    """Which side of the hyperplane with normal `r` the point `p` lies on; on it counts as 1."""
    return dot(r, p) >= 0.0


class SimHash:
    """`tables` keys of `bits` hyperplane bits each."""

    def __init__(self, dim: int, bits: int, tables: int, seed: int) -> None:
        if dim < 1 or not 1 <= bits <= 64:
            raise ValueError(f"SimHash needs dim >= 1 and 1 <= bits <= 64, got {dim} and {bits}")
        if tables < 1:
            raise ValueError(f"LSH needs at least one table, got tables = {tables}")
        self.dim = dim
        self.tables = tables
        rng = SplitMix64(seed)
        self.planes = [
            [[rng.standard_normal() for _ in range(dim)] for _ in range(bits)]
            for _ in range(tables)
        ]

    def key(self, table: int, v: Sequence[float]) -> tuple[bool, ...]:
        return tuple(sim_bit(r, v) for r in self.planes[table])


def p_stable_cell(a: Sequence[float], b: float, w: float, p: Sequence[float]) -> int:
    """The cell of `p` along direction `a`, with offset `b` and width `w`."""
    return math.floor((dot(a, p) + b) / w)


class PStable:
    """`tables` keys of `k` p-stable cells each: Gaussian directions, offsets uniform in [0, w)."""

    def __init__(self, dim: int, k: int, tables: int, w: float, seed: int) -> None:
        if dim < 1 or k < 1:
            raise ValueError(f"p-stable LSH needs dim >= 1 and k >= 1, got {dim} and {k}")
        if tables < 1:
            raise ValueError(f"LSH needs at least one table, got tables = {tables}")
        if not (w > 0 and math.isfinite(w)):
            raise ValueError(f"p-stable LSH needs a finite cell width w > 0, got {w}")
        self.dim = dim
        self.tables = tables
        self.w = w
        rng = SplitMix64(seed)
        self.directions = [
            [[rng.standard_normal() for _ in range(dim)] for _ in range(k)] for _ in range(tables)
        ]
        self.offsets = [[rng.next_f64() * w for _ in range(k)] for _ in range(tables)]

    def key(self, table: int, v: Sequence[float]) -> tuple[int, ...]:
        return tuple(
            p_stable_cell(a, b, self.w, v)
            for a, b in zip(self.directions[table], self.offsets[table], strict=True)
        )


class LSHIndex:
    """Every point hashed into every table; a query re-ranks its candidates exactly."""

    def __init__(self, points: Sequence[Sequence[float]], family: HashFamily) -> None:
        self.points = copy_points(points)
        if self.points and len(self.points[0]) != family.dim:
            dim = len(self.points[0])
            raise ValueError(f"the points have dimension {dim} but the family hashes {family.dim}")
        self.family = family
        self.buckets: list[dict[Hashable, list[int]]] = []
        for t in range(family.tables):
            table: dict[Hashable, list[int]] = {}
            for i, p in enumerate(self.points):
                table.setdefault(family.key(t, p), []).append(i)
            self.buckets.append(table)

    def candidates(self, q: Sequence[float]) -> list[int]:
        """The ids, ascending and each once, of the points sharing q's key in some table."""
        check_query(self.points, q)
        found: set[int] = set()
        for t, table in enumerate(self.buckets):
            found.update(table.get(self.family.key(t, q), []))
        return sorted(found)

    def k_nearest(self, q: Sequence[float], k: int) -> list[tuple[float, int]]:
        """The `min(k, candidates)` nearest candidates, ranked exactly, as `scan.k_nearest`."""
        return scan.k_nearest_among(self.points, self.candidates(q), q, k)

    def nearest(self, q: Sequence[float]) -> int | None:
        """The nearest candidate, if any."""
        found = self.k_nearest(q, 1)
        return found[0][1] if found else None

    def is_in_its_bucket(self) -> bool:
        """Box invariant 1: every stored point sits in the bucket its key names, in every table.
        There is one bucket map per table; in each, every stored id names a point whose key is
        its bucket's, and every point is found in the bucket its key names. The Lean
        `InItsBucket`."""
        if len(self.buckets) != self.family.tables:
            return False
        n = len(self.points)
        for t, table in enumerate(self.buckets):
            for key, ids in table.items():
                if any(not 0 <= i < n or self.family.key(t, self.points[i]) != key for i in ids):
                    return False
            for i, p in enumerate(self.points):
                if i not in table.get(self.family.key(t, p), []):
                    return False
        return True

    def is_one_bucket_per_key(self) -> bool:
        """Not in the box: in each table, every key has one bucket, and no bucket is empty.
        A dict holds one bucket per key by its type, and the build never stores an empty one, so
        this checks the second half only. The Lean `OneBucketPerKey`."""
        return all(len(ids) > 0 for table in self.buckets for ids in table.values())

    def is_each_point_once_per_table(self) -> bool:
        """Not in the box: in each table, every point is stored exactly once (the bucket its
        key names holds it, by box invariant 1, and no other bucket does). The Lean
        `EachPointOncePerTable`."""
        for table in self.buckets:
            stored = Counter(i for ids in table.values() for i in ids)
            if any(stored[i] != 1 for i in range(len(self.points))):
                return False
        return True

    def check_valid(self) -> str | None:
        """The first piece of the Lean `LSH.Valid` or `LSH.WellFormed` the index breaks, or
        `None`."""
        if not self.is_in_its_bucket():
            return "invariant 1 (in_its_bucket)"
        if not self.is_one_bucket_per_key():
            return "not in the box (one_bucket_per_key)"
        if not self.is_each_point_once_per_table():
            return "not in the box (each_point_once_per_table)"
        return None

    def is_valid(self) -> bool:
        """The Lean `LSH.Valid` and `LSH.WellFormed`: `is_in_its_bucket`,
        `is_one_bucket_per_key` and `is_each_point_once_per_table`."""
        return self.check_valid() is None


def is_measured_exactly(index: LSHIndex, q: Sequence[float], k: int, result: list[int]) -> bool:
    """Box invariant 2: a shared bucket only makes a point a candidate: every candidate is measured
    exactly before one is reported. Every candidate names a stored point, and the answer holds
    min(k, candidates) of them, each once, none farther from q than a candidate left out. A query
    not of the points' dimension (the family's, when there are no points), or with a non-finite
    coordinate, gives False, and so does a candidate past the points, which cannot be measured.
    The Lean `MeasuredExactly`, on the answer (`Answer`)."""
    dim = len(index.points[0]) if index.points else index.family.dim
    if len(q) != dim or not all(math.isfinite(x) for x in q):
        return False
    # gathered here, not by index.candidates, so a broken candidates() cannot vouch for itself
    found: set[int] = set()
    for t, table in enumerate(index.buckets[: index.family.tables]):
        found.update(table.get(index.family.key(t, q), []))

    if any(not 0 <= c < len(index.points) for c in found):
        return False

    def sq_dist_of(i: int) -> float:
        return sq_dist(index.points[i], q)

    if len(set(result)) != len(result) or len(result) != min(k, len(found)):
        return False
    if not set(result) <= found:
        return False
    left_out = found - set(result)
    return all(sq_dist_of(r) <= sq_dist_of(c) for r in result for c in left_out)
