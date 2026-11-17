# SPDX-License-Identifier: Apache-2.0
"""The Geometry chapter: finding what is near, from the plane to hundreds of dimensions.

The modules follow the chapter's order:

- `scan` -- checking every point: the specification of nearest-neighbor and box queries, and
  the oracle every other structure is tested against;
- `orientation` -- which side of a line, exactly;
- `hull` -- the convex hull, by Andrew's monotone chain;
- `range_tree` -- every key in a range, in 1D and 2D;
- `kdtree` -- the k-d tree, its range query and best-first nearest neighbors;
- `projection`, `lsh` -- random projection, and locality-sensitive hashing over any family
  (SimHash, p-stable);
- `hnsw` -- the graph index, layered or flat;
- `rabitq` -- one-bit codes with an unbiased estimate, as a filter before an exact check.

Points are `list[float]`; a point's id, its number in the input counting from 0, is a plain
`int`; squared distances are returned with ids as `(distance, id)`, nearest first. Invalid input
raises `ValueError`. Every index copies the points it is built from. `point` holds the shared
arithmetic (`sq_dist`, `dot`, `normalized`).

The classes are exported by name. The operations that are functions are reached through their
modules, which the package exports as modules: `scan.nearest`, `scan.k_nearest`, `scan.in_box`,
`orientation.orient2d`. The randomized structures draw from `_rng.SplitMix64`, the Rust's
generator, so a seed draws the same levels, hyperplanes and rotations in both languages.
"""

from __future__ import annotations

from . import hull, orientation, point, scan
from .hnsw import HNSW
from .kdtree import KDTree
from .lsh import LSHIndex, PStable, SimHash
from .projection import GaussianProjection
from .rabitq import RaBitQ, SignCodes
from .range_tree import RangeTree1D, RangeTree2D

__all__ = [
    "HNSW",
    "GaussianProjection",
    "KDTree",
    "LSHIndex",
    "PStable",
    "RaBitQ",
    "RangeTree1D",
    "RangeTree2D",
    "SignCodes",
    "SimHash",
    "hull",
    "orientation",
    "point",
    "scan",
]
