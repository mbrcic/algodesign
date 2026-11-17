# SPDX-License-Identifier: Apache-2.0
"""Which side of a line? The sign of one determinant, exactly.

`orient2d(a, b, c)` is `+1` if walking a -> b -> c turns left (counterclockwise), `-1` if it turns
right, and `0` if the three points are collinear: the sign of `(b - a) x (c - a)` (dBCKO §1.1;
O'Rourke §1.3).

**The Python and the Rust compute the exact sign of the same determinant, by different
arithmetic.** Both first try the plain floating-point determinant, and trust it only when it is
farther from zero than Shewchuk's error bound `ccwerrboundA` allows rounding to move it (Shewchuk
1997 §4). When it is not, the Rust continues with Shewchuk's adaptive expansion arithmetic
(`rust/crates/algodesign/src/geometry/orientation.rs`), while this module recomputes the
determinant in exact rationals, `fractions.Fraction`. The Rust is built for speed, this code for a
first reading; the contract, the exact sign, is the same. One difference follows from the
arithmetic: rationals neither overflow nor underflow, so this sign is exact for every finite
input. The Rust's floats can: where a step could overflow or underflow, the Rust answers NaN,
"cannot decide", never a wrong sign. Every input whose coordinates are zero or of magnitude in
[2^-400, 2^500] is always decided. The Python returns the sign itself; the Rust returns a float
with that sign.

`orient2d_fast` is the plain determinant alone, for the chapter's failure demonstration (Kettner
et al. 2008): near a line it can call a left turn a right turn.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/Orientation.lean`:
`orient_swap`, `orient_cycle`, `orient_self_left`, `orient_eq_zero_iff`.
"""

from __future__ import annotations

import math
from fractions import Fraction

Point2 = tuple[float, float]

EPSILON = 2.0**-53
"""Half an ulp of 1: the largest relative error of one rounded operation."""

CCW_ERR_BOUND_A = (3.0 + 16.0 * EPSILON) * EPSILON
"""Shewchuk's `ccwerrboundA`: the plain determinant's sign is right when its size exceeds this
times `|detleft| + |detright|`."""


def orient2d(a: Point2, b: Point2, c: Point2) -> int:
    """The exact sign of `(b - a) x (c - a)`: `+1` left turn, `-1` right turn, `0` collinear."""
    for x in (*a, *b, *c):
        if not math.isfinite(x):
            raise ValueError("orient2d needs finite coordinates")
    # The fast path: Shewchuk's form of the determinant, `(a - c) x (b - c)`, the same value.
    detleft = (a[0] - c[0]) * (b[1] - c[1])
    detright = (a[1] - c[1]) * (b[0] - c[0])
    det = detleft - detright
    bound = CCW_ERR_BOUND_A * (abs(detleft) + abs(detright))
    # Shewchuk's bound assumes no overflow and no underflow. So the float answer is trusted only
    # when everything is finite, the products are far above the underflow range, and the
    # determinant clears the bound with a margin that covers any underflowed low bits.
    if math.isfinite(det) and bound >= 2.0**-900 and abs(det) > bound * (1.0 + 2.0**-40):
        return 1 if det > 0 else -1
    return exact_sign(a, b, c)


def exact_sign(a: Point2, b: Point2, c: Point2) -> int:
    """The sign of `(b - a) x (c - a)` in exact rationals: each coordinate becomes a `Fraction`
    before any subtraction, so nothing is rounded."""
    ax, ay, bx, by, cx, cy = (Fraction(v) for v in (*a, *b, *c))
    det = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    return (det > 0) - (det < 0)


def orient2d_fast(a: Point2, b: Point2, c: Point2) -> float:
    """The plain floating-point determinant, whose sign is not guaranteed near a line."""
    return (a[0] - c[0]) * (b[1] - c[1]) - (a[1] - c[1]) * (b[0] - c[0])
