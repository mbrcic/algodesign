# SPDX-License-Identifier: Apache-2.0
"""The orientation test: the exact sign of one determinant, on every finite input.

Mirrors the Rust's `orientation::tests` and the Lean's `Orientation.lean`. The oracle is the
determinant computed in `Fraction`, which is exact; the plain float determinant is shown failing
on Kettner et al.'s grid, which is the reason the filter-then-exact discipline exists.
"""

from __future__ import annotations

import math
from fractions import Fraction

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.geometry.orientation import orient2d, orient2d_fast

Pt = tuple[float, float]


def exact_sign(a: Pt, b: Pt, c: Pt) -> int:
    ax, ay, bx, by, cx, cy = (Fraction(v) for v in (*a, *b, *c))
    det = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax)
    return (det > 0) - (det < 0)


def sign(x: float) -> int:
    return (x > 0) - (x < 0)


small = st.integers(-8, 8).map(float)
small_pt = st.tuples(small, small)


def test_lean_examples() -> None:
    # Lean: AlgoDesignTests/Geometry.lean, left, right, collinear, all equal.
    assert orient2d((0.0, 0.0), (1.0, 0.0), (0.0, 1.0)) == 1
    assert orient2d((0.0, 0.0), (1.0, 0.0), (0.0, -1.0)) == -1
    assert orient2d((0.0, 0.0), (1.0, 1.0), (3.0, 3.0)) == 0
    assert orient2d((2.0, 2.0), (2.0, 2.0), (2.0, 2.0)) == 0


@given(small_pt, small_pt, small_pt)
def test_the_lean_identities_on_integers(a: Pt, b: Pt, c: Pt) -> None:
    # Lean: orient_swap, orient_cycle, orient_self_left, and orient_eq_zero_iff (zero exactly
    # when the integer determinant is zero).
    s = orient2d(a, b, c)
    assert orient2d(b, a, c) == -s
    assert orient2d(b, c, a) == s
    assert orient2d(a, a, c) == 0
    det = (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])
    assert (s == 0) == (det == 0)


def coord() -> st.SearchStrategy[float]:
    """`m * 2**e` with |m| < 2**20 and |e| <= 60, as the Rust's strategy."""
    return st.builds(lambda m, e: m * 2.0**e, st.integers(-(2**20), 2**20), st.integers(-60, 60))


@given(coord(), coord(), coord(), coord(), st.integers(0, 2**20), st.integers(-3, 3))
def test_the_sign_is_exact_near_a_line(
    ax: float, ay: float, bx: float, by: float, t: int, nudge: int
) -> None:
    # c on the line through a and b (rounded), then nudged by a few ulps: the cases where the
    # float determinant is least trustworthy.
    f = t / 2**20
    cx = ax + f * (bx - ax)
    cy = ay + f * (by - ay)
    for _ in range(abs(nudge)):
        cy = math.nextafter(cy, math.inf if nudge > 0 else -math.inf)
    a, b, c = (ax, ay), (bx, by), (cx, cy)
    assert orient2d(a, b, c) == exact_sign(a, b, c)


def kettner_grid(scale: float) -> list[tuple[Pt, Pt, Pt]]:
    """Kettner et al. 2008, Fig. 1: p on a 64 x 64 grid of ulp steps from (0.5, 0.5), q = (12, 12),
    r = (24, 24), all times `scale`, in the three cyclic orders of the arguments."""
    q, r = (12.0 * scale, 12.0 * scale), (24.0 * scale, 24.0 * scale)
    u = 2.0**-53
    triples = []
    for i in range(64):
        for j in range(64):
            p = ((0.5 + i * u) * scale, (0.5 + j * u) * scale)
            triples += [(p, q, r), (q, r, p), (r, p, q)]
    return triples


def test_the_fast_determinant_alone_gets_signs_wrong() -> None:
    # The plain determinant must give some triple the *opposite* nonzero sign, or the
    # demonstration (and the test of the filter) is empty; orient2d must be right everywhere.
    flipped = 0
    for a, b, c in kettner_grid(1.0):
        exact = exact_sign(a, b, c)
        if sign(orient2d_fast(a, b, c)) == -exact != 0:
            flipped += 1
        assert orient2d(a, b, c) == exact, (a, b, c)
    assert flipped > 0


def test_the_sign_is_exact_where_the_products_underflow() -> None:
    # The same grid scaled toward the bottom of the range. At 2**-515 the products sit at the
    # edge of the normal range and the plain determinant still gives wrong signs; at 2**-540 they
    # are subnormals. Rounding there is not relative, so Shewchuk's bound does not hold and the
    # filter must not trust it.
    for scale in (2.0**-515, 2.0**-540):
        for a, b, c in kettner_grid(scale):
            assert orient2d(a, b, c) == exact_sign(a, b, c), (scale, a, b, c)


@pytest.mark.parametrize(
    ("a", "b", "c"),
    [
        # Products just below the normal range, where the plain determinant has the wrong nonzero
        # sign and clears the bound: found by a randomized search, it is what the
        # filter's underflow guard is for.
        (
            (2.0577058592273212e-156, 2.0577058592273258e-156),
            (1.4873327929928048e-155, 1.4873327929928052e-155),
            (4.595529367609762e-155, 4.595529367609762e-155),
        ),
        (
            (1.4399480500089076e-155, 1.4399480500089076e-155),
            (8.17167480433404e-157, 8.171674804334068e-157),
            (6.102081621207356e-155, 6.102081621207352e-155),
        ),
        ((0.0, 0.0), (1e-170, 0.0), (0.0, 1e-170)),  # the products underflow
        ((0.0, 0.0), (3e-320, 0.0), (0.0, 5e-324)),  # subnormal coordinates
        ((1e300, 1e300), (1e300, 2e300), (0.0, 0.0)),  # the products overflow
        ((-1.7e308, 0.0), (1.7e308, 1e-300), (0.0, 1.7e308)),
        ((1e300, -1e300), (-1e300, 1e300), (5e299, -5e299)),  # collinear, huge
    ],
)
def test_the_sign_is_exact_at_the_ends_of_the_range(a: Pt, b: Pt, c: Pt) -> None:
    # Where the Rust's guarantee ends (no overflow or underflow), the Python's does not: its exact
    # stage is rational arithmetic, which neither overflows nor underflows.
    assert orient2d(a, b, c) == exact_sign(a, b, c)
    assert orient2d(b, a, c) == -exact_sign(a, b, c)


def test_a_non_finite_coordinate_is_rejected() -> None:
    with pytest.raises(ValueError, match="finite"):
        orient2d((0.0, 0.0), (1.0, math.inf), (0.0, 1.0))
