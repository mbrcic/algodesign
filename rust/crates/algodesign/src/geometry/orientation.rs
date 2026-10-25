//! Which side of a line? The sign of `(b − a) × (c − a)`, exactly (dBCKO §1.1; O'Rourke §1.3):
//! positive if `a → b → c` turns left (counterclockwise), negative if it turns right, zero if the
//! three points are collinear.
//!
//! A transcription of Shewchuk's adaptive `orient2d` (Shewchuk 1997 §4; `predicates.c`, public
//! domain): a floating-point filter whose error bound decides when the fast answer can be
//! trusted, then exact expansion arithmetic only when it cannot. It is exact for every coordinate
//! zero or between `2^-400` (about `3.9e-121`) and `2^500` (about `3.3e150`); outside that range
//! it answers the exact sign or NaN, "cannot decide", never a wrong sign. Both languages compute
//! the exact sign of the same determinant: the Rust with Shewchuk's filter and expansions, which
//! decide most inputs at the speed of plain floating point, the Python with exact rationals, which
//! read as the definition. Lean: `Orientation.lean`, over any ordered commutative ring.
//!
//! The error bounds assume IEEE double precision with round-to-nearest-even, no fused multiply-add
//! (Rust never contracts `a * b + c`, and nothing here calls `mul_add`) and no overflow or
//! underflow, which the range guard in [`orient2d`] keeps out. Each private function names the
//! `predicates.c` macro or routine it transcribes.

/// `epsilon` of `exactinit()`: half an ulp of 1, `2^-53`.
const EPSILON: f64 = f64::EPSILON / 2.0;
/// `splitter` of `exactinit()`: `2^27 + 1`, which splits a double into two 26-bit halves.
const SPLITTER: f64 = 134_217_729.0;
/// `resulterrbound` of `exactinit()`.
const RESULT_ERR_BOUND: f64 = (3.0 + 8.0 * EPSILON) * EPSILON;
/// `ccwerrboundA` of `exactinit()`.
const CCW_ERR_BOUND_A: f64 = (3.0 + 16.0 * EPSILON) * EPSILON;
/// `ccwerrboundB` of `exactinit()`.
const CCW_ERR_BOUND_B: f64 = (2.0 + 12.0 * EPSILON) * EPSILON;
/// `ccwerrboundC` of `exactinit()`.
const CCW_ERR_BOUND_C: f64 = (9.0 + 64.0 * EPSILON) * EPSILON * EPSILON;

/// `2^k`, by repeated doubling or halving, each step exact in the normal range.
const fn pow2(k: i32) -> f64 {
    let mut x = 1.0;
    let mut i = 0;
    while i < k {
        x *= 2.0;
        i += 1;
    }
    while i > k {
        x *= 0.5;
        i -= 1;
    }
    x
}

/// The smallest magnitude of a nonzero coordinate inside the range, `2^-400`.
const RANGE_MIN: f64 = pow2(-400);
/// The largest magnitude of a coordinate inside the range, `2^500`.
const RANGE_MAX: f64 = pow2(500);
/// The smallest magnitude either product of the filter may have for its error bound to be
/// trusted, `2^-960`.
const FILTER_MIN_PRODUCT: f64 = pow2(-960);
/// The largest sum of the filter's products' magnitudes for which it is trusted, `2^1020`.
const FILTER_MAX_SUM: f64 = pow2(1020);

/// The sign of `(b − a) × (c − a)`, exactly, or NaN when it cannot be decided: positive if
/// `a → b → c` turns left, negative if it turns right, zero if collinear (Shewchuk's
/// `orient2d(pa, pb, pc)`, which computes the same determinant as `(a − c) × (b − c)`). Inside the
/// range it is never NaN and is bit for bit Shewchuk's result; outside it the range guard's checks
/// (1, the products' signs; 2, the filter's bounds; 3, the later stages' range) answer NaN wherever
/// an operation could under- or overflow. The range is where the filter can be trusted: both
/// products at least `2^-960` in magnitude, so no bit of an exact product falls below the
/// smallest subnormal `2^-1074`, and their magnitudes' sum at most `2^1020`, so nothing
/// overflows. Lean: `orient_swap`, `orient_cycle`, `orient_self_left`, `orient_eq_zero_iff`.
#[must_use]
pub fn orient2d(a: [f64; 2], b: [f64; 2], c: [f64; 2]) -> f64 {
    let (acx, bcy) = (a[0] - c[0], b[1] - c[1]);
    let (acy, bcx) = (a[1] - c[1], b[0] - c[0]);
    let detleft = acx * bcy;
    let detright = acy * bcx;
    let det = detleft - detright;
    // `smaller` is the lesser magnitude of the two products, for check 2. A zero `detright`
    // reaches check 2 rather than returning at once, so that check 1 is paid for only there.
    let (detsum, smaller) = if detleft > 0.0 {
        if detright < 0.0 {
            return det;
        }
        let smaller = if detleft < detright {
            detleft
        } else {
            detright
        };
        (detleft + detright, smaller)
    } else if detleft < 0.0 {
        if detright > 0.0 {
            return det;
        }
        let smaller = if detleft > detright {
            -detleft
        } else {
            -detright
        };
        (-detleft - detright, smaller)
    } else {
        // Check 1.
        return if underflowed(detleft, acx, bcy) || underflowed(detright, acy, bcx) {
            f64::NAN
        } else {
            det
        };
    };
    // Check 2; false for NaN too.
    if !(smaller >= FILTER_MIN_PRODUCT && detsum <= FILTER_MAX_SUM) {
        return outside_the_filter(det, detright, acy, bcx);
    }
    let errbound = CCW_ERR_BOUND_A * detsum;
    if det >= errbound || -det >= errbound {
        return det;
    }
    orient2d_adapt(a, b, c, detsum)
}

/// Check 1 of [`orient2d`]: `p`, the rounded product of `x` and `y`, is zero although neither
/// factor is, so it underflowed.
fn underflowed(p: f64, x: f64, y: f64) -> bool {
    p == 0.0 && x != 0.0 && y != 0.0
}

/// Where check 2 of [`orient2d`] fails: `detright` zero because a factor is (`detleft` is not
/// zero here), so the sign is `detleft`'s, Shewchuk's early return; otherwise a refusal.
#[cold]
fn outside_the_filter(det: f64, detright: f64, acy: f64, bcx: f64) -> f64 {
    if detright == 0.0 && !underflowed(detright, acy, bcx) {
        det
    } else {
        f64::NAN
    }
}

/// Check 3 of [`orient2d`]: both coordinates zero or of magnitude in `[RANGE_MIN, RANGE_MAX]`
/// (`false` for NaN and infinities).
fn in_range(p: [f64; 2]) -> bool {
    let ok = |x: f64| {
        let m = x.abs();
        (m == 0.0) | (RANGE_MIN..=RANGE_MAX).contains(&m)
    };
    ok(p[0]) & ok(p[1])
}

/// The plain floating-point determinant, with no guarantee about its sign (`orient2dfast`). It is
/// here for the chapter's failure demonstration (Kettner et al. 2008): near a line it can call a
/// left turn right.
#[must_use]
pub fn orient2d_fast(a: [f64; 2], b: [f64; 2], c: [f64; 2]) -> f64 {
    (a[0] - c[0]) * (b[1] - c[1]) - (a[1] - c[1]) * (b[0] - c[0])
}

/// `orient2dadapt`: the filter's answer was not trusted, so refine it in stages.
fn orient2d_adapt(pa: [f64; 2], pb: [f64; 2], pc: [f64; 2], detsum: f64) -> f64 {
    let acx = pa[0] - pc[0];
    let bcx = pb[0] - pc[0];
    let acy = pa[1] - pc[1];
    let bcy = pb[1] - pc[1];

    let (detleft, detlefttail) = two_product(acx, bcy);
    let (detright, detrighttail) = two_product(acy, bcx);
    let b = two_two_diff(detleft, detlefttail, detright, detrighttail);

    let mut det = estimate(&b);
    let errbound = CCW_ERR_BOUND_B * detsum;
    if det >= errbound || -det >= errbound {
        return det;
    }

    let acxtail = two_diff_tail(pa[0], pc[0], acx);
    let bcxtail = two_diff_tail(pb[0], pc[0], bcx);
    let acytail = two_diff_tail(pa[1], pc[1], acy);
    let bcytail = two_diff_tail(pb[1], pc[1], bcy);
    if acxtail == 0.0 && acytail == 0.0 && bcxtail == 0.0 && bcytail == 0.0 {
        return det;
    }
    // Check 3 of `orient2d`, before the stages that multiply the tails.
    if !(in_range(pa) & in_range(pb) & in_range(pc)) {
        return f64::NAN;
    }

    let errbound = CCW_ERR_BOUND_C * detsum + RESULT_ERR_BOUND * det.abs();
    det += (acx * bcytail + bcy * acxtail) - (acy * bcxtail + bcx * acytail);
    if det >= errbound || -det >= errbound {
        return det;
    }

    let (s1, s0) = two_product(acxtail, bcy);
    let (t1, t0) = two_product(acytail, bcx);
    let u = two_two_diff(s1, s0, t1, t0);
    let mut c1 = [0.0; 8];
    let c1len = fast_expansion_sum_zeroelim(&b, &u, &mut c1);

    let (s1, s0) = two_product(acx, bcytail);
    let (t1, t0) = two_product(acy, bcxtail);
    let u = two_two_diff(s1, s0, t1, t0);
    let mut c2 = [0.0; 12];
    let c2len = fast_expansion_sum_zeroelim(&c1[..c1len], &u, &mut c2);

    let (s1, s0) = two_product(acxtail, bcytail);
    let (t1, t0) = two_product(acytail, bcxtail);
    let u = two_two_diff(s1, s0, t1, t0);
    let mut d = [0.0; 16];
    let dlen = fast_expansion_sum_zeroelim(&c2[..c2len], &u, &mut d);

    d[dlen - 1]
}

/// `Fast_Two_Sum`: `x + y = a + b` exactly, for `|a| ≥ |b|`.
fn fast_two_sum(a: f64, b: f64) -> (f64, f64) {
    let x = a + b;
    let bvirt = x - a;
    (x, b - bvirt)
}

/// `Two_Sum`: `x + y = a + b` exactly.
fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let x = a + b;
    let bvirt = x - a;
    let avirt = x - bvirt;
    let bround = b - bvirt;
    let around = a - avirt;
    (x, around + bround)
}

/// `Two_Diff_Tail`: the roundoff `y` of `x = fl(a − b)`, so `x + y = a − b` exactly.
fn two_diff_tail(a: f64, b: f64, x: f64) -> f64 {
    let bvirt = a - x;
    let avirt = x + bvirt;
    let bround = bvirt - b;
    let around = a - avirt;
    around + bround
}

/// `Two_Diff`: `x + y = a − b` exactly.
fn two_diff(a: f64, b: f64) -> (f64, f64) {
    let x = a - b;
    (x, two_diff_tail(a, b, x))
}

/// `Split`: `a = hi + lo`, each with at most 26 significant bits.
fn split(a: f64) -> (f64, f64) {
    let c = SPLITTER * a;
    let abig = c - a;
    let hi = c - abig;
    (hi, a - hi)
}

/// `Two_Product`: `x + y = a·b` exactly.
fn two_product(a: f64, b: f64) -> (f64, f64) {
    let x = a * b;
    let (ahi, alo) = split(a);
    let (bhi, blo) = split(b);
    let err1 = x - (ahi * bhi);
    let err2 = err1 - (alo * bhi);
    let err3 = err2 - (ahi * blo);
    (x, (alo * blo) - err3)
}

/// `Two_One_Diff`: `(a1 + a0) − b` as a three-component expansion `(x2, x1, x0)`.
fn two_one_diff(a1: f64, a0: f64, b: f64) -> (f64, f64, f64) {
    let (i, x0) = two_diff(a0, b);
    let (x2, x1) = two_sum(a1, i);
    (x2, x1, x0)
}

/// `Two_Two_Diff`: `(a1 + a0) − (b1 + b0)` as a four-component expansion, least significant
/// first (`[x0, x1, x2, x3]`, the order `predicates.c` stores `B[0..4]` in).
fn two_two_diff(a1: f64, a0: f64, b1: f64, b0: f64) -> [f64; 4] {
    let (j, zero, x0) = two_one_diff(a1, a0, b0);
    let (x3, x2, x1) = two_one_diff(j, zero, b1);
    [x0, x1, x2, x3]
}

/// `estimate`: the sum of an expansion's components, an approximation of its value.
fn estimate(e: &[f64]) -> f64 {
    e.iter().sum()
}

/// `fast_expansion_sum_zeroelim`: `h = e + f` as a nonoverlapping expansion with zero components
/// removed; returns its length. `e` and `f` are nonempty expansions, least significant first.
/// `h` has room for `e.len() + f.len()` components.
fn fast_expansion_sum_zeroelim(e: &[f64], f: &[f64], h: &mut [f64]) -> usize {
    // `predicates.c` reads `e[++eindex]` one past the end and never uses that value; here the read
    // past the end yields 0.0, which is equally unused.
    let at = |x: &[f64], i: usize| x.get(i).copied().unwrap_or(0.0);
    let (elen, flen) = (e.len(), f.len());
    let (mut enow, mut fnow) = (e[0], f[0]);
    let (mut eindex, mut findex) = (0, 0);
    let mut q;
    if (fnow > enow) == (fnow > -enow) {
        q = enow;
        eindex += 1;
        enow = at(e, eindex);
    } else {
        q = fnow;
        findex += 1;
        fnow = at(f, findex);
    }
    let mut hindex = 0;
    if eindex < elen && findex < flen {
        let (qnew, hh) = if (fnow > enow) == (fnow > -enow) {
            let r = fast_two_sum(enow, q);
            eindex += 1;
            enow = at(e, eindex);
            r
        } else {
            let r = fast_two_sum(fnow, q);
            findex += 1;
            fnow = at(f, findex);
            r
        };
        q = qnew;
        if hh != 0.0 {
            h[hindex] = hh;
            hindex += 1;
        }
        while eindex < elen && findex < flen {
            let (qnew, hh) = if (fnow > enow) == (fnow > -enow) {
                let r = two_sum(q, enow);
                eindex += 1;
                enow = at(e, eindex);
                r
            } else {
                let r = two_sum(q, fnow);
                findex += 1;
                fnow = at(f, findex);
                r
            };
            q = qnew;
            if hh != 0.0 {
                h[hindex] = hh;
                hindex += 1;
            }
        }
    }
    while eindex < elen {
        let (qnew, hh) = two_sum(q, enow);
        eindex += 1;
        enow = at(e, eindex);
        q = qnew;
        if hh != 0.0 {
            h[hindex] = hh;
            hindex += 1;
        }
    }
    while findex < flen {
        let (qnew, hh) = two_sum(q, fnow);
        findex += 1;
        fnow = at(f, findex);
        q = qnew;
        if hh != 0.0 {
            h[hindex] = hh;
            hindex += 1;
        }
    }
    if q != 0.0 || hindex == 0 {
        h[hindex] = q;
        hindex += 1;
    }
    hindex
}

#[cfg(test)]
#[path = "unit_tests/orientation.rs"]
mod tests;
