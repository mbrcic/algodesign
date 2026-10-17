use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;

/// The exact determinant's sign, over rationals: the oracle.
fn exact_sign(a: [f64; 2], b: [f64; 2], c: [f64; 2]) -> i8 {
    let r = |x: f64| BigRational::from_float(x).unwrap();
    let det = (r(b[0]) - r(a[0])) * (r(c[1]) - r(a[1])) - (r(b[1]) - r(a[1])) * (r(c[0]) - r(a[0]));
    match det.cmp(&BigRational::from_integer(BigInt::from(0))) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn sign(x: f64) -> i8 {
    if x > 0.0 {
        1
    } else if x < 0.0 {
        -1
    } else {
        0
    }
}

fn f(p: [i16; 2]) -> [f64; 2] {
    [f64::from(p[0]), f64::from(p[1])]
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean orientation examples
    assert!(orient2d([0.0, 0.0], [1.0, 0.0], [0.0, 1.0]) > 0.0);
    assert!(orient2d([0.0, 0.0], [1.0, 0.0], [0.0, -1.0]) < 0.0);
    assert_eq!(orient2d([0.0, 0.0], [1.0, 1.0], [3.0, 3.0]), 0.0);
    assert_eq!(orient2d([2.0, 2.0], [2.0, 2.0], [2.0, 2.0]), 0.0);
}

#[test]
fn the_fast_filter_alone_gets_signs_wrong() {
    // Kettner et al. 2008, Fig. 1: p on a 64 × 64 grid of ulp steps (2^-53) from (0.5, 0.5),
    // q = (12, 12), r = (24, 24), all three nearly on the line y = x. The plain determinant must
    // disagree with the exact sign somewhere on this grid, or the demonstration is empty; the
    // adaptive one must agree everywhere.
    let (q, r) = ([12.0, 12.0], [24.0, 24.0]);
    let u = f64::EPSILON / 2.0;
    let mut wrong = 0;
    for i in 0..64 {
        for j in 0..64 {
            let p = [0.5 + f64::from(i) * u, 0.5 + f64::from(j) * u];
            if sign(orient2d_fast(p, q, r)) != exact_sign(p, q, r) {
                wrong += 1;
            }
            assert_eq!(sign(orient2d(p, q, r)), exact_sign(p, q, r), "at {p:?}");
        }
    }
    assert!(wrong > 0, "the grid never fooled the fast filter");
}

/// A double `m · 2^e` with `|m| < 2^20` and `|e| ≤ 60`: well inside the range where no product
/// overflows or underflows, which Shewchuk's error bounds assume.
fn coord() -> impl Strategy<Value = f64> {
    (-(1i64 << 20)..(1i64 << 20), -60i32..60).prop_map(|(m, e)| m as f64 * 2f64.powi(e))
}

#[test]
fn outside_the_range_it_refuses() {
    // Where Shewchuk's error bounds stop holding (they assume no overflow or underflow), the
    // answer is NaN, "cannot decide". Before the range guard these two got 0 (the products
    // underflow) and NaN (they overflow); the exact-rational oracle says both turn left.
    let tiny = ([0.0, 0.0], [1e-170, 0.0], [0.0, 1e-170]);
    assert_eq!(exact_sign(tiny.0, tiny.1, tiny.2), 1);
    assert!(orient2d(tiny.0, tiny.1, tiny.2).is_nan());
    let huge = ([1e300, 1e300], [1e300, 2e300], [0.0, 0.0]);
    assert_eq!(exact_sign(huge.0, huge.1, huge.2), 1);
    assert!(orient2d(huge.0, huge.1, huge.2).is_nan());
}

/// The triples at the ends of the range pinned in `python/tests/geometry/test_orientation.py`
/// (`test_the_sign_is_exact_at_the_ends_of_the_range`), in its order; the Lean–Rust
/// comparison copies the same seven. Before the range guard the Rust got 6 of them wrong,
/// #0 with a wrong nonzero sign.
const PINNED_EDGE: [([f64; 2], [f64; 2], [f64; 2]); 7] = [
    (
        [2.057_705_859_227_321_2e-156, 2.057_705_859_227_325_8e-156],
        [1.487_332_792_992_804_8e-155, 1.487_332_792_992_805_2e-155],
        [4.595_529_367_609_762e-155, 4.595_529_367_609_762e-155],
    ),
    (
        [1.439_948_050_008_907_6e-155, 1.439_948_050_008_907_6e-155],
        [8.171_674_804_334_04e-157, 8.171_674_804_334_068e-157],
        [6.102_081_621_207_356e-155, 6.102_081_621_207_352e-155],
    ),
    ([0.0, 0.0], [1e-170, 0.0], [0.0, 1e-170]),
    ([0.0, 0.0], [3e-320, 0.0], [0.0, 5e-324]),
    ([1e300, 1e300], [1e300, 2e300], [0.0, 0.0]),
    ([-1.7e308, 0.0], [1.7e308, 1e-300], [0.0, 1.7e308]),
    ([1e300, -1e300], [-1e300, 1e300], [5e299, -5e299]),
];

/// `orient2d`'s contract outside its range: NaN, or the exact sign. `sign` maps NaN to 0, so a
/// NaN is tested for first, not compared.
fn nan_or_exact(a: [f64; 2], b: [f64; 2], c: [f64; 2]) -> Result<(), String> {
    let got = orient2d(a, b, c);
    if got.is_nan() || sign(got) == exact_sign(a, b, c) {
        Ok(())
    } else {
        Err(format!(
            "orient2d({a:?}, {b:?}, {c:?}) = {got:e}, the exact sign is {}",
            exact_sign(a, b, c)
        ))
    }
}

#[test]
fn the_pinned_edge_triples_get_nan_or_the_exact_sign() {
    for (i, &(a, b, c)) in PINNED_EDGE.iter().enumerate() {
        for (p, q, r) in [(a, b, c), (b, a, c), (b, c, a)] {
            if let Err(e) = nan_or_exact(p, q, r) {
                panic!("pinned triple #{i}: {e}");
            }
        }
    }
}

#[test]
fn the_confidently_wrong_triple_is_refused() {
    // #0, coordinates near 1e-156: the products are subnormal, so the filter's error bound no
    // longer holds, and the plain determinant had the wrong nonzero sign (+1 for -1).
    let (a, b, c) = PINNED_EDGE[0];
    assert_eq!(exact_sign(a, b, c), -1);
    assert!(orient2d(a, b, c).is_nan());
}

#[test]
fn the_guard_leaves_the_bits_unchanged() {
    // The bits Shewchuk's predicate returns without the range guard (`pre_guard.rs` in
    // `examples/orient2d_guard_ab`): five triples inside the range, from a plain
    // turn to two on Kettner et al.'s grid near y = x and one of mixed magnitudes, and one outside
    // it that the signs alone decide. A guard that moved any
    // in-range answer, even in its last bit, fails here; the example's `bits` mode compares
    // 7.1 million more.
    type Pinned = ([f64; 2], [f64; 2], [f64; 2], u64);
    let pinned: [Pinned; 6] = [
        ([0.0, 0.0], [1.0, 0.0], [0.0, 1.0], 0x3FF0_0000_0000_0000),
        ([0.1, 0.2], [0.7, -0.3], [-0.4, 0.9], 0x3FC5_C28F_5C28_F5C4),
        (
            [0.5, 0.5],
            [12.0, 12.0],
            [24.0, 24.000_000_000_000_004],
            0x3D27_0000_0000_0000,
        ),
        (
            [0.500_000_000_000_000_1, 0.5],
            [12.0, 12.0],
            [24.0, 24.0],
            0xBCD8_0000_0000_0000,
        ),
        (
            [1e100, 3e-100],
            [-2e120, 7e99],
            [5e-110, -1e110],
            0x6FC0_7D45_7124_123D,
        ),
        (
            [0.0, 0.0],
            [1.0, 0.0],
            [0.0, -5e-324],
            0x8000_0000_0000_0001,
        ),
    ];
    for (a, b, c, bits) in pinned {
        let got = orient2d(a, b, c);
        assert_eq!(got.to_bits(), bits, "{a:?} {b:?} {c:?}: {got:e}");
    }
}

#[test]
fn the_exact_stages_refuse_outside_the_range() {
    // Check 3 of the guard. Both triples pass the filter's check (their products are at least
    // 2^-960), the filter cannot decide, and the exact stages' tail products underflow: without
    // check 3 both return 0 for a nonzero exact sign (the properties below find them).
    let tiny = pow2(-1022);
    let (a, b, c) = ([0.0, 0.0], [0.0, tiny], [tiny, pow2(62)]);
    assert_eq!(exact_sign(a, b, c), -1);
    assert!(orient2d(a, b, c).is_nan());
    // `mixed_magnitudes_near_a_line_…` at x = 511772687597568, y = 985162418487296, k = 1017,
    // nudge = -1, big = 0: a and b near 0.1, c near 1e-307.
    let a = [0.113_636_364_229_023_68, 0.218_750_000_000_000_22];
    let b = [0.227_272_728_458_047_36, 0.437_500_000_000_000_44];
    let c = [8.091_177_709_497_71e-308, 1.557_551_700_955_042_4e-307];
    assert_eq!(exact_sign(a, b, c), -1);
    assert!(orient2d(a, b, c).is_nan());
}

/// `2^k` for `k` in `-1074..=1023`, subnormal powers included (`2f64.powi` underflows there).
fn pow2(k: i32) -> f64 {
    assert!((-1074..=1023).contains(&k));
    if k >= -1022 {
        f64::from_bits(((k + 1023) as u64) << 52)
    } else {
        f64::from_bits(1u64 << (k + 1074))
    }
}

/// A double of either sign with a full 53-bit significand and exponent `e`, so its magnitude is
/// in `[2^e, 2^(e+1))`; or zero.
fn full(m: u64, negative: bool, e: i32, zero: bool) -> f64 {
    if zero {
        return 0.0;
    }
    let x = ((1u64 << 52) | (m & ((1u64 << 52) - 1))) as f64 * pow2(e - 52);
    if negative {
        -x
    } else {
        x
    }
}

/// A full-significand coordinate with its exponent in `e`, zero one time in eight.
fn coord_in(e: std::ops::RangeInclusive<i32>) -> impl Strategy<Value = f64> {
    (any::<u64>(), any::<bool>(), e, 0u8..8).prop_map(|(m, n, e, z)| full(m, n, e, z == 0))
}

proptest! {
    #[test]
    fn swap_negates(a in any::<[i16; 2]>(), b in any::<[i16; 2]>(), c in any::<[i16; 2]>()) {
        // Lean: orient_swap
        prop_assert_eq!(sign(orient2d(f(b), f(a), f(c))), -sign(orient2d(f(a), f(b), f(c))));
    }

    #[test]
    fn cycle_keeps(a in any::<[i16; 2]>(), b in any::<[i16; 2]>(), c in any::<[i16; 2]>()) {
        // Lean: orient_cycle
        prop_assert_eq!(sign(orient2d(f(b), f(c), f(a))), sign(orient2d(f(a), f(b), f(c))));
    }

    #[test]
    fn degenerate_is_zero(a in any::<[i16; 2]>(), c in any::<[i16; 2]>()) {
        // Lean: orient_self_left
        prop_assert_eq!(orient2d(f(a), f(a), f(c)), 0.0);
    }

    #[test]
    fn zero_iff_collinear_on_integers(a in any::<[i8; 2]>(), d in any::<[i8; 2]>(), t in -20i32..20) {
        // Lean: orient_eq_zero_iff -- c = a + t·d is collinear with a and b = a + d
        let a = [f64::from(a[0]), f64::from(a[1])];
        let b = [a[0] + f64::from(d[0]), a[1] + f64::from(d[1])];
        let c = [a[0] + f64::from(t) * f64::from(d[0]), a[1] + f64::from(t) * f64::from(d[1])];
        prop_assert_eq!(orient2d(a, b, c), 0.0);
    }

    #[test]
    fn sign_is_exact_near_a_line(
        x in -1e6f64..1e6, y in -1e6f64..1e6, ulps in -8i64..8, scale in -40i32..40,
    ) {
        // Points on the line through a and b, then nudged by a few ulps: the hard case.
        let s = 2f64.powi(scale);
        let a = [x * s, y * s];
        let b = [(x + 3.0) * s, (y + 7.0) * s];
        let c0 = [(x + 6.0) * s, (y + 14.0) * s];
        let c = [c0[0], f64::from_bits((c0[1].to_bits() as i64).wrapping_add(ulps) as u64)];
        prop_assume!(c[1].is_finite());
        prop_assert_eq!(sign(orient2d(a, b, c)), exact_sign(a, b, c));
    }

    #[test]
    fn sign_is_exact_anywhere(p in [[coord(), coord()], [coord(), coord()], [coord(), coord()]]) {
        prop_assert_eq!(sign(orient2d(p[0], p[1], p[2])), exact_sign(p[0], p[1], p[2]));
    }

    #[test]
    fn exact_on_a_line_with_inexact_differences(
        x in 1i64..(1 << 52), y in 1i64..(1 << 52), k in 60i32..200, nudge in -2i64..3,
    ) {
        // a = (X, Y) and b = (2X, 2Y) are large; c = (X, Y)·2^-k is tiny and exactly on the line
        // through the origin and a, so the exact determinant is 0 when c is not nudged. Neither
        // a − c nor b − c is representable, so the tails are nonzero, and only the last, exact
        // stage of `orient2dadapt` decides. Nudging c's y by a few ulps makes the sign nonzero.
        let (x, y) = ((x | 1) as f64, (y | 1) as f64);
        let s = 2f64.powi(-k);
        let a = [x, y];
        let b = [2.0 * x, 2.0 * y];
        let c = [x * s, f64::from_bits(((y * s).to_bits() as i64 + nudge) as u64)];
        prop_assert_eq!(sign(orient2d(a, b, c)), exact_sign(a, b, c));
    }
}

/// Any finite double: a random sign and significand under a biased exponent field in `0..=2046`
/// (0 is the subnormals), so exponents `-1074..=1023` all occur; zero one time in eight.
fn any_finite() -> impl Strategy<Value = f64> {
    (any::<u64>(), 0u64..=2046, 0u8..8).prop_map(|(bits, field, z)| {
        if z == 0 {
            0.0
        } else {
            f64::from_bits((bits & 0x800F_FFFF_FFFF_FFFF) | (field << 52))
        }
    })
}

/// A near-collinear triple in `[-1, 1]²` (as the Lean–Rust comparison builds them: `c` on the
/// segment `ab`, then moved a few ulps), every coordinate then scaled by `2^k`.
fn near_line_scaled(
    a: [f64; 2],
    b: [f64; 2],
    t: f64,
    nudge: i64,
    k: i32,
) -> ([f64; 2], [f64; 2], [f64; 2]) {
    let s = pow2(k);
    let c = [a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])];
    let c = [
        c[0],
        f64::from_bits((c[1].to_bits() as i64).wrapping_add(nudge) as u64),
    ];
    let sc = |p: [f64; 2]| [p[0] * s, p[1] * s];
    (sc(a), sc(b), sc(c))
}

fn finite(p: [f64; 2]) -> bool {
    p[0].is_finite() && p[1].is_finite()
}

/// Inside the documented range: every coordinate zero or of magnitude in `[2^-400, 2^500]`.
fn in_range(p: [f64; 2]) -> bool {
    p.iter()
        .all(|&x| x == 0.0 || (pow2(-400)..=pow2(500)).contains(&x.abs()))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4096))]

    #[test]
    fn anywhere_the_answer_is_nan_or_the_exact_sign(
        p in [[any_finite(), any_finite()], [any_finite(), any_finite()],
              [any_finite(), any_finite()]],
    ) {
        // Independent exponents per coordinate: mixed magnitudes are where a product
        // underflows to zero while its factors do not.
        prop_assert_eq!(nan_or_exact(p[0], p[1], p[2]), Ok(()));
        prop_assert_eq!(nan_or_exact(p[1], p[0], p[2]), Ok(()));
    }

    #[test]
    fn near_a_line_at_any_scale_the_answer_is_nan_or_the_exact_sign(
        a in [-1.0f64..1.0, -1.0f64..1.0], b in [-1.0f64..1.0, -1.0f64..1.0],
        t in 0.0f64..1.0, nudge in -3i64..4, k in -1074i32..=1023,
    ) {
        // One scale per triple, across every exponent: the exact stages run near the line, so
        // their products and tails underflow or overflow at the ends.
        let (a, b, c) = near_line_scaled(a, b, t, nudge, k);
        prop_assume!(finite(a) && finite(b) && finite(c));
        prop_assert_eq!(nan_or_exact(a, b, c), Ok(()));
    }

    #[test]
    fn mixed_magnitudes_near_a_line_get_nan_or_the_exact_sign(
        x in 1i64..(1 << 52), y in 1i64..(1 << 52), k in 0i32..1074, nudge in -2i64..3,
        big in 0i32..=970,
    ) {
        // As `exact_on_a_line_with_inexact_differences`, without its bound on `k`: a and b near
        // 2^big, c = a·2^-k exactly on the line through the origin and a, then nudged. Neither
        // a − c nor b − c is representable, so only the exact stages decide, on tails as small as
        // c, whose products underflow once c is small enough.
        let (x, y) = ((x | 1) as f64 * pow2(big - 52), (y | 1) as f64 * pow2(big - 52));
        let a = [x, y];
        let b = [2.0 * x, 2.0 * y];
        let s = pow2(-k);
        let cy = y * s;
        prop_assume!(cy != 0.0 && (x * s) != 0.0);
        let c = [x * s, f64::from_bits((cy.to_bits() as i64 + nudge) as u64)];
        prop_assume!(c[1].is_finite());
        prop_assert_eq!(nan_or_exact(a, b, c), Ok(()));
    }

    #[test]
    fn inside_the_range_the_sign_is_exact_and_never_nan(
        p in [[coord_in(-400..=499), coord_in(-400..=499)],
              [coord_in(-400..=499), coord_in(-400..=499)],
              [coord_in(-400..=499), coord_in(-400..=499)]],
    ) {
        // The other half of the contract: a guard that refused everything would pass the tests
        // above.
        let r = orient2d(p[0], p[1], p[2]);
        prop_assert!(!r.is_nan(), "NaN in range at {:?}", p);
        prop_assert_eq!(sign(r), exact_sign(p[0], p[1], p[2]));
    }

    #[test]
    fn near_a_line_inside_the_range_the_sign_is_exact_and_never_nan(
        a in [-1.0f64..1.0, -1.0f64..1.0], b in [-1.0f64..1.0, -1.0f64..1.0],
        t in 0.0f64..1.0, nudge in -3i64..4, k in -330i32..=498,
    ) {
        let (a, b, c) = near_line_scaled(a, b, t, nudge, k);
        prop_assume!(in_range(a) && in_range(b) && in_range(c));
        let r = orient2d(a, b, c);
        prop_assert!(!r.is_nan(), "NaN in range at {:?}", (a, b, c));
        prop_assert_eq!(sign(r), exact_sign(a, b, c));
    }
}

#[test]
fn sign_is_exact_with_a_coordinate_of_two_to_the_53() {
    // A coordinate of 2^53, where f64 stops holding every integer; the sign is still the exact one.
    let p = [[0.0, 0.0], [0.0, -1.0], [1.0, 9007199254740992.0]];
    assert_eq!(
        sign(orient2d(p[0], p[1], p[2])),
        exact_sign(p[0], p[1], p[2])
    );
}
