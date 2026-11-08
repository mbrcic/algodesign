// SPDX-License-Identifier: Apache-2.0
//! Rabin–Karp string matching (CLRS §32.2): a radix-[`BASE`] fingerprint rolled one byte at a
//! time, modulo a random prime below Motwani–Raghavan §7.6's [`threshold`]. Every hash hit is
//! verified, so answers are exact; expected `O(n + m)`. [`search_with`] takes fixed parameters,
//! as in the chapter's hand trace.
//!
//! Lean: `RabinKarp/Search.lean`, `rabinKarpSearch_eq_occurrenceList`.
//!
//! **Against the Python, and how fast.** The same fingerprints, hits and false alarms, with the
//! arithmetic rearranged: the leaving byte's weight `-(c · base^m) mod q` is a 256-entry table, so
//! a slide is `t · base + drop[c] + e`, one product and one reduction, where the Python computes
//! `(t − c · high) · base + e`; at base 256 or 10 the reduction is a table lookup (`SmallBase`),
//! otherwise Möller–Granlund's division by an invariant integer. The Python draws its prime with
//! `random.Random`, so one seed does not give one prime in both. The chapter teaches it for its
//! expected `O(n + m)` and its fingerprint, not for speed on prose.
//! `STRINGS_SCAN_ONLY=1 cargo bench -p algodesign --bench strings` times it beside the naive scan.

/// Base the chapter traces by hand: `(10, 13)`, over digit values 0-9.
pub const BOOK_BASE: u64 = 10;
/// Modulus the chapter traces by hand: small, so collisions occur.
pub const BOOK_MOD: u64 = 13;
/// The radix the library runs: one digit per byte.
pub const BASE: u64 = 256;
/// The largest threshold [`threshold`] returns, as in the Python; the reducers accept any `u64`
/// modulus.
pub const MAX_THRESHOLD: u64 = 1 << 61;

/// Motwani–Raghavan's threshold `τ = x·⌈log₂ x⌉`, `x = N²·M` with lengths in bits, clamped to
/// `[3, MAX_THRESHOLD]`.
#[allow(
    clippy::missing_panics_doc,
    reason = "the expect cannot fire: the value is clamped to at most MAX_THRESHOLD < 2^64"
)]
#[must_use]
pub fn threshold(n: usize, m: usize) -> u64 {
    let text_bits = (n as u128).saturating_mul(8);
    let pattern_bits = (m as u128).saturating_mul(8);
    let x = text_bits
        .saturating_mul(text_bits)
        .saturating_mul(pattern_bits);
    let log = if x < 2 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    };
    let tau = x.saturating_mul(u128::from(log));
    u64::try_from(tau.clamp(3, u128::from(MAX_THRESHOLD))).expect("clamped below 2^61")
}

/// Whether `x` is prime: Miller–Rabin with the first twelve primes as witnesses, exact for every
/// `u64` (Sorenson and Webster 2017).
#[allow(
    clippy::missing_panics_doc,
    reason = "the expect cannot fire: a product reduced modulo x < 2^64 fits u64"
)]
#[must_use]
pub fn is_prime(x: u64) -> bool {
    const WITNESSES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    if x < 2 {
        return false;
    }
    for p in WITNESSES {
        if x % p == 0 {
            return x == p;
        }
    }
    let modulus = u128::from(x);
    let mul = |a: u64, b: u64| -> u64 {
        u64::try_from(u128::from(a) * u128::from(b) % modulus).expect("reduced below x")
    };
    let pow = |mut b: u64, mut e: u64| -> u64 {
        let mut acc = 1;
        while e > 0 {
            if e & 1 == 1 {
                acc = mul(acc, b);
            }
            b = mul(b, b);
            e >>= 1;
        }
        acc
    };
    // x - 1 = d · 2^s with d odd.
    let s = (x - 1).trailing_zeros();
    let d = (x - 1) >> s;
    'witness: for a in WITNESSES {
        let mut y = pow(a, d);
        if y == 1 || y == x - 1 {
            continue;
        }
        for _ in 1..s {
            y = mul(y, y);
            if y == x - 1 {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

/// splitmix64 (Steele, Lea and Flood 2014).
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// A prime drawn uniformly below `tau` from the stream `seed` starts.
///
/// # Panics
///
/// If `tau < 3`.
#[must_use]
pub fn random_prime_below(tau: u64, seed: u64) -> u64 {
    assert!(tau >= 3, "no prime lies below {tau}");
    let bits = 64 - (tau - 1).leading_zeros();
    let mut rng = SplitMix64(seed);
    loop {
        let x = rng.next() >> (64 - bits);
        if x < tau && is_prime(x) {
            return x;
        }
    }
}

/// Reduction modulo a fixed `u64` without division (Möller and Granlund 2011, Algorithm 4).
/// Values are kept scaled by `2^shift`, so that the divisor `d = q << shift` has its top bit set.
#[derive(Clone, Copy, Debug)]
struct Modulus {
    d: u64,
    shift: u32,
    /// The reciprocal `⌊(2^128 - 1) / d⌋ - 2^64`.
    v: u64,
}

impl Modulus {
    /// The reducer for a positive modulus `q`.
    fn new(q: u64) -> Modulus {
        debug_assert!(q > 0, "a zero modulus is refused before a reducer is built");
        let shift = q.leading_zeros();
        let d = q << shift;
        let v = u64::try_from(u128::MAX / u128::from(d) - (1u128 << 64))
            .expect("d has its top bit set, so the reciprocal is below 2^64");
        Modulus { d, shift, v }
    }

    /// `x mod q` in the ordinary scale, for `x < q · 2^64`.
    fn reduce(self, x: u128) -> u64 {
        self.reduce_scaled(x << self.shift) >> self.shift
    }
}

/// How a search reduces `t · base + addend` modulo `d`, in [`Modulus`]'s scale.
trait Reduce: Copy {
    /// `x mod d`.
    fn reduce_scaled(self, x: u128) -> u64;
}

impl Reduce for Modulus {
    #[inline]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "splitting a u128 into its two u64 halves"
    )]
    fn reduce_scaled(self, x: u128) -> u64 {
        let (u1, u0) = ((x >> 64) as u64, x as u64); // u1 < d, from x < d · 2^64
        let p = u128::from(self.v) * u128::from(u1);
        let (q0, carry) = (p as u64).overflowing_add(u0);
        let q1 = ((p >> 64) as u64)
            .wrapping_add(u1)
            .wrapping_add(u64::from(carry))
            .wrapping_add(1);
        let mut r = u0.wrapping_sub(q1.wrapping_mul(self.d));
        if r > q0 {
            r = r.wrapping_add(self.d);
        }
        if r >= self.d {
            r -= self.d;
        }
        r
    }
}

/// The reduction for a base of at most [`BASE`]: the high word is below 258, so
/// `k · 2^64 mod d` is a table lookup.
#[derive(Clone, Copy)]
struct SmallBase<'a> {
    d: u64,
    /// `k · 2^64 mod d` for every high word `k`.
    wrap: &'a [u64; 258],
}

impl Reduce for SmallBase<'_> {
    #[inline]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "splitting a u128 into its two u64 halves"
    )]
    fn reduce_scaled(self, x: u128) -> u64 {
        let (k, low) = ((x >> 64) as usize, x as u64);
        // `low < 2d`, then the sum is below `2d`: one subtraction each.
        let low = if low >= self.d { low - self.d } else { low };
        let (sum, carried) = low.overflowing_add(self.wrap[k]);
        if carried || sum >= self.d {
            sum.wrapping_sub(self.d)
        } else {
            sum
        }
    }
}

/// The fingerprint arithmetic for one search, in [`Modulus`]'s scale.
struct Fingerprint {
    modulus: Modulus,
    /// `base mod q`.
    base: u64,
    /// For each byte `c`, `-(c · base^m) mod q`: removing `c` as the leaving digit.
    drop: [u64; 256],
    /// For each byte `c`, `c mod q`: adding `c` as the entering digit.
    enter: [u64; 256],
    /// [`SmallBase`]'s table, filled only when `base ≤ 256`.
    wrap: [u64; 258],
    small_base: bool,
}

impl Fingerprint {
    /// The arithmetic for a window of `m ≥ 1` bytes; panics on a zero modulus.
    fn new(base: u64, modulus: u64, m: usize) -> Fingerprint {
        let base = base % modulus;
        let reducer = Modulus::new(modulus);
        // CLRS's `h = base^(m-1) mod q`: the weight of the character leaving the window.
        let mut high = 1 % modulus;
        for _ in 1..m {
            high = reducer.reduce(u128::from(high) * u128::from(base));
        }
        let shifted = reducer.reduce(u128::from(high) * u128::from(base));
        let (mut drop, mut enter) = ([0u64; 256], [0u64; 256]);
        for (c, (out, inn)) in (0u8..=255).zip(drop.iter_mut().zip(enter.iter_mut())) {
            let weight = reducer.reduce(u128::from(c) * u128::from(shifted));
            *out = (if weight == 0 { 0 } else { modulus - weight }) << reducer.shift;
            *inn = (u64::from(c) % modulus) << reducer.shift;
        }
        let small_base = base <= BASE;
        let mut wrap = [0u64; 258];
        if small_base {
            for (k, slot) in (0u64..).zip(wrap.iter_mut()) {
                *slot = reducer.reduce_scaled(u128::from(k) << 64);
            }
        }
        Fingerprint {
            modulus: reducer,
            base,
            drop,
            enter,
            wrap,
            small_base,
        }
    }

    /// The fingerprint of `window` by Horner's rule.
    fn hash_of<R: Reduce>(&self, reduce: R, window: &[u8]) -> u64 {
        window.iter().fold(0, |acc, &c| {
            reduce.reduce_scaled(
                u128::from(acc) * u128::from(self.base) + u128::from(self.enter[usize::from(c)]),
            )
        })
    }

    /// One slide: `t_s · base + drop[leaving] + enter[entering]`. Lean: `rollHash_eq`.
    #[inline]
    fn roll<R: Reduce>(&self, reduce: R, window_hash: u64, leaving: u8, entering: u8) -> u64 {
        reduce.reduce_scaled(
            u128::from(window_hash) * u128::from(self.base)
                + u128::from(self.drop[usize::from(leaving)])
                + u128::from(self.enter[usize::from(entering)]),
        )
    }

    /// A scaled fingerprint brought back to the ordinary one.
    #[cfg(any(test, feature = "unchecked"))]
    fn value(&self, scaled: u64) -> u64 {
        scaled >> self.modulus.shift
    }
}

/// CLRS's loop: compare fingerprints, verify a hit, slide. `1 ≤ m ≤ n`.
fn scan<R: Reduce>(text: &[u8], pat: &[u8], fingerprint: &Fingerprint, reduce: R) -> Vec<u32> {
    scan_observed(text, pat, fingerprint, reduce, |_, _| {})
}

/// [`scan`], telling `seen` its state at each window, before the window is checked: the carried
/// (scaled) number and the positions found so far.
fn scan_observed<R: Reduce>(
    text: &[u8],
    pat: &[u8],
    fingerprint: &Fingerprint,
    reduce: R,
    mut seen: impl FnMut(u64, &[u32]),
) -> Vec<u32> {
    let m = pat.len();
    let last = text.len() - m;
    let pat_hash = fingerprint.hash_of(reduce, pat);
    let mut window_hash = fingerprint.hash_of(reduce, &text[..m]);
    let mut matches = Vec::new();

    for i in 0..=last {
        seen(window_hash, &matches);
        if window_hash == pat_hash {
            let window = &text[i..i + m];
            if window == pat {
                matches.push(u32::try_from(i).expect("search_with asserted n <= u32::MAX"));
            } else {
                #[cfg(test)]
                SPURIOUS.with(|s| s.set(s.get() + 1));
            }
        }
        if i < last {
            window_hash = fingerprint.roll(reduce, window_hash, text[i], text[i + m]);
        }
    }

    matches
}

/// Every start of `pat` in `text`, ascending, with a fresh random prime. Expected `O(n + m)`.
///
/// # Panics
///
/// If `text.len()` exceeds `u32::MAX`.
#[must_use]
pub fn search(text: &[u8], pat: &[u8]) -> Vec<u32> {
    use std::hash::BuildHasher;
    // `RandomState` is keyed from OS randomness.
    let seed = std::collections::hash_map::RandomState::new().hash_one(0u64);
    search_seeded(text, pat, seed)
}

/// [`search`] with the prime drawn from `seed`.
///
/// # Panics
///
/// If `text.len()` exceeds `u32::MAX`.
#[must_use]
pub fn search_seeded(text: &[u8], pat: &[u8], seed: u64) -> Vec<u32> {
    let (n, m) = (text.len(), pat.len());
    let modulus = if m == 0 || m > n {
        1 // unused: `search_with` answers both cases before its loop
    } else {
        random_prime_below(threshold(n, m), seed)
    };
    search_with(text, pat, BASE, modulus)
}

/// CLRS's RABIN-KARP-MATCHER with fixed `base` and `modulus`: every occurrence. Worst case
/// `O(n·m)`. Lean: `rabinKarpSearch_eq_occurrenceList`.
///
/// # Panics
///
/// If `text.len()` exceeds `u32::MAX`, or `modulus` is zero and the scan runs.
#[must_use]
pub fn search_with(text: &[u8], pat: &[u8], base: u64, modulus: u64) -> Vec<u32> {
    let m = pat.len();
    let n = text.len();
    if m > n {
        return Vec::new();
    }
    assert!(
        u32::try_from(n).is_ok(),
        "positions are u32: one search reports at most u32::MAX characters; shard instead"
    );
    if m == 0 {
        return (0..=u32::try_from(n).expect("asserted above")).collect();
    }

    let fingerprint = Fingerprint::new(base, modulus, m);
    if fingerprint.small_base {
        let reduce = SmallBase {
            d: fingerprint.modulus.d,
            wrap: &fingerprint.wrap,
        };
        scan(text, pat, &fingerprint, reduce)
    } else {
        scan(text, pat, &fingerprint, fingerprint.modulus)
    }
}

/// Box invariant 2: `carried` is the fingerprint of the window at the head of `rest`. Lean:
/// `RabinKarp.NumberMatchesWindow`.
#[must_use]
pub fn is_number_matches_window(
    base: u64,
    modulus: u64,
    pat: &[u8],
    rest: &[u8],
    carried: u64,
) -> bool {
    let window = &rest[..pat.len().min(rest.len())];
    let fresh = window.iter().try_fold(0u128, |acc, &c| {
        let next = acc
            .checked_mul(u128::from(base))?
            .checked_add(u128::from(c))?;
        Some(next.checked_rem(u128::from(modulus)).unwrap_or(next))
    });
    fresh == Some(u128::from(carried))
}

/// Box invariant 3: equal numbers only make a window a candidate: every candidate is checked
/// letter by letter before it is reported. As the scan's state: `found` is exactly the occurrences
/// of `pat` in `text` before `start`, in increasing order. Lean: `RabinKarp.FoundSoFarExact`.
#[must_use]
pub fn is_found_so_far_exact(text: &[u8], pat: &[u8], start: usize, found: &[u32]) -> bool {
    let exact = (0..=text.len())
        .filter(|&i| i < start && text[i..].starts_with(pat))
        .map(Some);
    exact.eq(found.iter().map(|&j| usize::try_from(j).ok()))
}

/// Both pieces, on the scan standing at `start` with `carried` and `found`. Lean:
/// `RabinKarp.Valid`.
#[must_use]
pub fn is_valid(
    base: u64,
    modulus: u64,
    text: &[u8],
    pat: &[u8],
    start: usize,
    carried: u64,
    found: &[u32],
) -> bool {
    check_valid(base, modulus, text, pat, start, carried, found).is_ok()
}

/// [`is_valid`], naming the first piece that fails. A `start` past the text has no window, so
/// its number matches none.
///
/// # Errors
///
/// `"invariant 2 (number_matches_window)"` or `"invariant 3 (found_so_far_exact)"`.
pub fn check_valid(
    base: u64,
    modulus: u64,
    text: &[u8],
    pat: &[u8],
    start: usize,
    carried: u64,
    found: &[u32],
) -> Result<(), &'static str> {
    let rest = text.get(start..);
    if !rest.is_some_and(|rest| is_number_matches_window(base, modulus, pat, rest, carried)) {
        return Err("invariant 2 (number_matches_window)");
    }
    if !is_found_so_far_exact(text, pat, start, found) {
        return Err("invariant 3 (found_so_far_exact)");
    }
    Ok(())
}

/// The state [`search_with`]'s scan stands in at each window, before checking it: the number it
/// carries, unscaled, and the positions it has found so far.
///
/// # Panics
///
/// As [`search_with`] does.
#[cfg(feature = "unchecked")]
#[must_use]
pub fn scan_states(text: &[u8], pat: &[u8], base: u64, modulus: u64) -> Vec<(u64, Vec<u32>)> {
    let (n, m) = (text.len(), pat.len());
    if m == 0 || m > n {
        return Vec::new();
    }
    let fingerprint = Fingerprint::new(base, modulus, m);
    let mut out = Vec::with_capacity(n - m + 1);
    let seen = |scaled, found: &[u32]| out.push((fingerprint.value(scaled), found.to_vec()));
    if fingerprint.small_base {
        let reduce = SmallBase {
            d: fingerprint.modulus.d,
            wrap: &fingerprint.wrap,
        };
        let _ = scan_observed(text, pat, &fingerprint, reduce, seen);
    } else {
        let _ = scan_observed(text, pat, &fingerprint, fingerprint.modulus, seen);
    }
    out
}

#[cfg(test)]
thread_local! {
    /// Spurious fingerprint hits that verification rejected.
    static SPURIOUS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
#[path = "unit_tests/rabin_karp.rs"]
mod tests;
