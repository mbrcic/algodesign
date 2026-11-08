// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::naive;
use proptest::prelude::*;

/// Primality by trial division: slow, and obviously right.
fn trial_division(x: u64) -> bool {
    x >= 2 && (2..).take_while(|d| d * d <= x).all(|d| x % d != 0)
}

/// The fingerprint of `window` in plain `u128` arithmetic: the reducer's reference.
fn reference_hash(window: &[u8], base: u64, modulus: u64) -> u64 {
    let (base, modulus) = (u128::from(base), u128::from(modulus));
    let hash = window.iter().fold(0u128, |acc, &c| {
        (acc * (base % modulus) + u128::from(c)) % modulus
    });
    u64::try_from(hash).expect("reduced below a u64 modulus")
}

proptest! {
    /// The search at a drawn prime is the naive one, the empty pattern included.
    #[test]
    fn matches_naive_at_a_drawn_prime(
        text in prop::collection::vec(0u8..4, 0..200),
        pat in prop::collection::vec(0u8..4, 0..8),
        seed in any::<u64>(),
    ) {
        // Lean: rabinKarpSearch_eq_occurrenceList
        prop_assert_eq!(search_seeded(&text, &pat, seed), naive::search(&text, &pat));
    }

    /// Any `u64` base, at a drawn prime.
    #[test]
    fn matches_naive_for_any_base_at_a_drawn_prime(
        text in prop::collection::vec(0u8..4, 0..200),
        pat in prop::collection::vec(0u8..4, 1..8),
        base in any::<u64>(),
        seed in any::<u64>(),
    ) {
        let p = random_prime_below(threshold(text.len(), pat.len()), seed);
        // Lean: rabinKarpSearch_eq_occurrenceList (every base)
        prop_assert_eq!(search_with(&text, &pat, base, p), naive::search(&text, &pat));
    }

    #[test]
    fn matches_naive_at_the_book_parameters(
        text in prop::collection::vec(0u8..4, 0..200),
        pat in prop::collection::vec(0u8..4, 0..8),
    ) {
        // Lean: rabinKarpSearch_eq_occurrenceList (every positive modulus, 13 included)
        prop_assert_eq!(
            search_with(&text, &pat, BOOK_BASE, BOOK_MOD),
            naive::search(&text, &pat)
        );
    }

    /// A prime below 64, so false fingerprint matches reach the verification.
    #[test]
    fn matches_naive_at_a_drawn_small_prime(
        text in prop::collection::vec(0u8..4, 0..200),
        pat in prop::collection::vec(0u8..4, 1..8),
        seed in any::<u64>(),
    ) {
        let p = random_prime_below(64, seed);
        // Lean: rabinKarpSearch_eq_occurrenceList (every positive modulus)
        prop_assert_eq!(search_with(&text, &pat, BASE, p), naive::search(&text, &pat));
    }

    /// The rolled value equals a from-scratch hash and [`reference_hash`] at every window,
    /// with every reducer the search may pick.
    #[test]
    fn the_roll_agrees_with_a_recomputed_hash_at_every_window(
        text in prop::collection::vec(any::<u8>(), 1..200),
        m in 1usize..8,
        seed in any::<u64>(),
    ) {
        prop_assume!(m <= text.len());
        fn walk<R: Reduce>(
            text: &[u8],
            m: usize,
            fingerprint: &Fingerprint,
            reduce: R,
            reference: impl Fn(&[u8]) -> u64,
        ) -> Result<(), TestCaseError> {
            let mut rolled = fingerprint.hash_of(reduce, &text[..m]);
            prop_assert_eq!(fingerprint.value(rolled), reference(&text[..m]));
            for i in 0..text.len() - m {
                rolled = fingerprint.roll(reduce, rolled, text[i], text[i + m]);
                let window = &text[i + 1..=i + m];
                prop_assert_eq!(rolled, fingerprint.hash_of(reduce, window)); // Lean: rollHash_eq
                prop_assert_eq!(fingerprint.value(rolled), reference(window));
            }
            Ok(())
        }
        fn check(text: &[u8], m: usize, base: u64, modulus: u64) -> Result<(), TestCaseError> {
            let fingerprint = Fingerprint::new(base, modulus, m);
            let reference = |window: &[u8]| reference_hash(window, base, modulus);
            walk(text, m, &fingerprint, fingerprint.modulus, reference)?;
            prop_assert_eq!(fingerprint.small_base, base % modulus <= BASE);
            if fingerprint.small_base {
                let small = SmallBase { d: fingerprint.modulus.d, wrap: &fingerprint.wrap };
                walk(text, m, &fingerprint, small, reference)?;
            }
            Ok(())
        }
        check(&text, m, BASE, random_prime_below(threshold(text.len(), m), seed))?;
        check(&text, m, BASE, random_prime_below(MAX_THRESHOLD, seed))?;
        check(&text, m, BOOK_BASE, BOOK_MOD)?;
        check(&text, m, seed, u64::MAX - seed % 1000)?;
        check(&text, m, seed, 1 + seed % 300)?;
    }

    /// Both reducers are `%` on the ranges the fingerprint arithmetic feeds them.
    #[test]
    fn the_reducer_is_the_remainder(
        q in prop_oneof![
            1u64..=300,
            (1u64 << 60)..(1u64 << 61),
            any::<u64>().prop_map(|q| q.max(1)),
        ],
        high in any::<u64>(),
        low in any::<u64>(),
    ) {
        let x = (u128::from(high % q) << 64) | u128::from(low);
        let reducer = Modulus::new(q);
        let want = u64::try_from(x % u128::from(q)).expect("below q");
        prop_assert_eq!(reducer.reduce(x), want);
        prop_assert_eq!(Reduce::reduce_scaled(reducer, x << reducer.shift), want << reducer.shift);

        let fingerprint = Fingerprint::new(BASE, q, 1);
        let small = SmallBase { d: reducer.d, wrap: &fingerprint.wrap };
        let y = (u128::from(high % 258) << 64) | u128::from(low);
        let want = u64::try_from(y % u128::from(reducer.d)).expect("below d");
        prop_assert_eq!(small.reduce_scaled(y), want);
    }

    /// A draw is a prime below its threshold, and the same seed draws the same prime.
    #[test]
    fn a_draw_is_a_prime_below_the_threshold(tau in 3u64..=MAX_THRESHOLD, seed in any::<u64>()) {
        let p = random_prime_below(tau, seed);
        prop_assert!(p < tau);
        prop_assert!(is_prime(p));
        prop_assert_eq!(p, random_prime_below(tau, seed));
    }
}

/// Miller–Rabin against trial division below 20 000, and on Carmichael numbers and strong
/// pseudoprimes to bases up to 23.
#[test]
fn is_prime_is_exact() {
    for x in 0..20_000 {
        assert_eq!(is_prime(x), trial_division(x), "{x}");
    }
    for composite in [
        561,
        1_105,
        2_047,
        1_373_653,
        25_326_001,
        3_215_031_751,
        2_152_302_898_747,
        3_474_749_660_383,
        341_550_071_728_321,
        3_825_123_056_546_413_051,
        u64::MAX,
    ] {
        assert!(!is_prime(composite), "{composite}");
    }
    for prime in [(1 << 61) - 1, 18_446_744_073_709_551_557, 4_294_967_291] {
        assert!(is_prime(prime), "{prime}");
    }
}

/// The threshold by hand at small sizes, and the cap.
#[test]
fn threshold_is_motwani_raghavan_s_clamped() {
    // N = 64, M = 24: x = 64² · 24 = 98304, ⌈log₂ 98304⌉ = 17.
    assert_eq!(threshold(8, 3), 98304 * 17);
    // N = 8, M = 8: x = 512, log₂ 512 = 9.
    assert_eq!(threshold(1, 1), 512 * 9);
    assert_eq!(threshold(0, 0), 3);
    assert_eq!(threshold(1 << 30, 1 << 20), MAX_THRESHOLD);
    assert_eq!(threshold(usize::MAX, usize::MAX), MAX_THRESHOLD);
}

/// Different seeds draw different primes.
#[test]
fn seeds_draw_different_primes() {
    let drawn: std::collections::BTreeSet<u64> = (0..64)
        .map(|seed| random_prime_below(MAX_THRESHOLD, seed))
        .collect();
    assert!(
        drawn.len() > 60,
        "{} distinct primes in 64 draws",
        drawn.len()
    );
}

/// A base near `2^64` is reduced before it enters a product.
#[test]
fn a_base_above_the_modulus_loses_no_match() {
    let base = u64::MAX - 1000;
    assert_eq!(
        search_with(b"aaaa", b"aaa", base, (1 << 61) - 1),
        vec![0, 1]
    );
}

#[test]
fn book_parameters_produce_collisions_that_verification_rejects() {
    // Mod 13 collides often; the collisions are counted, so the test is not vacuous.
    let text = b"31415926535897932384626433832795";
    SPURIOUS.with(|s| s.set(0));
    assert_eq!(
        search_with(text, b"26", BOOK_BASE, BOOK_MOD),
        naive::search(text, b"26")
    );
    let rejected = SPURIOUS.with(std::cell::Cell::get);
    assert!(
        rejected > 0,
        "no window collided with the pattern's fingerprint"
    );
}

/// The chapter's hand trace (base 10, modulus 13, digit values): 11 at 5, a match, and at 13,
/// a false alarm.
#[test]
fn book_parameters_reproduce_the_chapters_trace_on_digit_values() {
    let text: [u8; 19] = [1, 7, 6, 7, 6, 4, 0, 2, 5, 9, 2, 1, 9, 6, 5, 9, 4, 7, 8];
    let pat: [u8; 5] = [4, 0, 2, 5, 9];
    let m = pat.len();
    let fingerprint = Fingerprint::new(BOOK_BASE, BOOK_MOD, m);
    assert!(fingerprint.small_base);
    let reduce = SmallBase {
        d: fingerprint.modulus.d,
        wrap: &fingerprint.wrap,
    };

    let mut window_hash = fingerprint.hash_of(reduce, &text[..m]);
    let mut row = vec![fingerprint.value(window_hash)];
    for i in 0..text.len() - m {
        window_hash = fingerprint.roll(reduce, window_hash, text[i], text[i + m]);
        row.push(fingerprint.value(window_hash));
    }

    assert_eq!(fingerprint.value(fingerprint.hash_of(reduce, &pat)), 11);
    assert_eq!(row, [9, 12, 1, 1, 0, 11, 5, 12, 4, 0, 8, 3, 4, 11, 3]);
    let elevens: Vec<usize> = (0..row.len()).filter(|&i| row[i] == 11).collect();
    assert_eq!(elevens, [5, 13]);
    assert_ne!(text[13..13 + m], pat);
    assert_eq!(search_with(&text, &pat, BOOK_BASE, BOOK_MOD), vec![5]);
}

/// A text past `u32::MAX` bytes is refused (the zeroed text is never touched).
#[test]
#[cfg(target_pointer_width = "64")]
#[should_panic(expected = "positions are u32")]
fn a_text_past_u32_max_is_refused() {
    let _ = search_with(&vec![0u8; u32::MAX as usize + 2], &[], BASE, 13);
}

#[test]
#[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
fn a_zero_modulus_panics_once_there_is_a_window_to_fingerprint() {
    let _ = search_with(b"banana", b"an", BASE, 0);
}

#[test]
fn a_zero_modulus_is_never_reached_without_a_window() {
    assert_eq!(
        search_with(b"banana", b"", BASE, 0),
        vec![0, 1, 2, 3, 4, 5, 6]
    );
    assert_eq!(search_with(b"ab", b"abc", BASE, 0), Vec::<u32>::new());
}

/// The empty pattern occurs at every shift `0..=n`, on every entry point.
#[test]
fn the_empty_pattern_occurs_at_every_shift() {
    let every: Vec<u32> = (0..=6).collect();
    assert_eq!(search(b"banana", b""), every);
    assert_eq!(search_seeded(b"banana", b"", 7), every);
    assert_eq!(search_with(b"banana", b"", BOOK_BASE, BOOK_MOD), every);
    assert_eq!(naive::search(b"banana", b""), every);
    assert_eq!(search(b"", b""), vec![0]);
}

/// The unseeded entry point answers like every other.
#[test]
fn search_draws_its_own_prime_and_answers_exactly() {
    let text = b"abracadabra, abracadabra";
    assert_eq!(search(text, b"abra"), naive::search(text, b"abra"));
    assert_eq!(search(text, b"zz"), Vec::<u32>::new());
}

/// The reducer switches between bases 256 and 257, and both answer right near `2^64` and at
/// modulus 1.
#[test]
fn the_reducer_switches_between_bases_256_and_257() {
    let text: Vec<u8> = (0..2000u32)
        .map(|i| if i % 7 == 3 { 0xFE } else { 0xFF })
        .collect();
    let patterns: [&[u8]; 4] = [&text[..1], &text[100..105], &text[3..40], &[0xFF; 9]];
    for q in [u64::MAX, (1u64 << 63) + 1, u64::MAX - 58] {
        assert!(Fingerprint::new(256, q, 3).small_base);
        assert!(!Fingerprint::new(257, q, 3).small_base);
        for base in [255, 256, 257, 258] {
            for pat in patterns {
                assert_eq!(search_with(&text, pat, base, q), naive::search(&text, pat));
            }
        }
    }
    for pat in patterns {
        assert_eq!(search_with(&text, pat, BASE, 1), naive::search(&text, pat));
    }
}

/// Primes below 64 produce more than one rejected false match per seed.
#[test]
fn a_small_prime_reaches_the_verification() {
    let mut state = 0x2545_f491_u32;
    let text: Vec<u8> = (0..200)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            u8::try_from(state % 3).unwrap()
        })
        .collect();
    let pat = [3u8, 3, 3];
    SPURIOUS.with(|s| s.set(0));
    for seed in 0..32 {
        let p = random_prime_below(64, seed);
        assert!(search_with(&text, &pat, BASE, p).is_empty());
    }
    let rejected = SPURIOUS.with(std::cell::Cell::get);
    assert!(
        rejected > 32,
        "only {rejected} false matches rejected over 32 seeds"
    );
}

/// The scan's state is valid at every window, and each piece, corrupted alone, is named.
#[cfg(feature = "unchecked")]
#[test]
fn the_scan_state_is_valid_at_every_window() {
    let text = b"abracadabra, abracadabra";
    for (base, modulus) in [(10, 13), (256, 1_000_000_007), (BASE, (1 << 61) - 1)] {
        for m in 1..=5 {
            let pat = &text[..m];
            let states = scan_states(text, pat, base, modulus);
            assert_eq!(states.len(), text.len() - m + 1);
            for (i, (h, found)) in states.iter().enumerate() {
                let (h, found) = (*h, found.as_slice());
                assert!(
                    is_number_matches_window(base, modulus, pat, &text[i..], h),
                    "{base} {modulus} {m} {i}"
                );
                assert!(is_found_so_far_exact(text, pat, i, found), "{m} {i}");
                assert_eq!(check_valid(base, modulus, text, pat, i, h, found), Ok(()));
                assert_eq!(
                    check_valid(base, modulus, text, pat, i, (h + 1) % modulus, found),
                    Err("invariant 2 (number_matches_window)")
                );
                let mut early = found.to_vec();
                early.push(u32::try_from(i).expect("short text"));
                assert_eq!(
                    check_valid(base, modulus, text, pat, i, h, &early),
                    Err("invariant 3 (found_so_far_exact)")
                );
            }
        }
    }
}

/// `FoundSoFarExact` asks for exactly the occurrences before the cursor, in increasing order.
#[test]
fn found_so_far_is_exact_and_ascending() {
    let text = b"aaaa";
    assert!(is_found_so_far_exact(text, b"aa", 0, &[]));
    assert!(is_found_so_far_exact(text, b"aa", 2, &[0, 1]));
    assert!(is_found_so_far_exact(text, b"aa", 4, &[0, 1, 2]));
    assert!(!is_found_so_far_exact(text, b"aa", 2, &[1, 0]));
    assert!(!is_found_so_far_exact(text, b"aa", 2, &[0]));
    assert!(!is_found_so_far_exact(text, b"aa", 2, &[0, 1, 2]));
    // The empty pattern occurs at every position, the end included.
    assert!(is_found_so_far_exact(text, b"", 5, &[0, 1, 2, 3, 4]));
    // A cursor past the text has no window.
    assert_eq!(
        check_valid(10, 13, text, b"aa", 5, 0, &[0, 1, 2]),
        Err("invariant 2 (number_matches_window)")
    );
}

#[test]
fn a_zero_modulus_reduces_nothing() {
    assert!(is_number_matches_window(10, 0, b"ab", b"ab", 97 * 10 + 98));
    assert!(!is_number_matches_window(
        u64::MAX,
        0,
        &[1; 8],
        &[255; 8],
        0
    ));
}
