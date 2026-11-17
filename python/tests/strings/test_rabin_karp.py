# SPDX-License-Identifier: Apache-2.0
"""Rabin-Karp, checked the way `rust/crates/algodesign/src/strings/rabin_karp.rs` checks it.

The property tests mirror that module's proptests and the fixed cases it pins, so that the Python
rendering and the Rust production layer are held to the same statements rather than to two
independently chosen ones.
"""

import random
from typing import Any
from unittest import mock

import pytest
from hypothesis import assume, given
from hypothesis import strategies as st

from algodesign.strings import naive, rabin_karp
from algodesign.strings.rabin_karp import (
    BASE,
    BOOK_BASE,
    BOOK_MOD,
    MAX_THRESHOLD,
    _hash_of,
    _high_power,
    _roll,
    check_valid,
    is_found_so_far_exact,
    is_number_matches_window,
    is_prime,
    random_prime_below,
    search,
    threshold,
)

from .rk_watch import carried_numbers

# The book's pair, and base 256 at a prime drawn by the library's own rule from a fixed seed.
PARAMETERS = [(BOOK_BASE, BOOK_MOD), (BASE, random_prime_below(MAX_THRESHOLD, random.Random(5)))]

# Alphabet `{0, 1, 2, 3}`, the Rust proptests' `0u8..4`. It includes `SENTINEL` (0) and
# `SEPARATOR` (1) deliberately: Rabin-Karp reserves no byte -- it is a search over arbitrary
# bytes, and the modules that do reserve those two (`bwt`, `records`) refuse them at their own
# boundary, not here. Generating them is the check that this module has no hidden opinion about
# them. A four-letter alphabet is also what makes `BOOK_MOD = 13` collide often enough for the
# verification step to be exercised rather than merely present.
SYMBOLS = st.integers(min_value=0, max_value=3)
texts = st.lists(SYMBOLS, max_size=200).map(bytes)
patterns = st.lists(SYMBOLS, min_size=0, max_size=7).map(bytes)
nonempty_texts = st.lists(SYMBOLS, min_size=1, max_size=200).map(bytes)


@given(texts, patterns, st.integers(min_value=0, max_value=2**64 - 1))
def test_matches_naive_at_a_drawn_prime(text: bytes, pattern: bytes, seed: int) -> None:
    """`search`, at whatever prime the seed draws, returns exactly `naive.search`'s answer -- the
    empty pattern included, which the pattern strategy reaches.

    Mirrors `matches_naive_at_a_drawn_prime`. `text` may be shorter than `pattern`, which is how
    the pattern-longer-than-text guard gets exercised.
    """
    assert search(text, pattern, rng=random.Random(seed)) == naive.search(text, pattern)


@given(texts, patterns)
def test_matches_naive_at_the_book_parameters(text: bytes, pattern: bytes) -> None:
    """Mirrors `matches_naive_at_the_book_parameters`."""
    assert search(text, pattern, base=BOOK_BASE, mod=BOOK_MOD) == naive.search(text, pattern)


@given(st.integers(min_value=3, max_value=MAX_THRESHOLD), st.integers(min_value=0))
def test_a_draw_is_a_prime_below_the_threshold(tau: int, seed: int) -> None:
    """Mirrors `a_draw_is_a_prime_below_the_threshold`: a prime, below `tau`, and the same one
    again from the same seed."""
    p = random_prime_below(tau, random.Random(seed))
    assert p < tau and is_prime(p)
    assert p == random_prime_below(tau, random.Random(seed))


def _trial_division(x: int) -> bool:
    return x >= 2 and all(x % d for d in range(2, int(x**0.5) + 1))


def test_is_prime_is_exact() -> None:
    """Mirrors `is_prime_is_exact`: trial division below 20 000, Carmichael numbers, and the strong
    pseudoprimes that fool every prime witness up to 23, which only 29, 31 and 37 expose."""
    for x in range(20_000):
        assert is_prime(x) == _trial_division(x), x
    for composite in (561, 1_105, 2_047, 1_373_653, 25_326_001, 3_215_031_751,
                      2_152_302_898_747, 3_474_749_660_383, 341_550_071_728_321,
                      3_825_123_056_546_413_051, 2**64 - 1):
        assert not is_prime(composite), composite
    for prime in (2**61 - 1, 18_446_744_073_709_551_557, 4_294_967_291):
        assert is_prime(prime), prime


def test_threshold_is_motwani_raghavan_s_clamped() -> None:
    """Mirrors `threshold_is_motwani_raghavan_s_clamped`: `x * ceil(log2 x)`, `x = N*N*M` with both
    lengths in bits, `N = 8n`, `M = 8m`."""
    # N = 64, M = 24: x = 64 * 64 * 24 = 98304, ceil(log2 98304) = 17.
    assert threshold(8, 3) == 98304 * 17
    # N = 8, M = 8: x = 512, log2 512 = 9.
    assert threshold(1, 1) == 512 * 9
    assert threshold(0, 0) == 3
    assert threshold(2**30, 2**20) == MAX_THRESHOLD


def test_seeds_draw_different_primes() -> None:
    """Mirrors `seeds_draw_different_primes`: the draw is not a constant in disguise."""
    drawn = {random_prime_below(MAX_THRESHOLD, random.Random(seed)) for seed in range(64)}
    assert len(drawn) > 60


@given(nonempty_texts, st.integers(min_value=1, max_value=7))
def test_the_roll_agrees_with_a_recomputed_hash_at_every_window(text: bytes, m: int) -> None:
    """The rolling step's *value*, at every window, against a hash recomputed from scratch.

    Mirrors `the_roll_agrees_with_a_recomputed_hash_at_every_window`, and exists for the reason
    that test gives: `test_matches_naive_at_a_drawn_prime` sees the roll only through an
    answer that byte-verifies every hash hit, so it would stay green on a roll that was wrong
    everywhere except at the true occurrences -- correct answers, and a filter degraded back to
    O(n*m). That is the property the whole module is for, so it is checked directly. `_roll` is a
    function rather than three lines inside `search`'s loop precisely so this comparison runs
    against the shipped arithmetic.

    Lean: `rollHash_eq` (one slide equals recomputing the hash from scratch); this test holds the
    shipped `_roll` to it.
    """
    assume(m <= len(text))
    for base, modulus in PARAMETERS:
        high = _high_power(m, base, modulus)
        rolled = _hash_of(text[:m], base, modulus)
        for i in range(len(text) - m):
            rolled = _roll(rolled, text[i], text[i + m], base, high, modulus)
            assert rolled == _hash_of(text[i + 1 : i + 1 + m], base, modulus)


def test_only_the_pattern_and_the_first_window_are_hashed_from_scratch() -> None:
    """The roll is the algorithm: after the first window, every fingerprint comes from the one
    before it in O(1). Hashing each window afresh gives the same fingerprints -- the test above
    cannot tell -- at O(m) per window. So `_hash_of` runs exactly twice per search, however long
    the text, at both parameter sets."""
    rng = random.Random(11)
    for n in (3, 10, 200):
        text = bytes(rng.choice(b"abc") for _ in range(n))
        for m in (1, 2, 3):
            for base, modulus in PARAMETERS:
                with mock.patch.object(
                    rabin_karp, "_hash_of", wraps=rabin_karp._hash_of
                ) as hash_of:
                    found = search(text, text[1 : 1 + m], base=base, mod=modulus)
                assert found == naive.search(text, text[1 : 1 + m])
                assert hash_of.call_count == 2, (n, m, hash_of.call_count)


class _Window(bytes):
    """A window cut out of a `_WatchedText`, which reports every comparison made with it."""

    start: int
    log: list[tuple[int, bool]]

    def __eq__(self, other: object) -> bool:
        result = bytes(self) == other
        self.log.append((self.start, result))
        return result

    def __hash__(self) -> int:
        return bytes.__hash__(self)


class _WatchedText(bytes):
    """Bytes whose slices are `_Window`s: every byte comparison `search` makes on a window --
    its verification step -- is recorded as `(start, equal?)` in `log`."""

    log: list[tuple[int, bool]]

    def __getitem__(self, index: Any) -> Any:
        value = super().__getitem__(index)
        if isinstance(index, slice):
            window = _Window(value)
            window.start = index.indices(len(self))[0]
            window.log = self.log
            return window
        return value


def test_book_parameters_produce_collisions_that_verification_rejects() -> None:
    """Modulus 13 collides constantly on a small alphabet; the verify step makes the answer
    identical anyway. The digits of pi as ASCII bytes -- not the chapter's trace, which the next
    test reproduces.

    Watched from inside `search`: it verifies exactly the windows whose fingerprint equals the
    pattern's, and at least one of those is a collision it rejects. A search that quietly used
    other parameters -- a large drawn prime, say -- would give the same answer with no
    collision to reject, and fails here."""
    text = b"31415926535897932384626433832795"
    pattern = b"26"
    m = len(pattern)
    target = _hash_of(pattern, BOOK_BASE, BOOK_MOD)
    fingerprint_hits = [
        i
        for i in range(len(text) - m + 1)
        if _hash_of(text[i : i + m], BOOK_BASE, BOOK_MOD) == target
    ]
    watched = _WatchedText(text)
    watched.log = []
    assert search(watched, pattern, base=BOOK_BASE, mod=BOOK_MOD) == naive.search(text, pattern)
    assert naive.search(text, pattern) == [6, 21]
    verified = [start for start, _ in watched.log]
    rejected = [start for start, equal in watched.log if not equal]
    assert verified == fingerprint_hits
    assert rejected, "no collision reached the verification step"
    assert sorted(set(verified) - set(rejected)) == [6, 21]


def test_book_parameters_reproduce_the_chapters_trace_on_digit_values() -> None:
    """The chapter's hand trace: text 1767640259219659478, pattern 40259, base 10, modulus 13. The
    trace's characters are digit values, so they go in as `bytes([1, 7, 6, ...])`; ASCII
    `b"1767..."` would shift every fingerprint. The pattern hashes to 11, the rolled row of window
    fingerprints is the chapter's, and 11 comes up twice: at 5, a match, and at 13, where 65947 is
    the false alarm the byte comparison rejects."""
    text = bytes(int(c) for c in "1767640259219659478")
    pattern = bytes(int(c) for c in "40259")
    m = len(pattern)

    high = _high_power(m, BOOK_BASE, BOOK_MOD)
    window_hash = _hash_of(text[:m], BOOK_BASE, BOOK_MOD)
    row = [window_hash]
    for i in range(len(text) - m):
        window_hash = _roll(window_hash, text[i], text[i + m], BOOK_BASE, high, BOOK_MOD)
        row.append(window_hash)

    assert _hash_of(pattern, BOOK_BASE, BOOK_MOD) == 11
    assert row == [9, 12, 1, 1, 0, 11, 5, 12, 4, 0, 8, 3, 4, 11, 3]
    assert [i for i, fingerprint in enumerate(row) if fingerprint == 11] == [5, 13]
    assert text[13 : 13 + m] == bytes([6, 5, 9, 4, 7]) != pattern
    assert search(text, pattern, base=BOOK_BASE, mod=BOOK_MOD) == [5]


def test_the_empty_pattern_occurs_at_every_shift() -> None:
    """The chapter's convention, as in the Rust's `the_empty_pattern_occurs_at_every_shift`: `n + 1`
    positions, the last one past the final byte, whatever the parameters."""
    every = list(range(7))
    assert search(b"banana", b"") == every
    assert search(b"banana", b"", base=BOOK_BASE, mod=BOOK_MOD) == every
    assert naive.search(b"banana", b"") == every
    assert search(b"", b"") == [0]


@given(texts, patterns)
def test_search_needs_no_parameters(text: bytes, pattern: bytes) -> None:
    """A first call passes a text and a pattern and nothing else: the base defaults to 256 and the
    modulus is drawn. Every other test here passes one or the other, so without this one a
    `search` that needed them -- a `TypeError` on a student's first call -- would pass them
    all."""
    assert search(text, pattern) == naive.search(text, pattern)


def test_the_parameters_are_keyword_only() -> None:
    """Swapped positionally, `base` and `mod` would still give the right answer, since every hit
    is verified; keyword-only is what makes the swap impossible to write."""
    with pytest.raises(TypeError):
        search(b"banana", b"an", BOOK_BASE, BOOK_MOD)  # type: ignore[call-arg]


def test_positions_are_reported_in_increasing_order() -> None:
    assert search(b"banana", b"ana") == [1, 3]
    assert search(b"aaaa", b"aa", base=BOOK_BASE, mod=BOOK_MOD) == [0, 1, 2]


def test_a_zero_modulus_raises_once_there_is_a_window_to_fingerprint() -> None:
    """A fingerprint modulo zero has no value, so the search refuses the modulus as soon as it
    would need one. Where the Rust panics, the Python raises the package's `ValueError`."""
    with pytest.raises(ValueError, match="modulus must be positive"):
        search(b"banana", b"an", mod=0)
    with pytest.raises(ValueError, match="modulus must be positive"):
        search(b"banana", b"an", mod=-7)


def test_a_zero_modulus_is_never_reached_without_a_window() -> None:
    """The `Raises:` note is exact about this: both answers come before any reduction."""
    assert search(b"banana", b"", mod=0) == list(range(7))
    assert search(b"ab", b"abc", mod=0) == []


def test_no_prime_lies_below_two() -> None:
    with pytest.raises(ValueError):
        random_prime_below(2, random.Random(0))


def test_the_scan_state_is_valid_at_every_window() -> None:
    """Mirrors `the_scan_state_is_valid_at_every_window`: `RabinKarp.Valid` at every window, with
    the number the real `search` carries there (`rk_watch`), and each piece, corrupted alone,
    named."""
    text = b"abracadabra, abracadabra"
    for base, mod in [(10, 13), (256, 1_000_000_007), (BASE, (1 << 61) - 1)]:
        for m in range(1, 6):
            pat = text[:m]
            carried = carried_numbers(text, pat, base, mod)
            assert len(carried) == len(text) - m + 1
            answer = search(text, pat, base=base, mod=mod)
            for i, h in enumerate(carried):
                found = [j for j in answer if j < i]
                assert is_number_matches_window(base, mod, pat, text[i:], h)
                assert is_found_so_far_exact(text, pat, i, found)
                assert check_valid(base, mod, text, pat, start=i, carried=h, found=found) is None
                assert check_valid(
                    base, mod, text, pat, start=i, carried=(h + 1) % mod, found=found
                ) == (
                    "invariant 2 (number_matches_window)"
                )
                assert check_valid(base, mod, text, pat, start=i, carried=h, found=[*found, i]) == (
                    "invariant 3 (found_so_far_exact)"
                )


def test_found_so_far_is_exact_and_ascending() -> None:
    """Mirrors `found_so_far_is_exact_and_ascending`."""
    text = b"aaaa"
    assert is_found_so_far_exact(text, b"aa", 0, [])
    assert is_found_so_far_exact(text, b"aa", 2, [0, 1])
    assert is_found_so_far_exact(text, b"aa", 4, [0, 1, 2])
    assert not is_found_so_far_exact(text, b"aa", 2, [1, 0])
    assert not is_found_so_far_exact(text, b"aa", 2, [0])
    assert not is_found_so_far_exact(text, b"aa", 2, [0, 1, 2])
    # The empty pattern occurs at every position, the end included.
    assert is_found_so_far_exact(text, b"", 5, [0, 1, 2, 3, 4])
    # A cursor past the text has no window.
    assert check_valid(10, 13, text, b"aa", start=5, carried=0, found=[0, 1, 2]) == (
        "invariant 2 (number_matches_window)"
    )


def test_a_zero_modulus_reduces_nothing() -> None:
    assert is_number_matches_window(10, 0, b"ab", b"ab", 97 * 10 + 98)
