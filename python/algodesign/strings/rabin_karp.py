# SPDX-License-Identifier: Apache-2.0
"""Rabin-Karp string matching (CLRS §32.2), with the modulus a prime drawn at random.

Reduce each length-m window of the text to a number -- its fingerprint: the window read as a
radix-`base` number, modulo `mod` -- and compare numbers instead of strings. Sliding the window
one position updates the fingerprint in O(1): remove the leaving character's contribution, shift by
one digit, add the entering character.

Two different windows can collide, so every fingerprint match is confirmed by comparing the bytes,
as CLRS's RABIN-KARP-MATCHER does: a collision costs a wasted comparison, never a wrong answer.

**Why the modulus is drawn.** Motwani-Raghavan §7.6 fingerprints a window read as an integer
modulo a prime `p` "chosen uniformly at random from the set of primes smaller than a threshold τ",
and with `τ = N² M log(N² M)` (text and pattern measured in bits) a false match anywhere in the
text has probability `O(1/N)`, over that draw. So the verified search runs in expected O(n + m)
whatever the text is: no text is bad for every prime, and an adversary who does not know the prime
cannot force the collisions. A byte is eight bits, so the window as an integer is its radix-256
value (`BASE`), and `threshold(n, m)` is their τ with `N = 8n` and `M = 8m`. A *fixed* public
modulus has no such bound: anyone who knows it can build a text in which many windows collide with
the pattern and force the O(n*m) worst case. Passing `mod` fixes the modulus and gives that up.

τ is capped at `MAX_THRESHOLD` (`2**61`); for texts of a few megabytes the cap binds.

`BOOK_BASE`/`BOOK_MOD` give the chapter's hand trace when the characters are the digit *values*
0-9 -- `bytes([1, 7, 6, 7, ...])`, not `b"1767..."`.

The Rust differs here: a slide reads the leaving byte's weight from a table, and its prime comes
from `SplitMix64`, so one seed does not give one prime in both.

The Lean statements behind this module, in `lean/AlgoDesign/Strings/RabinKarp/` (specification:
`RabinKarp/Spec.lean`):
`rabinKarpSearch_eq_occurrenceList`, `rollHash_eq`.
"""

from __future__ import annotations

import random

BOOK_BASE = 10
"""The base the chapter traces by hand, with `BOOK_MOD`, over digit values 0-9."""

BOOK_MOD = 13
"""The modulus the chapter traces by hand, over digit values 0-9.

Small and collision-prone on a decimal alphabet on purpose, so that the verification step is
exercised on the printed page rather than merely asserted there.
"""

BASE = 256
"""The base the library runs: one digit per byte, so a window's fingerprint is the window read as
an integer, modulo the drawn prime -- Motwani-Raghavan's fingerprint exactly."""

MAX_THRESHOLD = 2**61
"""The largest threshold `threshold` returns; every drawn prime is below it."""

_WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def threshold(n: int, m: int) -> int:
    """Motwani-Raghavan's τ for an `n`-byte text and an `m`-byte pattern: `x * ceil(log2(x))` with
    `x = N*N*M`, both sizes in bits, `N = 8n` and `M = 8m`. Kept between 3 and `MAX_THRESHOLD`.
    """
    x = (8 * n) * (8 * n) * (8 * m)
    tau = x * (x - 1).bit_length() if x >= 2 else 0
    return min(max(tau, 3), MAX_THRESHOLD)


def is_prime(x: int) -> bool:
    """Whether `x` is prime: Miller-Rabin with the first twelve primes as witnesses, exact below
    3.18 * 10**23 (Sorenson and Webster, 2017)."""
    if x < 2:
        return False
    for p in _WITNESSES:
        if x % p == 0:
            return x == p
    d, s = x - 1, 0
    while d % 2 == 0:
        d, s = d // 2, s + 1
    for a in _WITNESSES:
        y = pow(a, d, x)
        if y in (1, x - 1):
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def random_prime_below(tau: int, rng: random.Random) -> int:
    """A prime drawn uniformly from the primes below `tau`: draw integers uniformly below `tau` and
    keep the first prime.

    Raises:
        ValueError: if `tau < 3`, which has no prime below it.
    """
    if tau < 3:
        raise ValueError(f"rabin_karp.random_prime_below: no prime lies below {tau}")
    while True:
        x = rng.randrange(tau)
        if is_prime(x):
            return x


def _high_power(m: int, base: int, mod: int) -> int:
    """`base ** (m - 1) % mod` -- CLRS's `h`, the weight of the character that leaves the window."""
    high = 1
    for _ in range(1, m):
        high = high * base % mod
    return high


def _hash_of(window: bytes, base: int, mod: int) -> int:
    """The fingerprint of `window`, computed from scratch by Horner's rule."""
    value = 0
    for character in window:
        value = (value * base + character) % mod
    return value


def _roll(ht: int, leaving: int, entering: int, base: int, high: int, mod: int) -> int:
    """One slide, the chapter's line: drop the leaving character, shift by one digit, add the
    entering one, all modulo `mod`. Python's `%` lands in `[0, mod)` even after a negative
    subtraction."""
    return ((ht - leaving * high) * base + entering) % mod


def search(
    text: bytes,
    pattern: bytes,
    *,
    base: int = BASE,
    mod: int | None = None,
    rng: random.Random | None = None,
) -> list[int]:
    """Every start position at which `pattern` occurs in `text`, in increasing order.

    Fingerprint the pattern once, roll a fingerprint across the text in O(1) per slide, and compare
    bytes only where the two fingerprints agree; a position is reported only after that comparison
    succeeds. Every occurrence is reported, overlapping ones included: `search(b"aaaa", b"aa")` is
    `[0, 1, 2]`. The empty pattern occurs at every shift `0..n` -- `n + 1` positions, CLRS's
    convention -- and a pattern longer than the text nowhere. The FM-index agrees: it searches its
    text without the sentinel, one byte shorter, so `FMIndex(t).count(b"")` is `len(t)`.

    `mod` is drawn by `random_prime_below(threshold(n, m), rng)` unless given; a seeded `rng`
    repeats a run exactly. Pass `base=BOOK_BASE, mod=BOOK_MOD`, and digit values as the characters,
    to follow the chapter's trace.

    Raises:
        ValueError: if `mod` is not positive, once there is a window to fingerprint (a non-empty
            pattern no longer than the text); the two answers before that need no modulus.
    """
    n, m = len(text), len(pattern)
    if m == 0:
        return list(range(n + 1))
    if m > n:
        return []
    if mod is not None and mod < 1:
        raise ValueError(f"rabin_karp.search: the modulus must be positive, got {mod}")
    if mod is None:
        mod = random_prime_below(threshold(n, m), rng if rng is not None else random.Random())
    high = _high_power(m, base, mod)
    hp = _hash_of(pattern, base, mod)
    ht = _hash_of(text[:m], base, mod)
    result: list[int] = []
    for i in range(n - m + 1):
        if hp == ht and text[i:i + m] == pattern:  # verify to rule out a collision
            result.append(i)
        if i < n - m:
            ht = _roll(ht, text[i], text[i + m], base, high, mod)
    return result


def is_number_matches_window(
    base: int, mod: int, pattern: bytes, rest: bytes, carried: int
) -> bool:
    """Box invariant 2: the number kept is always the current window's number. The
    Lean `RabinKarp.NumberMatchesWindow`: `carried` is the fingerprint of the first `len(pattern)`
    bytes of `rest`, computed from scratch by Horner's rule."""
    value = 0
    for character in rest[: len(pattern)]:
        value = value * base + character
        if mod != 0:
            value %= mod
    return value == carried


def is_found_so_far_exact(text: bytes, pattern: bytes, start: int, found: list[int]) -> bool:
    """Box invariant 3: equal numbers only make a window a candidate: every candidate is checked
    letter by letter before it is reported. The Lean `RabinKarp.FoundSoFarExact`: `found` is
    exactly the occurrences of `pattern` in `text` before `start`, in increasing order."""
    exact = [i for i in range(len(text) + 1) if i < start and text[i:].startswith(pattern)]
    return found == exact


def check_valid(
    base: int, mod: int, text: bytes, pattern: bytes, *, start: int, carried: int, found: list[int]
) -> str | None:
    """The first piece of the Lean `RabinKarp.Valid` the scan's state breaks, or `None`. The scan
    stands at `start` with `carried` and `found`; a `start` past the text has no window, so its
    number matches none. The scan's state is passed by name, as `search`'s `base` and `mod` are,
    so that two of its numbers cannot be swapped unnoticed."""
    if start > len(text) or not is_number_matches_window(
            base, mod, pattern, text[start:], carried):
        return "invariant 2 (number_matches_window)"
    if not is_found_so_far_exact(text, pattern, start, found):
        return "invariant 3 (found_so_far_exact)"
    return None


def is_valid(
    base: int, mod: int, text: bytes, pattern: bytes, *, start: int, carried: int, found: list[int]
) -> bool:
    """The Lean `RabinKarp.Valid`: its two pieces. Lean: `RabinKarp.valid_roll` keeps it through
    one slide."""
    return check_valid(base, mod, text, pattern, start=start, carried=carried, found=found) is None
