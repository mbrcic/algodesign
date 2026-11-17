# SPDX-License-Identifier: Apache-2.0
"""The number Rabin-Karp's `search` carries at each window, read off the real `search`.

Box invariant 2 says the number kept is always the current window's number. To test that of the
code the book prints, and not of a second copy of its loop, `carried_numbers` runs
`rabin_karp.search` itself and records what its two arithmetic steps hand back: the from-scratch
fingerprint of the first window (`_hash_of`, the last of its two calls; the first is the
pattern's), then each slide's result (`_roll`). If the loop's rolling ever changes, what is
recorded changes with it.

`test_rabin_karp.py` uses this module. It is a helper, not a test module: it holds no test, and it imports nothing
but the library and the standard library.
"""

from __future__ import annotations

from unittest import mock

from algodesign.strings import rabin_karp


def carried_numbers(text: bytes, pattern: bytes, base: int, mod: int) -> list[int]:
    """The number `rabin_karp.search(text, pattern, base=base, mod=mod)` carries at each window,
    in order: one per window, none when there is no window to fingerprint."""
    hashes: list[int] = []
    rolled: list[int] = []
    real_hash, real_roll = rabin_karp._hash_of, rabin_karp._roll

    def hash_spy(window: bytes, base: int, mod: int) -> int:
        hashes.append(real_hash(window, base, mod))
        return hashes[-1]

    def roll_spy(ht: int, leaving: int, entering: int, base: int, high: int, mod: int) -> int:
        rolled.append(real_roll(ht, leaving, entering, base, high, mod))
        return rolled[-1]

    with (mock.patch.object(rabin_karp, "_hash_of", hash_spy),
          mock.patch.object(rabin_karp, "_roll", roll_spy)):
        rabin_karp.search(text, pattern, base=base, mod=mod)
    return [hashes[-1], *rolled] if hashes else []
