# SPDX-License-Identifier: Apache-2.0
"""SplitMix64, the seeded generator every randomized structure in the library draws from.

It is the Rust's generator (`rust/crates/algodesign/src/rng.rs`) written out again, so a seed
gives the same integers and the same uniform draws in both languages: the same priorities in a
treap, the same levels in a graph, the same hyperplanes in a hash table. The normal draw goes
through `ln`, `sqrt` and `cos`, whose last bits may differ between runtimes, so the tests check it
to 1e-15 rather than exactly.

Steele, Lea and Flood (2014); Vigna's `splitmix64.c`.
"""

from __future__ import annotations

import math

MASK = (1 << 64) - 1


class SplitMix64:
    """A 64-bit state advanced by a fixed odd constant, then scrambled into each output."""

    def __init__(self, seed: int) -> None:
        self.state = seed & MASK

    def next_u64(self) -> int:
        """The next 64-bit integer."""
        self.state = (self.state + 0x9E3779B97F4A7C15) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        return z ^ (z >> 31)

    def next_f64(self) -> float:
        """Uniform in [0, 1): the top 53 bits."""
        return (self.next_u64() >> 11) / (1 << 53)

    def standard_normal(self) -> float:
        """A standard normal by Box-Muller; `1 - u` keeps the logarithm's argument in (0, 1]."""
        u = 1.0 - self.next_f64()
        v = self.next_f64()
        return math.sqrt(-2.0 * math.log(u)) * math.cos(math.tau * v)
