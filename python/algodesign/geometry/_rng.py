# SPDX-License-Identifier: Apache-2.0
"""SplitMix64 for the geometry structures: the library's one generator, `algodesign._rng`, so a
seed builds the same projection, hash tables and graph in Python and Rust."""

from __future__ import annotations

from .._rng import MASK, SplitMix64

__all__ = ["MASK", "SplitMix64"]
