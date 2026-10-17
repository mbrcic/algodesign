# SPDX-License-Identifier: Apache-2.0
"""The generator matches the Rust's, so a seed builds the same structures in both languages.

The values were printed by the Rust's `SplitMix64` (`rust/crates/algodesign/src/geometry/rng.rs`).
The integers and the uniform draws are pinned exactly. The normal draws go through `ln`, `sqrt`
and `cos`, whose last bits may differ between runtimes, so they are checked to 1e-15 relative.
"""

from __future__ import annotations

import math

import pytest

from algodesign.geometry._rng import SplitMix64

U64_0 = [
    16294208416658607535,
    7960286522194355700,
    487617019471545679,
    17909611376780542444,
    1961750202426094747,
    6038094601263162090,
    3207296026000306913,
    14232521865600346940,
    4532161160992623299,
    17561866513979060390,
]
F64_0 = [
    0.8833108082136426,
    0.43152799704850997,
    0.026433771592597743,
    0.9708819781538285,
    0.10634669156721244,
    0.32732576421812576,
    0.17386786595968284,
    0.771546556331567,
    0.24568894884013137,
    0.9520306913678265,
]
NORMAL_0 = [
    -1.8839083333524405,
    0.22760793546360525,
    -0.22143788059715477,
    0.08341854419566393,
    0.7170826494218734,
    0.06961828150383062,
    -1.1459220136058275,
    -1.558991217105635,
    0.10815806473571521,
    0.377441935140085,
]

U64_42 = [
    13679457532755275413,
    2949826092126892291,
    5139283748462763858,
    6349198060258255764,
    701532786141963250,
    16015981125662989062,
    4028864712777624925,
    14769051326987775908,
    6270620877612482005,
    11408980392250668974,
]
F64_42 = [
    0.7415648787718233,
    0.1599103928769201,
    0.27860113025513866,
    0.34419071652363753,
    0.03803016854024621,
    0.8682280765465323,
    0.21840519371218436,
    0.8006318767135033,
    0.3399310389170206,
    0.6184820663561348,
]
NORMAL_42 = [
    0.8822489062222688,
    -0.4508498757188601,
    0.1883526341159315,
    0.219586379190761,
    -0.6703714655421094,
    -0.676527986719054,
    -1.1907770929543502,
    0.42664665906935234,
    -0.46744487648429395,
    -0.1657685144281162,
]

CASES = [(0, U64_0, F64_0, NORMAL_0), (42, U64_42, F64_42, NORMAL_42)]


@pytest.mark.parametrize(("seed", "u64", "f64", "normal"), CASES, ids=["seed 0", "seed 42"])
def test_the_streams_match_the_rust(
    seed: int, u64: list[int], f64: list[float], normal: list[float]
) -> None:
    rng = SplitMix64(seed)
    assert [rng.next_u64() for _ in range(10)] == u64
    rng = SplitMix64(seed)
    assert [rng.next_f64() for _ in range(10)] == f64
    rng = SplitMix64(seed)
    for got, want in zip([rng.standard_normal() for _ in range(10)], normal, strict=True):
        assert math.isclose(got, want, rel_tol=1e-15, abs_tol=0.0)
