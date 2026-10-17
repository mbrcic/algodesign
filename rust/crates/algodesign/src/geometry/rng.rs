//! The geometry structures' random source: the crate's SplitMix64 (`crate::rng`), which the
//! Python's `_rng.SplitMix64` repeats, so a seed builds the same projection, hash tables and
//! graph in both languages.

pub(crate) use crate::rng::SplitMix64;

impl SplitMix64 {
    /// Uniform in `[0, 1)`: the top 53 bits.
    pub(crate) fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// A standard normal by Box–Muller; `1 - u` keeps the logarithm's argument in `(0, 1]`.
    pub(crate) fn standard_normal(&mut self) -> f64 {
        let (u, v) = (1.0 - self.next_f64(), self.next_f64());
        (-2.0 * u.ln()).sqrt() * (std::f64::consts::TAU * v).cos()
    }
}

/// The first `n` values of each of the generator's three draws, each from a fresh stream seeded
/// with `seed`: `next_u64`, `next_f64` and `standard_normal`. Public for tests; not part of the
/// API.
#[cfg(feature = "unchecked")]
#[doc(hidden)]
#[must_use]
pub fn draws(seed: u64, n: usize) -> (Vec<u64>, Vec<f64>, Vec<f64>) {
    let (mut a, mut b, mut c) = (
        SplitMix64::new(seed),
        SplitMix64::new(seed),
        SplitMix64::new(seed),
    );
    (
        (0..n).map(|_| a.next_u64()).collect(),
        (0..n).map(|_| b.next_f64()).collect(),
        (0..n).map(|_| c.standard_normal()).collect(),
    )
}

#[cfg(test)]
#[path = "unit_tests/rng.rs"]
mod tests;
