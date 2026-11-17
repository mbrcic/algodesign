// SPDX-License-Identifier: Apache-2.0
//! Capacity scaling: each round sends along one augmenting path whose every arrow has residual
//! capacity at least a threshold Δ, the rule's memory from one round to the next.
//!
//! Δ starts at the largest power of two not above the largest capacity of any arrow. A round runs
//! Edmonds–Karp's search over the arrows with residual capacity at least Δ only and sends the path
//! it finds its bottleneck, which is at least Δ. When the search misses the sink, the round halves
//! Δ and searches again. An arrow needs residual capacity above zero at any threshold, so Δ = 0
//! searches as Δ = 1 does; when that search misses the sink the round sends nothing, Δ is zero, and
//! the search was one over every arrow with residual capacity. This is the capacity-scaling
//! algorithm of Ahuja and Orlin (Ahuja, Magnanti and Orlin, *Network Flows*, §7.3) and of Cormen,
//! Leiserson, Rivest and Stein, *Introduction to Algorithms*, 4th ed., Problem 24-5, one path per
//! round.
//!
//! Cost: one search, linear in vertices plus arrows, per path and per halving: `O(m² log U)` for
//! `m` arrows and the largest capacity `U`, since each threshold sends at most `2m` paths.
//!
//! **Against the Python, and how fast.** As Edmonds–Karp's rule, whose search and sending it
//! shares; the threshold only narrows the search.
//!
//! Lean counterpart: `AlgoDesign.Flows.CapacityScaling` (its rule keeps `PathRule.Promise`).

use super::edmonds_karp::{search, send_along_labels, NONE};
use super::max_flow::PathRule;
use super::network::Capacity;
use super::residual::Residual;

/// Capacity scaling: one round, one path whose every arrow has residual capacity at least the
/// threshold, the threshold halved inside the round when no such path is left.
///
/// Lean: `Flows.CapacityScaling.rule`, the threshold its memory.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow_with, CapacityScaling, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![5u64, 3, 4], 0, 2).unwrap();
/// assert_eq!(max_flow_with(&net, CapacityScaling::new()).value, 7);
/// ```
#[derive(Debug, Clone, Default)]
pub struct CapacityScaling<C = u64> {
    /// The threshold Δ, kept from round to round.
    threshold: C,
    /// Whether the rule is started and not yet spent: set by [`PathRule::start`], cleared by a
    /// round that sends nothing.
    started: bool,
    /// The arrow that labeled each vertex in the last search.
    label: Vec<u32>,
    /// The search's queue.
    queue: Vec<u32>,
}

impl<C: Capacity> CapacityScaling<C> {
    /// The rule, ready for any network: [`PathRule::start`] sets the first threshold.
    #[must_use]
    pub fn new() -> Self {
        Self {
            threshold: C::ZERO,
            started: false,
            label: Vec::new(),
            queue: Vec::new(),
        }
    }

    /// The threshold Δ now: the least residual capacity every arrow of the next path must have.
    pub fn threshold(&self) -> C {
        self.threshold
    }
}

impl<C: Capacity> PathRule<C> for CapacityScaling<C> {
    /// Δ, the largest power of two not above the largest capacity of any arrow, each capacity read
    /// as the residual capacities of its pair added up: on the zero flow, the largest residual
    /// capacity.
    fn start(&mut self, r: &Residual<C>) {
        self.threshold = largest_capacity(r).power_of_two_below();
        self.started = true;
        self.label = vec![NONE; r.n()];
        self.queue = vec![0; r.n()];
    }

    /// One path at the largest threshold that still has one, or nothing when not even Δ = 1 has
    /// one. A rule not started for a network of this many vertices starts itself first, its
    /// threshold read from the capacities; so does a rule whose last round sent nothing, so a
    /// second run starts afresh. Between rounds the threshold is kept.
    fn round(&mut self, r: &mut Residual<C>) -> bool {
        if !self.started || self.label.len() != r.n() {
            PathRule::<C>::start(self, r);
        }
        loop {
            // An arrow needs residual capacity above zero at any threshold: Δ = 0 searches as Δ = 1
            // does.
            let at_least = self.threshold.max(C::ONE);
            if search(r, at_least, &mut self.label, &mut self.queue) {
                send_along_labels(r, &self.label);
                return true;
            }
            if self.threshold <= C::ONE {
                // Δ = 0 would search exactly as Δ = 1 just did.
                self.threshold = C::ZERO;
                self.started = false;
                return false;
            }
            self.threshold = self.threshold.half();
        }
    }
}

/// The largest capacity of any arrow, each read as the residual capacities of its pair added up;
/// zero when there is no arrow.
pub(super) fn largest_capacity<C: Capacity>(r: &Residual<C>) -> C {
    r.residual_capacity
        .chunks_exact(2)
        .map(|pair| pair[0] + pair[1])
        .max()
        .unwrap_or(C::ZERO)
}

#[cfg(test)]
#[path = "unit_tests/capacity_scaling.rs"]
mod tests;
