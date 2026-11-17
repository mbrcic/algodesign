// SPDX-License-Identifier: Apache-2.0
//! Dinic with scaling: each round is a round of Dinic's over the arrows whose residual capacity is
//! at least a threshold Δ, the rule's memory from one round to the next, as in capacity scaling.
//!
//! Δ starts at the largest power of two not above the largest capacity of any arrow. A round runs
//! Dinic's round, the layers of a first-in-first-out search and one walk with a current-arrow
//! pointer per vertex, over the arrows with residual capacity at least Δ only, so every path it
//! sends carries at least Δ. When the layers miss the sink, the round halves Δ and tries again. An
//! arrow needs residual capacity above zero at any threshold, so Δ = 0 searches as Δ = 1 does; when
//! the layers at Δ = 1 miss the sink, the round sends nothing and Δ is zero. This is capacity
//! scaling with the shortest augmenting path algorithm as its subroutine (Ahuja, Magnanti and
//! Orlin, *Network Flows*, §7.4, p. 220, "Application to Capacity Scaling Algorithm"); Dinic's
//! rounds as that subroutine, with Δ in the search and in the walk, are this library's choice
//! (KACTL's `Dinic.h` keeps it in the search only).
//!
//! Cost: at most `n` rounds per threshold for `n` vertices, each `O(n m)` for `m` arrows:
//! `O(n² m log U)` for the largest capacity `U`.
//!
//! **Against the Python, and how fast.** The Python also returns the round's paths; here the list
//! is built only when the trace is recorded, and the arrays are Dinic's, allocated once per run.
//! It is not taught and has no Lean counterpart.

use super::capacity_scaling::largest_capacity;
use super::max_flow::PathRule;
use super::network::Capacity;
#[cfg(any(test, feature = "unchecked"))]
use super::residual::Augmentation;
use super::residual::Residual;

/// No layer: not labeled by the round's search.
const NONE: u32 = u32::MAX;

/// Dinic with scaling: one round of Dinic's over the arrows with residual capacity at least the
/// threshold, the threshold halved inside the round when the layers miss the sink.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow_with, DinicScaling, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![5u64, 3, 4], 0, 2).unwrap();
/// assert_eq!(max_flow_with(&net, DinicScaling::new()).value, 7);
/// ```
#[derive(Debug, Clone, Default)]
pub struct DinicScaling<C = u64> {
    /// The threshold Δ, kept from round to round.
    threshold: C,
    /// Whether the rule is started and not yet spent: set by [`PathRule::start`], cleared by a
    /// round that sends nothing.
    started: bool,
    /// Each vertex's layer; `NONE` if the search did not label it.
    layer: Vec<u32>,
    /// The search's queue.
    queue: Vec<u32>,
    /// Each vertex's current arrow, as a position in the packed rows.
    current: Vec<u32>,
    /// The walk's path from the source, as residual arrows.
    path: Vec<u32>,
}

impl<C: Capacity> DinicScaling<C> {
    /// The rule, ready for any network: [`PathRule::start`] sets the first threshold.
    #[must_use]
    pub fn new() -> Self {
        Self {
            threshold: C::ZERO,
            started: false,
            layer: Vec::new(),
            queue: Vec::new(),
            current: Vec::new(),
            path: Vec::new(),
        }
    }

    /// The threshold Δ now: the least residual capacity every arrow of the next path must have.
    pub fn threshold(&self) -> C {
        self.threshold
    }

    /// The layers by a first-in-first-out search from the source over the arrows with residual
    /// capacity at least `at_least`, stopped as soon as the sink is labeled. Whether it was.
    fn layers(&mut self, r: &Residual<C>, at_least: C) -> bool {
        let (s, t) = (r.source as usize, r.sink as usize);
        // The arrays are bound once, so the loop reads them as plain slices.
        let (offsets, rows, heads, residual_capacity) = (
            &r.offsets[..],
            &r.rows[..],
            &r.heads[..],
            &r.residual_capacity[..],
        );
        let layer = &mut self.layer[..];
        let queue = &mut self.queue[..];
        layer.fill(NONE);
        layer[s] = 0;
        queue[0] = s as u32;
        let (mut head, mut tail) = (0, 1);
        while head < tail {
            let u = queue[head] as usize;
            head += 1;
            let next = layer[u] + 1;
            for &e in &rows[offsets[u] as usize..offsets[u + 1] as usize] {
                let e = e as usize;
                if residual_capacity[e] >= at_least {
                    let v = heads[e] as usize;
                    if layer[v] == NONE {
                        layer[v] = next;
                        if v == t {
                            return true;
                        }
                        queue[tail] = v as u32;
                        tail += 1;
                    }
                }
            }
        }
        false
    }

    /// One walk through the layers over the arrows with residual capacity at least `at_least`,
    /// sending every path it finds, as Dinic's round does.
    fn walk(&mut self, r: &mut Residual<C>, at_least: C) {
        let (s, t) = (r.source as usize, r.sink as usize);
        let n = r.n();
        // The arrays are bound once, so the loop reads them as plain slices.
        let (offsets, rows, heads) = (&r.offsets[..], &r.rows[..], &r.heads[..]);
        let residual_capacity = &mut r.residual_capacity[..];
        let layer = &self.layer[..];
        let current = &mut self.current[..];
        let path = &mut self.path;
        let sink_layer = layer[t];
        current.copy_from_slice(&offsets[..n]);
        path.clear();
        let mut u = s;
        loop {
            if u == t {
                let mut amount = C::MAX;
                for &e in path.iter() {
                    amount = amount.min(residual_capacity[e as usize]);
                }
                for &e in path.iter() {
                    let e = e as usize;
                    residual_capacity[e] = residual_capacity[e] - amount;
                    residual_capacity[e ^ 1] = residual_capacity[e ^ 1] + amount;
                }
                watched!(r.added.push(Augmentation {
                    path: path.clone(),
                    amount
                }));
                // Start again from the source.
                path.clear();
                u = s;
                continue;
            }
            let mut stepped = false;
            // A vertex on the sink's layer other than the sink is a dead end at once.
            if layer[u] < sink_layer {
                let end = offsets[u + 1];
                let deeper = layer[u] + 1;
                while current[u] < end {
                    let e = rows[current[u] as usize];
                    let v = heads[e as usize] as usize;
                    if residual_capacity[e as usize] >= at_least && layer[v] == deeper {
                        path.push(e);
                        u = v;
                        stepped = true;
                        break;
                    }
                    current[u] += 1;
                }
            }
            if !stepped {
                // A dead end: step back and move the tail's pointer past the arrow into it.
                match path.pop() {
                    // The source is a dead end: the round ends.
                    None => break,
                    Some(e) => {
                        u = heads[(e ^ 1) as usize] as usize;
                        current[u] += 1;
                    }
                }
            }
        }
    }
}

impl<C: Capacity> PathRule<C> for DinicScaling<C> {
    /// Δ, the largest power of two not above the largest capacity of any arrow, each capacity read
    /// as the residual capacities of its pair added up: on the zero flow, the largest residual
    /// capacity.
    fn start(&mut self, r: &Residual<C>) {
        let n = r.n();
        self.threshold = largest_capacity(r).power_of_two_below();
        self.started = true;
        self.layer = vec![NONE; n];
        self.queue = vec![0; n];
        self.current = vec![0; n];
        self.path = Vec::with_capacity(n);
    }

    /// Dinic's round at the largest threshold whose layers still reach the sink, or nothing when
    /// not even Δ = 1 has them reach it. A rule not started for a network of this many vertices
    /// starts itself first, its threshold read from the capacities; so does a rule whose last round
    /// sent nothing, so a second run starts afresh. Between rounds the threshold is kept.
    fn round(&mut self, r: &mut Residual<C>) -> bool {
        if !self.started || self.layer.len() != r.n() {
            PathRule::<C>::start(self, r);
        }
        loop {
            // An arrow needs residual capacity above zero at any threshold: Δ = 0 searches as Δ = 1
            // does.
            let at_least = self.threshold.max(C::ONE);
            if self.layers(r, at_least) {
                self.walk(r, at_least);
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

#[cfg(test)]
#[path = "unit_tests/dinic_scaling.rs"]
mod tests;
