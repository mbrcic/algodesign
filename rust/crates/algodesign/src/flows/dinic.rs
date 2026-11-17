// SPDX-License-Identifier: Apache-2.0
//! Dinic's path rule in the Even–Itai form, the library's default: each round sends a blocking
//! flow through the layers of one search.
//!
//! A first-in-first-out search from the source over the arrows with residual capacity, each row in
//! input order and stopped as soon as the sink is labeled, gives each vertex it labels a layer, its
//! distance from the source. An arrow is admissible when it has residual capacity and goes exactly
//! one layer deeper. A vertex on the sink's layer other than the sink is a dead end as soon as the
//! walk reaches it, its row not scanned, so every path sent ends at the sink. Then one depth-first
//! walk over admissible arrows, each vertex with a pointer to its current arrow, set to the first
//! of its row at the start of the round. The walk follows the current arrow from the vertex it
//! stands at; at a vertex whose pointer has run past its row, a dead end, it steps back along the
//! last arrow and moves that arrow's tail's pointer one on. On reaching the sink it sends the
//! path's bottleneck along it and starts again from the source. The round ends when the source's
//! pointer has run past its row; a round whose search misses the sink sends nothing. The walk keeps
//! its path on an explicit stack, so a deep network cannot exhaust the call stack. This is Dinic,
//! "Algorithm for solution of a problem of maximum flow in a network with power estimation" (1970),
//! in the form of Even and Itai (Even, *Graph Algorithms*, 1979; Dinitz, "Dinitz' algorithm: the
//! original version and Even's version", 2006), with Ahuja, Magnanti and Orlin, *Network Flows*,
//! pp. 216 and 222, for the pointers and the order.
//!
//! Cost: at most `n` rounds for `n` vertices, since the sink's layer grows every round; each
//! round's search is linear, and its walk `O(n m)` for `m` arrows, since each path takes at most
//! `n` arrows and saturates one, and each dead end moves a pointer for good. `O(n² m)` in all.
//!
//! **Against the Python, and how fast.** The same layers, the same walk and the same ties. The
//! Python also returns the round's paths; here the list is built only when the trace is recorded.
//! The layers, the queue, the pointers and the path are allocated once per run, and a round reads
//! the packed rows as plain slices.
//!
//! Lean counterpart: `AlgoDesign.Flows.Dinic` (its rule keeps `PathRule.Promise` and meets
//! `Ops.RoundsAtMostN`).

use super::max_flow::PathRule;
use super::network::Capacity;
#[cfg(any(test, feature = "unchecked"))]
use super::residual::Augmentation;
use super::residual::Residual;

/// No layer: not labeled by the round's search.
const NONE: u32 = u32::MAX;

/// Dinic's path rule in the Even–Itai form: one round sends a blocking flow along the layers of a
/// first-in-first-out search, by one walk with a current-arrow pointer per vertex that starts
/// again from the source after each path.
///
/// Lean: `Flows.Dinic.rule`.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow_with, Dinic, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![5u64, 3, 4], 0, 2).unwrap();
/// assert_eq!(max_flow_with(&net, Dinic::new()).value, 7);
/// ```
#[derive(Debug, Clone, Default)]
pub struct Dinic {
    /// Each vertex's layer; `NONE` if the search did not label it.
    layer: Vec<u32>,
    /// The search's queue.
    queue: Vec<u32>,
    /// Each vertex's current arrow, as a position in the packed rows.
    current: Vec<u32>,
    /// The walk's path from the source, as residual arrows.
    path: Vec<u32>,
    /// The steps of each round's walk, recorded in test builds and under the `unchecked` feature
    /// only.
    #[cfg(any(test, feature = "unchecked"))]
    sweep_steps: Vec<usize>,
}

impl Dinic {
    /// The rule, ready for any network.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The number of steps of each round's walk that sent something, in order. A step is one
    /// move along an admissible arrow, one move of a pointer, one dead end (back one arrow, its
    /// tail's pointer moved past it) or one path sent, and the last step, which finds the source a
    /// dead end and ends the round; starting again from the source is no step itself, but its
    /// moves along arrows are counted again. Only in test builds and under the `unchecked`
    /// feature.
    ///
    /// Lean: `dinicSweepSteps`.
    #[cfg(any(test, feature = "unchecked"))]
    #[must_use]
    pub fn sweep_steps(&self) -> &[usize] {
        &self.sweep_steps
    }

    /// The layers by a first-in-first-out search from the source over the arrows with residual
    /// capacity, stopped as soon as the sink is labeled. Whether it was.
    fn layers<C: Capacity>(&mut self, r: &Residual<C>) -> bool {
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
                if residual_capacity[e] > C::ZERO {
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
}

impl<C: Capacity> PathRule<C> for Dinic {
    fn start(&mut self, r: &Residual<C>) {
        let n = r.n();
        self.layer = vec![NONE; n];
        self.queue = vec![0; n];
        self.current = vec![0; n];
        watched!(self.sweep_steps.clear());
        self.path = Vec::with_capacity(n);
    }

    fn round(&mut self, r: &mut Residual<C>) -> bool {
        if self.layer.len() != r.n() {
            PathRule::<C>::start(self, r);
        }
        if !self.layers(r) {
            return false;
        }
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
        watched!(let mut steps = 0usize;);
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
                watched!(steps += 1);
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
                    if residual_capacity[e as usize] > C::ZERO && layer[v] == deeper {
                        path.push(e);
                        watched!(steps += 1);
                        u = v;
                        stepped = true;
                        break;
                    }
                    current[u] += 1;
                    watched!(steps += 1);
                }
            }
            if !stepped {
                // A dead end: step back and move the tail's pointer past the arrow into it.
                match path.pop() {
                    None => {
                        // The source is a dead end: this last step ends the round.
                        watched!(steps += 1);
                        break;
                    }
                    Some(e) => {
                        u = heads[(e ^ 1) as usize] as usize;
                        current[u] += 1;
                        watched!(steps += 1);
                    }
                }
            }
        }
        watched!(self.sweep_steps.push(steps));
        true
    }
}

#[cfg(test)]
#[path = "unit_tests/dinic.rs"]
mod tests;
