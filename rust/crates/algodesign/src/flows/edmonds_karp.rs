// SPDX-License-Identifier: Apache-2.0
//! Edmonds–Karp's path rule: each round sends along one augmenting path with the fewest arrows.
//!
//! A round is one first-in-first-out search from the source over the arrows with residual
//! capacity, each vertex's row walked in input order, stopped as soon as the sink is labeled. A
//! vertex keeps the arrow that labeled it first. The path those arrows lead back along from the
//! sink is sent its bottleneck, the smallest residual capacity on it. A round whose search
//! misses the sink sends nothing. This is Edmonds and Karp, "Theoretical improvements in
//! algorithmic efficiency for network flow problems" (1972), with the queue discipline "labeled
//! first, scanned first" of Ford and Fulkerson (1957), and the tie rule "first vertex labeled wins"
//! of Ahuja, Magnanti and Orlin, *Network Flows*, p. 216.
//!
//! Cost: one search, linear in vertices plus arrows, per round; at most `n m` rounds for `n`
//! vertices and `m` arrows, since a path's length never falls and each length sees each arrow
//! become the bottleneck at most once (`O(n m²)` in all).
//!
//! **Against the Python, and how fast.** The same search, the same ties and the same path. The
//! Python also returns the round's path; here the list is built only when the trace is recorded,
//! and the labels and the queue are allocated once and kept from round to round.
//!
//! Lean counterpart: `AlgoDesign.Flows.EdmondsKarp` (its rule keeps `PathRule.Promise` and meets
//! `Ops.AugmentationsAtMostNM`).

use super::max_flow::PathRule;
use super::network::Capacity;
use super::residual::Residual;

/// No label yet.
pub(super) const NONE: u32 = u32::MAX;
/// The source's label: it is where every path starts.
pub(super) const ROOT: u32 = u32::MAX - 1;

/// Edmonds–Karp's path rule: one round, one path with the fewest arrows, found by a
/// first-in-first-out search stopped when the sink is labeled.
///
/// Lean: `Flows.EdmondsKarp.rule`.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow_with, EdmondsKarp, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![5u64, 3, 4], 0, 2).unwrap();
/// assert_eq!(max_flow_with(&net, EdmondsKarp::new()).value, 7);
/// ```
#[derive(Debug, Clone, Default)]
pub struct EdmondsKarp {
    /// The arrow that labeled each vertex; `ROOT` at the source, `NONE` if unlabeled.
    label: Vec<u32>,
    /// The search's queue.
    queue: Vec<u32>,
}

impl EdmondsKarp {
    /// The rule, ready for any network.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<C: Capacity> PathRule<C> for EdmondsKarp {
    fn start(&mut self, r: &Residual<C>) {
        self.label = vec![NONE; r.n()];
        self.queue = vec![0; r.n()];
    }

    fn round(&mut self, r: &mut Residual<C>) -> bool {
        if self.label.len() != r.n() {
            PathRule::<C>::start(self, r);
        }
        if !search(r, C::ONE, &mut self.label, &mut self.queue) {
            return false;
        }
        send_along_labels(r, &self.label);
        true
    }
}

/// A first-in-first-out search from the source over the arrows with residual capacity at least
/// `at_least`, each row in input order, stopped as soon as the sink is labeled; each vertex labeled
/// with the arrow that reached it first. Whether the sink was labeled.
pub(super) fn search<C: Capacity>(
    r: &Residual<C>,
    at_least: C,
    label: &mut [u32],
    queue: &mut [u32],
) -> bool {
    let (s, t) = (r.source as usize, r.sink as usize);
    label.fill(NONE);
    label[s] = ROOT;
    queue[0] = s as u32;
    let (mut head, mut tail) = (0, 1);
    while head < tail {
        let u = queue[head] as usize;
        head += 1;
        for k in r.offsets[u] as usize..r.offsets[u + 1] as usize {
            let e = r.rows[k];
            if r.residual_capacity[e as usize] >= at_least {
                let v = r.heads[e as usize] as usize;
                if label[v] == NONE {
                    label[v] = e;
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

/// Send the bottleneck along the path the labels lead back along from the sink.
pub(super) fn send_along_labels<C: Capacity>(r: &mut Residual<C>, label: &[u32]) {
    let (s, t) = (r.source as usize, r.sink as usize);
    let mut amount = C::MAX;
    let mut v = t;
    while v != s {
        let e = label[v] as usize;
        amount = amount.min(r.residual_capacity[e]);
        v = r.heads[e ^ 1] as usize;
    }
    let mut v = t;
    while v != s {
        let e = label[v] as usize;
        r.push(e, amount);
        v = r.heads[e ^ 1] as usize;
    }
    watched!({
        let mut path = Vec::new();
        let mut v = t;
        while v != s {
            path.push(label[v]);
            v = r.heads[label[v] as usize ^ 1] as usize;
        }
        path.reverse();
        r.note(path, amount);
    });
}

#[cfg(test)]
#[path = "unit_tests/edmonds_karp.rs"]
mod tests;
