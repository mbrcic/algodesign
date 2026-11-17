// SPDX-License-Identifier: Apache-2.0
//! Push-relabel: a largest flow by heights and excess, highest vertex first, with the gap and
//! global relabel steps.
//!
//! Where max flow's loop keeps a flow from the start and stops when no augmenting path is left,
//! push-relabel keeps a cut's promise from the start and makes the flow legal at the end. It begins
//! by filling every arrow that leaves the source, so the vertices those arrows reach hold more than
//! they pass on, an excess. Each vertex has a height, a lower bound on the number of arrows with
//! residual capacity between it and the sink: the sink stands at 0, the source at `n` for `n`
//! vertices, and no arrow with residual capacity drops by more than one. A vertex with an excess
//! pushes along an arrow with residual capacity that goes exactly one down, as much as the excess
//! and the residual capacity allow; when no such arrow is left, it is relabeled one above the
//! lowest vertex its arrows with residual capacity reach. The procedure is Goldberg and Tarjan's,
//! "A new approach to the maximum-flow problem" (1988); its first phase is as in Cherkassky and
//! Goldberg, "On implementing the push-relabel method for the maximum flow problem" (1997), with
//! Ahuja, Magnanti and Orlin, *Network Flows*, ch. 7, for the steps:
//!
//! - **Highest first.** Each height keeps a stack of the vertices with an excess standing there;
//!   the vertex taken next is the last one put on the highest stack that holds one. It pushes from
//!   its current arrow on, in its row's input order, until its excess is gone, or relabels when
//!   its row runs out; the current arrow returns to the start of the row after a relabel (AMO
//!   pp. 216–217, 231–233).
//! - **The gap step.** When a relabel leaves a height below `n` with no vertex at all, no vertex
//!   above that height can reach the sink any more: all of them go up to `n` at once (AMO p. 230).
//! - **Global relabels.** A first-in-first-out search backward from the sink over the arrows with
//!   residual capacity, each row in input order, the first vertex labeled keeping its label, gives
//!   every vertex its exact count of arrows to the sink, and `n` to the source and to every vertex
//!   that cannot reach the sink (AMO p. 230). One runs at the start, on the filled source arrows,
//!   and then again after every `n` relabels, as in Cherkassky and Goldberg.
//! - **Two phases.** The first phase works only on vertices below `n`, so it ends with the largest
//!   amount in the sink and some excess stranded on vertices that cannot reach it: a preflow, and
//!   the cut is already final. The second phase runs the same pushes and relabels, highest first,
//!   on the stranded excess with the gap step and global relabels off, along the arrows that carry
//!   flow only, until all of it is back in the source (AMO Exercise 7.11(d): delete the arrows that
//!   carry no flow); heights stay below `2n` (AMO p. 228). The answer is then a flow. Cherkassky
//!   and Goldberg return the excess by decomposing the preflow instead.
//!
//! The answer has max flow's shape ([`MaxFlow`]): the flow, its amount, and the source's side of a
//! minimum cut, the vertices the final residual graph reaches from the source. Arrows are filled
//! from the source only to other vertices, so a loop carries nothing, as in max flow.
//!
//! Cost: `O(n m + n² √m)` for `n` vertices and `m` arrows, which is `O(n² √m)` when no two arrows
//! share both ends (`m ≤ n²`). The first phase is the highest-first rule's bound (Cheriyan and
//! Maheshwari, "Analysis of preflow push algorithms for maximum network flow", 1989; AMO Theorem
//! 7.19), with global relabels and the gap step inside it: each global relabel is one search,
//! linear in vertices plus arrows, and the gap step only raises heights to `n`. The second phase,
//! which uses only arrows that carry flow, is `O(n m + n^{5/2})`; AMO Exercise 7.11(d) states
//! `O(n m)` for it. That bound is argued here, not proved: in the second phase heights stay below
//! `2n`, so each vertex is relabeled at most `2n` times; an arrow back that a push empties stays
//! empty, so at most `m` pushes empty one; and AMO Theorem 7.19's count of the other pushes, on the
//! arrows that carry flow, gives `O(n^{5/2} + m √n)`.
//!
//! The pushes, relabels, gap steps and global relabels are counted only in test builds and under
//! the `unchecked` feature (`push_relabel_with_counts`).
//!
//! **Against the Python, and how fast.** The same procedure and ties: the Python keeps the vertices
//! of each height in a set and its stacks in lists, where here they are linked through arrays, and
//! its gap step looks at every height above the empty one, where here it goes up only to a kept
//! bound on the highest height in use.
//!
//! Lean counterpart: `AlgoDesign.Flows.PushRelabel` (`Flows/PushRelabel.lean`): the promise is
//! argued, not proved; an answer that passes max flow's checks is a largest flow
//! (`PushRelabel.largest_of_passesChecks`).

use super::max_flow::MaxFlow;
use super::network::{Capacity, Network};
use super::residual::Residual;

/// No vertex: the end of a list.
const NONE: u32 = u32::MAX;

/// How often each step ran: pushes along arrows after the source's arrows were filled, relabels in
/// both phases, gap steps, and global relabels, the one at the start included. Only in test builds
/// and under the `unchecked` feature.
#[cfg(any(test, feature = "unchecked"))]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Counts {
    /// Pushes along one arrow each.
    pub pushes: u64,
    /// Relabels, each lifting one vertex.
    pub relabels: u64,
    /// Gap steps, each after a relabel left a height empty.
    pub gaps: u64,
    /// Backward searches from the sink, the first one included.
    pub global_relabels: u64,
}

/// A largest flow from the source to the sink of `net`, and the source's side of a cut of the same
/// amount, by push-relabel: highest vertex first, with the gap step and global relabels, then a
/// second phase that returns the stranded excess to the source. `O(n m + n² √m)`, so `O(n² √m)`
/// when no two arrows share both ends.
///
/// The same answer type as [`max_flow`](super::max_flow()), with the same amount and the same side:
/// the vertices a largest flow's residual graph reaches from the source are the same for every
/// largest flow. The flow may differ where the largest flow is not unique.
///
/// Lean: `PushRelabel.PushRelabelPromise` (argued), `PushRelabel.largest_of_passesChecks`.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow, push_relabel, Network};
/// use algodesign::graphs::Digraph;
///
/// // 0 → 1 → 3 and 0 → 2 → 3, and 1 → 2 between them.
/// let g = Digraph::new(4, &[(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]).unwrap();
/// let net = Network::new(g, vec![3u64, 2, 2, 1, 3], 0, 3).unwrap();
/// let answer = push_relabel(&net);
/// assert_eq!(answer.value, 4);
/// assert_eq!(answer.value, max_flow(&net).value);
/// assert_eq!(answer.side, [true, true, true, false]);
/// ```
#[must_use]
pub fn push_relabel<C: Capacity + TryFrom<u64>>(net: &Network<C>) -> MaxFlow<C> {
    let mut run = Run::new(net);
    run.first_phase();
    run.second_phase();
    run.answer()
}

/// [`push_relabel`], with how often each step ran. Only in test builds and under the `unchecked`
/// feature.
#[cfg(any(test, feature = "unchecked"))]
pub fn push_relabel_with_counts<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
) -> (MaxFlow<C>, Counts) {
    let mut run = Run::new(net);
    run.first_phase();
    run.second_phase();
    (run.answer(), run.counts)
}

/// One run: the residual graph, each vertex's height, excess and current arrow, the vertices of
/// each height below `n`, and the stacks of vertices with an excess.
struct Run<C> {
    r: Residual<C>,
    n: usize,
    s: usize,
    t: usize,
    /// Each vertex's height: below `2n`.
    height: Vec<u32>,
    /// What each vertex holds more than it passed on; the source's is never read.
    excess: Vec<u64>,
    /// Each vertex's current arrow, as a position in the packed rows.
    current: Vec<u32>,
    /// The number of vertices at each height below `n`.
    count: Vec<u32>,
    /// The first vertex at each height below `n`, `NONE` for none: the lists the gap step lifts.
    first: Vec<u32>,
    /// The vertex after each in its height's list.
    next: Vec<u32>,
    /// The vertex before each in its height's list.
    prev: Vec<u32>,
    /// The top of each height's stack of vertices with an excess, `2n` heights.
    top: Vec<u32>,
    /// The vertex below each on its stack.
    below: Vec<u32>,
    /// At least the highest height whose stack is not empty.
    level: usize,
    /// At least the highest height below `n` with a vertex.
    highest: usize,
    /// The backward search's queue.
    queue: Vec<u32>,
    /// Relabels since the last global relabel.
    relabels_since: usize,
    #[cfg(any(test, feature = "unchecked"))]
    counts: Counts,
}

impl<C: Capacity + TryFrom<u64>> Run<C> {
    /// Fill every arrow from the source to another vertex, then the first global relabel.
    fn new(net: &Network<C>) -> Self {
        let n = net.n();
        let mut run = Self {
            r: Residual::new(net),
            n,
            s: net.source() as usize,
            t: net.sink() as usize,
            height: vec![0; n],
            excess: vec![0; n],
            current: vec![0; n],
            count: vec![0; n],
            first: vec![NONE; n],
            next: vec![NONE; n],
            prev: vec![NONE; n],
            top: vec![NONE; 2 * n],
            below: vec![NONE; n],
            level: 0,
            highest: 0,
            queue: vec![0; n],
            relabels_since: 0,
            #[cfg(any(test, feature = "unchecked"))]
            counts: Counts::default(),
        };
        let s = run.s;
        for k in run.r.offsets[s] as usize..run.r.offsets[s + 1] as usize {
            let e = run.r.rows[k] as usize;
            let v = run.r.heads[e] as usize;
            let residual_capacity = run.r.residual_capacity[e];
            if residual_capacity > C::ZERO && v != s {
                run.r.push(e, residual_capacity);
                run.excess[v] += residual_capacity.to_u64();
            }
        }
        run.global_relabel();
        run
    }

    /// Exact heights by a first-in-first-out search backward from the sink over the arrows with
    /// residual capacity, the source and every vertex that cannot reach the sink at `n`; then the
    /// lists and the stacks built again, and every current arrow back at the start of its row.
    fn global_relabel(&mut self) {
        let (n, s, t) = (self.n, self.s, self.t);
        let unlabeled = n as u32;
        self.height.fill(unlabeled);
        self.height[t] = 0;
        self.queue[0] = t as u32;
        let (mut head, mut tail) = (0, 1);
        while head < tail {
            let v = self.queue[head] as usize;
            head += 1;
            let up = self.height[v] + 1;
            // An arrow `e` leaving `v` pairs with `e ^ 1`, which enters `v` from `u`.
            for k in self.r.offsets[v] as usize..self.r.offsets[v + 1] as usize {
                let e = self.r.rows[k] as usize;
                let u = self.r.heads[e] as usize;
                if u != s
                    && self.height[u] == unlabeled
                    && self.r.residual_capacity[e ^ 1] > C::ZERO
                {
                    self.height[u] = up;
                    self.queue[tail] = u as u32;
                    tail += 1;
                }
            }
        }
        self.first.fill(NONE);
        self.count.fill(0);
        self.top.fill(NONE);
        self.level = 0;
        self.highest = 0;
        self.current.copy_from_slice(&self.r.offsets[..n]);
        for v in 0..n {
            let h = self.height[v] as usize;
            if v != s && h < n {
                self.insert(v, h);
                if v != t && self.excess[v] > 0 {
                    self.activate(v, h);
                }
            }
        }
        self.relabels_since = 0;
        watched!(self.counts.global_relabels += 1);
    }

    /// Put `v` at the front of the list of height `h`, below `n`.
    fn insert(&mut self, v: usize, h: usize) {
        let f = self.first[h];
        self.next[v] = f;
        self.prev[v] = NONE;
        if f != NONE {
            self.prev[f as usize] = v as u32;
        }
        self.first[h] = v as u32;
        self.count[h] += 1;
        self.highest = self.highest.max(h);
    }

    /// Take `v` out of the list of height `h`.
    fn remove(&mut self, v: usize, h: usize) {
        let (p, x) = (self.prev[v], self.next[v]);
        if p == NONE {
            self.first[h] = x;
        } else {
            self.next[p as usize] = x;
        }
        if x != NONE {
            self.prev[x as usize] = p;
        }
        self.count[h] -= 1;
    }

    /// Put `v` on the stack of height `h`.
    fn activate(&mut self, v: usize, h: usize) {
        self.below[v] = self.top[h];
        self.top[h] = v as u32;
        self.level = self.level.max(h);
    }

    /// The vertex with an excess on the highest stack, taken off it; `None` when every stack is
    /// empty. An entry whose vertex has since moved to another height or lost its excess is
    /// dropped on the way.
    fn highest_active(&mut self) -> Option<usize> {
        loop {
            let h = self.level;
            while self.top[h] != NONE {
                let v = self.top[h] as usize;
                self.top[h] = self.below[v];
                if self.height[v] as usize == h && self.excess[v] > 0 {
                    return Some(v);
                }
            }
            if h == 0 {
                return None;
            }
            self.level -= 1;
        }
    }

    /// Push from `u` along its current arrow on, until its excess is gone; when its row runs out,
    /// relabel it.
    fn discharge(&mut self, u: usize, first_phase: bool) {
        let end = self.r.offsets[u + 1];
        while self.current[u] < end {
            let e = self.r.rows[self.current[u] as usize] as usize;
            let residual_capacity = self.r.residual_capacity[e];
            if residual_capacity > C::ZERO && usable(e, first_phase) {
                let v = self.r.heads[e] as usize;
                if self.height[u] == self.height[v] + 1 {
                    // The excess may not fit `C`; then it is more than the residual capacity.
                    let amount = C::try_from(self.excess[u])
                        .map_or(residual_capacity, |x| x.min(residual_capacity));
                    self.r.push(e, amount);
                    watched!(self.counts.pushes += 1);
                    self.excess[u] -= amount.to_u64();
                    if self.excess[v] == 0 && v != self.s && v != self.t {
                        self.activate(v, self.height[v] as usize);
                    }
                    self.excess[v] += amount.to_u64();
                    if self.excess[u] == 0 {
                        // The arrow may still have residual capacity: it stays the current one.
                        return;
                    }
                }
            }
            self.current[u] += 1;
        }
        self.relabel(u, first_phase);
    }

    /// Lift `u` one above the lowest other vertex its arrows with residual capacity reach, its
    /// current arrow at the start of its row. In the first phase no higher than `n`, and the gap
    /// step follows when its old height is left empty; `u` goes back on a stack if it stays below
    /// `n`. In the second phase it always goes back on a stack.
    fn relabel(&mut self, u: usize, first_phase: bool) {
        let (start, end) = (self.r.offsets[u] as usize, self.r.offsets[u + 1] as usize);
        let mut lowest = u32::MAX;
        for k in start..end {
            let e = self.r.rows[k] as usize;
            let v = self.r.heads[e] as usize;
            // A loop leads back to `u` itself and says nothing about the way down.
            if self.r.residual_capacity[e] > C::ZERO && v != u && usable(e, first_phase) {
                lowest = lowest.min(self.height[v]);
            }
        }
        // A vertex with an excess has an arrow with residual capacity back toward the source; in
        // the second phase one that carries flow, since flow brought the excess there.
        debug_assert!(
            lowest != u32::MAX,
            "vertex {u} has an excess and no arrow with residual capacity"
        );
        self.current[u] = start as u32;
        self.relabels_since += 1;
        watched!(self.counts.relabels += 1);
        let n = self.n;
        if first_phase {
            let old = self.height[u] as usize;
            let new = (lowest as usize + 1).min(n);
            self.remove(u, old);
            self.height[u] = new as u32;
            if new < n {
                self.insert(u, new);
            }
            if self.count[old] == 0 {
                self.gap(old);
            }
            let h = self.height[u] as usize;
            if h < n {
                self.activate(u, h);
                self.level = h;
            }
        } else {
            let h = lowest as usize + 1;
            self.height[u] = h as u32;
            self.activate(u, h);
            self.level = h;
        }
    }

    /// The gap step: no vertex is left at height `empty`, so every vertex above it goes to `n`.
    fn gap(&mut self, empty: usize) {
        watched!(self.counts.gaps += 1);
        let n = self.n as u32;
        for h in empty + 1..=self.highest {
            let mut v = self.first[h];
            while v != NONE {
                self.height[v as usize] = n;
                v = self.next[v as usize];
            }
            self.first[h] = NONE;
            self.count[h] = 0;
        }
        // The sink stays at height 0, so `empty` is at least 1.
        self.highest = empty - 1;
    }

    /// The first phase: vertices below `n`, highest first, with a global relabel after every `n`
    /// relabels; it ends when no vertex below `n` has an excess.
    fn first_phase(&mut self) {
        loop {
            if self.relabels_since >= self.n {
                self.global_relabel();
            }
            match self.highest_active() {
                Some(u) => self.discharge(u, true),
                None => break,
            }
        }
    }

    /// The second phase: every vertex still holding an excess, highest first, until all of it is
    /// back in the source, along arrows that carry flow only (`usable`).
    fn second_phase(&mut self) {
        let (n, s, t) = (self.n, self.s, self.t);
        self.top.fill(NONE);
        self.level = 0;
        self.current.copy_from_slice(&self.r.offsets[..n]);
        for v in 0..n {
            if v != s && v != t && self.excess[v] > 0 {
                self.activate(v, self.height[v] as usize);
            }
        }
        while let Some(u) = self.highest_active() {
            self.discharge(u, false);
        }
    }

    /// The flow, its amount, what reached the sink, and the vertices the residual graph reaches
    /// from the source.
    fn answer(&self) -> MaxFlow<C> {
        MaxFlow {
            value: self.excess[self.t],
            flow: self.r.flow(),
            side: self.r.reached(),
        }
    }
}

/// Whether the residual arrow `e` may be used: every arrow in the first phase; in the second only
/// an arrow back against arrow `e / 2`, whose residual capacity is that arrow's flow, so excess
/// returns only along the flow that brought it (the arrows that carry no flow deleted; Ahuja,
/// Magnanti and Orlin, Exercise 7.11(d)).
fn usable(e: usize, first_phase: bool) -> bool {
    first_phase || e % 2 == 1
}

#[cfg(test)]
#[path = "unit_tests/push_relabel.rs"]
mod tests;
