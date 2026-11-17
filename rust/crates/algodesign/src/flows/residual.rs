// SPDX-License-Identifier: Apache-2.0
//! The residual graph of a flow: every arrow `i` of the network paired with its reverse arrow.
//!
//! Arrow `i` gives two residual arrows, stored side by side: `along i` at index `2i`, from the
//! arrow's tail to its head, with the capacity the arrow has left, and `back i` at index
//! `2i + 1`, from its head to its tail, with the amount the arrow carries, which can be taken back.
//! So `e ^ 1` is the other arrow of `e`'s pair, and the two residual capacities of a pair
//! always add up to the arrow's capacity. Only the residual capacities are stored; the flow on
//! arrow `i` is the residual capacity of `back i` (Ahuja, Magnanti and Orlin, *Network Flows*,
//! §2.4; Cherkassky and Goldberg's stored form).
//!
//! Each vertex lists the residual arrows that leave it in input order: for each arrow id in
//! increasing order, `along i` at its tail and `back i` at its head, the order every search of the
//! topic walks a vertex's row in (first vertex labeled wins). The rows are one packed array, built
//! once by counting.
//!
//! **Against the Python, and how fast.** The same arrows, rows and ties. Here the rows are one
//! packed array and each arrow's head and residual capacity sit in arrays by index, so a search
//! reads them as plain slices; the library's rules change residual capacities in pairs in place,
//! and an outside rule sends one arrow at a time through [`Residual::send`], where the Python's
//! `augment` sends a whole path. Every max flow builds one inside its call.
//!
//! Lean counterpart: `AlgoDesign.Flows.ResidualArrow` (`Flows/MaxFlow/Spec.lean`): index `2i` is
//! `along i`, index `2i + 1` is `back i`.

use super::network::{Capacity, Network};

/// One added path: the residual arrows it takes, from the source to the sink, and the amount sent
/// along it.
///
/// Lean: `Flows.Augmentation`, arrow `2i` as `along i` and `2i + 1` as `back i`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Augmentation<C = u64> {
    /// The residual arrows, in order from the source.
    pub path: Vec<u32>,
    /// The amount sent.
    pub amount: C,
}

/// The residual graph of a flow on a network: for each residual arrow, the vertex it points to and
/// its residual capacity, and each vertex's row.
///
/// An outside path rule changes the flow through [`Residual::send`] alone, and the library's own
/// rules change the two residual capacities of a pair together the same way, so they keep adding up
/// to the arrow's capacity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Residual<C = u64> {
    pub(super) source: u32,
    pub(super) sink: u32,
    /// Where each vertex's row starts in `rows`; `n + 1` entries.
    pub(super) offsets: Vec<u32>,
    /// Every vertex's row, one after the other: the residual arrows leaving it.
    pub(super) rows: Vec<u32>,
    /// The vertex each residual arrow points to.
    pub(super) heads: Vec<u32>,
    /// The residual capacity of each residual arrow.
    pub(super) residual_capacity: Vec<C>,
    /// The paths added in the round running now, in order.
    #[cfg(any(test, feature = "unchecked"))]
    pub(super) added: Vec<Augmentation<C>>,
}

impl<C: Capacity> Residual<C> {
    /// The residual graph of the zero flow on `net`: every `along i` with arrow `i`'s capacity as
    /// its residual capacity, every `back i` with none. Linear in vertices plus arrows.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::flows::{Network, Residual};
    /// use algodesign::graphs::Digraph;
    ///
    /// let g = Digraph::new(3, &[(0, 1), (1, 2)]).unwrap();
    /// let r = Residual::new(&Network::new(g, vec![4u64, 3], 0, 2).unwrap());
    /// // Vertex 1: back 0 (index 1), then along 1 (index 2).
    /// assert_eq!(r.out(1), [1, 2]);
    /// assert_eq!((r.residual_capacity(2), r.residual_capacity(3)), (3, 0));
    /// ```
    pub fn new(net: &Network<C>) -> Self {
        let n = net.n();
        let g = net.graph();
        let m = g.arrow_count();
        let mut heads = vec![0u32; 2 * m];
        let mut residual_capacity = vec![C::ZERO; 2 * m];
        let mut offsets = vec![0u32; n + 1];
        for i in 0..m {
            let (tail, head) = g.arrow(i);
            heads[2 * i] = head;
            heads[2 * i + 1] = tail;
            residual_capacity[2 * i] = net.arrow_capacity(i);
            offsets[tail as usize + 1] += 1;
            offsets[head as usize + 1] += 1;
        }
        for v in 0..n {
            offsets[v + 1] += offsets[v];
        }
        let mut fill = offsets.clone();
        let mut rows = vec![0u32; 2 * m];
        // In index order: `along i` at its tail, then `back i` at its head, for each id in turn.
        for e in 0..2 * m {
            let at = heads[e ^ 1] as usize;
            rows[fill[at] as usize] = e as u32;
            fill[at] += 1;
        }
        Self {
            source: net.source(),
            sink: net.sink(),
            offsets,
            rows,
            heads,
            residual_capacity,
            #[cfg(any(test, feature = "unchecked"))]
            added: Vec::new(),
        }
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.offsets.len() - 1
    }

    /// Where the flow starts.
    #[must_use]
    pub fn source(&self) -> u32 {
        self.source
    }

    /// Where the flow ends.
    #[must_use]
    pub fn sink(&self) -> u32 {
        self.sink
    }

    /// The number of residual arrows: twice the network's.
    #[must_use]
    pub fn arrow_count(&self) -> usize {
        self.heads.len()
    }

    /// The residual arrows leaving `v`, in input order: for each arrow id in increasing order,
    /// `along i` (index `2i`) if `v` is its tail and `back i` (index `2i + 1`) if `v` is its head.
    ///
    /// # Panics
    ///
    /// If `v` is not a vertex.
    #[must_use]
    pub fn out(&self, v: u32) -> &[u32] {
        let v = v as usize;
        &self.rows[self.offsets[v] as usize..self.offsets[v + 1] as usize]
    }

    /// The vertex the residual arrow `e` points to.
    ///
    /// # Panics
    ///
    /// If `e` is not below [`Residual::arrow_count`].
    #[must_use]
    pub fn head(&self, e: u32) -> u32 {
        self.heads[e as usize]
    }

    /// The vertex the residual arrow `e` leaves: where the other arrow of its pair points.
    ///
    /// # Panics
    ///
    /// If `e` is not below [`Residual::arrow_count`].
    #[must_use]
    pub fn tail(&self, e: u32) -> u32 {
        self.heads[(e ^ 1) as usize]
    }

    /// The residual capacity of the residual arrow `e`.
    ///
    /// # Panics
    ///
    /// If `e` is not below [`Residual::arrow_count`].
    #[must_use]
    pub fn residual_capacity(&self, e: u32) -> C {
        self.residual_capacity[e as usize]
    }

    /// Send `amount` along the residual arrow `e`: its residual capacity shrinks by `amount` and
    /// that of the other arrow of its pair grows by as much. Along arrow `i` this adds to the
    /// arrow's flow; back against it, it takes away.
    ///
    /// # Panics
    ///
    /// If `e` is not below [`Residual::arrow_count`], or `amount` is more than its residual
    /// capacity.
    pub fn send(&mut self, e: u32, amount: C) {
        let residual_capacity = self.residual_capacity[e as usize];
        assert!(
            amount <= residual_capacity,
            "sending {amount:?} along arrow {e} with residual capacity {residual_capacity:?}"
        );
        self.push(e as usize, amount);
    }

    /// [`Residual::send`] for the library's own rules, which send at most an arrow's residual
    /// capacity.
    #[inline]
    pub(super) fn push(&mut self, e: usize, amount: C) {
        self.residual_capacity[e] = self.residual_capacity[e] - amount;
        self.residual_capacity[e ^ 1] = self.residual_capacity[e ^ 1] + amount;
    }

    /// Note a path the round running now added, for the trace of the rounds. Called only in test
    /// builds and under the `unchecked` feature.
    #[cfg(any(test, feature = "unchecked"))]
    pub(super) fn note(&mut self, path: Vec<u32>, amount: C) {
        self.added.push(Augmentation { path, amount });
    }

    /// The amount on each arrow of the network, by id: the residual capacity of `back i`.
    #[must_use]
    pub fn flow(&self) -> Vec<C> {
        self.residual_capacity
            .iter()
            .skip(1)
            .step_by(2)
            .copied()
            .collect()
    }

    /// The vertices the residual graph reaches from the source: those an arrow with residual
    /// capacity leads to, step by step. First-in-first-out, run until the queue is empty; linear in
    /// vertices plus arrows.
    ///
    /// Lean: `Flows.reached`.
    #[must_use]
    pub fn reached(&self) -> Vec<bool> {
        let n = self.n();
        let mut seen = vec![false; n];
        let mut queue = Vec::with_capacity(n);
        seen[self.source as usize] = true;
        queue.push(self.source);
        let mut head = 0;
        while head < queue.len() {
            let u = queue[head];
            head += 1;
            for &e in self.out(u) {
                let v = self.heads[e as usize];
                if self.residual_capacity[e as usize] > C::ZERO && !seen[v as usize] {
                    seen[v as usize] = true;
                    queue.push(v);
                }
            }
        }
        seen
    }
}

#[cfg(test)]
#[path = "unit_tests/residual.rs"]
mod tests;
