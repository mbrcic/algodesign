// SPDX-License-Identifier: Apache-2.0
//! A topological order of a directed graph: every arrow goes forward in it. Two methods, each with
//! its own answer when there is none.
//!
//! [`topological_order`] is Kahn's method with a FIFO queue, as Weiss, *Data Structures and
//! Algorithm Analysis in C++*, 4th ed., §9.2, Fig. 9.7: count the arrows entering each vertex,
//! queue every vertex whose count is 0 scanning from vertex 0 upward, then repeatedly take the
//! front, append it to the order and lower the count of each vertex its row reaches, queueing a
//! vertex when its count reaches 0. When vertices remain unplaced, the answer is the stuck set,
//! every one of them (Ahuja, Magnanti and Orlin, *Network Flows*, pp. 77–78): A ↔ B → C leaves all
//! three.
//!
//! [`dfs_order`] is the reverse of a depth-first search's finishing order (CLRS 4th ed., §20.4),
//! with roots from vertex 0 upward and an explicit stack of frames, each a vertex and its next row
//! position (Tarjan and Zwick 2024, §6.1). A vertex is marked when its frame is pushed, and the
//! search advances one arrow at a time. An arrow to a vertex whose frame is still on the stack
//! closes a cycle, returned as w, …, v, w: the vertices from w up to v on the stack, then w again.
//!
//! Loops and doubled arrows are accepted: a loop makes its vertex wait on itself (Kahn: stuck;
//! DFS: the cycle v, v), and a doubled arrow counts twice. Neither method recurses on the call
//! stack, so a path of any length is safe.
//!
//! [`KahnState`] is a state of Kahn's walk, with one check per piece of the Lean `Valid` on it.
//!
//! Lean counterpart: `AlgoDesign.Graphs.TopoOrder`.

use std::fmt;

use super::digraph::Digraph;

/// Kahn's answer when there is no topological order: the vertices never placed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stuck {
    /// Every vertex not placed, in increasing order; never empty.
    pub vertices: Vec<u32>,
}

impl fmt::Display for Stuck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "no order: vertices {:?} wait forever", self.vertices)
    }
}

impl std::error::Error for Stuck {}

/// The depth-first search's answer when there is no topological order: one cycle, named.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cycle {
    /// The cycle w, …, v, w: each vertex has an arrow to the next, and the last is the first.
    /// A loop at v is v, v.
    pub vertices: Vec<u32>,
}

impl fmt::Display for Cycle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "no order: the cycle {:?}", self.vertices)
    }
}

impl std::error::Error for Cycle {}

/// Kahn's topological order, or the stuck set. Linear in vertices plus arrows.
///
/// The order itself serves as the queue: a vertex is appended when its count reaches 0, and a read
/// position walks it, so the queue is the order's unread tail.
///
/// # Errors
///
/// [`Stuck`] with every vertex left unplaced when the graph has a cycle.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{topological_order, Digraph};
///
/// // 2 must come before 0, and 0 before 1.
/// let g = Digraph::new(3, &[(2, 0), (0, 1)]).unwrap();
/// assert_eq!(topological_order(&g).unwrap(), [2, 0, 1]);
///
/// // A ↔ B → C: every vertex waits forever.
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// assert_eq!(topological_order(&g).unwrap_err().vertices, [0, 1, 2]);
/// ```
pub fn topological_order(g: &Digraph) -> Result<Vec<u32>, Stuck> {
    kahn(g, |_, _, _| {})
}

/// Kahn's walk, handing `watch` its state at the start and after every step: the order so far
/// (placed, then queued), where the queue starts in it, and the counts. Only test builds and the
/// `unchecked` feature make the calls; `KahnState::trace` records the states.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn kahn(g: &Digraph, mut watch: impl FnMut(&[u32], usize, &[u32])) -> Result<Vec<u32>, Stuck> {
    let n = g.n();
    let into = &g.into.offsets;
    let mut waits: Vec<u32> = (0..n).map(|v| (into[v + 1] - into[v]) as u32).collect();
    let mut order: Vec<u32> = Vec::with_capacity(n);
    // Seed: every vertex with nothing to wait for, from vertex 0 upward.
    order.extend((0..n as u32).filter(|&v| waits[v as usize] == 0));
    watched!(watch(&order, 0, &waits));
    let (offsets, neighbours) = (&g.out.offsets, &g.out.neighbours);
    let mut front = 0;
    while front < order.len() {
        let v = order[front] as usize;
        front += 1;
        for &w in &neighbours[offsets[v]..offsets[v + 1]] {
            let c = &mut waits[w as usize];
            *c -= 1;
            if *c == 0 {
                order.push(w);
            }
        }
        watched!(watch(&order, front, &waits));
    }
    if order.len() == n {
        Ok(order)
    } else {
        let vertices = (0..n as u32).filter(|&v| waits[v as usize] > 0).collect();
        Err(Stuck { vertices })
    }
}

/// A state of Kahn's walk, as the walk holds it: the order so far, whose unread tail is the queue,
/// and each vertex's count. The states come only from the walk itself, under the `unchecked`
/// feature, for tests that watch it: `cargo test --features unchecked`.
///
/// Lean: `TopoOrder.KahnState`; the checks below are the pieces of its `Valid`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KahnState {
    /// The vertices placed, in order, then the ready vertices, front first.
    order: Vec<u32>,
    /// Where the ready vertices start in `order`.
    front: usize,
    /// For each vertex, the arrows into it from vertices not yet placed.
    waits: Vec<u32>,
}

impl KahnState {
    /// The vertices placed so far, in order.
    fn placed(&self) -> &[u32] {
        &self.order[..self.front.min(self.order.len())]
    }

    /// The ready vertices, front first.
    fn queue(&self) -> &[u32] {
        &self.order[self.front.min(self.order.len())..]
    }

    /// The count of `v`; 0 past the counts.
    fn count(&self, v: usize) -> u32 {
        self.waits.get(v).copied().unwrap_or(0)
    }

    /// Where each vertex stands in the placed list, if it is there, for the vertices of `g`.
    fn positions(&self, g: &Digraph) -> Vec<Option<usize>> {
        let mut at = vec![None; g.n()];
        for (i, &v) in self.placed().iter().enumerate() {
            if let Some(slot) = at.get_mut(v as usize) {
                slot.get_or_insert(i);
            }
        }
        at
    }

    /// Box invariant 1: each placed vertex comes after everything it waits for. Each placed vertex
    /// is a vertex of the graph, placed once, and every arrow into it comes from a vertex placed
    /// earlier.
    ///
    /// Lean: `PlacedAfterWaits`.
    #[must_use]
    pub fn is_placed_after_waits(&self, g: &Digraph) -> bool {
        let at = self.positions(g);
        let placed = self.placed();
        let once = placed
            .iter()
            .enumerate()
            .all(|(i, &v)| at.get(v as usize) == Some(&Some(i)));
        once && (0..g.arrow_count()).all(|id| {
            let (a, b) = g.arrow(id);
            match at[b as usize] {
                Some(j) => at[a as usize].is_some_and(|i| i < j),
                None => true,
            }
        })
    }

    /// Box invariant 2: each unplaced vertex counts the unplaced vertices it still waits for. The
    /// count is of arrows, so a doubled arrow counts twice.
    ///
    /// Lean: `CountsUnplacedWaits`.
    #[must_use]
    pub fn is_counts_unplaced_waits(&self, g: &Digraph) -> bool {
        let at = self.positions(g);
        let mut unplaced_into = vec![0u32; g.n()];
        for id in 0..g.arrow_count() {
            let (a, b) = g.arrow(id);
            if at[a as usize].is_none() {
                unplaced_into[b as usize] += 1;
            }
        }
        (0..g.n()).all(|v| at[v].is_some() || self.count(v) == unplaced_into[v])
    }

    /// Box invariant 3: the ready list holds exactly the unplaced vertices whose count is zero. The
    /// queue holds each of them once and nothing else.
    ///
    /// Lean: `ReadyIsZero`.
    #[must_use]
    pub fn is_ready_is_zero(&self, g: &Digraph) -> bool {
        let at = self.positions(g);
        let queue = self.queue();
        let mut queued = vec![false; g.n()];
        let each_ready_once = queue.iter().all(|&v| {
            let v = v as usize;
            let fresh = v < g.n() && !queued[v] && at[v].is_none() && self.count(v) == 0;
            if fresh {
                queued[v] = true;
            }
            fresh
        });
        each_ready_once && (0..g.n()).all(|v| at[v].is_some() || self.count(v) != 0 || queued[v])
    }

    /// Lean `Valid`: [`KahnState::is_placed_after_waits`], [`KahnState::is_counts_unplaced_waits`]
    /// and [`KahnState::is_ready_is_zero`].
    #[must_use]
    pub fn is_valid(&self, g: &Digraph) -> bool {
        self.check_valid(g).is_ok()
    }

    /// [`KahnState::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (placed_after_waits)"`, `"invariant 2 (counts_unplaced_waits)"` or
    /// `"invariant 3 (ready_is_zero)"`.
    pub fn check_valid(&self, g: &Digraph) -> Result<(), &'static str> {
        if !self.is_placed_after_waits(g) {
            return Err("invariant 1 (placed_after_waits)");
        }
        if !self.is_counts_unplaced_waits(g) {
            return Err("invariant 2 (counts_unplaced_waits)");
        }
        if !self.is_ready_is_zero(g) {
            return Err("invariant 3 (ready_is_zero)");
        }
        Ok(())
    }

    /// Every state of Kahn's walk on `g`, from the start to the end, one per step. For tests; not
    /// part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(g: &Digraph) -> Vec<Self> {
        let mut states = Vec::new();
        let _ = kahn(g, |order, front, waits| {
            states.push(Self {
                order: order.to_vec(),
                front,
                waits: waits.to_vec(),
            });
        });
        states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no
    /// walk reaches. Not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(order: Vec<u32>, front: usize, waits: Vec<u32>) -> Self {
        Self {
            order,
            front,
            waits,
        }
    }

    /// The stored parts: the order, where the queue starts in it, and the counts. For tests; not
    /// part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn parts(&self) -> (&[u32], usize, &[u32]) {
        (&self.order, self.front, &self.waits)
    }
}

/// Not entered yet.
const NEW: u8 = 0;
/// Entered, its frame still on the stack.
const OPEN: u8 = 1;
/// Finished.
const DONE: u8 = 2;

/// The reverse depth-first finishing order, or the first cycle the search closes. Linear in
/// vertices plus arrows.
///
/// # Errors
///
/// [`Cycle`] w, …, v, w at the first arrow v → w whose target's frame is still on the stack.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{dfs_order, Digraph};
///
/// let g = Digraph::new(3, &[(2, 0), (0, 1)]).unwrap();
/// assert_eq!(dfs_order(&g).unwrap(), [2, 0, 1]);
///
/// // The cycle is named, its first vertex repeated at the end.
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// assert_eq!(dfs_order(&g).unwrap_err().vertices, [0, 1, 0]);
/// ```
pub fn dfs_order(g: &Digraph) -> Result<Vec<u32>, Cycle> {
    let n = g.n();
    let (offsets, neighbours) = (&g.out.offsets, &g.out.neighbours);
    let mut mark = vec![NEW; n];
    let mut finished: Vec<u32> = Vec::with_capacity(n);
    // Each frame: the vertex, its next row position, and where its row ends.
    let mut frames: Vec<(u32, usize, usize)> = Vec::with_capacity(n);
    for root in 0..n {
        if mark[root] != NEW {
            continue;
        }
        mark[root] = OPEN;
        frames.push((root as u32, offsets[root], offsets[root + 1]));
        while let Some(top) = frames.last_mut() {
            let (v, next, end) = *top;
            if next == end {
                frames.pop();
                mark[v as usize] = DONE;
                finished.push(v);
                continue;
            }
            top.1 += 1;
            let w = neighbours[next];
            match mark[w as usize] {
                NEW => {
                    mark[w as usize] = OPEN;
                    let w = w as usize;
                    frames.push((w as u32, offsets[w], offsets[w + 1]));
                }
                OPEN => {
                    let from = frames
                        .iter()
                        .rposition(|f| f.0 == w)
                        .expect("an open vertex has its frame on the stack");
                    let mut vertices: Vec<u32> = frames[from..].iter().map(|f| f.0).collect();
                    vertices.push(w);
                    return Err(Cycle { vertices });
                }
                _ => {}
            }
        }
    }
    finished.reverse();
    Ok(finished)
}

#[cfg(test)]
#[path = "unit_tests/topo.rs"]
mod tests;
