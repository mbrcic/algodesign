// SPDX-License-Identifier: Apache-2.0
//! Single failures in an undirected graph: the bridges, the cut vertices, the blocks, and the
//! block-cut forest that answers which vertices separate two others.
//!
//! [`blocks()`] is the low-link walk with a link stack (Drozdek, *Data Structures and Algorithms
//! in C++*, 4th ed., §8.6.1, pp. 416–418; Hopcroft and Tarjan 1973). The walk keeps its path as
//! explicit frames (vertex, arrival link id, next row position), starts at vertices 0 upward, and
//! gives each vertex an entry number from 1 in the order vertices are first entered. Its climb-back
//! number `low` starts as its entry number. Walking the row of the top vertex v, an entry (w, e):
//!
//! - is skipped when it is a loop (w is v), or when e is the link v arrived by: the walk skips the
//!   link, by its id, not the vertex it came from (cp-algorithms, "Finding bridges": "pass to dfs
//!   the index of the edge used to enter the vertex"), so the second copy of a doubled link climbs
//!   back;
//! - when w was not entered: e goes on the link stack and the walk descends to w;
//! - when w was entered earlier than v: e goes on the link stack and `low[v]` takes w's entry
//!   number if that is smaller (the neighbour's entry number, not its climb-back number);
//! - when w was entered later than v: skipped, since w is below v and pushed e already.
//!
//! When a child c finishes under v, having arrived by link e: `low[v]` takes `low[c]` if that is
//! smaller; if `low[c] >= entry[v]`, the link stack is popped down to and including e, and those
//! links are one block; if `low[c] > entry[v]`, e is a bridge. A vertex other than a root with such
//! a child is a cut vertex; a root is a cut vertex when it has two or more children. A vertex with
//! no link except loops (or no link at all) is an isolated vertex: a block of its own with no
//! links, emitted when it finishes as its own root. Loops are in no block.
//!
//! [`BlockCutForest`] joins every block to the cut vertices it holds (Diestel, *Graph Theory*,
//! §3.1): one tree per piece of the graph. Two vertices in one piece are separated by exactly the
//! cut vertices strictly between their nodes on the forest path.
//!
//! Nothing recurses on the call stack, so a path of any length is safe. Linear in vertices plus
//! links.
//!
//! [`Walk`] is a state of the walk, with one check per piece of the Lean `Valid` on it.
//!
//! Lean counterpart: `AlgoDesign.Graphs.Blocks`.

use super::digraph::Graph;

/// No link: a root's arrival link, and a loop's block.
const NONE: u32 = u32::MAX;

/// What the walk finds: the bridges, the cut vertices and the blocks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Blocks {
    /// The bridges' link ids, increasing.
    bridges: Vec<u32>,
    /// The cut vertices, increasing.
    cut_vertices: Vec<u32>,
    /// Each link's block, by link id; [`NONE`] for a loop.
    block_of_link: Vec<u32>,
    /// Block `i`'s links are `links[link_offsets[i]..link_offsets[i + 1]]`.
    link_offsets: Vec<usize>,
    /// Every block's links, block after block, each in the order the link stack popped them.
    links: Vec<u32>,
    /// Block `i`'s vertices are `vertices[vertex_offsets[i]..vertex_offsets[i + 1]]`.
    vertex_offsets: Vec<usize>,
    /// Every block's vertices, block after block, each increasing.
    vertices: Vec<u32>,
}

impl Blocks {
    /// The bridges: each link whose removal alone leaves more pieces, by id, increasing.
    #[must_use]
    pub fn bridges(&self) -> &[u32] {
        &self.bridges
    }

    /// The cut vertices: each vertex whose removal alone leaves more pieces, increasing.
    #[must_use]
    pub fn cut_vertices(&self) -> &[u32] {
        &self.cut_vertices
    }

    /// The block holding link `e`, or `None` for a loop.
    ///
    /// # Panics
    ///
    /// If `e` is not a link id of the graph.
    #[must_use]
    pub fn block_of_link(&self, e: usize) -> Option<u32> {
        let m = self.block_of_link.len();
        assert!(e < m, "link {e} out of range 0..{m}");
        Some(self.block_of_link[e]).filter(|&b| b != NONE)
    }

    /// The number of blocks.
    #[must_use]
    pub fn count(&self) -> usize {
        self.link_offsets.len() - 1
    }

    /// Block `i`'s links, in the order the link stack popped them; empty for an isolated vertex.
    ///
    /// # Panics
    ///
    /// If `i` is not below [`Blocks::count`].
    #[must_use]
    pub fn block_links(&self, i: usize) -> &[u32] {
        let b = self.count();
        assert!(i < b, "block {i} out of range 0..{b}");
        &self.links[self.link_offsets[i]..self.link_offsets[i + 1]]
    }

    /// Block `i`'s vertices, increasing: the ends of its links, or the isolated vertex alone.
    ///
    /// # Panics
    ///
    /// If `i` is not below [`Blocks::count`].
    #[must_use]
    pub fn block_vertices(&self, i: usize) -> &[u32] {
        let b = self.count();
        assert!(i < b, "block {i} out of range 0..{b}");
        &self.vertices[self.vertex_offsets[i]..self.vertex_offsets[i + 1]]
    }
}

/// One frame of the walk's path.
struct Frame {
    /// The vertex.
    v: u32,
    /// The link it arrived by; [`NONE`] for a root.
    arrival: u32,
    /// The next position in its row.
    next: usize,
}

/// A state of the walk of [`blocks()`], as the walk holds it, with what the invariants read and the
/// walk never does: the link and the vertex each vertex was entered from, and the vertex of each
/// block without links. A vertex entered and not on the path has finished; it has taken every entry
/// of its row, a vertex on the path as many as its frame says. The states come only from the walk
/// itself, under the `unchecked` feature, for tests that watch it: `cargo test --features
/// unchecked`.
///
/// Lean: `Blocks.Walk`; the checks below are the pieces of its `Valid`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Walk {
    /// Each vertex's entry number, from 1; 0 if not entered.
    entry: Vec<u32>,
    /// Each vertex's climb-back number.
    low: Vec<u32>,
    /// The frames of the path, the current vertex last: (vertex, arrival link or [`NONE`], how many
    /// entries of its row it has taken).
    path: Vec<(u32, u32, usize)>,
    /// The link stack, top last.
    link_stack: Vec<u32>,
    /// Block `i`'s links are `links[link_offsets[i]..link_offsets[i + 1]]`.
    link_offsets: Vec<usize>,
    /// Every block's links, block after block, in the order the stack gave them up.
    links: Vec<u32>,
    /// The link each vertex was entered by; [`NONE`] for a root or a vertex not entered.
    arrival: Vec<u32>,
    /// The vertex each vertex was entered from; a root, itself.
    up: Vec<u32>,
    /// The vertex of each block without links, in the order those blocks came out.
    alone: Vec<u32>,
}

/// Which links are in one block: two links that are not loops, the same or on one cycle through
/// distinct vertices. Read as: in one piece, and no vertex's deletion parts them (the far end of a
/// link at the deleted vertex stands for the link). The pieces of the graph without each vertex
/// are found once, so a pair costs `O(n)`.
struct SameBlock<'a> {
    g: &'a Graph,
    /// `pieces[x]` labels each vertex by its piece once vertex `x` is deleted; `pieces[n]`, of the
    /// whole graph.
    pieces: Vec<Vec<usize>>,
}

impl<'a> SameBlock<'a> {
    fn new(g: &'a Graph) -> Self {
        let n = g.n();
        let pieces = (0..=n)
            .map(|gone| {
                let mut u = super::union_find::UnionFind::new(n);
                for id in 0..g.link_count() {
                    let (a, b) = g.link(id);
                    if a as usize != gone && b as usize != gone {
                        u.union(a as usize, b as usize);
                    }
                }
                (0..n).map(|v| u.find(v)).collect()
            })
            .collect();
        Self { g, pieces }
    }

    /// Link `i` by its ends, if it is a link and not a loop.
    fn ends(&self, i: usize) -> Option<(usize, usize)> {
        (i < self.g.link_count())
            .then(|| self.g.link(i))
            .filter(|&(a, b)| a != b)
            .map(|(a, b)| (a as usize, b as usize))
    }

    fn holds(&self, e: usize, f: usize) -> bool {
        let (Some((a, b)), Some((c, d))) = (self.ends(e), self.ends(f)) else {
            return false;
        };
        let n = self.g.n();
        e == f
            || (self.pieces[n][a] == self.pieces[n][c]
                && (0..n).all(|x| {
                    let p = if a == x { b } else { a };
                    let q = if c == x { d } else { c };
                    self.pieces[x][p] == self.pieces[x][q]
                }))
    }
}

impl Walk {
    fn entry_of(&self, v: usize) -> u32 {
        self.entry.get(v).copied().unwrap_or(0)
    }

    fn arrival_of(&self, v: usize) -> u32 {
        self.arrival.get(v).copied().unwrap_or(NONE)
    }

    fn on_path(&self, v: usize) -> Option<&(u32, u32, usize)> {
        self.path.iter().find(|f| f.0 as usize == v)
    }

    fn finished(&self, v: usize) -> bool {
        self.entry_of(v) != 0 && self.on_path(v).is_none()
    }

    /// The entries of `x`'s row the walk has taken, as (neighbour, link).
    fn looked<'g>(&self, g: &'g Graph, x: usize) -> impl Iterator<Item = (u32, u32)> + 'g {
        let row = g.adj(x);
        let taken = match self.on_path(x) {
            Some(&(_, _, taken)) => taken,
            None if self.entry_of(x) != 0 => row.len(),
            None => 0,
        };
        row.iter().take(taken)
    }

    /// Whether `x` is in `v`'s explored subtree: `x` is `v`, or some vertex on the chain from `x`
    /// up, at most `n` steps, finished as a child of `v`.
    fn explored(&self, g: &Graph, v: usize, x: usize) -> bool {
        let mut y = x;
        x == v
            || (0..=g.n()).any(|_| {
                let child = self.finished(y) && self.arrival_of(y) != NONE;
                let here = child && self.up.get(y).is_some_and(|&u| u as usize == v);
                if self.arrival_of(y) == NONE {
                    y = usize::MAX;
                } else {
                    y = self.up.get(y).map_or(usize::MAX, |&u| u as usize);
                }
                here
            })
    }

    /// The earliest entry number `v`'s explored subtree reaches by one taken row entry, never the
    /// link the vertex taking it arrived by; at most `v`'s own.
    fn climb(&self, g: &Graph, v: usize) -> u32 {
        (0..g.n())
            .filter(|&x| self.explored(g, v, x))
            .flat_map(|x| {
                let arrived = self.arrival_of(x);
                self.looked(g, x)
                    .filter(move |&(_, id)| id != arrived)
                    .map(|(w, _)| self.entry_of(w as usize))
            })
            .fold(self.entry_of(v), u32::min)
    }

    /// Box invariant 1: each vertex's climb-back number is the earliest entry number the part of
    /// the walk below it can reach, without the link it arrived by; formally, using at most one
    /// link that is not on the walk's path, and never the link by which the walk arrived at the
    /// vertex.
    ///
    /// Lean: `ClimbBackIsEarliest`.
    #[must_use]
    pub fn is_climb_back_is_earliest(&self, g: &Graph) -> bool {
        (0..g.n()).all(|v| {
            self.entry_of(v) == 0 || self.low.get(v).copied().unwrap_or(0) == self.climb(g, v)
        })
    }

    /// Block `k`'s links; empty past the blocks.
    fn block(&self, k: usize) -> &[u32] {
        match (self.link_offsets.get(k), self.link_offsets.get(k + 1)) {
            (Some(&a), Some(&b)) if a <= b && b <= self.links.len() => &self.links[a..b],
            _ => &[],
        }
    }

    /// Box invariant 2: the link stack holds the explored links whose block has not come off yet,
    /// and every block that has come off is whole; formally, exactly those links, and every block
    /// that has come off is a whole block of the network. Each such link is on the stack once, and
    /// a block without links is an isolated vertex.
    ///
    /// Lean: `StackHoldsOpenLinks`.
    #[must_use]
    pub fn is_stack_holds_open_links(&self, g: &Graph) -> bool {
        let m = g.link_count();
        let blocks = self.link_offsets.len().saturating_sub(1);
        let mut seen = std::collections::HashSet::new();
        let once = self.link_stack.iter().all(|&e| seen.insert(e));
        let on_stack: Vec<bool> = (0..m as u32).map(|f| seen.contains(&f)).collect();
        let in_blocks: std::collections::HashSet<u32> = self.links.iter().copied().collect();
        let mut taken = vec![false; m];
        for x in 0..g.n() {
            for (w, id) in self.looked(g, x) {
                if w as usize != x {
                    taken[id as usize] = true;
                }
            }
        }
        let open = (0..m).all(|f| on_stack[f] == (taken[f] && !in_blocks.contains(&(f as u32))));
        let same = SameBlock::new(g);
        let whole = (0..blocks).all(|k| {
            let b = self.block(k);
            b.iter()
                .all(|&e| (0..m).all(|f| b.contains(&(f as u32)) == same.holds(e as usize, f)))
        });
        // The `j`-th block without links is the vertex `alone[j]`.
        let empties = (0..blocks).filter(|&k| self.block(k).is_empty()).count();
        let isolated = (0..empties).all(|j| {
            self.alone.get(j).is_some_and(|&v| {
                (v as usize) < g.n() && g.adj(v as usize).iter().all(|(w, _)| w == v)
            })
        });
        once && open && whole && isolated
    }

    /// Lean `Valid`: [`Walk::is_climb_back_is_earliest`] and [`Walk::is_stack_holds_open_links`].
    #[must_use]
    pub fn is_valid(&self, g: &Graph) -> bool {
        self.check_valid(g).is_ok()
    }

    /// [`Walk::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (climb_back_is_earliest)"` or `"invariant 2 (stack_holds_open_links)"`.
    pub fn check_valid(&self, g: &Graph) -> Result<(), &'static str> {
        if !self.is_climb_back_is_earliest(g) {
            return Err("invariant 1 (climb_back_is_earliest)");
        }
        if !self.is_stack_holds_open_links(g) {
            return Err("invariant 2 (stack_holds_open_links)");
        }
        Ok(())
    }

    /// Every state of the walk on `g`, one per step: after each vertex is entered as a root, each
    /// row entry is taken, each vertex finishes under its parent, and each root finishes. For
    /// tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(g: &Graph) -> Vec<Self> {
        struct Record<'g> {
            g: &'g Graph,
            arrival: Vec<u32>,
            up: Vec<u32>,
            alone: Vec<u32>,
            states: Vec<Walk>,
        }
        impl Watch for Record<'_> {
            fn enter(&mut self, v: usize, arrival: u32, up: usize) {
                self.arrival[v] = arrival;
                self.up[v] = up as u32;
            }
            fn alone(&mut self, v: usize) {
                self.alone.push(v as u32);
            }
            fn step(&mut self, s: &Parts<'_>) {
                let offsets = &self.g.adj.offsets;
                self.states.push(Walk {
                    entry: s.entry.to_vec(),
                    low: s.low.to_vec(),
                    path: s
                        .frames
                        .iter()
                        .map(|f| (f.v, f.arrival, f.next - offsets[f.v as usize]))
                        .collect(),
                    link_stack: s.link_stack.to_vec(),
                    link_offsets: s.link_offsets.to_vec(),
                    links: s.links.to_vec(),
                    arrival: self.arrival.clone(),
                    up: self.up.clone(),
                    alone: self.alone.clone(),
                });
            }
        }
        let n = g.n();
        let mut record = Record {
            g,
            arrival: vec![NONE; n],
            up: (0..n as u32).collect(),
            alone: Vec::new(),
            states: Vec::new(),
        };
        let _ = walk(g, &mut record);
        record.states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no
    /// walk reaches. Not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(parts: WalkParts) -> Self {
        let WalkParts {
            entry,
            low,
            path,
            link_stack,
            link_offsets,
            links,
            arrival,
            up,
            alone,
        } = parts;
        Self {
            entry,
            low,
            path,
            link_stack,
            link_offsets,
            links,
            arrival,
            up,
            alone,
        }
    }

    /// The stored parts. For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn parts(&self) -> WalkParts {
        WalkParts {
            entry: self.entry.clone(),
            low: self.low.clone(),
            path: self.path.clone(),
            link_stack: self.link_stack.clone(),
            link_offsets: self.link_offsets.clone(),
            links: self.links.clone(),
            arrival: self.arrival.clone(),
            up: self.up.clone(),
            alone: self.alone.clone(),
        }
    }
}

/// A [`Walk`]'s stored parts, each as the field of the same name holds it. For tests; not part of
/// the API.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WalkParts {
    pub entry: Vec<u32>,
    pub low: Vec<u32>,
    pub path: Vec<(u32, u32, usize)>,
    pub link_stack: Vec<u32>,
    pub link_offsets: Vec<usize>,
    pub links: Vec<u32>,
    pub arrival: Vec<u32>,
    pub up: Vec<u32>,
    pub alone: Vec<u32>,
}

/// The bridges, cut vertices and blocks of `g`, by one low-link walk with a link stack. Linear in
/// vertices plus links.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{blocks, Graph};
///
/// // A triangle 0 – 1 – 2 with a tail 2 – 3: link 3 is a bridge, vertex 2 a cut vertex.
/// let g = Graph::new(4, &[(0, 1), (1, 2), (2, 0), (2, 3)]).unwrap();
/// let b = blocks(&g);
/// assert_eq!(b.bridges(), [3]);
/// assert_eq!(b.cut_vertices(), [2]);
/// assert_eq!(b.count(), 2);
/// assert_eq!(b.block_of_link(0), b.block_of_link(2));
/// ```
#[must_use]
pub fn blocks(g: &Graph) -> Blocks {
    walk(g, &mut ())
}

/// What the walk shows as it goes: each vertex as it is entered, each block without links as its
/// vertex finishes, and its whole state after every step. Only test builds and the `unchecked`
/// feature make the calls; `Walk::trace` records the states.
#[cfg_attr(not(any(test, feature = "unchecked")), allow(dead_code))]
trait Watch {
    /// `v` is entered from `up` by link `arrival` ([`NONE`] for a root, entered from itself).
    fn enter(&mut self, _v: usize, _arrival: u32, _up: usize) {}
    /// The root `v` finished with no child: a block of its own with no links.
    fn alone(&mut self, _v: usize) {}
    /// The state after a step.
    fn step(&mut self, _state: &Parts<'_>) {}
}

impl Watch for () {}

/// The walk's own arrays, as a step leaves them.
// Read only by the recorder the tests use.
#[cfg_attr(not(any(test, feature = "unchecked")), allow(dead_code))]
struct Parts<'a> {
    entry: &'a [u32],
    low: &'a [u32],
    frames: &'a [Frame],
    link_stack: &'a [u32],
    links: &'a [u32],
    link_offsets: &'a [usize],
}

/// The walk of [`blocks()`], showing `watch` each step.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn walk(g: &Graph, watch: &mut impl Watch) -> Blocks {
    let n = g.n();
    let (offsets, neighbours, ids) = (&g.adj.offsets, &g.adj.neighbours, &g.adj.ids);
    let mut entry = vec![0u32; n]; // 0: not entered yet
    let mut low = vec![0u32; n];
    let mut time = 0u32;
    let mut is_cut = vec![false; n];
    let mut bridges: Vec<u32> = Vec::new();
    let mut link_stack: Vec<u32> = Vec::new();
    let mut block_of_link = vec![NONE; g.link_count()];
    let mut link_offsets = vec![0usize];
    let mut links: Vec<u32> = Vec::with_capacity(g.link_count());
    let mut frames: Vec<Frame> = Vec::new();
    // Show `watch` the state a step leaves.
    macro_rules! show {
        () => {
            watched!(watch.step(&Parts {
                entry: &entry,
                low: &low,
                frames: &frames,
                link_stack: &link_stack,
                links: &links,
                link_offsets: &link_offsets,
            }))
        };
    }
    for root in 0..n {
        if entry[root] != 0 {
            continue;
        }
        time += 1;
        entry[root] = time;
        low[root] = time;
        let mut children = 0usize;
        frames.push(Frame {
            v: root as u32,
            arrival: NONE,
            next: offsets[root],
        });
        watched!(watch.enter(root, NONE, root));
        show!();
        while let Some(top) = frames.last_mut() {
            let v = top.v as usize;
            let k = top.next;
            if k < offsets[v + 1] {
                top.next += 1;
                let (w, e) = (neighbours[k] as usize, ids[k]);
                if w == v || e == top.arrival {
                    show!();
                    continue;
                }
                if entry[w] == 0 {
                    link_stack.push(e);
                    time += 1;
                    entry[w] = time;
                    low[w] = time;
                    if frames.len() == 1 {
                        children += 1;
                    }
                    frames.push(Frame {
                        v: w as u32,
                        arrival: e,
                        next: offsets[w],
                    });
                    watched!(watch.enter(w, e, v));
                } else if entry[w] < entry[v] {
                    link_stack.push(e);
                    low[v] = low[v].min(entry[w]);
                }
                show!();
                continue;
            }
            // Every entry of v walked: v finishes.
            let Frame { v: c, arrival, .. } = frames.pop().expect("a frame");
            let Some(parent) = frames.last() else {
                continue;
            };
            let (c, u) = (c as usize, parent.v as usize);
            low[u] = low[u].min(low[c]);
            if low[c] >= entry[u] {
                let b = link_offsets.len() as u32 - 1;
                loop {
                    let x = link_stack
                        .pop()
                        .expect("the arrival link is on the link stack");
                    links.push(x);
                    block_of_link[x as usize] = b;
                    if x == arrival {
                        break;
                    }
                }
                link_offsets.push(links.len());
                if frames.len() > 1 {
                    is_cut[u] = true;
                }
            }
            if low[c] > entry[u] {
                bridges.push(arrival);
            }
            show!();
        }
        if children >= 2 {
            is_cut[root] = true;
        }
        if children == 0 {
            // No link but loops: an isolated vertex, a block with no links.
            link_offsets.push(links.len());
            watched!(watch.alone(root));
        }
        show!();
    }
    bridges.sort_unstable();
    let cut_vertices = (0..n as u32).filter(|&v| is_cut[v as usize]).collect();
    let (vertex_offsets, vertices) = vertices_of_blocks(g, &block_of_link, &link_offsets);
    Blocks {
        bridges,
        cut_vertices,
        block_of_link,
        link_offsets,
        links,
        vertex_offsets,
        vertices,
    }
}

/// Each block's vertices, increasing, packed. Walking the vertices 0 upward, a vertex is listed
/// with the block of each of its links (once per block), and an isolated vertex with the next block
/// that has no links, since those come out in increasing vertex order; one stable counting pass by
/// block then keeps each block's vertices increasing. Linear in vertices plus links.
fn vertices_of_blocks(
    g: &Graph,
    block_of_link: &[u32],
    link_offsets: &[usize],
) -> (Vec<usize>, Vec<u32>) {
    let b = link_offsets.len() - 1;
    let (offsets, ids) = (&g.adj.offsets, &g.adj.ids);
    let mut empty = (0..b).filter(|&i| link_offsets[i] == link_offsets[i + 1]);
    let mut stamp = vec![NONE; b]; // the last vertex listed with each block
    let mut pairs: Vec<(u32, u32)> = Vec::new(); // (block, vertex), vertices increasing
    for v in 0..g.n() {
        let mut any = false;
        for &e in &ids[offsets[v]..offsets[v + 1]] {
            let i = block_of_link[e as usize];
            if i == NONE {
                continue;
            }
            any = true;
            if stamp[i as usize] != v as u32 {
                stamp[i as usize] = v as u32;
                pairs.push((i, v as u32));
            }
        }
        if !any {
            let i = empty.next().expect("an isolated vertex has a block");
            pairs.push((i as u32, v as u32));
        }
    }
    let mut vertex_offsets = vec![0usize; b + 1];
    for &(i, _) in &pairs {
        vertex_offsets[i as usize + 1] += 1;
    }
    for i in 0..b {
        vertex_offsets[i + 1] += vertex_offsets[i];
    }
    let mut vertices = vec![0u32; pairs.len()];
    let mut at = vertex_offsets.clone();
    for &(i, v) in &pairs {
        vertices[at[i as usize]] = v;
        at[i as usize] += 1;
    }
    (vertex_offsets, vertices)
}

/// The block-cut forest: nodes `0..b` are the blocks, then one node per cut vertex in increasing
/// vertex order; a cut vertex's node is joined to every block holding it. One tree per piece,
/// rooted at the node of the piece's smallest vertex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockCutForest {
    /// The number of blocks; nodes from here on are cut vertices.
    block_count: usize,
    /// The cut vertices, increasing: node `block_count + k` is `cut_vertices[k]`.
    cut_vertices: Vec<u32>,
    /// Each vertex's node: its own if it is a cut vertex, else its one block.
    node_of: Vec<u32>,
    /// The node above each node; a root is its own parent.
    parent: Vec<u32>,
    /// The number of steps from each node up to its root.
    depth: Vec<u32>,
}

/// The debug-build check of [`BlockCutForest::new`]: `b` covers `g`'s links, each block's links
/// join vertices of that block, and every vertex is in a block. Linear in vertices plus links.
#[cfg(debug_assertions)]
fn refuse_another_graphs_blocks(g: &Graph, b: &Blocks) {
    let n = g.n();
    let m = g.link_count();
    assert!(
        b.block_of_link.len() == m,
        "the blocks hold {} links, the graph has {m}: they are another graph's",
        b.block_of_link.len()
    );
    // Each block's vertices stamped with its index, then its links read against the stamps.
    let mut stamp = vec![NONE; n];
    for i in 0..b.count() {
        for &p in b.block_vertices(i) {
            assert!(
                (p as usize) < n,
                "block {i} holds vertex {p}, not one of 0..{n}"
            );
            stamp[p as usize] = i as u32;
        }
        for &e in b.block_links(i) {
            let (x, y) = g.link(e as usize);
            assert!(
                stamp[x as usize] == i as u32 && stamp[y as usize] == i as u32,
                "link {e} of the graph is not in block {i}: the blocks are another graph's"
            );
        }
    }
    if let Some(v) = stamp.iter().position(|&s| s == NONE) {
        panic!("vertex {v} is in no block: the blocks are another graph's");
    }
}

impl BlockCutForest {
    /// The forest of `g` and its blocks `b`, which must be [`blocks()`] of `g`. Linear in vertices
    /// plus links.
    ///
    /// In debug builds, that `b` is `g`'s is checked as far as one pass can: `b` covers `g`'s
    /// links, each block's links join vertices of that block, and every vertex is in a block.
    /// Release builds do not check.
    ///
    /// # Panics
    ///
    /// In debug builds, if `b` was computed on another graph and that check sees it. In any build,
    /// if `b` names a vertex outside `g`.
    #[must_use]
    pub fn new(g: &Graph, b: &Blocks) -> Self {
        #[cfg(debug_assertions)]
        refuse_another_graphs_blocks(g, b);
        let n = g.n();
        let block_count = b.count();
        let size = block_count + b.cut_vertices.len();
        let mut node_of = vec![NONE; n];
        for (k, &c) in b.cut_vertices.iter().enumerate() {
            node_of[c as usize] = (block_count + k) as u32;
        }
        // The forest's links, block side: each block to the cut vertices it holds.
        let mut degree = vec![0usize; size + 1];
        for i in 0..block_count {
            for &p in b.block_vertices(i) {
                let x = node_of[p as usize];
                if x == NONE || (x as usize) < block_count {
                    node_of[p as usize] = i as u32;
                } else {
                    degree[i + 1] += 1;
                    degree[x as usize + 1] += 1;
                }
            }
        }
        for x in 0..size {
            degree[x + 1] += degree[x];
        }
        let mut around = vec![0u32; degree[size]];
        let mut at = degree.clone();
        for i in 0..block_count {
            for &p in b.block_vertices(i) {
                let x = node_of[p as usize] as usize;
                if x >= block_count {
                    around[at[i]] = x as u32;
                    at[i] += 1;
                    around[at[x]] = i as u32;
                    at[x] += 1;
                }
            }
        }
        let mut parent = vec![NONE; size];
        let mut depth = vec![0u32; size];
        let mut stack: Vec<u32> = Vec::new();
        for &top in &node_of {
            if parent[top as usize] != NONE {
                continue;
            }
            parent[top as usize] = top;
            stack.push(top);
            while let Some(x) = stack.pop() {
                let x = x as usize;
                for &y in &around[degree[x]..degree[x + 1]] {
                    if parent[y as usize] == NONE {
                        parent[y as usize] = x as u32;
                        depth[y as usize] = depth[x] + 1;
                        stack.push(y);
                    }
                }
            }
        }
        Self {
            block_count,
            cut_vertices: b.cut_vertices.clone(),
            node_of,
            parent,
            depth,
        }
    }

    /// The number of nodes: blocks plus cut vertices.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.parent.len()
    }

    /// The node above `x`; a root is its own parent.
    ///
    /// # Panics
    ///
    /// If `x` is not below [`BlockCutForest::node_count`].
    #[must_use]
    pub fn parent(&self, x: usize) -> u32 {
        let size = self.parent.len();
        assert!(x < size, "node {x} out of range 0..{size}");
        self.parent[x]
    }

    /// The number of steps from `x` up to its root.
    ///
    /// # Panics
    ///
    /// If `x` is not below [`BlockCutForest::node_count`].
    #[must_use]
    pub fn depth(&self, x: usize) -> u32 {
        let size = self.depth.len();
        assert!(x < size, "node {x} out of range 0..{size}");
        self.depth[x]
    }

    /// A vertex's node: a cut vertex's own node, any other vertex's one block.
    ///
    /// # Panics
    ///
    /// If `vertex` is not a vertex of the graph.
    #[must_use]
    pub fn node_of(&self, vertex: usize) -> u32 {
        let n = self.node_of.len();
        assert!(vertex < n, "vertex {vertex} out of range 0..{n}");
        self.node_of[vertex]
    }

    /// The vertices whose failure alone separates `u` from `v`, increasing: the cut vertices
    /// strictly between their nodes on the forest path; `None` when `u` and `v` are in different
    /// pieces. `u == v` gives no separators. Walks up from the deeper end, so linear in the path's
    /// length (plus sorting the answer).
    ///
    /// # Panics
    ///
    /// If `u` or `v` is not a vertex of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::{blocks, BlockCutForest, Graph};
    ///
    /// // The path 0 – 1 – 2 – 3, and a vertex 4 on its own.
    /// let g = Graph::new(5, &[(0, 1), (1, 2), (2, 3)]).unwrap();
    /// let f = BlockCutForest::new(&g, &blocks(&g));
    /// assert_eq!(f.separators(0, 3), Some(vec![1, 2]));
    /// assert_eq!(f.separators(1, 2), Some(vec![]));
    /// // Different pieces: nothing to separate.
    /// assert_eq!(f.separators(0, 4), None);
    /// ```
    #[must_use]
    pub fn separators(&self, u: usize, v: usize) -> Option<Vec<u32>> {
        let (a, b) = (self.node_of(u) as usize, self.node_of(v) as usize);
        let (mut x, mut y) = (a, b);
        let mut found = Vec::new();
        let mut take = |z: usize| {
            if z >= self.block_count && z != a && z != b {
                found.push(self.cut_vertices[z - self.block_count]);
            }
        };
        // Every node left on the way is on the path below the meeting node, and is left once.
        while x != y {
            if self.depth[x] < self.depth[y] {
                std::mem::swap(&mut x, &mut y);
            }
            if self.parent[x] as usize == x {
                return None; // two different roots: two pieces
            }
            take(x);
            x = self.parent[x] as usize;
        }
        take(x);
        found.sort_unstable();
        Some(found)
    }
}

#[cfg(test)]
#[path = "unit_tests/block_cut.rs"]
mod tests;
