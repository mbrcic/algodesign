// SPDX-License-Identifier: Apache-2.0
//! Directed and undirected graphs on the vertices `0..n`, stored as sorted rows.
//!
//! A directed graph keeps every arrow twice: once in the row of the vertex it leaves (forward),
//! once in the row of the vertex it enters (reversed). An undirected graph keeps every link once in
//! each end's row, so a loop is twice in its own vertex's row (Ahuja, Magnanti and Orlin, *Network
//! Flows*, §2.3, p. 38: "we will store each arc (i, j) of an undirected network twice"). Every
//! entry is a (neighbour, id) pair, the id being the arrow's or link's position in the input, and
//! each row is sorted by neighbour, then id: the order every algorithm of the chapter walks it in.
//! Loops and doubled arrows or links are accepted; each algorithm says what it does with them.
//!
//! The rows come from one global two-pass counting sort per direction: the entries, taken in id
//! order, are spread stably by neighbour, and that sequence is spread stably by the row's own
//! vertex, so each row ends sorted by (neighbour, id). Linear in vertices plus entries.
//!
//! Lean counterpart: `AlgoDesign.Graphs.Digraph` and `AlgoDesign.Graphs.Graph` (`Digraph.lean`;
//! `Digraph.out`, `Digraph.into` and `Graph.adj` are the rows).

use std::fmt;

/// The largest number of vertices plus one: vertices are below 2³¹, so an algorithm may count up to
/// twice the number of vertices in a `u32` and still keep a value apart.
const VERTEX_LIMIT: usize = 1 << 31;

/// Why a graph was refused at construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphError {
    /// `n` is 2³¹ or more.
    TooManyVertices {
        /// The number of vertices asked for.
        n: usize,
    },
    /// More than `u32::MAX` arrows, so some id would not fit a `u32`.
    TooManyArrows {
        /// The number of arrows given.
        count: usize,
    },
    /// More than `u32::MAX` links, so some id would not fit a `u32`.
    TooManyLinks {
        /// The number of links given.
        count: usize,
    },
    /// An arrow or link names a vertex that is not below `n`; the first such one is reported.
    EndpointOutOfRange {
        /// The arrow's or link's id.
        id: usize,
        /// The end that is out of range.
        vertex: u32,
        /// The number of vertices.
        n: usize,
    },
}

impl fmt::Display for GraphError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooManyVertices { n } => write!(f, "{n} vertices: at most 2^31 - 1 allowed"),
            Self::TooManyArrows { count } => {
                write!(f, "{count} arrows: at most u32::MAX allowed")
            }
            Self::TooManyLinks { count } => write!(f, "{count} links: at most u32::MAX allowed"),
            Self::EndpointOutOfRange { id, vertex, n } => {
                write!(f, "entry {id} names vertex {vertex}, out of range 0..{n}")
            }
        }
    }
}

impl std::error::Error for GraphError {}

/// One vertex's row: its entries as two parallel slices, `neighbours[k]` reached by the arrow or
/// link `ids[k]`, sorted by (neighbour, id).
///
/// Two slices rather than one slice of pairs: a walk that needs only the neighbours (an order, the
/// strong components) reads half the bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Row<'a> {
    /// The neighbour of each entry.
    pub neighbours: &'a [u32],
    /// The id of the arrow or link of each entry.
    pub ids: &'a [u32],
}

impl<'a> Row<'a> {
    /// The number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.neighbours.len()
    }

    /// Whether the row has no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.neighbours.is_empty()
    }

    /// The entries as (neighbour, id) pairs, in row order (Lean's row is this list).
    pub fn iter(&self) -> impl Iterator<Item = (u32, u32)> + 'a {
        self.neighbours
            .iter()
            .copied()
            .zip(self.ids.iter().copied())
    }
}

/// The rows of every vertex, packed: vertex `v`'s entries are at `offsets[v]..offsets[v + 1]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Rows {
    /// Where each vertex's row starts; `n + 1` values, the last the number of entries.
    pub(crate) offsets: Vec<usize>,
    /// The neighbour of each entry.
    pub(crate) neighbours: Vec<u32>,
    /// The id of each entry.
    pub(crate) ids: Vec<u32>,
}

impl Rows {
    /// The rows of the entries `(vertex, neighbour, id)`, given in increasing id, by two stable
    /// counting passes: spread by neighbour, then by vertex.
    fn sort(n: usize, entries: impl Iterator<Item = (u32, u32, u32)> + Clone) -> Self {
        let mut by_neighbour = vec![0usize; n + 1];
        let mut offsets = vec![0usize; n + 1];
        for (v, w, _) in entries.clone() {
            by_neighbour[w as usize + 1] += 1;
            offsets[v as usize + 1] += 1;
        }
        for i in 0..n {
            by_neighbour[i + 1] += by_neighbour[i];
            offsets[i + 1] += offsets[i];
        }
        let len = offsets[n];
        // First pass: by neighbour, ids still increasing inside each neighbour.
        let mut vertex = vec![0u32; len];
        let mut id = vec![0u32; len];
        let mut next = by_neighbour.clone();
        for (v, w, i) in entries {
            let at = &mut next[w as usize];
            vertex[*at] = v;
            id[*at] = i;
            *at += 1;
        }
        // Second pass: by vertex, walking the neighbours in increasing order.
        let mut neighbours = vec![0u32; len];
        let mut ids = vec![0u32; len];
        let mut next = offsets.clone();
        for w in 0..n {
            for k in by_neighbour[w]..by_neighbour[w + 1] {
                let at = &mut next[vertex[k] as usize];
                neighbours[*at] = w as u32;
                ids[*at] = id[k];
                *at += 1;
            }
        }
        Self {
            offsets,
            neighbours,
            ids,
        }
    }

    fn row(&self, v: usize) -> Row<'_> {
        let n = self.offsets.len() - 1;
        assert!(v < n, "vertex {v} out of range 0..{n}");
        let r = self.offsets[v]..self.offsets[v + 1];
        Row {
            neighbours: &self.neighbours[r.clone()],
            ids: &self.ids[r],
        }
    }
}

/// Refuses `n` vertices with `count` arrows or links whose ends are `ends`, before anything is
/// allocated; `too_many` is the error for `count` past `u32::MAX`.
fn check(
    n: usize,
    count: usize,
    too_many: GraphError,
    ends: &[(u32, u32)],
) -> Result<(), GraphError> {
    if n >= VERTEX_LIMIT {
        return Err(GraphError::TooManyVertices { n });
    }
    if count > u32::MAX as usize {
        return Err(too_many);
    }
    for (id, &(a, b)) in ends.iter().enumerate() {
        for vertex in [a, b] {
            if vertex as usize >= n {
                return Err(GraphError::EndpointOutOfRange { id, vertex, n });
            }
        }
    }
    Ok(())
}

/// A directed graph on the vertices `0..n`: the arrows by id, each vertex's forward row (the arrows
/// leaving it) and reversed row (the arrows entering it).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Digraph {
    /// Each arrow as (from, to), by id.
    arrows: Vec<(u32, u32)>,
    /// The arrows leaving each vertex, as (to, id).
    pub(crate) out: Rows,
    /// The arrows entering each vertex, as (from, id).
    pub(crate) into: Rows,
}

impl Digraph {
    /// The graph on `0..n` with `arrows[i] = (from, to)` as arrow `i`. Linear in `n` plus the
    /// number of arrows.
    ///
    /// # Errors
    ///
    /// [`GraphError::TooManyVertices`] if `n >= 2³¹`, [`GraphError::TooManyArrows`] past `u32::MAX`
    /// arrows, [`GraphError::EndpointOutOfRange`] for the first arrow with an end not below `n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::Digraph;
    ///
    /// // Three vertices, arrows 0 → 1, 1 → 2 and 0 → 2; arrow i is the i-th pair.
    /// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
    /// // A row lists (neighbour, arrow id), sorted by neighbour.
    /// let row: Vec<(u32, u32)> = g.out(0).iter().collect();
    /// assert_eq!(row, [(1, 0), (2, 2)]);
    /// assert_eq!(g.arrow(1), (1, 2));
    /// assert!(Digraph::new(2, &[(0, 2)]).is_err());
    /// ```
    pub fn new(n: usize, arrows: &[(u32, u32)]) -> Result<Self, GraphError> {
        let too_many = GraphError::TooManyArrows {
            count: arrows.len(),
        };
        check(n, arrows.len(), too_many, arrows)?;
        let with_ids = arrows.iter().zip(0u32..);
        Ok(Self {
            arrows: arrows.to_vec(),
            out: Rows::sort(n, with_ids.clone().map(|(&(a, b), i)| (a, b, i))),
            into: Rows::sort(n, with_ids.map(|(&(a, b), i)| (b, a, i))),
        })
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.out.offsets.len() - 1
    }

    /// The number of arrows.
    #[must_use]
    pub fn arrow_count(&self) -> usize {
        self.arrows.len()
    }

    /// Arrow `id` as (from, to).
    ///
    /// # Panics
    ///
    /// If `id` is not below [`Digraph::arrow_count`].
    #[must_use]
    pub fn arrow(&self, id: usize) -> (u32, u32) {
        let m = self.arrows.len();
        assert!(id < m, "arrow {id} out of range 0..{m}");
        self.arrows[id]
    }

    /// The forward row of `v`: every arrow leaving `v`, as (to, id).
    ///
    /// Lean: `Digraph.out`.
    ///
    /// # Panics
    ///
    /// If `v` is not a vertex (`v >= n`).
    #[must_use]
    pub fn out(&self, v: usize) -> Row<'_> {
        self.out.row(v)
    }

    /// The reversed row of `v`: every arrow entering `v`, as (from, id). Named `into` in the Lean
    /// and the Python; here `into` would clash with `Into::into`.
    ///
    /// Lean: `Digraph.into`.
    ///
    /// # Panics
    ///
    /// If `v` is not a vertex (`v >= n`).
    #[must_use]
    pub fn incoming(&self, v: usize) -> Row<'_> {
        self.into.row(v)
    }
}

/// An undirected graph on the vertices `0..n`: the links by id and each vertex's row, a link in
/// both ends' rows under one id and a loop twice in its vertex's row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Graph {
    /// Each link by its two ends, as given, by id.
    links: Vec<(u32, u32)>,
    /// Each vertex's row, as (neighbour, id).
    pub(crate) adj: Rows,
}

impl Graph {
    /// The graph on `0..n` with `links[i] = (a, b)` as link `i`. Linear in `n` plus the number of
    /// links.
    ///
    /// # Errors
    ///
    /// [`GraphError::TooManyVertices`] if `n >= 2³¹`, [`GraphError::TooManyLinks`] past `u32::MAX`
    /// links, [`GraphError::EndpointOutOfRange`] for the first link with an end not below `n`.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::Graph;
    ///
    /// // A triangle 0 – 1 – 2; each link sits in both ends' rows under one id.
    /// let g = Graph::new(3, &[(0, 1), (1, 2), (2, 0)]).unwrap();
    /// let row: Vec<(u32, u32)> = g.adj(0).iter().collect();
    /// assert_eq!(row, [(1, 0), (2, 2)]);
    /// ```
    pub fn new(n: usize, links: &[(u32, u32)]) -> Result<Self, GraphError> {
        let too_many = GraphError::TooManyLinks { count: links.len() };
        check(n, links.len(), too_many, links)?;
        let halves = links
            .iter()
            .zip(0u32..)
            .flat_map(|(&(a, b), i)| [(a, b, i), (b, a, i)]);
        Ok(Self {
            links: links.to_vec(),
            adj: Rows::sort(n, halves),
        })
    }

    /// The number of vertices.
    #[must_use]
    pub fn n(&self) -> usize {
        self.adj.offsets.len() - 1
    }

    /// The number of links.
    #[must_use]
    pub fn link_count(&self) -> usize {
        self.links.len()
    }

    /// Link `id` by its two ends, in the order given.
    ///
    /// # Panics
    ///
    /// If `id` is not below [`Graph::link_count`].
    #[must_use]
    pub fn link(&self, id: usize) -> (u32, u32) {
        let m = self.links.len();
        assert!(id < m, "link {id} out of range 0..{m}");
        self.links[id]
    }

    /// The row of `v`: one entry per end of a link at `v`, as (neighbour, id).
    ///
    /// Lean: `Graph.adj`.
    ///
    /// # Panics
    ///
    /// If `v` is not a vertex (`v >= n`).
    #[must_use]
    pub fn adj(&self, v: usize) -> Row<'_> {
        self.adj.row(v)
    }
}

#[cfg(test)]
#[path = "unit_tests/digraph.rs"]
mod tests;
