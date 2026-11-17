// SPDX-License-Identifier: Apache-2.0
//! The answer of a walk from one start: each vertex's cost and its recorded previous vertex.
//!
//! A vertex never reached has no cost and no previous vertex. The start has cost 0 and no previous
//! vertex, so following the previous vertices back from any reached vertex ends there.
//!
//! A path names its vertices, not its arrows. Where several arrows join two consecutive vertices,
//! its cost is that of the cheapest of them: a cost is recorded only when it strictly drops, so the
//! arrow that set it last is the cheapest from that previous vertex.
//!
//! Lean counterpart: `AlgoDesign.Paths.Dijkstra.Answer`.

/// Each vertex's cost and previous vertex, for one start.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Distances {
    /// The cost of each vertex; `None` for a vertex never reached.
    pub cost: Vec<Option<i64>>,
    /// The previous vertex of each vertex on its path; `None` for the start and for a vertex never
    /// reached.
    pub previous: Vec<Option<u32>>,
}

impl Distances {
    /// The vertices from the start to `v`, following the previous vertices back from `v`; `None`
    /// when `v` was never reached, or when the records do not lead back within one step per
    /// vertex. Linear in the path's length.
    ///
    /// # Panics
    ///
    /// If `v` is not below the number of vertices.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::paths::Distances;
    ///
    /// // From 1: 0 is reached from 1, and 2 from 0; 3 never.
    /// let d = Distances {
    ///     cost: vec![Some(2), Some(0), Some(7), None],
    ///     previous: vec![Some(1), None, Some(0), None],
    /// };
    /// assert_eq!(d.path_to(2), Some(vec![1, 0, 2]));
    /// assert_eq!(d.path_to(3), None);
    /// ```
    #[must_use]
    pub fn path_to(&self, v: u32) -> Option<Vec<u32>> {
        let n = self.cost.len();
        assert!((v as usize) < n, "vertex {v} out of range 0..{n}");
        self.cost[v as usize]?;
        let mut path = vec![v];
        let mut at = v;
        while let Some(&Some(p)) = self.previous.get(at as usize) {
            if path.len() == n {
                return None;
            }
            path.push(p);
            at = p;
        }
        path.reverse();
        Some(path)
    }
}

#[cfg(test)]
#[path = "unit_tests/distances.rs"]
mod tests;
