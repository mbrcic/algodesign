// SPDX-License-Identifier: Apache-2.0
//! Union-find that can take back its merges, last first.
//!
//! Westbrook and Tarjan (*SIAM J. Comput.* 18(1), 1989, p. 3, crediting Mannila and Ukkonen):
//! union by rank without path compression, so a merge writes one link and perhaps one rank, and a
//! log of those writes undoes it. A lookup walks up to the root and changes nothing. A merge has
//! the same guard and tie rule as [`UnionFind`](super::UnionFind): look up `x`'s root, then
//! `y`'s; if they are the same, merge nothing; otherwise the root of lower rank goes under the
//! other, and on equal ranks the second root goes under the first, whose rank rises by one.
//!
//! The log has one entry per `union` call: the root that stopped being a root and whether the
//! other root's rank rose, or an empty entry when nothing merged, so a call that merged nothing
//! still takes one `undo`. `undo` takes back the last entry, restoring the links, the ranks and
//! the group count; on an empty log it does nothing and answers `false`.
//!
//! There is no `check_valid`: the invariant, the union-find's together with every state the log
//! rolls back to being legal, is the Lean `Valid` (`RollbacksLegal`).
//!
//! Lean counterpart: `AlgoDesign.Graphs.UndoUnionFind`.

/// A union-find over the items `0..n`, fixed at construction, with a log of its merges.
///
/// Links are `u32` (every item is below `n`, at most `u32::MAX`) and ranks `u8` (a rank never
/// exceeds log₂ n, which is below 32).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UndoUnionFind {
    /// The link upward from each item; a root links to itself.
    parent: Vec<u32>,
    /// Each item's rank.
    rank: Vec<u8>,
    /// The number of groups.
    count: usize,
    /// One entry per `union` call: the root put under the other and whether the other's rank
    /// rose, or `None` when nothing merged.
    log: Vec<Option<(u32, bool)>>,
}

impl UndoUnionFind {
    /// Every item alone: each its own root, of rank 0, so `n` groups; the log empty. `O(n)`.
    ///
    /// # Panics
    ///
    /// If `n` exceeds `u32::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::UndoUnionFind;
    ///
    /// let mut u = UndoUnionFind::new(3);
    /// u.union(0, 1);
    /// u.union(1, 2);
    /// assert!(u.joined(0, 2));
    /// // Take the last merge back.
    /// assert!(u.undo());
    /// assert!(!u.joined(0, 2));
    /// assert!(u.joined(0, 1));
    /// assert_eq!(u.count(), 2);
    /// ```
    #[must_use]
    pub fn new(n: usize) -> Self {
        let m = u32::try_from(n).expect("at most u32::MAX items");
        Self {
            parent: (0..m).collect(),
            rank: vec![0; n],
            count: n,
            log: Vec::new(),
        }
    }

    /// The root of `x`'s group, found by walking up; nothing changes. At most log₂ n links up.
    ///
    /// # Panics
    ///
    /// If `x` is not an item (`x >= n`).
    #[must_use]
    pub fn find(&self, x: usize) -> usize {
        assert!(
            x < self.parent.len(),
            "item {x} out of range 0..{}",
            self.parent.len()
        );
        let mut root = x;
        while self.parent[root] as usize != root {
            root = self.parent[root] as usize;
        }
        root
    }

    /// Merge the groups of `x` and `y`, logging it; `true` if two groups became one, `false` if
    /// they were already one (then only the log changes, by an empty entry). Two lookups.
    ///
    /// # Panics
    ///
    /// If `x` or `y` is not an item.
    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            self.log.push(None);
            return false;
        }
        let entry = if self.rank[rx] < self.rank[ry] {
            self.parent[rx] = ry as u32;
            (rx as u32, false)
        } else if self.rank[ry] < self.rank[rx] {
            self.parent[ry] = rx as u32;
            (ry as u32, false)
        } else {
            self.parent[ry] = rx as u32;
            self.rank[rx] += 1;
            (ry as u32, true)
        };
        self.log.push(Some(entry));
        self.count -= 1;
        true
    }

    /// Take back the last `union` call: the root it put under is a root again, the other root's
    /// rank falls back if it rose, and the group count rises again; `false` if the log is empty.
    /// `O(1)`.
    pub fn undo(&mut self) -> bool {
        let Some(last) = self.log.pop() else {
            return false;
        };
        if let Some((child, rose)) = last {
            let child = child as usize;
            if rose {
                // Nothing after the merge was kept, so the root above `child` is still its parent.
                self.rank[self.parent[child] as usize] -= 1;
            }
            self.parent[child] = child as u32;
            self.count += 1;
        }
        true
    }

    /// Are `x` and `y` in one group? Looks up `x`, then `y`. Two lookups.
    ///
    /// # Panics
    ///
    /// If `x` or `y` is not an item.
    #[must_use]
    pub fn joined(&self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }

    /// The number of groups. `O(1)`.
    #[must_use]
    pub fn count(&self) -> usize {
        self.count
    }

    /// The link upward from each item, as stored. Public for tests; not part of the
    /// API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn parents(&self) -> &[u32] {
        &self.parent
    }

    /// Each item's rank, as stored. Public for tests; not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn ranks(&self) -> &[u8] {
        &self.rank
    }
}

#[cfg(test)]
#[path = "unit_tests/union_find_undo.rs"]
mod tests;
