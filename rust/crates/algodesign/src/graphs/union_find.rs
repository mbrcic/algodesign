// SPDX-License-Identifier: Apache-2.0
//! Union-find over the items `0..n`: are these two joined yet, while links keep arriving.
//!
//! Each group is a tree whose root stands for it. A lookup is CLRS's `FIND-SET` with full path
//! compression (CLRS 4th ed., §19.3, p. 530), here in two passes: walk up to the root, then walk
//! the path again pointing every item on it at the root. A merge is Weiss's `unionSets` (Weiss,
//! *Data Structures and Algorithm Analysis in C++*, 4th ed., §8.5, Fig. 8.14): look up `x`'s root
//! first, then `y`'s; if they are the same, merge nothing; otherwise the root of lower rank goes
//! under the other, and on equal ranks the second root goes under the first, whose rank rises by
//! one. The lookup order is part of the method: compression makes the links depend on it.
//!
//! Compression only points an item at another higher up its own tree. That is a fact about a
//! lookup's step, not one of the box's invariants and not a state, so no state check holds it: the
//! Lean states it of a lookup (`FindSpec.points_higher`).
//!
//! Lean counterpart: `AlgoDesign.Graphs.UnionFind` (`Spec.lean` holds the contract and `Valid`).

/// A union-find over the items `0..n`, fixed at construction.
///
/// Links are `u32` (every item is below `n`, at most `u32::MAX`, so `item as u32` is exact) and
/// ranks `u8` (a rank never exceeds log₂ n, which is below 32).
///
/// The links and ranks themselves are read only by tests (feature `unchecked`), which compare them
/// with the Lean's and the Python's after every operation: `cargo test --features unchecked`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnionFind {
    /// The link upward from each item; a root links to itself.
    parent: Vec<u32>,
    /// Each item's rank.
    rank: Vec<u8>,
    /// The number of groups.
    count: usize,
}

impl UnionFind {
    /// Every item alone: each its own root, of rank 0, so `n` groups. `O(n)`.
    ///
    /// Lean: `valid_init`.
    ///
    /// # Panics
    ///
    /// If `n` exceeds `u32::MAX`.
    ///
    /// # Examples
    ///
    /// ```
    /// use algodesign::graphs::UnionFind;
    ///
    /// let mut u = UnionFind::new(4);
    /// assert!(u.union(0, 1));
    /// assert!(u.union(2, 3));
    /// assert!(!u.union(1, 0)); // already one group
    /// assert!(u.joined(0, 1));
    /// assert!(!u.joined(1, 2));
    /// assert_eq!(u.count(), 2);
    /// ```
    #[must_use]
    pub fn new(n: usize) -> Self {
        let m = u32::try_from(n).expect("at most u32::MAX items");
        Self {
            parent: (0..m).collect(),
            rank: vec![0; n],
            count: n,
        }
    }

    /// The root of `x`'s group; every item on the walk now points straight at it. At most
    /// log₂ n links up, twice.
    ///
    /// Lean: `find_spec`, `valid_find`.
    ///
    /// # Panics
    ///
    /// If `x` is not an item (`x >= n`).
    pub fn find(&mut self, x: usize) -> usize {
        assert!(
            x < self.parent.len(),
            "item {x} out of range 0..{}",
            self.parent.len()
        );
        let mut root = x;
        while self.parent[root] as usize != root {
            root = self.parent[root] as usize;
        }
        let mut i = x;
        while i != root {
            let next = self.parent[i] as usize;
            self.parent[i] = root as u32;
            i = next;
        }
        root
    }

    /// Merge the groups of `x` and `y`; `true` if two groups became one, `false` if they were
    /// already one (then nothing changes but the compression of the two lookups). Two lookups.
    ///
    /// Lean: `union_spec`, `valid_union`.
    ///
    /// # Panics
    ///
    /// If `x` or `y` is not an item.
    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return false;
        }
        if self.rank[rx] < self.rank[ry] {
            self.parent[rx] = ry as u32;
        } else if self.rank[ry] < self.rank[rx] {
            self.parent[ry] = rx as u32;
        } else {
            self.parent[ry] = rx as u32;
            self.rank[rx] += 1;
        }
        self.count -= 1;
        true
    }

    /// Are `x` and `y` in one group? Looks up `x`, then `y`. Two lookups.
    ///
    /// Lean: `valid_joined`.
    ///
    /// # Panics
    ///
    /// If `x` or `y` is not an item.
    pub fn joined(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        rx == ry
    }

    /// The number of groups. `O(1)`.
    #[must_use]
    pub fn count(&self) -> usize {
        self.count
    }

    /// The item `i` links up to; an index past the link array links to itself, so every check
    /// below can walk any stored state without leaving the arrays (Lean `parent`, which reads a
    /// state the tests send it the same way).
    fn up(&self, i: usize) -> usize {
        self.parent.get(i).map_or(i, |&p| p as usize)
    }

    /// The rank of `i`; 0 past the rank array.
    fn rank_of(&self, i: usize) -> u8 {
        self.rank.get(i).copied().unwrap_or(0)
    }

    /// Where `n` steps up from `i` lead, compressing nothing (Lean `root`).
    fn root_of(&self, i: usize) -> usize {
        (0..self.parent.len()).fold(i, |r, _| self.up(r))
    }

    /// Box invariant 1: following parents up from any item ends at its group's root.
    /// Every link stays among the items, and `n` steps up reach an item that is its own parent.
    ///
    /// Lean: `UpwardEndsAtRoot`.
    #[must_use]
    pub fn is_upward_ends_at_root(&self) -> bool {
        let n = self.parent.len();
        (0..n).all(|i| {
            let r = self.root_of(i);
            self.up(i) < n && self.up(r) == r
        })
    }

    /// Box invariant 2, first half: ranks rise toward the root. An item that is not a root has a
    /// smaller rank than its parent.
    ///
    /// Lean: `RanksRiseUpward`.
    #[must_use]
    pub fn is_ranks_rise_upward(&self) -> bool {
        (0..self.parent.len())
            .all(|i| self.up(i) == i || self.rank_of(i) < self.rank_of(self.up(i)))
    }

    /// Box invariant 2, second half: a root of rank `r` has at least `2^r` items, those in its
    /// tree, compared as `r` against the size's bit length, so no rank overflows a shift.
    ///
    /// Lean: `RootRankBoundsSize`.
    #[must_use]
    pub fn is_root_rank_bounds_size(&self) -> bool {
        let n = self.parent.len();
        let mut size = vec![0usize; n];
        for i in 0..n {
            if let Some(s) = size.get_mut(self.root_of(i)) {
                *s += 1;
            }
        }
        // 2^r <= size exactly when r is below size's bit length.
        (0..n).all(|r| {
            self.up(r) != r || u32::from(self.rank_of(r)) < usize::BITS - size[r].leading_zeros()
        })
    }

    /// Not in the box: the group count is the number of roots.
    ///
    /// Lean: `CountIsRoots`.
    #[must_use]
    pub fn is_count_is_roots(&self) -> bool {
        self.count == (0..self.parent.len()).filter(|&r| self.up(r) == r).count()
    }

    /// Layout: one rank per item. Not a Lean piece: the Lean's ranks are a function on the items.
    #[must_use]
    pub fn one_rank_per_item(&self) -> bool {
        self.rank.len() == self.parent.len()
    }

    /// Lean `Valid` and `WellFormed`: [`UnionFind::is_upward_ends_at_root`],
    /// [`UnionFind::is_ranks_rise_upward`], [`UnionFind::is_root_rank_bounds_size`] and
    /// [`UnionFind::is_count_is_roots`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`UnionFind::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (upward_ends_at_root)"`, `"invariant 2 (ranks_rise_upward)"`,
    /// `"invariant 2 (root_rank_bounds_size)"` or `"not in the box (count_is_roots)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_upward_ends_at_root() {
            return Err("invariant 1 (upward_ends_at_root)");
        }
        if !self.is_ranks_rise_upward() {
            return Err("invariant 2 (ranks_rise_upward)");
        }
        if !self.is_root_rank_bounds_size() {
            return Err("invariant 2 (root_rank_bounds_size)");
        }
        if !self.is_count_is_roots() {
            return Err("not in the box (count_is_roots)");
        }
        Ok(())
    }

    /// A union-find from its stored parts, unchecked, for tests to judge states
    /// no sequence of operations reaches. Not part of the API.
    #[cfg(feature = "unchecked")]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(parent: Vec<u32>, rank: Vec<u8>, count: usize) -> Self {
        Self {
            parent,
            rank,
            count,
        }
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
#[path = "unit_tests/union_find.rs"]
mod tests;
