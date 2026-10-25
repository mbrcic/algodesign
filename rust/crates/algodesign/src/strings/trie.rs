// SPDX-License-Identifier: Apache-2.0
//! R-way trie over byte keys (Sedgewick–Wayne §5.2, `TrieST`). A node holds an optional value
//! and 256 child slots; the key is the path. Every operation is a loop, and `Drop`, `Clone`,
//! `PartialEq` and `Debug` are written by hand so a long key cannot overflow the stack.
//!
//! Lean: `lean/AlgoDesign/Strings/Trie/`.
//!
//! **Against the Python, and how fast.** A node here is an array of 256 child slots, one index per
//! byte and no hashing, where the Python's children live in a `dict`: so every node costs 256
//! pointers, `remove` is `O(R · |key|)` and `is_no_dead_branches` `O(R · n)`. `remove` is
//! Sedgewick–Wayne's recursive `TrieST.delete` as two loops. The API differs too: `iter` and
//! `iter_with_prefix` here, `keys()` and `contains` there. Not measured on its own; the
//! `words` group of
//! `STRINGS_STRUCTURES_ONLY=1 cargo bench -p algodesign --bench strings` times it beside the
//! Patricia tree and `BTreeMap` on the corpus's distinct words.

use std::fmt;

const ALPHABET: usize = 256;

/// The value at this path and one child slot per next byte.
struct Node<V> {
    value: Option<V>,
    next: Box<[Option<Box<Node<V>>>; ALPHABET]>,
}

impl<V> Node<V> {
    fn empty() -> Self {
        Node {
            value: None,
            next: Box::new(std::array::from_fn(|_| None)),
        }
    }
}

/// An R-way trie from byte-string keys to `V`; the empty key lives at the root. Its operations
/// keep [`Trie::is_valid`]; only `from_parts_unchecked` (feature `unchecked`, for tests that
/// build a broken trie on purpose: `cargo test --features unchecked`) can break it.
pub struct Trie<V> {
    root: Node<V>,
    len: usize,
}

impl<V> Default for Trie<V> {
    fn default() -> Self {
        Trie::new()
    }
}

impl<V> Trie<V> {
    /// The empty trie.
    #[must_use]
    pub fn new() -> Self {
        Trie {
            root: Node::empty(),
            len: 0,
        }
    }

    /// Number of keys currently holding a value. `O(1)`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is this trie empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Store `v` at `key`, returning the value it replaces. `O(|key|)`. Lean: `get_insert`.
    pub fn insert(&mut self, key: &[u8], v: V) -> Option<V> {
        let mut node = &mut self.root;
        for &byte in key {
            node = &mut **node.next[byte as usize].get_or_insert_with(|| Box::new(Node::empty()));
        }
        let old = node.value.replace(v);
        if old.is_none() {
            self.len += 1;
        }
        old
    }

    /// Remove `key`, returning its value, and cut the path suffix no other key uses
    /// (Sedgewick–Wayne's `TrieST.delete`). `O(R·|key|)`. Lean: `get_remove`, `words_remove`.
    #[allow(
        clippy::missing_panics_doc,
        reason = "the expects cannot fire: the second walk retraces the path the first walk found"
    )]
    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        // Depth of the deepest node that survives.
        let mut cut = 0;
        let mut node = &self.root;
        for (depth, &byte) in key.iter().enumerate() {
            if node.value.is_some() || node.next.iter().flatten().nth(1).is_some() {
                cut = depth;
            }
            node = node.next[byte as usize].as_deref()?;
        }
        node.value.as_ref()?;
        let prune = !key.is_empty() && node.next.iter().all(Option::is_none);
        self.len -= 1;

        let mut node = &mut self.root;
        if !prune {
            for &byte in key {
                node = node.next[byte as usize]
                    .as_deref_mut()
                    .expect("the path was walked");
            }
            return node.value.take();
        }
        for &byte in &key[..cut] {
            node = node.next[byte as usize]
                .as_deref_mut()
                .expect("the path was walked");
        }
        let mut chain = node.next[key[cut] as usize]
            .take()
            .expect("the path was walked");
        for &byte in &key[cut + 1..] {
            chain = chain.next[byte as usize]
                .take()
                .expect("the path was walked");
        }
        chain.value.take()
    }

    /// The node at `key`, if the path exists (whether or not it holds a value).
    fn node_at(&self, key: &[u8]) -> Option<&Node<V>> {
        let mut node = &self.root;
        for &byte in key {
            node = node.next[byte as usize].as_deref()?;
        }
        Some(node)
    }

    /// The value stored at `key`; `None` if absent or only a prefix of a stored key. `O(|key|)`.
    #[must_use]
    pub fn get(&self, key: &[u8]) -> Option<&V> {
        self.node_at(key).and_then(|n| n.value.as_ref())
    }

    /// Every stored key beginning with `p`, in lexicographic order.
    #[must_use]
    pub fn keys_with_prefix(&self, p: &[u8]) -> Vec<Vec<u8>> {
        self.iter_with_prefix(p).map(|(k, _)| k).collect()
    }

    /// Every `(key, value)` pair whose key begins with `p`, in lexicographic order, lazily.
    pub fn iter_with_prefix(&self, p: &[u8]) -> impl Iterator<Item = (Vec<u8>, &V)> + '_ {
        self.node_at(p)
            .map(|node| Iter::new(node, p.to_vec()))
            .into_iter()
            .flatten()
    }

    /// The longest prefix of `key` (the empty one included) that is a stored key. `O(|key|)`.
    #[must_use]
    pub fn longest_prefix<'k>(&self, key: &'k [u8]) -> Option<&'k [u8]> {
        let mut node = &self.root;
        let mut best = if node.value.is_some() { Some(0) } else { None };
        for (i, &byte) in key.iter().enumerate() {
            match node.next[byte as usize].as_deref() {
                Some(n) => {
                    node = n;
                    if node.value.is_some() {
                        best = Some(i + 1);
                    }
                }
                None => break,
            }
        }
        best.map(|len| &key[..len])
    }

    /// Every stored `(key, value)` pair, in lexicographic order.
    pub fn iter(&self) -> impl Iterator<Item = (Vec<u8>, &V)> + '_ {
        Iter::new(&self.root, Vec::new())
    }

    fn walk(&self) -> impl Iterator<Item = &Node<V>> + '_ {
        let mut stack = vec![&self.root];
        std::iter::from_fn(move || {
            let node = stack.pop()?;
            stack.extend(node.next.iter().filter_map(Option::as_deref));
            Some(node)
        })
    }

    /// Number of nodes, root included (1 for an empty trie): at most one per byte of the stored
    /// keys, besides the root. Lean: `Trie.nodeCount_le`.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.walk().count()
    }

    /// Box invariant 2: paths leaving the same point carry different letters. Lean:
    /// `Trie.DistinctLetters`. Held by the type (one slot per byte), so always `true`.
    #[must_use]
    pub fn is_distinct_letters(&self) -> bool {
        self.walk().all(|n| {
            let mut seen = [false; ALPHABET];
            n.next
                .iter()
                .enumerate()
                .filter(|(_, c)| c.is_some())
                .all(|(b, _)| !std::mem::replace(&mut seen[b], true))
        })
    }

    /// Box invariant 3: every branch leads to a stored word, so no node below the root is both
    /// valueless and childless. Lean: `Trie.NoDeadBranches`. `O(R·n)`.
    #[must_use]
    pub fn is_no_dead_branches(&self) -> bool {
        self.walk()
            .skip(1)
            .all(|n| n.value.is_some() || n.next.iter().any(Option::is_some))
    }

    /// Layout check (no Lean counterpart): the cached `len` equals the number of valued nodes.
    #[must_use]
    pub fn is_len_matches(&self) -> bool {
        self.walk().filter(|n| n.value.is_some()).count() == self.len
    }

    /// Lean `Trie.Valid` (distinct letters, no dead branches), then the layout check
    /// `is_len_matches`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Trie::is_valid`], naming the first check that fails.
    ///
    /// # Errors
    ///
    /// The name of the first failing check.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        // Box invariant 1, a word is a path of letters to a mark, is what `get` means: the paths
        // are the words. A child moved to another slot spells other words in a legal trie, so no
        // check of the tree alone can see it; the tests compare the keys with the words put in.
        if !self.is_distinct_letters() {
            return Err("invariant 2 (distinct_letters)");
        }
        if !self.is_no_dead_branches() {
            return Err("invariant 3 (no_dead_branches)");
        }
        if !self.is_len_matches() {
            return Err("layout (len_matches)");
        }
        Ok(())
    }

    /// The trie `root` writes out, `len` as given, unchecked. Feature `unchecked`.
    ///
    /// # Panics
    ///
    /// If one `children` list repeats a byte.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn from_parts_unchecked(root: TrieParts<V>, len: usize) -> Self {
        let mut flat: Vec<(usize, u8, Node<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, root)];
        while let Some((parent, byte, parts)) = stack.pop() {
            let me = flat.len();
            let mut node = Node::empty();
            node.value = parts.value;
            flat.push((parent, byte, node));
            stack.extend(parts.children.into_iter().map(|(b, c)| (me, b, c)));
        }
        while flat.len() > 1 {
            let (parent, byte, node) = flat.pop().expect("more than the root is left");
            let slot = &mut flat[parent].2.next[usize::from(byte)];
            assert!(
                slot.is_none(),
                "a repeated byte in one child list: a node has one slot per byte"
            );
            *slot = Some(Box::new(node));
        }
        let (_, _, root) = flat.pop().expect("the root was pushed first");
        Trie { root, len }
    }

    /// The trie written out as [`TrieParts`], children in byte order. Feature `unchecked`.
    #[cfg(feature = "unchecked")]
    #[allow(
        clippy::missing_panics_doc,
        reason = "the stack holds the root until the last pop"
    )]
    #[must_use]
    pub fn to_parts(&self) -> TrieParts<V>
    where
        V: Clone,
    {
        let parts = |node: &Node<V>| TrieParts {
            value: node.value.clone(),
            children: Vec::new(),
        };
        let mut flat: Vec<(usize, u8, TrieParts<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, &self.root)];
        while let Some((parent, byte, node)) = stack.pop() {
            let me = flat.len();
            flat.push((parent, byte, parts(node)));
            for (b, child) in (0..=u8::MAX).zip(node.next.iter()) {
                if let Some(c) = child {
                    stack.push((me, b, c.as_ref()));
                }
            }
        }
        while flat.len() > 1 {
            let (parent, byte, node) = flat.pop().expect("more than the root is left");
            flat[parent].2.children.push((byte, node));
        }
        flat.pop().expect("the root was pushed first").2
    }
}

/// A trie written out as plain data, for [`Trie::from_parts_unchecked`] and [`Trie::to_parts`].
#[cfg(feature = "unchecked")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrieParts<V> {
    /// The value stored at this node's path, if any.
    pub value: Option<V>,
    /// The children, each under the byte that leads to it.
    pub children: Vec<(u8, TrieParts<V>)>,
}

/// Depth-first traversal that carries the path.
struct Iter<'a, V> {
    path: Vec<u8>,
    stack: Vec<(&'a Node<V>, usize, u8)>,
    start: Option<&'a Node<V>>,
}

impl<'a, V> Iter<'a, V> {
    fn new(start: &'a Node<V>, path: Vec<u8>) -> Self {
        Iter {
            path,
            stack: Vec::new(),
            start: Some(start),
        }
    }

    /// Push the children highest byte first, then yield the node's value, if any.
    fn visit(&mut self, node: &'a Node<V>) -> Option<(Vec<u8>, &'a V)> {
        let depth = self.path.len();
        for (b, child) in (0..=u8::MAX).zip(node.next.iter()).rev() {
            if let Some(c) = child {
                self.stack.push((c.as_ref(), depth, b));
            }
        }
        node.value.as_ref().map(|v| (self.path.clone(), v))
    }
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (Vec<u8>, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(start) = self.start.take() {
            if let Some(item) = self.visit(start) {
                return Some(item);
            }
        }
        while let Some((node, parent_depth, byte)) = self.stack.pop() {
            self.path.truncate(parent_depth);
            self.path.push(byte);
            if let Some(item) = self.visit(node) {
                return Some(item);
            }
        }
        None
    }
}

// Iterative: the derived drop glue would recurse once per node.
impl<V> Drop for Trie<V> {
    fn drop(&mut self) {
        let mut stack: Vec<Box<Node<V>>> =
            self.root.next.iter_mut().filter_map(Option::take).collect();
        while let Some(mut node) = stack.pop() {
            stack.extend(node.next.iter_mut().filter_map(Option::take));
        }
    }
}

// Structural and iterative: each node is copied once, `O(R·nodes)`, where re-inserting every key
// would copy each key's path again.
impl<V: Clone> Clone for Trie<V> {
    fn clone(&self) -> Self {
        // Pre-order: a parent's index is below its children's, so popping attaches leaves first.
        let mut flat: Vec<(usize, u8, Node<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, &self.root)];
        while let Some((parent, byte, node)) = stack.pop() {
            let me = flat.len();
            let mut copy = Node::empty();
            copy.value.clone_from(&node.value);
            flat.push((parent, byte, copy));
            for (b, child) in (0..=u8::MAX).zip(node.next.iter()) {
                if let Some(c) = child {
                    stack.push((me, b, c.as_ref()));
                }
            }
        }
        while flat.len() > 1 {
            let (parent, byte, node) = flat.pop().expect("more than the root is left");
            flat[parent].2.next[usize::from(byte)] = Some(Box::new(node));
        }
        let (_, _, root) = flat.pop().expect("the root was pushed first");
        Trie {
            root,
            len: self.len,
        }
    }
}

// Both tries walked in lockstep, `O(R·nodes)`. A trie `insert` builds is the only one for its
// keys, so this is equality of the two maps.
impl<V: PartialEq> PartialEq for Trie<V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let mut stack = vec![(&self.root, &other.root)];
        while let Some((a, b)) = stack.pop() {
            if a.value != b.value {
                return false;
            }
            for (x, y) in a.next.iter().zip(b.next.iter()) {
                match (x, y) {
                    (None, None) => {}
                    (Some(x), Some(y)) => stack.push((x.as_ref(), y.as_ref())),
                    _ => return false,
                }
            }
        }
        true
    }
}

impl<V: Eq> Eq for Trie<V> {}

/// Insert every pair in turn; a later value for a key wins.
impl<K: AsRef<[u8]>, V> Extend<(K, V)> for Trie<V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k.as_ref(), v);
        }
    }
}

/// The empty trie extended by every pair.
impl<K: AsRef<[u8]>, V> FromIterator<(K, V)> for Trie<V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut out = Trie::new();
        out.extend(iter);
        out
    }
}

impl<V: fmt::Debug> fmt::Debug for Trie<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(test)]
#[path = "unit_tests/trie.rs"]
mod tests;
