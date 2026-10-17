// SPDX-License-Identifier: Apache-2.0
//! Patricia, the path-compressed radix tree over byte keys: an edge-labelled compressed trie
//! (Weiss §12.4.2; Nipkow et al. §12.3). Children are sorted by first byte and found by binary
//! search; `insert` splits an edge where a key diverges mid-label.
//!
//! Lean: `lean/AlgoDesign/Strings/Patricia/`.
//!
//! **Against the Python, and how fast.** Children are a `Vec` sorted by first byte, each child
//! boxed so an entry is 16 bytes for the binary search, where the Python files them in a `dict` by
//! first byte; so `is_valid` adds one layout check the Python has no use for, `is_sorted_heads`
//! (the Lean `SortedHeads`). `remove` is a loop over an index path; the Python's recurses. Not yet
//! measured; the `words` group of
//! `STRINGS_STRUCTURES_ONLY=1 cargo bench -p algodesign --bench strings` times it beside the trie
//! and `BTreeMap` on the corpus's distinct words.

use std::fmt;

/// `label` is the incoming edge (empty only at the root); `children` are sorted by first byte.
/// Boxing a child keeps an entry at 16 bytes for the binary search.
struct Node<V> {
    label: Box<[u8]>,
    value: Option<V>,
    children: Vec<(u8, Box<Node<V>>)>,
}

impl<V> Node<V> {
    fn leaf(label: &[u8], value: V) -> Self {
        Node {
            label: label.to_vec().into_boxed_slice(),
            value: Some(value),
            children: Vec::new(),
        }
    }
}

/// Merge `node`, valueless with exactly one child, into that child, concatenating the labels.
fn absorb_only_child<V>(node: &mut Node<V>) {
    debug_assert!(node.value.is_none() && node.children.len() == 1);
    let (_, child) = node.children.pop().expect("exactly one child");
    let Node {
        label,
        value,
        children,
    } = *child;
    let mut merged = std::mem::take(&mut node.label).into_vec();
    merged.extend_from_slice(&label);
    node.label = merged.into_boxed_slice();
    node.value = value;
    node.children = children;
}

fn common_prefix_len(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b.iter()).take_while(|(x, y)| x == y).count()
}

/// A path-compressed radix tree from byte-string keys to `V`; the empty key lives at the root. Its
/// operations keep [`Patricia::is_valid`]; only `from_parts_unchecked` (feature `unchecked`, for
/// tests that build a broken tree on purpose: `cargo test --features unchecked`) can break it.
pub struct Patricia<V> {
    root: Node<V>,
    len: usize,
}

impl<V> Default for Patricia<V> {
    fn default() -> Self {
        Patricia::new()
    }
}

impl<V> Patricia<V> {
    /// The empty Patricia tree.
    #[must_use]
    pub fn new() -> Self {
        Patricia {
            root: Node {
                label: Box::new([]),
                value: None,
                children: Vec::new(),
            },
            len: 0,
        }
    }

    /// Number of keys currently holding a value. `O(1)`.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is this Patricia tree empty?
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Store `v` at `key`, returning the value it replaces. `O(|key|)`. Lean: `valid_insertSorted`,
    /// `insertSpec_insertSorted_ofListSorted`.
    pub fn insert(&mut self, key: &[u8], v: V) -> Option<V> {
        let mut node = &mut self.root;
        let mut rest = key;
        loop {
            if rest.is_empty() {
                let old = node.value.replace(v);
                if old.is_none() {
                    self.len += 1;
                }
                return old;
            }
            let b = rest[0];
            let idx = match node.children.binary_search_by_key(&b, |(byte, _)| *byte) {
                Ok(i) => i,
                Err(i) => {
                    node.children.insert(i, (b, Box::new(Node::leaf(rest, v))));
                    self.len += 1;
                    return None;
                }
            };
            let label_len = node.children[idx].1.label.len();
            let common = common_prefix_len(&node.children[idx].1.label, rest);
            if common == label_len {
                rest = &rest[common..];
                node = &mut node.children[idx].1;
                continue;
            }
            // Split the edge after `common` bytes, in place: the old contents move to a new box.
            let slot = &mut node.children[idx].1;
            let old_label = std::mem::take(&mut slot.label);
            let suffix_first = old_label[common];
            let lower = Box::new(Node {
                label: old_label[common..].to_vec().into_boxed_slice(),
                value: slot.value.take(),
                children: std::mem::take(&mut slot.children),
            });
            slot.label = old_label[..common].to_vec().into_boxed_slice();
            if common == rest.len() {
                slot.value = Some(v);
                slot.children = vec![(suffix_first, lower)];
            } else {
                let rest_suffix = &rest[common..];
                let mut children = vec![
                    (suffix_first, lower),
                    (rest_suffix[0], Box::new(Node::leaf(rest_suffix, v))),
                ];
                children.sort_by_key(|(byte, _)| *byte);
                slot.children = children;
            }
            self.len += 1;
            return None;
        }
    }

    /// Remove `key`, returning its value; then unlink a node left childless or merge one left
    /// with one child. Lean: `get_remove`, `words_remove`, `branchesUnlessWordEnds_remove`,
    /// `noEmptyBranches_remove`.
    pub fn remove(&mut self, key: &[u8]) -> Option<V> {
        let mut path: Vec<usize> = Vec::new();
        let mut node = &self.root;
        let mut rest = key;
        while !rest.is_empty() {
            let idx = node
                .children
                .binary_search_by_key(&rest[0], |(byte, _)| *byte)
                .ok()?;
            let next = &node.children[idx].1;
            if !rest.starts_with(&next.label) {
                return None;
            }
            rest = &rest[next.label.len()..];
            node = next;
            path.push(idx);
        }
        node.value.as_ref()?;
        self.len -= 1;

        let Some((&last, above)) = path.split_last() else {
            return self.root.value.take();
        };
        let mut parent = &mut self.root;
        for &i in above {
            parent = &mut parent.children[i].1;
        }
        let target = &mut parent.children[last].1;
        let old = target.value.take();
        match target.children.len() {
            0 => {
                parent.children.remove(last);
                if !above.is_empty() && parent.value.is_none() && parent.children.len() == 1 {
                    absorb_only_child(parent);
                }
            }
            1 => absorb_only_child(target),
            _ => {}
        }
        old
    }

    /// The value stored at `key`, if any. `O(|key|)`.
    #[must_use]
    pub fn get(&self, key: &[u8]) -> Option<&V> {
        let mut node = &self.root;
        let mut rest = key;
        while !rest.is_empty() {
            let b = rest[0];
            let idx = node
                .children
                .binary_search_by_key(&b, |(byte, _)| *byte)
                .ok()?;
            let child = &node.children[idx].1;
            if !rest.starts_with(&child.label) {
                return None;
            }
            rest = &rest[child.label.len()..];
            node = child;
        }
        node.value.as_ref()
    }

    /// Every stored key beginning with `p`, in lexicographic order.
    #[must_use]
    pub fn keys_with_prefix(&self, p: &[u8]) -> Vec<Vec<u8>> {
        self.iter_with_prefix(p).map(|(k, _)| k).collect()
    }

    /// Every `(key, value)` pair whose key begins with `p`, in lexicographic order, lazily.
    pub fn iter_with_prefix(&self, p: &[u8]) -> impl Iterator<Item = (Vec<u8>, &V)> + '_ {
        self.subtree_at(p)
            .map(|(node, path)| Iter::new(node, path))
            .into_iter()
            .flatten()
    }

    /// The node whose subtree holds exactly the keys beginning with `p`, and its path.
    fn subtree_at(&self, p: &[u8]) -> Option<(&Node<V>, Vec<u8>)> {
        let mut node = &self.root;
        let mut consumed: Vec<u8> = Vec::new();
        let mut rest = p;
        while let Some(&b) = rest.first() {
            let Ok(idx) = node.children.binary_search_by_key(&b, |(byte, _)| *byte) else {
                return None;
            };
            let child = &node.children[idx].1;
            if child.label.len() <= rest.len() {
                if !rest.starts_with(&child.label) {
                    return None;
                }
                rest = &rest[child.label.len()..];
            } else if !child.label.starts_with(rest) {
                return None;
            } else {
                rest = &[];
            }
            consumed.extend_from_slice(&child.label);
            node = child;
        }
        Some((node, consumed))
    }

    /// The longest prefix of `key` (the empty one included) that is a stored key. `O(|key|)`.
    #[must_use]
    pub fn longest_prefix<'k>(&self, key: &'k [u8]) -> Option<&'k [u8]> {
        let mut node = &self.root;
        let mut best = if node.value.is_some() { Some(0) } else { None };
        let mut consumed = 0usize;
        let mut rest = key;
        while !rest.is_empty() {
            let b = rest[0];
            let Ok(idx) = node.children.binary_search_by_key(&b, |(byte, _)| *byte) else {
                break;
            };
            let child = &node.children[idx].1;
            if !rest.starts_with(&child.label) {
                break;
            }
            consumed += child.label.len();
            rest = &rest[child.label.len()..];
            node = child;
            if node.value.is_some() {
                best = Some(consumed);
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
            stack.extend(node.children.iter().map(|(_, c)| c.as_ref()));
            Some(node)
        })
    }

    /// Number of nodes, root included (1 when empty): at most two per key once one key is
    /// stored. Lean: `Patricia.nodeCount_le`.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.walk().count()
    }

    /// Box invariant 2: the branches leaving a node start with different letters. Lean:
    /// `DistinctFirstLetters`, read from the labels (an empty label's head is `None`).
    #[must_use]
    pub fn is_distinct_first_letters(&self) -> bool {
        self.walk().all(|n| {
            // Slot 256 is the head `None`.
            let mut seen = [false; 257];
            n.children.iter().all(|(_, c)| {
                let head = c.label.first().map_or(256, |&b| usize::from(b));
                !std::mem::replace(&mut seen[head], true)
            })
        })
    }

    /// Box invariant 3: every node below the root where no word ends has two children or more.
    /// Lean: `BranchesUnlessWordEnds`.
    #[must_use]
    pub fn is_branches_unless_word_ends(&self) -> bool {
        self.walk()
            .skip(1)
            .all(|n| n.value.is_some() || n.children.len() >= 2)
    }

    /// Box invariant 4: every branch carries at least one letter. Lean: `NoEmptyBranches`.
    #[must_use]
    pub fn is_no_empty_branches(&self) -> bool {
        self.walk().skip(1).all(|n| !n.label.is_empty())
    }

    /// Lean `SortedHeads`: in every child list the labels' first bytes strictly ascend (an empty
    /// label reads as `0`).
    #[must_use]
    pub fn is_sorted_heads(&self) -> bool {
        let head = |c: &Node<V>| c.label.first().copied().unwrap_or(0);
        self.walk()
            .all(|n| n.children.windows(2).all(|w| head(&w[0].1) < head(&w[1].1)))
    }

    /// Layout check (no Lean counterpart): each child's tag equals its label's first byte.
    #[must_use]
    pub fn is_children_filed_by_head(&self) -> bool {
        self.walk().all(|n| {
            n.children
                .iter()
                .all(|(tag, c)| c.label.first() == Some(tag))
        })
    }

    /// Layout check (no Lean counterpart): the cached `len` equals the number of valued nodes.
    #[must_use]
    pub fn is_len_matches(&self) -> bool {
        self.walk().filter(|n| n.value.is_some()).count() == self.len
    }

    /// Lean `Patricia.Valid` (invariants 2, 3 and 4), then the layout checks
    /// `is_sorted_heads`, `is_children_filed_by_head` and `is_len_matches`.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`Patricia::is_valid`], naming the first check that fails.
    ///
    /// # Errors
    ///
    /// The name of the first failing check.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        // Box invariant 1, a word is the path from the root to a mark, is what `get` means. An
        // edge relabelled to start with another letter fails `is_children_filed_by_head`; one
        // changed after its first letter spells other words in a legal tree, which no check of the
        // tree alone can see, so the tests compare the keys with the words put in.
        let checks = [
            (
                Self::is_distinct_first_letters as fn(&Self) -> bool,
                "invariant 2 (distinct_first_letters)",
            ),
            (
                Self::is_branches_unless_word_ends,
                "invariant 3 (branches_unless_word_ends)",
            ),
            (
                Self::is_no_empty_branches,
                "invariant 4 (no_empty_branches)",
            ),
            (Self::is_sorted_heads, "layout (sorted_heads)"),
            (
                Self::is_children_filed_by_head,
                "layout (children_filed_by_head)",
            ),
            (Self::is_len_matches, "layout (len_matches)"),
        ];
        match checks.iter().find(|(holds, _)| !holds(self)) {
            Some(&(_, name)) => Err(name),
            None => Ok(()),
        }
    }

    /// The tree `root` writes out, everything as given, unchecked. Feature `unchecked`.
    ///
    /// # Panics
    ///
    /// If `root.label` is not empty.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn from_parts_unchecked(root: PatriciaParts<V>, len: usize) -> Self {
        assert!(
            root.label.is_empty(),
            "the root has no incoming edge, so its label must be empty"
        );
        // Pre-order: a parent's index is below its children's.
        let mut flat: Vec<(usize, u8, Node<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, root)];
        while let Some((parent, tag, parts)) = stack.pop() {
            let me = flat.len();
            flat.push((
                parent,
                tag,
                Node {
                    label: parts.label.into_boxed_slice(),
                    value: parts.value,
                    children: Vec::new(),
                },
            ));
            stack.extend(parts.children.into_iter().map(|(t, c)| (me, t, c)));
        }
        while flat.len() > 1 {
            let (parent, tag, node) = flat.pop().expect("more than the root is left");
            flat[parent].2.children.push((tag, Box::new(node)));
        }
        let (_, _, root) = flat.pop().expect("the root was pushed first");
        Patricia { root, len }
    }

    /// The tree written out as [`PatriciaParts`]. Feature `unchecked`.
    #[cfg(feature = "unchecked")]
    #[allow(
        clippy::missing_panics_doc,
        reason = "the stack holds the root until the last pop"
    )]
    #[must_use]
    pub fn to_parts(&self) -> PatriciaParts<V>
    where
        V: Clone,
    {
        let parts = |node: &Node<V>| PatriciaParts {
            label: node.label.to_vec(),
            value: node.value.clone(),
            children: Vec::new(),
        };
        let mut flat: Vec<(usize, u8, PatriciaParts<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, &self.root)];
        while let Some((parent, tag, node)) = stack.pop() {
            let me = flat.len();
            flat.push((parent, tag, parts(node)));
            stack.extend(node.children.iter().map(|(t, c)| (me, *t, c.as_ref())));
        }
        while flat.len() > 1 {
            let (parent, tag, node) = flat.pop().expect("more than the root is left");
            flat[parent].2.children.push((tag, node));
        }
        flat.pop().expect("the root was pushed first").2
    }
}

/// A Patricia tree written out as plain data, for [`Patricia::from_parts_unchecked`] and
/// [`Patricia::to_parts`]. Its derived glue recurses once per level.
#[cfg(feature = "unchecked")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatriciaParts<V> {
    /// The incoming edge's label; empty at the root.
    pub label: Vec<u8>,
    /// The value stored at the end of this node's path, if any.
    pub value: Option<V>,
    /// The children, each under its tag.
    pub children: Vec<(u8, PatriciaParts<V>)>,
}

/// Depth-first traversal that carries the path, one edge label per step.
struct Iter<'a, V> {
    path: Vec<u8>,
    /// Unvisited nodes, each with the path length to truncate to and the label to append.
    stack: Vec<(&'a Node<V>, usize, &'a [u8])>,
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

    /// Push the children last first, then yield the node's value, if any.
    fn visit(&mut self, node: &'a Node<V>) -> Option<(Vec<u8>, &'a V)> {
        let depth = self.path.len();
        for (_, child) in node.children.iter().rev() {
            self.stack.push((child.as_ref(), depth, &child.label));
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
        while let Some((node, parent_depth, label)) = self.stack.pop() {
            self.path.truncate(parent_depth);
            self.path.extend_from_slice(label);
            if let Some(item) = self.visit(node) {
                return Some(item);
            }
        }
        None
    }
}

// Iterative: the derived drop glue would recurse once per node.
impl<V> Drop for Patricia<V> {
    fn drop(&mut self) {
        let mut stack: Vec<Box<Node<V>>> = self.root.children.drain(..).map(|(_, c)| c).collect();
        while let Some(mut node) = stack.pop() {
            stack.extend(node.children.drain(..).map(|(_, c)| c));
        }
    }
}

// Structural and iterative: each node is copied once, `O(nodes)` plus the labels, where
// re-inserting every key would copy each key's path again.
impl<V: Clone> Clone for Patricia<V> {
    fn clone(&self) -> Self {
        // Pre-order: a parent's index is below its children's, so popping attaches leaves first,
        // and each child list comes back in its original, sorted order.
        let mut flat: Vec<(usize, u8, Node<V>)> = Vec::new();
        let mut stack = vec![(usize::MAX, 0u8, &self.root)];
        while let Some((parent, tag, node)) = stack.pop() {
            let me = flat.len();
            flat.push((
                parent,
                tag,
                Node {
                    label: node.label.clone(),
                    value: node.value.clone(),
                    children: Vec::with_capacity(node.children.len()),
                },
            ));
            stack.extend(node.children.iter().map(|(t, c)| (me, *t, c.as_ref())));
        }
        while flat.len() > 1 {
            let (parent, tag, node) = flat.pop().expect("more than the root is left");
            flat[parent].2.children.push((tag, Box::new(node)));
        }
        let (_, _, root) = flat.pop().expect("the root was pushed first");
        Patricia {
            root,
            len: self.len,
        }
    }
}

// Both trees walked in lockstep, `O(nodes)` plus the labels. A tree `insert` builds is the only
// compressed trie for its keys, so this is equality of the two maps.
impl<V: PartialEq> PartialEq for Patricia<V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let mut stack = vec![(&self.root, &other.root)];
        while let Some((a, b)) = stack.pop() {
            if a.label != b.label || a.value != b.value || a.children.len() != b.children.len() {
                return false;
            }
            for ((s, x), (t, y)) in a.children.iter().zip(b.children.iter()) {
                if s != t {
                    return false;
                }
                stack.push((x.as_ref(), y.as_ref()));
            }
        }
        true
    }
}

impl<V: Eq> Eq for Patricia<V> {}

/// Insert every pair in turn; a later value for a key wins.
impl<K: AsRef<[u8]>, V> Extend<(K, V)> for Patricia<V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, iter: I) {
        for (k, v) in iter {
            self.insert(k.as_ref(), v);
        }
    }
}

/// The empty tree extended by every pair.
impl<K: AsRef<[u8]>, V> FromIterator<(K, V)> for Patricia<V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut out = Patricia::new();
        out.extend(iter);
        out
    }
}

impl<V: fmt::Debug> fmt::Debug for Patricia<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(test)]
#[path = "unit_tests/patricia.rs"]
mod tests;
