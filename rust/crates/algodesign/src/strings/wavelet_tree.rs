// SPDX-License-Identifier: Apache-2.0
//! A **Huffman-shaped wavelet tree** over a byte sequence (Navarro, *Compact Data Structures*,
//! §6.2.4): `access`, `rank` (over the BWT, `occ`) and `select`, with its bits in a pluggable
//! bitvector backend, [`RankBits`]: [`BitIndex`] (plain) or [`Rrr`] (compressed).
//!
//! Stored bits: the Huffman encoding's length, below `n (H0 + 1)`; every node's bits concatenated
//! in preorder into one bitvector. Huffman ties merge the two lightest by `(weight, id)`, leaves
//! taking ids `0..σ` in ascending byte order. No Lean model.

use std::cmp::Reverse;
use std::collections::BinaryHeap;

use crate::strings::bits::partition_point;
use crate::strings::count_index::{Alphabet, BitIndex};
use crate::strings::rrr::Rrr;

/// What a wavelet tree needs from its bitvector: build it, then answer `rank`, `access` and
/// `select` over it.
///
/// Open on purpose, unlike [`Occ`](crate::strings::occ::Occ): any bitvector that answers these
/// queries can back a [`WaveletTree`], which is how [`BitIndex`] and [`Rrr`] both do.
pub trait RankBits: Sized {
    /// Index the first `len` bits of `words`, bit `i` being bit `i % 64` of word `i / 64`.
    fn build(words: &[u64], len: usize) -> Self;
    /// Bits indexed.
    fn len(&self) -> usize;
    /// Whether no bits are indexed.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Set bits strictly before `i`, saturating at `len`.
    fn rank1(&self, i: usize) -> usize;
    /// Bit `i` and how many positions before `i` hold the same bit. `i < len`.
    fn access_rank(&self, i: usize) -> (bool, usize);
    /// Position of the `j`-th (zero-based) set bit.
    fn select1(&self, j: usize) -> Option<usize>;
    /// Position of the `j`-th (zero-based) clear bit.
    fn select0(&self, j: usize) -> Option<usize>;
    /// Bytes this bitvector occupies, its directories included.
    fn size_bytes(&self) -> usize;
}

impl RankBits for Rrr {
    fn build(words: &[u64], len: usize) -> Self {
        Rrr::new(words, len)
    }
    fn len(&self) -> usize {
        Rrr::len(self)
    }
    fn rank1(&self, i: usize) -> usize {
        self.rank(i)
    }
    fn access_rank(&self, i: usize) -> (bool, usize) {
        Rrr::access_rank(self, i)
    }
    fn select1(&self, j: usize) -> Option<usize> {
        Rrr::select1(self, j)
    }
    fn select0(&self, j: usize) -> Option<usize> {
        Rrr::select0(self, j)
    }
    fn size_bytes(&self) -> usize {
        Rrr::size_bytes(self)
    }
}

impl RankBits for BitIndex {
    fn build(words: &[u64], len: usize) -> Self {
        BitIndex::new(words, len)
    }
    fn len(&self) -> usize {
        BitIndex::len(self)
    }
    fn rank1(&self, i: usize) -> usize {
        self.rank(i)
    }
    fn access_rank(&self, i: usize) -> (bool, usize) {
        let ones = self.rank(i);
        if self.get(i) {
            (true, ones)
        } else {
            (false, i - ones)
        }
    }
    fn select1(&self, j: usize) -> Option<usize> {
        self.select(j)
    }
    /// `BitIndex` has no `select0`, so this binary-searches `rank0`: `O(log n)` ranks.
    fn select0(&self, j: usize) -> Option<usize> {
        let n = BitIndex::len(self);
        if j >= n - self.rank(n) {
            return None;
        }
        // The smallest `p` with `rank0(p + 1) > j`.
        Some(partition_point(n, |p| p + 1 - self.rank(p + 1) <= j))
    }
    fn size_bytes(&self) -> usize {
        BitIndex::len(self).div_ceil(64) * size_of::<u64>() + self.overhead_bytes()
    }
}

/// Where a branch leads, unpacked from a [`Child`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Branch {
    /// Index into the tree's `nodes`.
    Node(u32),
    /// A leaf, holding its byte.
    Leaf(u8),
}

/// A [`Branch`] packed into four bytes, the top bit saying leaf.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Child(u32);

impl Child {
    const LEAF: u32 = 1 << 31;

    fn node(v: u32) -> Child {
        debug_assert!(v < Self::LEAF);
        Child(v)
    }

    fn leaf(s: u8) -> Child {
        Child(Self::LEAF | u32::from(s))
    }

    #[inline]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "a leaf holds the `u8` it was built from"
    )]
    fn branch(self) -> Branch {
        if self.0 & Self::LEAF == 0 {
            Branch::Node(self.0)
        } else {
            Branch::Leaf(self.0 as u8)
        }
    }
}

/// An internal node: where its bits sit in the tree's one bitvector, and its two children. Its
/// length is implied by preorder: the next node's start (or the total) minus its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Node {
    /// First bit of this node's bitvector.
    start: u32,
    /// Set bits in the whole bitvector before `start`.
    ones_before: u32,
    /// `child[0]` for a `0` bit, `child[1]` for a `1`.
    child: [Child; 2],
}

/// A symbol's Huffman code: `len` bits, the first in bit 0 of `bits`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Code {
    bits: u64,
    len: u32,
}

/// A Huffman-shaped wavelet tree over a byte sequence. See the module doc.
#[derive(Clone)]
pub struct WaveletTree<B: RankBits = BitIndex> {
    /// Length of the sequence.
    len: usize,
    /// The distinct bytes of the sequence.
    alphabet: Alphabet,
    /// Where the descent starts: `Leaf` for a one-symbol sequence, `Node(0)` otherwise.
    root: Child,
    /// Internal nodes, root first (preorder).
    nodes: Vec<Node>,
    /// Every node's bits, concatenated in preorder.
    bits: B,
    /// The code bits of each symbol, by dense index into `alphabet`; bit `d` is the code's
    /// `d`-th bit.
    code_bits: Vec<u64>,
    /// The code length of each symbol, likewise.
    code_lens: Vec<u8>,
}

impl<B: RankBits> WaveletTree<B> {
    /// Build the tree over `seq`. `O(n (H0 + 1) + σ log σ)`.
    ///
    /// # Panics
    ///
    /// If `seq` or its Huffman stream is longer than `u32::MAX`.
    #[must_use]
    pub fn new(seq: &[u8]) -> WaveletTree<B> {
        assert!(
            u32::try_from(seq.len()).is_ok(),
            "wavelet_tree: one tree covers at most u32::MAX positions; shard"
        );
        let alphabet = Alphabet::of(seq);
        let mut counts = [0u64; 256];
        for &b in seq {
            counts[b as usize] += 1;
        }

        // Huffman: pop the two lightest by (weight, id); `merged[k]` holds node `σ + k`'s
        // children.
        let sigma = alphabet.len();
        let mut heap: BinaryHeap<Reverse<(u64, usize)>> = alphabet
            .symbols()
            .iter()
            .enumerate()
            .map(|(id, &s)| Reverse((counts[s as usize], id)))
            .collect();
        let mut merged: Vec<[usize; 2]> = Vec::new();
        while heap.len() > 1 {
            let Some(Reverse((w0, a))) = heap.pop() else {
                break;
            };
            let Some(Reverse((w1, b))) = heap.pop() else {
                break;
            };
            merged.push([a, b]);
            heap.push(Reverse((w0 + w1, sigma + merged.len() - 1)));
        }

        // Lay the internal nodes out in preorder and give every leaf its code.
        let mut codes = vec![Code::default(); sigma];
        let mut layout: Vec<[Child; 2]> = Vec::with_capacity(merged.len());
        let root = if sigma == 0 {
            Child::leaf(0) // The empty sequence: no symbol is ever reached.
        } else {
            let top = sigma + merged.len() - 1;
            let mut placer = Placer {
                sigma,
                merged: &merged,
                symbols: alphabet.symbols(),
                codes: &mut codes,
                layout: &mut layout,
            };
            placer.place(top, Code::default())
        };

        // Each node's length is the total count of the symbols below it; its bits start where
        // its preorder predecessors' end.
        let mut paths: Vec<Vec<u32>> = vec![Vec::new(); sigma];
        let mut node_len = vec![0usize; layout.len()];
        for (d, &s) in alphabet.symbols().iter().enumerate() {
            let code = codes[d];
            let mut at = root;
            for depth in 0..code.len {
                let Branch::Node(v) = at.branch() else {
                    unreachable!("a code runs past a leaf")
                };
                paths[d].push(v);
                node_len[v as usize] +=
                    usize::try_from(counts[s as usize]).expect("a count is at most the length");
                at = layout[v as usize][((code.bits >> depth) & 1) as usize];
            }
        }
        let mut starts = Vec::with_capacity(layout.len());
        let mut total = 0usize;
        for &len in &node_len {
            starts.push(total);
            total += len;
        }
        assert!(
            u32::try_from(total).is_ok(),
            "wavelet_tree: the Huffman stream exceeds u32::MAX bits; shard"
        );

        // One pass over the sequence writes each symbol's bits into the nodes on its path.
        let mut words = vec![0u64; total.div_ceil(64)];
        let mut fill = starts.clone();
        for &s in seq {
            let d = alphabet
                .index_of(s)
                .expect("every symbol is in its own alphabet");
            let code = codes[d];
            for (depth, &v) in paths[d].iter().enumerate() {
                let (v, bit) = (v as usize, (code.bits >> depth) & 1);
                words[fill[v] / 64] |= bit << (fill[v] % 64);
                fill[v] += 1;
            }
        }
        let bits = B::build(&words, total);
        let nodes = layout
            .into_iter()
            .enumerate()
            .map(|(v, child)| Node {
                start: u32::try_from(starts[v]).expect("total <= u32::MAX, asserted above"),
                ones_before: u32::try_from(bits.rank1(starts[v])).expect("at most total"),
                child,
            })
            .collect();
        let code_bits = codes.iter().map(|c| c.bits).collect();
        let code_lens = codes
            .iter()
            .map(|c| u8::try_from(c.len).expect("a code fits its u64"))
            .collect();
        WaveletTree {
            len: seq.len(),
            alphabet,
            root,
            nodes,
            bits,
            code_bits,
            code_lens,
        }
    }

    /// Length of the sequence.
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the sequence is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The distinct bytes of the sequence, ascending.
    #[must_use]
    pub fn alphabet(&self) -> &Alphabet {
        &self.alphabet
    }

    /// Length of `c`'s Huffman code -- the depth of its leaf -- or `None` for a byte outside the
    /// alphabet.
    #[must_use]
    pub fn code_len(&self, c: u8) -> Option<u32> {
        self.alphabet.index_of(c).map(|d| self.code(d).len)
    }

    /// The code of dense symbol `d`.
    #[inline]
    fn code(&self, d: usize) -> Code {
        Code {
            bits: self.code_bits[d],
            len: u32::from(self.code_lens[d]),
        }
    }

    /// Bits in node `v`'s bitvector: up to the next node's start in preorder, or the end.
    fn node_len(&self, v: usize) -> usize {
        let end = self
            .nodes
            .get(v + 1)
            .map_or(self.bits.len(), |next| next.start as usize);
        end - self.nodes[v].start as usize
    }

    /// Set bits of node `v` before its position `i`.
    #[inline]
    fn node_rank1(&self, v: &Node, i: usize) -> usize {
        self.bits.rank1(v.start as usize + i) - v.ones_before as usize
    }

    /// Occurrences of `c` strictly before position `i`, saturating at `len`; `0` for a byte
    /// outside the alphabet. One bitvector rank per bit of `c`'s code.
    #[must_use]
    pub fn rank(&self, c: u8, i: usize) -> usize {
        let Some(d) = self.alphabet.index_of(c) else {
            return 0;
        };
        let code = self.code(d);
        let mut i = i.min(self.len);
        let mut at = self.root;
        for depth in 0..code.len {
            let Branch::Node(v) = at.branch() else {
                unreachable!("a code runs past a leaf")
            };
            let node = &self.nodes[v as usize];
            let bit = (code.bits >> depth) & 1;
            let ones = self.node_rank1(node, i);
            i = if bit == 1 { ones } else { i - ones };
            at = node.child[bit as usize];
        }
        i
    }

    /// The symbol at position `i`.
    ///
    /// # Panics
    ///
    /// If `i >= len`.
    #[must_use]
    pub fn access(&self, i: usize) -> u8 {
        self.access_rank(i).0
    }

    /// The symbol `c` at position `i` and `rank(c, i)`, in one descent.
    ///
    /// # Panics
    ///
    /// If `i >= len`.
    #[must_use]
    pub fn access_rank(&self, i: usize) -> (u8, usize) {
        assert!(
            i < self.len,
            "wavelet_tree: position {i} is past the end ({})",
            self.len
        );
        let mut i = i;
        let mut at = self.root;
        loop {
            match at.branch() {
                Branch::Leaf(s) => return (s, i),
                Branch::Node(v) => {
                    let node = &self.nodes[v as usize];
                    let (bit, same) = self.bits.access_rank(node.start as usize + i);
                    let ones_before = node.ones_before as usize;
                    i = if bit {
                        same - ones_before
                    } else {
                        same - (node.start as usize - ones_before)
                    };
                    at = node.child[usize::from(bit)];
                }
            }
        }
    }

    /// Position of the `j`-th (zero-based) occurrence of `c`, or `None` when there are not
    /// `j + 1`. Down to the leaf along `c`'s code, then up through `select` at each node.
    #[must_use]
    pub fn select(&self, c: u8, j: usize) -> Option<usize> {
        let d = self.alphabet.index_of(c)?;
        let code = self.code(d);
        let mut path = Vec::with_capacity(code.len as usize);
        let mut at = self.root;
        for depth in 0..code.len {
            let Branch::Node(v) = at.branch() else {
                unreachable!("a code runs past a leaf")
            };
            path.push(v as usize);
            at = self.nodes[v as usize].child[((code.bits >> depth) & 1) as usize];
        }
        let mut j = j;
        if path.is_empty() {
            return (j < self.len).then_some(j);
        }
        for (depth, &v) in path.iter().enumerate().rev() {
            let node = &self.nodes[v];
            let (start, ones_before) = (node.start as usize, node.ones_before as usize);
            let len = self.node_len(v);
            let ones = self.node_rank1(node, len);
            let at = if (code.bits >> depth) & 1 == 1 {
                if j >= ones {
                    return None;
                }
                self.bits.select1(ones_before + j)?
            } else {
                if j >= len - ones {
                    return None;
                }
                self.bits.select0(start - ones_before + j)?
            };
            j = at - start;
        }
        Some(j)
    }

    /// Bits stored in the tree: `Σ_c n_c |code(c)|`.
    #[must_use]
    pub fn stored_bits(&self) -> usize {
        self.bits.len()
    }

    /// Bytes this tree allocates: bitvector, node table, code table and alphabet.
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        self.bits.size_bytes()
            + self.nodes.len() * size_of::<Node>()
            + self.code_bits.len() * size_of::<u64>()
            + self.code_lens.len()
            + size_of::<Alphabet>()
            + self.alphabet.len()
    }
}

/// Lays the Huffman merges out as a preorder node table and assigns the codes.
struct Placer<'a> {
    sigma: usize,
    merged: &'a [[usize; 2]],
    symbols: &'a [u8],
    codes: &'a mut Vec<Code>,
    layout: &'a mut Vec<[Child; 2]>,
}

impl Placer<'_> {
    /// Give node `id`'s subtree its codes and preorder slots; return what a parent's branch
    /// should point at.
    fn place(&mut self, id: usize, code: Code) -> Child {
        if id < self.sigma {
            self.codes[id] = code;
            return Child::leaf(self.symbols[id]);
        }
        assert!(
            code.len < 64,
            "wavelet_tree: a Huffman code exceeded 64 bits"
        );
        let slot = self.layout.len();
        self.layout.push([Child::leaf(0); 2]);
        let [a, b] = self.merged[id - self.sigma];
        let zero = Code {
            bits: code.bits,
            len: code.len + 1,
        };
        let one = Code {
            bits: code.bits | (1 << code.len),
            len: code.len + 1,
        };
        let left = self.place(a, zero);
        let right = self.place(b, one);
        self.layout[slot] = [left, right];
        Child::node(u32::try_from(slot).expect("fewer than 256 nodes"))
    }
}

impl<B: RankBits> std::fmt::Debug for WaveletTree<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WaveletTree")
            .field("len", &self.len)
            .field("sigma", &self.alphabet.len())
            .field("internal_nodes", &self.nodes.len())
            .field("size_bytes", &self.size_bytes())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "unit_tests/wavelet_tree.rs"]
mod tests;
