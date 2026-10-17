/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Order.Defs.LinearOrder
public import AlgoDesign.Searching.RangeQuery
public import Mathlib.Data.Nat.Log
public import Cslib.Algorithms.Lean.TimeM
public import AlgoDesign.Searching.SearchTree

/-!
# B-tree: the specification

Sources: the Search chapter, "Frankenstein"; Vitter, *Algorithms and Data Structures for External
Memory*, §11.1, with CLRS's minimum degree `t` (CLRS ch. 18).

> **Goal:** a search tree for real memory, which hands over whole blocks: each fetch costs far
> more than looking inside what it brought.
>
> **Promise:** the search tree's.
>
> **Idea:** work in blocks: one wide node per block, so every fetch brings back many keys.
>
> **Invariants:**
>
> 1. The keys are in strictly increasing order, inside every node and across nodes.
> 2. A node that is not a leaf has one more child than it has keys.
> 3. No node is ever more than full; every node but the root is at least half full, rounded down,
>    and never empty.
> 4. The root is either a leaf or has at least two children.
> 5. Every leaf sits at the same depth.
>
> **Cost:** fetches grow with the depth, $\log n$ to the base $t$, and $t$ is about half a node's
> width.
>
> **Assumes:** writes do not outrun reads. Otherwise every write still walks to its leaf, and those
> walks become the cost that matters.

Words: `deg` is the box's `t`; a fetch is one block read, one node.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`BTree.contract` proves the library's operations, `ops`, meet it at every minimum degree
from 2.

- Goal [required] → the search tree's operations, each a field of `Ops`.
- Promise [proved] → `SearchTree.Promise`, the search tree's.
- Idea [mentioned] → kept by invariants 3 and 4.
- Invariants [proved] → `Valid deg`, one piece per box line: 1 `KeysInOrder`, 2 `OneMoreChild`,
  3 `HalfFullToFull`, 4 `RootBranches`, 5 `SameDepth`
  Not in the box: `DegreeAtLeastTwo`, the last conjunct of `Valid`.
- Cost [proved] → search, insert and delete in block reads, each a `SearchTree.Within`; the shared
  target, `BTree.logarithmic`.
- Assumes [mentioned] → "writes do not outrun reads" is the workload's, not the tree's; the cost
  model counts one step per block read.

-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- A B-tree of keys, variable-arity: a node is a list of keys and, if internal, a list of
children. The shape rules are in `Valid`, not in the type. -/
inductive BTree (α : Type) : Type where
  /-- A leaf: just its keys, no children. -/
  | leaf (keys : List α) : BTree α
  /-- An internal node: its keys, and one more child than it has keys. -/
  | node (keys : List α) (children : List (BTree α)) : BTree α
  deriving Repr

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## What a tree holds

`toList`, the keys in order. Two correct B-trees may differ in shape but agree on `toList`. -/

mutual

/-- The tree's keys, in order: child, key, child, key, …, child. -/
def toList : BTree α → List α
  | leaf ks => ks
  | node ks cs => childrenToList ks cs

/-- `toList` of a node: each child's keys, then the key that follows it. -/
def childrenToList : List α → List (BTree α) → List α
  | k :: ks, c :: cs => toList c ++ k :: childrenToList ks cs
  | [], c :: cs => toList c ++ childrenToList [] cs
  | ks, [] => ks

end

/-! ## The invariant

One piece per box line, in box order, then `DegreeAtLeastTwo`, not in the box. -/

/-- Box invariant 1: the keys are in strictly increasing order, inside every node and across
nodes. -/
def KeysInOrder (bt : BTree α) : Prop := (toList bt).Pairwise (· < ·)

mutual

/-- Box invariant 2: a node that is not a leaf has one more child than it has keys. -/
def OneMoreChild : BTree α → Prop
  | leaf _ => True
  | node ks cs => cs.length = ks.length + 1 ∧ ChildrenOneMoreChild cs

/-- `OneMoreChild` on every child. -/
def ChildrenOneMoreChild : List (BTree α) → Prop
  | [] => True
  | c :: cs => OneMoreChild c ∧ ChildrenOneMoreChild cs

end

/-- The keys a node holds itself, leaf or internal, not those of its children. -/
def nodeKeys : BTree α → List α
  | leaf ks => ks
  | node ks _ => ks

/-- A node's children; a leaf has none. -/
def children : BTree α → List (BTree α)
  | leaf _ => []
  | node _ cs => cs

mutual

/-- A node below the root, and every node beneath it, is at least half full and never more than
full: between `deg - 1` and `2 * deg - 1` keys. -/
def NodeHalfFull (deg : ℕ) : BTree α → Prop
  | leaf ks => deg - 1 ≤ ks.length ∧ ks.length ≤ 2 * deg - 1
  | node ks cs => deg - 1 ≤ ks.length ∧ ks.length ≤ 2 * deg - 1 ∧ ChildrenHalfFull deg cs

/-- `NodeHalfFull` on every child in a list. -/
def ChildrenHalfFull (deg : ℕ) : List (BTree α) → Prop
  | [] => True
  | c :: cs => NodeHalfFull deg c ∧ ChildrenHalfFull deg cs

end

/-- Box invariant 3: no node is ever more than full; every node but the root is at least half
full, rounded down, and never empty. Formally: the root holds at most `2 * deg - 1` keys, and every
node below it between `deg - 1` and `2 * deg - 1`, never empty since `2 ≤ deg`. -/
def HalfFullToFull (deg : ℕ) (bt : BTree α) : Prop :=
  (nodeKeys bt).length ≤ 2 * deg - 1 ∧ ∀ c ∈ children bt, NodeHalfFull deg c

/-- Box invariant 4: the root is either a leaf or has at least two children. -/
def RootBranches : BTree α → Prop
  | leaf _ => True
  | node _ cs => 2 ≤ cs.length

mutual

/-- The tree's depth if every leaf agrees on it, `none` otherwise. -/
def depth? : BTree α → Option ℕ
  | leaf _ => some 0
  | node _ cs => (childrenDepth? cs).map (· + 1)

/-- `some d` iff every child has `depth? = some d` for the same `d`; `none` if the list is empty
or disagrees. -/
def childrenDepth? : List (BTree α) → Option ℕ
  | [] => none
  | [c] => c.depth?
  | c :: cs =>
      match c.depth?, childrenDepth? cs with
      | some d, some d' => if d = d' then some d else none
      | _, _ => none

end

/-- Box invariant 5: every leaf sits at the same depth. -/
def SameDepth (t : BTree α) : Prop := t.depth? ≠ none

/-- Not in the box: the minimum degree is at least 2; smaller degrees are
rejected when the tree is constructed. -/
abbrev DegreeAtLeastTwo (deg : ℕ) : Prop := 2 ≤ deg

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per claim.
`BTree.lean`, the file that imports the whole structure, proves the library's operations meet it at
every minimum degree from 2
(`BTree.contract`). -/

/-- The operations the box speaks of at minimum degree `deg`: the search tree's, and versions of
search, insert and delete that count block reads. -/
structure Ops (α : Type) (deg : ℕ) where
  /-- The empty tree. -/
  empty : BTree α
  /-- Add a key. -/
  insert : α → BTree α → BTree α
  /-- Take a key out. -/
  delete : α → BTree α → BTree α
  /-- Is the key there? -/
  search : α → BTree α → Bool
  /-- The design's invariants. -/
  Valid : BTree α → Prop
  /-- Search, counting block reads. -/
  searchM : α → BTree α → TimeM ℕ Bool
  /-- Insert, counting block reads. -/
  insertM : α → BTree α → TimeM ℕ (BTree α)
  /-- Delete, counting block reads. -/
  deleteM : α → BTree α → TimeM ℕ (BTree α)
  /-- The counting versions answer as the operations do, so the costs are of the operations. -/
  counted : ∀ a t, (searchM a t).ret = search a t ∧ (insertM a t).ret = insert a t ∧
    (deleteM a t).ret = delete a t

/-- The tree's operations, listed in order by `BTree.toList`. -/
def Ops.tree {deg : ℕ} (o : Ops α deg) : SearchTree α (BTree α) where
  empty := o.empty
  insert := o.insert
  delete := o.delete
  search := o.search
  toList := BTree.toList
  Valid := o.Valid

/-- A legal B-tree of minimum degree `deg` (`deg` is the box's `t`): box invariants 1 to 5, then
`DegreeAtLeastTwo`, not in the box. -/
def Valid (deg : ℕ) (bt : BTree α) : Prop :=
  KeysInOrder bt ∧ OneMoreChild bt ∧ HalfFullToFull deg bt ∧ RootBranches bt ∧ SameDepth bt ∧
    DegreeAtLeastTwo deg

/-- **The B-tree's contract**, at minimum degree `deg`, the part of the design Lean checks, one
field per box field and one conjunct per box line. Costs count the steps the counting operations
count themselves. -/
structure Contract {deg : ℕ} (o : Ops α deg) : Prop where
  -- Goal: a search tree for real memory, which hands over whole blocks: each fetch costs far
  -- more than looking inside what it brought.
  /-- Promise: the search tree's. -/
  promise : o.tree.Promise  -- the search tree's
  -- Idea: work in blocks: one wide node per block, so every fetch brings back many keys.
  /-- Invariants: the box's five, in box order, at this degree. -/
  invariants : ∀ t, o.Valid t ↔
    KeysInOrder t ∧        -- 1. the keys are in strictly increasing order
    OneMoreChild t ∧       -- 2. a node that is not a leaf has one more child than keys
    HalfFullToFull deg t ∧ -- 3. never more than full; below the root, at least half full
    RootBranches t ∧       -- 4. the root is a leaf or has at least two children
    SameDepth t ∧          -- 5. every leaf sits at the same depth
    DegreeAtLeastTwo deg   -- not in the box: the degree is at least 2
  /-- Cost: fetches grow with the depth, `log n` to the base `t`. -/
  cost :
    o.tree.Within o.searchM (fun n => Nat.log deg ((n + 1) / 2) + 1) ∧  -- search: block reads
    o.tree.Within o.insertM (fun n => Nat.log deg ((n + 1) / 2) + 2) ∧  -- insert: one more
    o.tree.Within o.deleteM (fun n => Nat.log deg ((n + 1) / 2) + 2)    -- delete: one more
    -- "t is about half a node's width": a node holds at most `2 * deg - 1` keys, invariant 3
  -- Assumes: writes do not outrun reads. Otherwise every write still walks to its leaf, and those
  -- walks become the cost that matters.

end BTree

end AlgoDesign.Searching
