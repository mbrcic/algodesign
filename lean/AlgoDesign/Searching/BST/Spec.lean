/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Defs.LinearOrder
public import AlgoDesign.Searching.RangeQuery
public import AlgoDesign.Searching.SearchTree
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Binary search tree: the specification

Sources: the Search chapter, "Escaping the line"; Sedgewick and Wayne, *Algorithms* (4th ed.),
§3.2; Sedgewick and Flajolet, *An Introduction to the Analysis of Algorithms*, §6.6–6.11.

> **Goal:** keep a changing set of keys, adding a key without moving any already stored.
>
> **Promise:** a set, kept in order. Search says whether a key is there. Insert adds a key; delete
> takes one out. Every other key stays in the set. The keys come out in increasing order, so the
> next larger key and every key in a range can be read off.
>
> **Idea:** escape the line: hang the keys on a branching shape, where every key has room for two
> more below it.
>
> **Invariants:**
>
> 1. Everything left of a key is smaller, everything right of it is larger.
>
> **Cost:** operations follow paths through the tree. Keys inserted in sorted order can make those
> paths as long as the set.
>
> **Assumes:** the keys arrive in an order that looks random, not sorted or nearly so. Otherwise the
> tree grows into a line, and every operation walks the whole set.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`BST.contract` proves the library's operations, `ops`, meet it.

- Goal [mentioned] → the search tree's operations, each a field of `Ops`; "adding a key without
  moving any already stored": insert hangs one new node.
- Promise [proved] → `SearchTree.Promise`, the search tree's.
- Idea [mentioned] → the branching shape is the type, `BST`.
- Invariants [proved] → `Valid`, one piece per box line: 1 `Sorted`
  Not in the box: the empty tree is valid, `Ops.emptyValid`, and insert and delete keep it,
  `Ops.insertKeeps` and `Ops.deleteKeeps`.
- Cost [argued] → search and insert within the height, so within `n`, proved; delete's
  comparisons argued, `DeleteCost`; sorted input making the paths `n` long, proved,
  `height_foldl_insert_sorted`.
- Assumes [mentioned] → random order is the analysis's (`internalPathLength_eq`), not a theorem
  about `BST.insert`; the cost model counts one step per comparison.

-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- A binary search tree of keys, no associated values. -/
inductive BST (α : Type) : Type where
  /-- The empty tree. -/
  | leaf : BST α
  /-- A node with a left subtree, a key, and a right subtree. -/
  | node (left : BST α) (key : α) (right : BST α) : BST α
  deriving Repr, DecidableEq

namespace BST

variable {α : Type}

/-- Every key in the tree satisfies `p`. -/
def All (p : α → Prop) : BST α → Prop
  | leaf => True
  | node l k r => All p l ∧ p k ∧ All p r

variable [LinearOrder α]

omit [LinearOrder α] in
/-- The keys in order. -/
def toList : BST α → List α
  | leaf => []
  | node l k r => toList l ++ k :: toList r

/-- Box invariant 1: everything left of a key is smaller, everything right of it is larger.
Every key in the left subtree is less than the node's key, every key in the right subtree is
greater, recursively throughout. -/
def Sorted : BST α → Prop
  | leaf => True
  | node l k r => All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r

/-- Longest root-to-leaf path, in edges: the BST box's cost is stated in it, fixed here so no
design picks its own. Unbalanced BSTs can have `height = size`. -/
def height : BST α → ℕ
  | leaf => 0
  | node l _ r => max (height l) (height r) + 1

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per claim.
`BST.lean`, the file that imports the whole structure, proves the library's operations meet it
(`BST.contract`). -/

/-- The operations the box speaks of: the search tree's, and versions of search and insert that
count their comparisons. -/
structure Ops (α : Type) where
  /-- The empty tree. -/
  empty : BST α
  /-- Add a key. -/
  insert : α → BST α → BST α
  /-- Take a key out. -/
  delete : α → BST α → BST α
  /-- Is the key there? -/
  search : α → BST α → Bool
  /-- The design's invariants. -/
  Valid : BST α → Prop
  /-- Search, counting comparisons. -/
  searchM : α → BST α → TimeM ℕ Bool
  /-- Insert, counting comparisons. -/
  insertM : α → BST α → TimeM ℕ (BST α)
  /-- The counting versions answer as the operations do, so the costs are of the operations. -/
  counted : ∀ a t, (searchM a t).ret = search a t ∧ (insertM a t).ret = insert a t
  /-- The empty tree is valid. -/
  emptyValid : Valid empty
  /-- Insert keeps the invariants. -/
  insertKeeps : ∀ a t, Valid t → Valid (insert a t)
  /-- Delete keeps the invariants. -/
  deleteKeeps : ∀ a t, Valid t → Valid (delete a t)

/-- The tree's operations, listed in order by `BST.toList`. -/
def Ops.tree (o : Ops α) : SearchTree α (BST α) where
  empty := o.empty
  insert := o.insert
  delete := o.delete
  search := o.search
  toList := BST.toList
  Valid := o.Valid

/-- Operations follow paths through the tree, at most its height in comparisons: the counted
operation takes at most `height t` steps on any tree `t`. -/
def Ops.WithinHeight {β : Type} (_o : Ops α) (counted : α → BST α → TimeM ℕ β) : Prop :=
  ∀ a t, (counted a t).time ≤ height t

/-- **The BST invariant**: the box's one invariant, `Sorted`. Nothing constrains the shape. -/
def Valid (t : BST α) : Prop := Sorted t

/-- **The BST's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. Costs count the steps the counting operations count themselves. -/
structure Contract (o : Ops α) : Prop where
  -- Goal: keep a changing set of keys, adding a key without moving any already stored.
  /-- Promise: a set, kept in order. -/
  promise : o.tree.Promise  -- a set, kept in order
  -- Idea: escape the line: hang the keys on a branching shape, where every key has room for two
  -- more below it.
  /-- Invariants: the box's one. -/
  invariants : ∀ t, o.Valid t ↔
    Sorted t  -- 1. everything left of a key is smaller, everything right of it is larger
  /-- Cost: operations follow paths through the tree, at most its height in comparisons. -/
  cost :
    o.WithinHeight o.searchM ∧                   -- search: comparisons, one path
    o.WithinHeight o.insertM ∧                   -- insert: comparisons, one path
    o.tree.Within o.searchM (fun n => n) ∧       -- search: so at most n comparisons
    o.tree.Within o.insertM (fun n => n)         -- insert: so at most n comparisons
    -- delete's comparisons: argued, `DeleteCost`, beside delete
    -- sorted input can make the paths as long as the set: `height_foldl_insert_sorted`
  -- Assumes: the keys arrive in an order that looks random, not sorted or nearly so. Otherwise the
  -- tree grows into a line, and every operation walks the whole set.

end BST

end AlgoDesign.Searching
