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
public import AlgoDesign.Searching.RedBlackStandard.Spec
public import AlgoDesign.Searching.SearchTree

/-!
# Left-leaning red-black tree (LLRB): the specification

Sources: the Search chapter, "Sticky red links"; Sedgewick and Wayne, *Algorithms* (4th ed.),
§3.3, Algorithm 3.4.

> **Goal:** keep the search tree short, whatever order the keys arrive in.
>
> **Promise:** the search tree's.
>
> **Idea:** group the keys into nodes of one or two, held together by red links: a little
> imbalance, never more.
>
> **Invariants:**
>
> 1. The keys are in order, as in any search tree.
> 2. The top node is black.
> 3. A red link always leans left, never right.
> 4. No node ever has two red links touching it, not one on each side, and not one chained below
>    the other.
> 5. Every path from the root down to a spot where you'd fall off the tree crosses the same number
>    of black links.
>
> **Cost:** every operation grows with $\log n$: the tree is never much more than twice as tall as
> the best.
>
> **Assumes:** reaching any node costs about the same, as in the RAM model.

Words: a red link is the link into a node colored `red`.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`LLRB.contract` proves the library's operations, `ops`, meet it.

- Goal [required] → the search tree's operations, each a field of `Ops`.
- Promise [proved] → `SearchTree.Promise`, the search tree's.
- Idea [mentioned] → kept by invariants 2 to 5.
- Invariants [proved] → `Valid`, one piece per box line: 1 `Sorted`, 2 `RootBlack`,
  3 `LeftLeaning`, 4 `NoRedRed`, 5 `BlackHeightOk`
  Not in the box: the empty tree is valid, `Ops.emptyValid`, and insert and delete keep it,
  `Ops.insertKeeps` and `Ops.deleteKeeps`.
- Cost [argued] → the height, search, insert and delete's rotations proved; delete's comparisons
  argued, `DeleteCost`.
- Assumes [mentioned] → the cost model counts one step per comparison, whichever node it is at.

-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- A left-leaning red-black tree of keys, reusing `RedBlackStandard`'s `Color`. -/
inductive LLRB (α : Type) : Type where
  /-- The empty tree. -/
  | leaf : LLRB α
  /-- A node, colored (the color of the link from its parent), with a left subtree, a key, and a
  right subtree. -/
  | node (color : Color) (left : LLRB α) (key : α) (right : LLRB α) : LLRB α
  deriving Repr

namespace LLRB

variable {α : Type}

/-- Every key in the tree satisfies `p`. Same role as `BST.All`. -/
def All (p : α → Prop) : LLRB α → Prop
  | leaf => True
  | node _ l k r => All p l ∧ p k ∧ All p r

/-- Is the link into this node red (the `Prop` form of `isRed`)? -/
def IsRed : LLRB α → Prop
  | leaf => False
  | node c _ _ _ => c = .red

variable [LinearOrder α]

omit [LinearOrder α] in
/-- The keys in order. -/
def toList : LLRB α → List α
  | leaf => []
  | node _ l k r => toList l ++ k :: toList r

/-- Box invariant 1: the keys are in order, as in any search tree. Same shape as `BST.Sorted`. -/
def Sorted : LLRB α → Prop
  | leaf => True
  | node _ l k r => All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r

/-- Box invariant 2: the top node is black. Vacuously true for `leaf`. -/
def RootBlack : LLRB α → Prop
  | leaf => True
  | node c _ _ _ => c = .black

/-- Box invariant 3: a red link always leans left, never right. No right link is ever red. -/
def LeftLeaning : LLRB α → Prop
  | leaf => True
  | node _ l _ r => ¬ r.IsRed ∧ LeftLeaning l ∧ LeftLeaning r

/-- Box invariant 4: no node ever has two red links touching it, not one on each side, and not one
chained below the other. Invariant 3 already rules out one on each side, so this piece checks
the chain: a red node has no red child. -/
def NoRedRed : LLRB α → Prop
  | leaf => True
  | node c l _ r => (c = .red → ¬ l.IsRed ∧ ¬ r.IsRed) ∧ NoRedRed l ∧ NoRedRed r

/-- The black-height of a tree, if every root-to-leaf path agrees on it: red links contribute
nothing, `leaf` contributes `1`. -/
def blackHeight : LLRB α → Option ℕ
  | leaf => some 1
  | node c l _ r => do
      let bl ← l.blackHeight
      let br ← r.blackHeight
      if bl = br then some (bl + if c = .black then 1 else 0) else none

/-- Box invariant 5: every path from the root down to a spot where you'd fall off the tree crosses
the same number of black links. -/
def BlackHeightOk (t : LLRB α) : Prop := t.blackHeight ≠ none

/-- Longest root-to-leaf path, in edges: the box's "never much more than twice as tall as the
best" is stated in it. Same convention as `RBTree.height`. -/
def height : LLRB α → ℕ
  | leaf => 0
  | node _ l _ r => max (height l) (height r) + 1

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per claim.
`LLRB.lean`, the file that imports the whole structure, proves the library's operations meet it
(`LLRB.contract`). -/

/-- The operations the box speaks of: the search tree's, and versions of search, insert and delete
that count their steps (comparisons; rotations for delete). -/
structure Ops (α : Type) where
  /-- The empty tree. -/
  empty : LLRB α
  /-- Add a key. -/
  insert : α → LLRB α → LLRB α
  /-- Take a key out. -/
  delete : α → LLRB α → LLRB α
  /-- Is the key there? -/
  search : α → LLRB α → Bool
  /-- The design's invariants. -/
  Valid : LLRB α → Prop
  /-- Search, counting comparisons. -/
  searchM : α → LLRB α → TimeM ℕ Bool
  /-- Insert, counting comparisons. -/
  insertM : α → LLRB α → TimeM ℕ (LLRB α)
  /-- Delete, counting rotations. -/
  deleteRot : α → LLRB α → TimeM ℕ (LLRB α)
  /-- The counting versions answer as the operations do, so the costs are of the operations. -/
  counted : ∀ a t, (searchM a t).ret = search a t ∧ (insertM a t).ret = insert a t ∧
    (deleteRot a t).ret = delete a t
  /-- The empty tree is valid. -/
  emptyValid : Valid empty
  /-- Insert keeps the invariants. -/
  insertKeeps : ∀ a t, Valid t → Valid (insert a t)
  /-- Delete keeps the invariants. -/
  deleteKeeps : ∀ a t, Valid t → Valid (delete a t)

/-- The tree's operations, listed in order by `LLRB.toList`. -/
def Ops.tree (o : Ops α) : SearchTree α (LLRB α) where
  empty := o.empty
  insert := o.insert
  delete := o.delete
  search := o.search
  toList := LLRB.toList
  Valid := o.Valid

/-- **A legal LLRB tree**: the box's five invariants. -/
def Valid (t : LLRB α) : Prop :=
  Sorted t ∧ RootBlack t ∧ LeftLeaning t ∧ NoRedRed t ∧ BlackHeightOk t

/-- **The LLRB's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. Costs count the steps the counting operations count themselves. -/
structure Contract (o : Ops α) : Prop where
  -- Goal: keep the search tree short, whatever order the keys arrive in.
  /-- Promise: the search tree's. -/
  promise : o.tree.Promise  -- the search tree's
  -- Idea: group the keys into nodes of one or two, held together by red links: a little
  -- imbalance, never more.
  /-- Invariants: the box's five, in box order. -/
  invariants : ∀ t, o.Valid t ↔
    Sorted t ∧          -- 1. the keys are in order
    RootBlack t ∧       -- 2. the top node is black
    LeftLeaning t ∧     -- 3. a red link leans left
    NoRedRed t ∧        -- 4. no node touches two red links
    BlackHeightOk t     -- 5. every path crosses the same number of black links
  /-- Cost: every operation grows with `log n`, on any valid tree of `n` keys. -/
  cost :
    -- height: never more than 2 log₂(n + 1)
    (∀ t, o.Valid t → height t ≤ 2 * Nat.log2 (o.tree.size t + 1)) ∧
    o.tree.Within o.searchM (fun n => 2 * Nat.log2 (n + 1)) ∧   -- search: comparisons
    o.tree.Within o.insertM (fun n => 2 * Nat.log2 (n + 1)) ∧   -- insert: comparisons
    o.tree.Within o.deleteRot (fun n => 12 * Nat.log2 (n + 1))  -- delete: rotations
    -- delete's comparisons: argued, `DeleteCost`, beside delete
  -- Assumes: reaching any node costs about the same, as in the RAM model.

end LLRB

end AlgoDesign.Searching
