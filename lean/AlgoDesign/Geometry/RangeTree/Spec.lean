/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Basic
public import AlgoDesign.Geometry.Nearest

/-!
# The range tree: the specification

Sources: the Geometry chapter, the range tree; de Berg, Cheong, van Kreveld and Overmars,
*Computational Geometry* (3rd ed.), §5.1 (`FINDSPLITNODE`, `1DRANGEQUERY`, pp. 96–99) and §5.3
(the 2D range tree, `2DRANGEQUERY`).

> **Goal:** list every place in a strip of the map, when the places don't change.
>
> **Promise:** every stored point inside the strip, edges included, each once, and nothing else.
>
> **Idea:** sort once and hang the points on a balanced tree, so any range is a few whole
> subtrees, and each subtree can carry its own tree on the other coordinate.
>
> **Invariants:**
>
> 1. Every inner key separates its two sides: nothing on its left is larger, nothing on its right
>    is smaller.
> 2. Every inner node splits the points below it in half.
>
> **Cost:** a query walks two paths of $\log_2 n$ steps, plus one step per point reported.

Words: a place is a key; a strip is `[lo, hi]`, `InStrip`; an inner key is a split key.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`RangeTree1D.contract` proves the library's operations, `RangeTree1D.ops`, meet it.

- Goal [required] → a build from keys in any order and a query, each a field of `Ops`; nothing
  changes a built tree.
- Promise [proved] → on a valid tree, the query is the stored keys inside the strip, each stored
  copy once, in order; not in the box, the build stores exactly the keys it was given.
- Idea [mentioned] → sorting once and the balanced tree are invariants 1 and 2; "each subtree
  can carry its own tree on the other coordinate" is the 2D range tree, `RangeTree2D`, its query
  `RangeTree2D.Query2DSpec` [proved].
- Invariants [proved] → `Valid`:
  1 [proved] `KeysSeparate`.
  2 [proved] `SplitsHalve`.
- Cost [proved] → ticks per query: nodes walked and points reported.
- Assumes [none] → the box assumes nothing.
-/

@[expose] public section

namespace AlgoDesign.Geometry

open Cslib.Algorithms.Lean

/-- `x` is inside the strip `[lo, hi]`, edges included. -/
@[simp] abbrev InStrip {α : Type} [LinearOrder α] (lo hi x : α) : Prop := lo ≤ x ∧ x ≤ hi

/-- A 1D range tree: leaves hold keys; inner nodes hold a split key and two subtrees. -/
inductive RangeTree1D (α : Type) where
  | leaf (k : α)
  | node (split : α) (l r : RangeTree1D α)
  deriving Repr

namespace RangeTree1D

variable {α : Type}

/-- The stored keys, left to right. -/
def leaves : RangeTree1D α → List α
  | leaf k => [k]
  | node _ l r => leaves l ++ leaves r

variable [LinearOrder α]

/-- Box invariant 1: every inner key separates its two sides: nothing on its left is larger,
nothing on its right is smaller. -/
def KeysSeparate : RangeTree1D α → Prop
  | leaf _ => True
  | node s l r =>
      (∀ x ∈ leaves l, x ≤ s) ∧ (∀ x ∈ leaves r, s ≤ x) ∧ KeysSeparate l ∧ KeysSeparate r

omit [LinearOrder α] in
/-- Box invariant 2: every inner node splits the points below it in half. At every inner node the
left side holds `⌈n/2⌉` of the node's `n` keys and the right side the rest: the right count is at
most the left, and the left at most one more. -/
def SplitsHalve : RangeTree1D α → Prop
  | leaf _ => True
  | node _ l r =>
      (leaves r).length ≤ (leaves l).length ∧ (leaves l).length ≤ (leaves r).length + 1 ∧
        SplitsHalve l ∧ SplitsHalve r

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per claim.
`RangeTree.lean`, the file that imports the whole structure, proves the library's operations meet
it (`RangeTree1D.contract`). -/

/-- The operations the box speaks of: a build from keys in any order (`none` for no keys), a
query, the invariant, and a query that counts its steps. -/
structure Ops (α : Type) where
  /-- Build the tree over the keys, in any order, repeats allowed; `none` when there are none. -/
  build : List α → Option (RangeTree1D α)
  /-- The keys in `[lo, hi]`. -/
  query : α → α → RangeTree1D α → List α
  /-- The design's invariants. -/
  Valid : RangeTree1D α → Prop
  /-- The query, counting the nodes it walks and the points it reports. -/
  queryM : α → α → RangeTree1D α → TimeM ℕ (List α)
  /-- On a valid tree the counted query answers as the query does, so the cost is of the query. -/
  counted : ∀ lo hi t, Valid t → (queryM lo hi t).ret = query lo hi t

/-- Promise: every stored key inside `[lo, hi]`, edges included, each once, and nothing else. -/
def Ops.ListsTheStrip (o : Ops α) : Prop :=
  ∀ t, o.Valid t → ∀ lo hi, o.query lo hi t = (leaves t).filter (InStrip lo hi ·)

/-- Not in the box: the build makes a tree exactly when given keys, valid, with the keys given. -/
def Ops.KeepsInvariants (o : Ops α) : Prop :=
  (∀ xs, o.build xs = none ↔ xs = []) ∧                    -- a tree exactly when there are keys
  (∀ xs t, o.build xs = some t →
    (leaves t).Perm xs ∧ (leaves t).Pairwise (· ≤ ·)) ∧    -- the keys given, sorted
  ∀ xs t, o.build xs = some t → o.Valid t                  -- every tree it makes is valid

/-- **The range tree's invariant**: the box's two. -/
def Valid (t : RangeTree1D α) : Prop := KeysSeparate t ∧ SplitsHalve t

/-- **The range tree's contract**, the part of the design Lean checks, one field per box field and
one conjunct per box line. The cost counts the steps the counting query counts itself. -/
structure Contract (o : Ops α) : Prop where
  -- Goal: list every place in a strip of the map, when the places don't change.
  /-- Promise: every stored point inside the strip, edges included, each once, and nothing else. -/
  promise :
    o.ListsTheStrip ∧    -- every stored point inside the strip, each once, and nothing else
    o.KeepsInvariants    -- not in the box: the build stores the keys given; every tree is valid
  -- Idea: sort once and hang the points on a balanced tree, so any range is a few whole
  -- subtrees, and each subtree can carry its own tree on the other coordinate.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ t, o.Valid t ↔
    KeysSeparate t ∧  -- 1. every inner key separates its two sides
    SplitsHalve t     -- 2. every inner node splits the points below it in half
  /-- Cost: a query walks two paths of `log₂ n` steps, plus one step per point reported. -/
  cost :
    ∀ t, o.Valid t → ∀ lo hi, (o.queryM lo hi t).time ≤
      2 * Nat.clog 2 (leaves t).length + (o.query lo hi t).length + 1  -- ticks: nodes and points

end RangeTree1D

end AlgoDesign.Geometry
