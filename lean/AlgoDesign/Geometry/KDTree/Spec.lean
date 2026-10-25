/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Nearest

/-!
# The k-d tree: the specification

Sources: the Geometry chapter, the k-d tree; de Berg, Cheong, van Kreveld and Overmars,
*Computational Geometry* (3rd ed.), §5.2 (`BUILDKDTREE`, p. 100; Bentley 1975); Samet,
*Foundations of Multidimensional and Metric Data Structures*, §4.1 (best-first search).

> **Goal:** find the place nearest to wherever you stand, among a fixed set of places on a map.
>
> **Promise:** the same answers as the scan, the nearest stored point or the $k$ nearest. Also
> every stored point inside a rectangle.
>
> **Idea:** cut the map in two, each half in two along the other axis, taking turns. Then skip
> every region that cannot hold anything closer than the best found so far.
>
> **Invariants:**
>
> 1. Every cut divides the points below it: none on its left lies past the cut, none on its right
>    lies before it.
> 2. Every cut splits the points below it in half.
> 3. The search never skips a region that could hold a point closer than the best found so far.
>
> **Cost:** on points spread over a map, a nearest-neighbor search opens a few dozen regions, and
> measures about four points, out of a million.
>
> **Assumes:** the data's real dimension is low. Otherwise the search opens nearly every region.
> It is slower, never wrong.

Words: a place is a `Point`; a region is a subtree, queued with its offsets as a `Region`.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`KDTree.contract` proves the library's operations, `KDTree.ops`, meet it.

- Goal [required] → build a tree over a fixed set of points, then ask it for the nearest one; each
  a field of `Ops`.
- Promise [tested] → the scan's, `Nearest.Promise`, on every tree the build makes and, outside the
  contract, on every valid tree, `answers_of_valid` [proved]; the tie rule by the lowest id and
  leaves of more than one point [tested].
- Idea [mentioned] → kept by invariants 1 to 3.
- Invariants [proved] → `Valid` on the tree, then the search's state:
  1 [proved] `CutsSeparate`.
  2 [proved] `CutsHalve`.
  3 [proved] on a run of the search, not the tree: `BestFirst.NothingCloserSkipped`, kept by the
  search.
  Not in the box: every tree the build makes is valid, `Ops.buildValid`.
- Cost [measured] → regions opened and points measured per search, on a million points spread
  uniformly over a square.
- Assumes [measured] → "otherwise the search opens nearly every region" [measured]: for the ten
  nearest among 100,000 points spread evenly at random, 0.75% of the points measured at 8
  dimensions, 24.46% at 16, nearly every point from 32; "slower, never wrong" [proved], the
  promise in every dimension from one up.
-/
@[expose] public section

namespace AlgoDesign.Geometry

/-- A k-d tree over `d`-dimensional points: points in the leaves, cuts at the inner nodes. -/
inductive KDTree (d : ℕ) (α : Type) where
  | leaf (p : Point d α)
  | node (axis : Fin d) (split : α) (l r : KDTree d α)

namespace KDTree

variable {d : ℕ} {α : Type} [LinearOrder α]

/-- The stored points, left to right. -/
def points : KDTree d α → List (Point d α)
  | leaf p => [p]
  | node _ _ l r => points l ++ points r

/-- Box invariant 1: every cut divides the points below it: none on its left lies past the cut,
none on its right lies before it. At every inner node, every point on the left has the node's
coordinate `≤` the split, and every point on the right has it `≥` the split. -/
def CutsSeparate : KDTree d α → Prop
  | leaf _ => True
  | node a s l r =>
      (∀ x ∈ points l, x a ≤ s) ∧ (∀ x ∈ points r, s ≤ x a) ∧ CutsSeparate l ∧
        CutsSeparate r

/-- Box invariant 2: every cut splits the points below it in half. At every inner node the left
side holds `⌈n/2⌉` of the node's `n` points and the right side the rest: the right count is at
most the left, and the left at most one more. -/
def CutsHalve : KDTree d α → Prop
  | leaf _ => True
  | node _ _ l r =>
      (points r).length ≤ (points l).length ∧ (points l).length ≤ (points r).length + 1 ∧
        CutsHalve l ∧ CutsHalve r

/-! ### The search's running state -/

namespace BestFirst

variable [CommRing α] [IsStrictOrderedRing α]

/-- A queued region: a subtree, with the query's per-axis offsets from the region. -/
structure Region (d : ℕ) (α : Type) where
  /-- How far the query is from the region along each axis (signed; only the square is used). -/
  offsets : Point d α
  /-- The subtree the region holds. -/
  tree : KDTree d α

/-- A region's lower bound: the sum of its squared offsets. -/
def Region.bound (r : Region d α) : α := ∑ i, r.offsets i ^ 2

/-- The search's running state: the points measured so far, in the order measured, and the queue
in the order its regions entered it. -/
structure State (d : ℕ) (α : Type) where
  /-- The points whose distance to the query has been computed. -/
  measured : List (Point d α)
  /-- The regions waiting to be opened. -/
  queue : List (Region d α)

/-- A run of the search: the tree searched, the query, and the running state. The tree, the query
and every queued region's offsets have the same dimension `d`, by their types; what ties the state
to the tree and the query is the search's invariant, `Valid`. -/
structure Run (d : ℕ) (α : Type) where
  /-- The tree searched. -/
  tree : KDTree d α
  /-- The query point. -/
  query : Point d α
  /-- What the search has measured and what it has queued. -/
  state : State d α

/-- Box invariant 3: the search never skips a region that could hold a point closer than the best
found so far. Every stored point is already measured, or sits in a queued region whose bound is at
most its squared distance to the query. -/
def NothingCloserSkipped (r : Run d α) : Prop :=
  ∀ x ∈ points r.tree, x ∈ r.state.measured ∨
    ∃ g ∈ r.state.queue, x ∈ points g.tree ∧ g.bound ≤ sqDist x r.query

end BestFirst

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe. `KDTree.lean`, the file
that imports the whole structure, proves the library's operations meet it (`KDTree.contract`). -/

/-- The operations the box speaks of. A tree is built over a list of points, `none` for no points;
the queries take the built tree. -/
structure Ops (d : ℕ) (α : Type) where
  /-- Build a tree over the points, `none` when there are none. -/
  build : List (Point d α) → Option (KDTree d α)
  /-- The nearest stored point to the query. -/
  nearest : Point d α → Option (KDTree d α) → Option (Point d α)
  /-- The $k$ nearest stored points to the query, nearest first. -/
  kNearest : ℕ → Point d α → Option (KDTree d α) → List (Point d α)
  /-- The stored points inside the rectangle `[lo, hi]`. -/
  rectangle : Point d α → Point d α → Option (KDTree d α) → List (Point d α)
  /-- The design's invariants. -/
  Valid : KDTree d α → Prop
  /-- Every tree the build makes is valid. -/
  buildValid : ∀ ps t, build ps = some t → Valid t

section Parts

variable [CommRing α] [IsStrictOrderedRing α]

/-- Promise: the same answers as the scan, the nearest stored point or the $k$ nearest. Also
every stored point inside a rectangle; built over no points, nothing. -/
def Ops.AnswersAsTheScan (o : Ops d α) : Prop :=
  Nearest.Promise o.build o.nearest o.kNearest o.rectangle

end Parts

/-- **The k-d tree's invariant**: `CutsSeparate` (box invariant 1) and `CutsHalve` (box
invariant 2). Box invariant 3 is about the search, not the tree: `BestFirst.NothingCloserSkipped`,
on a `BestFirst.Run`. -/
def Valid (t : KDTree d α) : Prop := CutsSeparate t ∧ CutsHalve t

/-- **The k-d tree's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. -/
structure Contract [CommRing α] [IsStrictOrderedRing α] (o : Ops d α) : Prop where
  -- Goal: find the place nearest to wherever you stand, among a fixed set of places on a map.
  /-- Promise: the scan's. -/
  promise : o.AnswersAsTheScan  -- the same answers as the scan
  -- Idea: cut the map in two, each half in two along the other axis, taking turns. Then skip
  -- every region that cannot hold anything closer than the best found so far.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ t, o.Valid t ↔
    CutsSeparate t ∧  -- 1. every cut divides the points below it
    CutsHalve t       -- 2. every cut splits the points below it in half
    -- 3. the search never skips a region that could hold a closer point: on the search's run,
    --    not the tree, `BestFirst.NothingCloserSkipped`, proved kept by the search
  -- Cost: on points spread over a map, a nearest-neighbor search opens a few dozen regions, and
  -- measures about four points, out of a million: measured on the bench, not stated here.
  -- Assumes: the data's real dimension is low. Otherwise the search opens nearly every region.
  -- It is slower, never wrong.

end KDTree
end AlgoDesign.Geometry
