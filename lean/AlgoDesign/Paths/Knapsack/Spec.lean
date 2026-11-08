/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.List.Sublists
public import Mathlib.Order.Basic

/-!
# Knapsack as a longest path: the specification

Sources: the Paths chapter, "What fits in the box?"; Ahuja, Magnanti and Orlin, *Network Flows*
(1993), Fig. 4.3 (pp. 101–102), "Longest path formulation of the knapsack problem", and Lawler,
*Combinatorial Optimization* (1976), Fig. 3.2 (pp. 63–64), for the states (items decided, weight
used); AMO p. 102 for the table loop read as relaxation; Roughgarden, *Algorithms Illuminated*
Part 3, §16.5 (p. 131), for walking back through the table and taking an item on a tie.

Items `0, …, n - 1` each have a weight (a natural number) and a value (an integer); the box holds
a weight of at most `C`. A **vertex** `(i, w)` says the first `i` items are decided and they use
weight `w`. From `(i, w)` there are two moves: skip item `i`, to `(i + 1, w)`, gaining nothing;
or take it, to `(i + 1, w + weight i)`, gaining its value, when that weight is at most `C`. An item
of weight 0 gives two moves between the same two vertices, so a path is the list of its moves,
one per item decided, not of the vertices it passes. Every move decides one more item, so no path
comes back to a vertex (`NoCycle`): the graph has no cycle.

The answer is the best gain into the last layer (`i = n`), the least weight on a tie, and the
items taken on the way there, found by walking back through the table, taking an item when taking
and skipping it tie.

This is a supporting algorithm: it has no design box, and so no contract in Lean;
`Valid` and the theorems in `Knapsack/Walk.lean` and `Knapsack/Basic.lean` state what it does.

- The answer → `knapsack` (`Walk.lean`): the best value and the items chosen.
- The value is the best over every set of items within the capacity (`IsBest`), and the chosen
  items fit and have that value → `knapsack_spec`; walking back from a reached vertex gives items
  worth its gain → `chosen_spec`.
- The chapter's picture → `PathsArePackings`: each path from `(0, 0)` to the last layer is one
  packing within the capacity, with the path's gain as its value, and each such packing is one
  path → `paths_are_packings`; `NoCycle`: the graph has no cycle → `no_cycle`.
- Invariant → `Valid`: `LayersHoldLongest`, `DecidedAtMostItems`, held at the start and kept by
  every step → `valid_start`, `valid_step`.
- At most two moves tried from each of the `n (C + 1)` vertices before the last layer →
  `knapsack_cost`, on `State.tried`.
-/

@[expose] public section

namespace AlgoDesign.Paths

/-- An item: its weight and its value. -/
structure Item where
  /-- How much it weighs. -/
  weight : ℕ
  /-- What it is worth. -/
  value : ℤ
deriving DecidableEq, Repr

namespace Knapsack

/-! ## The graph of decisions -/

/-- A move: skip the next item, or take it. -/
inductive Move where
  /-- Leave the item out. -/
  | skip
  /-- Put the item in. -/
  | take
deriving DecidableEq, Repr

/-- Item `i`; an item weighing nothing and worth nothing past the end. -/
def item (items : List Item) (i : ℕ) : Item := items.getD i ⟨0, 0⟩

/-- **Where a move leads** from the vertex `(i, w)`: skipping item `i` to `(i + 1, w)`; taking it
to `(i + 1, w + weight i)` if that is at most `C`; `none` when there is no such move. -/
def next (items : List Item) (C : ℕ) : ℕ × ℕ → Move → Option (ℕ × ℕ)
  | (i, w), .skip => if i < items.length then some (i + 1, w) else none
  | (i, w), .take =>
    if i < items.length ∧ w + (item items i).weight ≤ C then some (i + 1, w + (item items i).weight)
    else none

/-- What a move deciding item `i` gains: nothing for a skip, the item's value for a take. -/
def gain (items : List Item) (i : ℕ) : Move → ℤ
  | .skip => 0
  | .take => (item items i).value

/-- Where the moves `p` lead from a vertex, each from where the one before arrived; `none` when
one of them is not a move. -/
def follow (items : List Item) (C : ℕ) : ℕ × ℕ → List Move → Option (ℕ × ℕ)
  | v, [] => some v
  | v, m :: p => (next items C v m).bind fun v' => follow items C v' p

/-- **The gain of a path** whose first move decides item `i`: the sum of its moves' gains. -/
def pathGain (items : List Item) : ℕ → List Move → ℤ
  | _, [] => 0
  | i, m :: p => gain items i m + pathGain items (i + 1) p

/-- **`p` is a path from `(0, 0)` to `v`.** -/
def IsPath (items : List Item) (C : ℕ) (p : List Move) (v : ℕ × ℕ) : Prop :=
  follow items C (0, 0) p = some v

/-- A known gain is at least `g`: there is one, and it is not below `g`. -/
def AtLeast : Option ℤ → ℤ → Prop
  | some d, g => g ≤ d
  | none, _ => False

/-- **`b` is the largest gain of a path from `(0, 0)` to `v`**: no path gains more, and some path
gains exactly `b`; `none` exactly when no path reaches `v`. -/
def LongestTo (items : List Item) (C : ℕ) (v : ℕ × ℕ) (b : Option ℤ) : Prop :=
  (∀ p, IsPath items C p v → AtLeast b (pathGain items 0 p)) ∧
    ∀ d ∈ b, ∃ p, IsPath items C p v ∧ pathGain items 0 p = d

/-- **The graph has no cycle**: no path of one move or more comes back to where it started. -/
def NoCycle (items : List Item) (C : ℕ) : Prop :=
  ∀ v p, p ≠ [] → follow items C v p ≠ some v

/-! ## Packings -/

/-- The weight of a set of items, listed by index. -/
def weightOf (items : List Item) (S : List ℕ) : ℕ := (S.map fun k => (item items k).weight).sum

/-- The value of a set of items, listed by index. -/
def valueOf (items : List Item) (S : List ℕ) : ℤ := (S.map fun k => (item items k).value).sum

/-- **A packing that fits**: a set of the items, listed by index in increasing order, whose weight
is at most the capacity. -/
def Fits (items : List Item) (C : ℕ) (S : List ℕ) : Prop :=
  S.Sublist (List.range items.length) ∧ weightOf items S ≤ C

/-- **`b` is the best value**: some packing that fits is worth `b`, and none is worth more. -/
def IsBest (items : List Item) (C : ℕ) (b : ℤ) : Prop :=
  (∃ S, Fits items C S ∧ valueOf items S = b) ∧ ∀ S, Fits items C S → valueOf items S ≤ b

/-- The items a path takes, its first move deciding item `i`. -/
def packingOf : ℕ → List Move → List ℕ
  | _, [] => []
  | i, .skip :: p => packingOf (i + 1) p
  | i, .take :: p => i :: packingOf (i + 1) p

/-- The path that takes exactly the items of `S`, deciding the items `0, …, n - 1`. -/
def pathOf (n : ℕ) (S : List ℕ) : List Move :=
  (List.range n).map fun k => if k ∈ S then .take else .skip

/-- **Paths are packings**: each path from `(0, 0)` to the last layer takes a packing that fits,
is the path of that packing, and gains its value, arriving at its weight; each packing that fits
is the path that takes it, which arrives at its weight, takes exactly it and gains its value. -/
def PathsArePackings (items : List Item) (C : ℕ) : Prop :=
  (∀ p w, IsPath items C p (items.length, w) →
    Fits items C (packingOf 0 p) ∧ pathOf items.length (packingOf 0 p) = p ∧
      weightOf items (packingOf 0 p) = w ∧ valueOf items (packingOf 0 p) = pathGain items 0 p) ∧
  ∀ S, Fits items C S →
    IsPath items C (pathOf items.length S) (items.length, weightOf items S) ∧
      packingOf 0 (pathOf items.length S) = S ∧
        pathGain items 0 (pathOf items.length S) = valueOf items S

/-! ## The walk's state -/

/-- **The state of the walk**: the table, one layer per number of items decided. -/
structure State where
  /-- How many items are decided: the layers `0, …, decided` are filled. -/
  decided : ℕ
  /-- The largest gain known into each vertex `(i, w)`; `none` while no move has reached it. -/
  best : ℕ → ℕ → Option ℤ
  /-- How many moves the walk has tried. -/
  tried : ℕ

/-- Every vertex of every layer filled, within the capacity, holds the largest gain of a path into
it from `(0, 0)`, and `none` when no path reaches it. -/
def LayersHoldLongest (items : List Item) (C : ℕ) (st : State) : Prop :=
  ∀ i ≤ st.decided, ∀ w ≤ C, LongestTo items C (i, w) (st.best i w)

/-- No more items are decided than there are. -/
def DecidedAtMostItems (items : List Item) (st : State) : Prop := st.decided ≤ items.length

/-! ## The answer -/

/-- **The answer**: the best value and the items chosen, by index in increasing order. -/
structure Packing where
  /-- The best value. -/
  value : ℤ
  /-- The items chosen. -/
  items : List ℕ
deriving DecidableEq, Repr

/-- Keep the gain at weight `w` of a layer when it is more than the best so far. -/
def keepBetter (row : ℕ → Option ℤ) (acc : Option (ℤ × ℕ)) (w : ℕ) : Option (ℤ × ℕ) :=
  match row w, acc with
  | none, _ => acc
  | some b, none => some (b, w)
  | some b, some (b₀, w₀) => if b₀ < b then some (b, w) else some (b₀, w₀)

/-- The best known gain among the weights `ws` of a layer, and its weight, the first of the
weights on a tie. -/
def bestEnd (row : ℕ → Option ℤ) (ws : List ℕ) : Option (ℤ × ℕ) := ws.foldl (keepBetter row) none

/-- Taking the item wins: the gain from taking it, `b + v`, is known and at least the gain from
skipping it. -/
def takeWins : Option ℤ → ℤ → Option ℤ → Bool
  | some b, v, c => c.all (· ≤ b + v)
  | none, _, _ => false

/-- **The items chosen**, walking back from the vertex `(i, w)` through the table: item `i - 1` is
taken when taking it fits and wins, ties included. -/
def chosen (items : List Item) (best : ℕ → ℕ → Option ℤ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | i + 1, w =>
    if (item items i).weight ≤ w ∧
        takeWins (best i (w - (item items i).weight)) (item items i).value (best i w) then
      chosen items best i (w - (item items i).weight) ++ [i]
    else chosen items best i w

/-- The answer a finished walk gives: the best gain into the last layer, the least weight on a
tie, and the items chosen on the way there. -/
def answer (items : List Item) (C : ℕ) (st : State) : Packing :=
  match bestEnd (st.best items.length) (List.range (C + 1)) with
  | some (b, w) => ⟨b, chosen items st.best items.length w⟩
  | none => ⟨0, []⟩

/-- **A legal state of the walk.** -/
def Valid (items : List Item) (C : ℕ) (st : State) : Prop :=
  LayersHoldLongest items C st ∧ DecidedAtMostItems items st

end Knapsack

end AlgoDesign.Paths
