/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Basic

/-!
# Red-black tree: search

`search`, the ordinary color-blind BST descent, and `search_correct`: on a `Sorted` tree it
answers `Mem`. The range query `range` is specified by `mem_range`. Its cost is in `Cost.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

/-! ### Search and timed operations

Ordinary BST descent, color-blind. `searchM`/`insertM` charge one tick per 3-way key comparison
(rotations and recoloring are free). Combined with `height_le_two_log`, a valid tree's search and
insert cost at most `2 ⌊lg(n+1)⌋` comparisons. -/

/-- Does `a` occur in the tree? Same descent as `BST.search`; color is ignored. -/
def search (a : α) : RBTree α → Bool
  | leaf => false
  | node _ l k r =>
      if a < k then search a l
      else if k < a then search a r
      else true

theorem search_correct {t : RBTree α} (ht : Sorted t) (a : α) :
    search a t = true ↔ Mem a t := by
  induction t with
  | leaf => simp [search, Mem]
  | node c l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold search
    split
    · rename_i h
      rw [ihl hsl]
      simp only [mem_node]
      constructor
      · tauto
      · rintro (hml | rfl | hmr)
        · exact hml
        · exact absurd h (lt_irrefl _)
        · exact absurd (hr.of_mem hmr) (not_lt.mpr (le_of_lt h))
    · split
      · rename_i h h'
        rw [ihr hsr]
        simp only [mem_node]
        constructor
        · tauto
        · rintro (hml | rfl | hmr)
          · exact absurd (hl.of_mem hml) (not_lt.mpr (le_of_lt h'))
          · exact absurd h' (lt_irrefl _)
          · exact hmr
      · rename_i h h'
        have : a = k := le_antisymm (not_lt.mp h') (not_lt.mp h)
        simp [this, Mem]

/-- **Range query**: the keys between two bounds, in order. -/
def range (lo hi : RangeBound α) (t : RBTree α) : List α :=
  keysInRange lo hi (toList t)

/-- **`range` holds exactly the keys of the tree that the bounds admit.** -/
theorem mem_range {lo hi : RangeBound α} {t : RBTree α} {a : α} :
    a ∈ range lo hi t ↔ Mem a t ∧ InRange lo hi a := by
  simp [range, keysInRange, List.mem_filter, mem_toList]

/-- Bounding neither end asks for the whole tree. -/
@[simp] theorem range_unbounded (t : RBTree α) :
    range .unbounded .unbounded t = toList t := by
  simp [range, keysInRange, inRange, InRange, RangeBound.Lower, RangeBound.Upper]

end RBTree

end AlgoDesign.Searching
