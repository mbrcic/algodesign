/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Basic

/-!
# LLRB: search

`search`, an ordinary color-blind BST descent, and `search_correct`: on a `Sorted` tree it
answers `Mem`. The range query `range` is specified by `mem_range`. Its cost is in `Cost.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-! ### Search and timed operations

Ordinary BST descent, color-blind. One tick per 3-way comparison; rotations and `fixUp` are free.
Combined with `height_le_two_log`, a valid tree's search and insert cost at most `2 ⌊lg(n+1)⌋`
comparisons. -/

/-- Does `a` occur in the tree? Same descent as `BST.search`; color is ignored. -/
def search (a : α) : LLRB α → Bool
  | leaf => false
  | node _ l k r =>
      if a < k then search a l
      else if k < a then search a r
      else true

theorem search_correct {t : LLRB α} (ht : Sorted t) (a : α) :
    search a t = true ↔ Mem a t := by
  induction t with
  | leaf => simp [search, Mem]
  | node c l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold search
    split
    · rename_i h
      rw [ihl hsl]
      simp only [Mem]
      constructor
      · tauto
      · rintro (hml | rfl | hmr)
        · exact hml
        · exact absurd h (lt_irrefl _)
        · exact absurd (hr.of_mem hmr) (not_lt.mpr (le_of_lt h))
    · split
      · rename_i h h'
        rw [ihr hsr]
        simp only [Mem]
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
def range (lo hi : RangeBound α) (t : LLRB α) : List α :=
  keysInRange lo hi (toList t)

/-- **`range` holds exactly the keys of the tree that the bounds admit.** -/
theorem mem_range {lo hi : RangeBound α} {t : LLRB α} {a : α} :
    a ∈ range lo hi t ↔ Mem a t ∧ InRange lo hi a := by
  simp [range, keysInRange, List.mem_filter, mem_toList]

/-- **The keys come out in increasing order**, the search tree's promise: a sorted tree's `toList`
is strictly increasing. -/
theorem sorted_toList {t : LLRB α} (ht : Sorted t) : (toList t).Pairwise (· < ·) := by
  induction t with
  | leaf => simp
  | node c l k r ihl ihr =>
    obtain ⟨hl, hr, sl, sr⟩ := ht
    simp only [toList_node]
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨ihl sl, ⟨fun b hb => hr.of_mem ((mem_toList r).1 hb), ihr sr⟩, ?_⟩
    intro a ha b hb
    have hak : a < k := hl.of_mem ((mem_toList l).1 ha)
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hak
    · exact lt_trans hak (hr.of_mem ((mem_toList r).1 hb))

/-- Bounding neither end asks for the whole tree. -/
@[simp] theorem range_unbounded (t : LLRB α) :
    range .unbounded .unbounded t = toList t := by
  simp [range, keysInRange, inRange, InRange, RangeBound.Lower, RangeBound.Upper]

end LLRB

end AlgoDesign.Searching
