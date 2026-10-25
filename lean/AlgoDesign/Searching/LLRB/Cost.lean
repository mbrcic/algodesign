/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Delete

/-!
# LLRB: cost

Comparisons counted through `Cslib.Algorithms.Lean.TimeM`, one tick per 3-way comparison, with
rotations and `fixUp` free. One tick whichever node the comparison is at: the box's assumption that
reaching any node costs about the same, as in the RAM model. `searchM` erases to `search`
(`ret_searchM`); `insertM` is in `Insert.lean`. Against `height_le_two_log`, a valid tree's search
and insert cost at most `2 ⌊lg(n+1)⌋` (`time_searchM_le_two_log`, `time_insertM_le_two_log`).
Deletion's comparisons are not costed; its rotations are, in `Rotations.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-- Search, one tick per three-way comparison: one per node on the path. -/
def searchM (a : α) : LLRB α → TimeM ℕ Bool
  | leaf => pure false
  | node _ l k r => do
      tick 1
      if a < k then searchM a l
      else if k < a then searchM a r
      else pure true

theorem ret_searchM (a : α) (t : LLRB α) : (searchM a t).ret = search a t := by
  induction t with
  | leaf => simp [searchM, search]
  | node c l k r ihl ihr =>
    simp only [searchM, search, ret_bind]
    split_ifs <;> simp [ihl, ihr]

theorem time_searchM_le_height (a : α) (t : LLRB α) : (searchM a t).time ≤ height t := by
  induction t with
  | leaf => simp [searchM, height]
  | node c l k r ihl ihr =>
    simp only [searchM, time_bind, time_tick, height_node]
    split_ifs
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihl (Nat.le_max_left (height l) (height r))) 1
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihr (Nat.le_max_right (height l) (height r))) 1
    · simp

theorem time_searchM_le_two_log {t : LLRB α} (ht : Valid t) (a : α) :
    (searchM a t).time ≤ 2 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_searchM_le_height a t) (height_le_two_log ht)

theorem time_insertAuxM_le_height (a : α) (t : LLRB α) :
    (insertAuxM a t).time ≤ height t := by
  induction t with
  | leaf => simp [insertAuxM, height]
  | node c l k r ihl ihr =>
    simp only [insertAuxM, time_bind, time_tick, height_node]
    split_ifs
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihl (Nat.le_max_left (height l) (height r))) 1
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihr (Nat.le_max_right (height l) (height r))) 1
    · simp

theorem time_insertM_le_height (a : α) (t : LLRB α) : (insertM a t).time ≤ height t := by
  simpa [insertM] using time_insertAuxM_le_height a t

theorem time_insertM_le_two_log {t : LLRB α} (ht : Valid t) (a : α) :
    (insertM a t).time ≤ 2 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_insertM_le_height a t) (height_le_two_log ht)

end LLRB

end AlgoDesign.Searching
