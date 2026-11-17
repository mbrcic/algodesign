/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Delete

/-!
# Red-black tree: cost

Comparisons counted through `Cslib.Algorithms.Lean.TimeM`, one tick per 3-way key comparison,
rotations and recoloring free: `searchM` and `insertM` erase to `search` and `insert`, and a valid
tree's search and insert cost at most `2 ⌊lg(n+1)⌋` comparisons (`time_searchM_le_two_log`,
`time_insertM_le_two_log`). Deletion's comparisons are not costed; its rotations are, in
`Rotations.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

/-- Instrumented search: one tick per node visited (one 3-way compare). -/
def searchM (a : α) : RBTree α → TimeM ℕ Bool
  | leaf => pure false
  | node _ l k r => do
      tick 1
      if a < k then searchM a l
      else if k < a then searchM a r
      else pure true

theorem ret_searchM (a : α) (t : RBTree α) : (searchM a t).ret = search a t := by
  induction t with
  | leaf => simp [searchM, search]
  | node c l k r ihl ihr =>
    simp only [searchM, search, ret_bind]
    split_ifs <;> simp [ihl, ihr]

theorem time_searchM_le_height (a : α) (t : RBTree α) : (searchM a t).time ≤ height t := by
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

theorem time_searchM_le_two_log {t : RBTree α} (ht : Valid t) (a : α) :
    (searchM a t).time ≤ 2 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_searchM_le_height a t) (height_le_two_log ht)

/-- Instrumented insert descent: one tick per comparison; fixups and the final `blacken` are
free. -/
def insM (a : α) : RBTree α → TimeM ℕ (RBTree α)
  | leaf => pure (node .red leaf a leaf)
  | node c l k r => do
      tick 1
      if a < k then
        let l' ← insM a l
        pure (insertFixupL c l' k r)
      else if k < a then
        let r' ← insM a r
        pure (insertFixupR c l k r')
      else
        pure (node c l k r)

/-- Insert, counted as `insM` counts (one tick per comparison on the path), the root then
painted black at no cost. -/
def insertM (a : α) (t : RBTree α) : TimeM ℕ (RBTree α) := blacken <$> insM a t

theorem ret_insM (a : α) (t : RBTree α) : (insM a t).ret = ins a t := by
  induction t with
  | leaf => simp [insM, ins]
  | node c l k r ihl ihr =>
    simp only [insM, ins, ret_bind]
    split_ifs <;> simp [ihl, ihr]

theorem ret_insertM (a : α) (t : RBTree α) : (insertM a t).ret = insert a t := by
  simp [insertM, insert, ret_insM]

theorem time_insM_le_height (a : α) (t : RBTree α) : (insM a t).time ≤ height t := by
  induction t with
  | leaf => simp [insM, height]
  | node c l k r ihl ihr =>
    simp only [insM, time_bind, time_tick, height_node]
    split_ifs
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihl (Nat.le_max_left (height l) (height r))) 1
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihr (Nat.le_max_right (height l) (height r))) 1
    · simp

theorem time_insertM_le_height (a : α) (t : RBTree α) : (insertM a t).time ≤ height t := by
  simpa [insertM] using time_insM_le_height a t

theorem time_insertM_le_two_log {t : RBTree α} (ht : Valid t) (a : α) :
    (insertM a t).time ≤ 2 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_insertM_le_height a t) (height_le_two_log ht)

end RBTree

end AlgoDesign.Searching
