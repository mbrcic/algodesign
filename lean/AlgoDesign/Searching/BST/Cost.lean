/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Delete

/-!
# Binary search tree: cost

Comparisons counted through `Cslib.Algorithms.Lean.TimeM`: `searchM` erases to `search`, and search
and insertion cost at most the height (`time_searchM_le_height`, `time_insertM_le_height`). There
is no worst-case height bound: nothing keeps the tree balanced.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}
variable [LinearOrder α]

/-- Instrumented search: one tick per 3-way key comparison. -/
def searchM (a : α) : BST α → TimeM ℕ Bool
  | leaf => pure false
  | node l k r => do
      tick 1
      if a < k then searchM a l
      else if k < a then searchM a r
      else pure true

theorem ret_searchM (a : α) (t : BST α) : (searchM a t).ret = search a t := by
  induction t with
  | leaf => simp [searchM, search]
  | node l k r ihl ihr =>
    simp only [searchM, search, ret_bind]
    split_ifs <;> simp [ihl, ihr]

theorem time_searchM_le_height (a : α) (t : BST α) : (searchM a t).time ≤ height t := by
  induction t with
  | leaf => simp [searchM, height]
  | node l k r ihl ihr =>
    simp only [searchM, time_bind, time_tick, height_node]
    split_ifs
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihl (Nat.le_max_left (height l) (height r))) 1
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihr (Nat.le_max_right (height l) (height r))) 1
    · simp

theorem time_insertM_le_height (a : α) (t : BST α) : (insertM a t).time ≤ height t := by
  induction t with
  | leaf => simp [insertM, height]
  | node l k r ihl ihr =>
    simp only [insertM, time_bind, time_tick, height_node]
    split_ifs
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihl (Nat.le_max_left (height l) (height r))) 1
    · simpa [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_trans ihr (Nat.le_max_right (height l) (height r))) 1
    · simp

/-- A line of keys: each key the right child of the one before. -/
def line : List α → BST α
  | [] => leaf
  | k :: ks => node leaf k (line ks)

omit [LinearOrder α] in
/-- A line is as tall as its keys are many. -/
theorem height_line : ∀ ks : List α, height (line ks) = ks.length
  | [] => rfl
  | k :: ks => by simp [line, height_line ks, height]

/-- A key larger than every key on a line hangs at its end. -/
theorem insert_line (a : α) : ∀ ks : List α, (∀ k ∈ ks, k < a) →
    insert a (line ks) = line (ks ++ [a])
  | [], _ => rfl
  | k :: ks, h => by
    have hk : k < a := h k (by simp)
    simp [line, insert, not_lt.2 hk.le, hk, insert_line a ks (fun x hx => h x (by simp [hx]))]

/-- Keys inserted in increasing order, after a line of smaller keys, extend the line. -/
theorem foldl_insert_line : ∀ (ks ys : List α), (ys ++ ks).Pairwise (· < ·) →
    ks.foldl (fun t k => insert k t) (line ys) = line (ys ++ ks)
  | [], ys, _ => by simp
  | k :: ks, ys, h => by
    have hk : ∀ y ∈ ys, y < k := fun y hy => (List.pairwise_append.1 h).2.2 y hy k (by simp)
    rw [List.foldl_cons, insert_line k ys hk, foldl_insert_line ks (ys ++ [k]) (by simpa using h)]
    simp

/-- **Sorted input makes the paths as long as the set**: keys inserted in increasing order into the
empty tree hang in one line, as tall as the keys are many, so a search for the last walks them
all. -/
theorem height_foldl_insert_sorted {ks : List α} (h : ks.Pairwise (· < ·)) :
    height (ks.foldl (fun t k => insert k t) leaf) = ks.length := by
  rw [show (leaf : BST α) = line [] from rfl, foldl_insert_line ks [] (by simpa using h),
    List.nil_append, height_line]

end BST

end AlgoDesign.Searching
