/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Search

/-!
# Binary search tree: insertion

`insert`, with `mem_insert` and `sorted_insert`, and `insertSpec`: `insert` discharges
`InsertSpec`. `insertM`, the comparison-counting twin, is here next to the `insert` it erases to
(`ret_insertM`).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}
variable [LinearOrder α]

/-- **What any insertion of `a` owes**, whichever algorithm performs it: the key set afterwards is
the old one plus exactly `a`, and a sorted tree stays sorted. The per-operation form the proofs
discharge; the promise, `SearchTree.Promise`, states the same for every operation at once. -/
def InsertSpec (a : α) (before after : BST α) : Prop :=
  (∀ b, Mem b after ↔ (b = a ∨ Mem b before)) ∧ (Sorted before → Sorted after)

/-- Insert `a`, following the ordering at every node. A duplicate key is a no-op — this models
a `Set`, so there's nothing to overwrite. -/
def insert (a : α) : BST α → BST α
  | leaf => node leaf a leaf
  | node l k r =>
      if a < k then node (insert a l) k r
      else if k < a then node l k (insert a r)
      else node l k r

theorem mem_insert (t : BST α) (a b : α) : Mem b (insert a t) ↔ b = a ∨ Mem b t := by
  induction t with
  | leaf => simp [insert]
  | node l k r ihl ihr =>
    unfold insert
    split
    · rename_i h
      simp only [mem_node, ihl]
      tauto
    · split
      · rename_i h h'
        simp only [mem_node, ihr]
        tauto
      · rename_i h h'
        have hka : k = a := le_antisymm (not_lt.mp h) (not_lt.mp h')
        simp only [mem_node]
        constructor
        · rintro (hl | rfl | hr) <;> tauto
        · rintro (rfl | hl | rfl | hr) <;> tauto

theorem All.insert {p : α → Prop} {t : BST α} (ht : All p t) {a : α} (ha : p a) :
    All p (BST.insert a t) := by
  induction t with
  | leaf => simp [BST.insert, ha]
  | node l k r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := ht
    unfold BST.insert
    split
    · exact ⟨ihl hl, hk, hr⟩
    · split
      · exact ⟨hl, hk, ihr hr⟩
      · exact ⟨hl, hk, hr⟩

theorem sorted_insert {t : BST α} (ht : Sorted t) (a : α) : Sorted (insert a t) := by
  induction t with
  | leaf => simp [insert]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold insert
    split
    · rename_i h
      exact ⟨hl.insert h, hr, ihl hsl, hsr⟩
    · split
      · rename_i h h'
        exact ⟨hl, hr.insert h', hsl, ihr hsr⟩
      · exact ⟨hl, hr, hsl, hsr⟩

/-- Instrumented insert: one tick per 3-way key comparison. Rotations do not arise on a plain
BST. -/
def insertM (a : α) : BST α → TimeM ℕ (BST α)
  | leaf => pure (node leaf a leaf)
  | node l k r => do
      tick 1
      if a < k then
        let l' ← insertM a l
        pure (node l' k r)
      else if k < a then
        let r' ← insertM a r
        pure (node l k r')
      else
        pure (node l k r)

theorem ret_insertM (a : α) (t : BST α) : (insertM a t).ret = insert a t := by
  induction t with
  | leaf => simp [insertM, insert]
  | node l k r ihl ihr =>
    simp only [insertM, insert, ret_bind]
    split_ifs <;> simp [ihl, ihr]

/-- **`insert` discharges `InsertSpec`**, assembled from `mem_insert` and `sorted_insert`. -/
theorem insertSpec (t : BST α) (a : α) : InsertSpec a t (insert a t) :=
  ⟨mem_insert t a, fun hs => sorted_insert hs a⟩

end BST

end AlgoDesign.Searching
