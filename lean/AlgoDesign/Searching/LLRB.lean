/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Spec
public import AlgoDesign.Searching.LLRB.Decide
public import AlgoDesign.Searching.LLRB.Basic
public import AlgoDesign.Searching.LLRB.Search
public import AlgoDesign.Searching.LLRB.Insert
public import AlgoDesign.Searching.LLRB.Balance
public import AlgoDesign.Searching.LLRB.Delete
public import AlgoDesign.Searching.LLRB.Cost
public import AlgoDesign.Searching.LLRB.Rotations

/-! The left-leaning red-black tree. Its contract is in `LLRB/Spec.lean`; this file imports
the whole structure. -/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean

namespace LLRB

variable {α : Type} [LinearOrder α]

/-! ## The library's LLRB meets its contract

`Contract` in `LLRB/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The LLRB as a search tree: its operations, and its five invariants as `Valid`. -/
def tree : SearchTree α (LLRB α) where
  empty := leaf
  insert := insert
  delete := deleteTop
  search := search
  toList := toList
  Valid := Valid

theorem valid_leaf : Valid (leaf : LLRB α) := by
  simp [Valid, Sorted, RootBlack, LeftLeaning, NoRedRed, BlackHeightOk, blackHeight]

/-- **Promise:** the search tree's. -/
theorem promise : (tree : SearchTree α (LLRB α)).Promise :=
  SearchTree.Promise.of_mem tree Mem (fun _ t => mem_toList t)
    valid_leaf rfl
    (fun a _ h => valid_insert h a) (fun a _ h => valid_deleteTop h a)
    (fun a b t _ => mem_insert t a b) (fun a b _ h => mem_deleteTop_iff h.1 a b)
    (fun a _ h => search_correct h.1 a) (fun _ h => sorted_toList h.1)

omit [LinearOrder α] in
theorem length_toList (t : LLRB α) : (toList t).length = size t := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr => simp [toList, size, ihl, ihr]; omega

/-- On a valid tree, the search tree's `size` is the tree's own. -/
theorem tree_size {t : LLRB α} (h : Valid t) : (tree : SearchTree α (LLRB α)).size t = size t := by
  rw [promise.size_eq_length h]; exact length_toList t

/-- The LLRB's range query is the search tree's, `SearchTree.range`. -/
theorem range_eq (lo hi : RangeBound α) (t : LLRB α) :
    range lo hi t = (tree : SearchTree α (LLRB α)).range t lo hi := rfl

/-- The library's operations, as the box names them; `searchM`, `insertM` and `deleteTopRot` are
its counting. -/
def ops : Ops α where
  empty := leaf
  insert := insert
  delete := deleteTop
  search := search
  Valid := Valid
  searchM := searchM
  insertM := insertM
  deleteRot := deleteTopRot
  counted a t := ⟨ret_searchM a t, ret_insertM a t, ret_deleteTopRot a t⟩

/-- The search tree the library's operations make is `tree`. -/
theorem tree_ops : (ops : Ops α).tree = tree := rfl

/-- **The library's LLRB meets its contract** (`Contract` in `LLRB/Spec.lean`). Delete's comparison
count, `DeleteCost`, is argued, not proved. -/
theorem contract : Contract (ops : Ops α) where
  promise := promise
  invariants _ := Iff.rfl
  cost := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t h
      rw [tree_ops, tree_size h]; exact height_le_two_log h
    · intro a _ h _
      rw [tree_ops] at *; simpa [ops, tree_size h] using time_searchM_le_two_log h a
    · intro a _ h _
      rw [tree_ops] at *; simpa [ops, tree_size h] using time_insertM_le_two_log h a
    · intro a _ h _
      rw [tree_ops] at *; simpa [ops, tree_size h] using
        le_trans (time_deleteTopRot_le_height h a)
          (by have := Nat.mul_le_mul_left 6 (height_le_two_log h); omega)

/-- **The design target "short", but for delete's comparisons:** given a counted delete that meets
the argued `DeleteCost`, the LLRB meets `SearchTree.Logarithmic 2`. The one piece missing is that
delete. -/
theorem logarithmic_of_deleteCost {deleteM : α → LLRB α → TimeM ℕ (LLRB α)}
    (hd : DeleteCost ops deleteM) :
    (tree : SearchTree α (LLRB α)).Logarithmic 2 searchM insertM deleteM :=
  ⟨contract.cost.2.1, contract.cost.2.2.1, hd.2⟩

end LLRB

end AlgoDesign.Searching
