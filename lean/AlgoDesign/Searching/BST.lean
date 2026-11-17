/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Spec
public import AlgoDesign.Searching.BST.Decide
public import AlgoDesign.Searching.BST.Basic
public import AlgoDesign.Searching.BST.Search
public import AlgoDesign.Searching.BST.Insert
public import AlgoDesign.Searching.BST.Delete
public import AlgoDesign.Searching.BST.Cost
public import AlgoDesign.Searching.BST.Analysis

/-! The binary search tree. Its contract is in `BST/Spec.lean`; this file imports
the whole structure. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace BST

variable {α : Type} [LinearOrder α]

/-! ## The library's BST meets its contract

`Contract` in `BST/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The BST as a search tree: its operations (delete is the chapter's TRANSPLANT), and its one
invariant as `Valid`. -/
def tree : SearchTree α (BST α) where
  empty := leaf
  insert := insert
  delete := delete
  search := search
  toList := toList
  Valid := Valid

/-- **Promise:** the search tree's. -/
theorem promise : (tree : SearchTree α (BST α)).Promise :=
  SearchTree.Promise.of_mem tree Mem (fun _ t => mem_toList t)
    rfl
    (fun a b t _ => mem_insert t a b) (fun a b _ h => mem_delete h a b)
    (fun a _ h => search_correct h a) (fun _ h => sorted_toList h)

omit [LinearOrder α] in
theorem length_toList (t : BST α) : (toList t).length = size t := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr => simp [toList, size, ihl, ihr]; omega

omit [LinearOrder α] in
theorem height_le_size (t : BST α) : height t ≤ size t := by
  induction t with
  | leaf => simp [height]
  | node l k r ihl ihr => simp only [height, size]; omega

/-- On a valid tree, the search tree's `size` is the tree's own. -/
theorem tree_size {t : BST α} (h : Valid t) : (tree : SearchTree α (BST α)).size t = size t := by
  rw [promise.size_eq_length h]; exact length_toList t

/-- The BST's range query is the search tree's, `SearchTree.range`. -/
theorem range_eq (lo hi : RangeBound α) (t : BST α) :
    range lo hi t = (tree : SearchTree α (BST α)).range t lo hi := rfl

/-- **In the search tree's terms:** the height is at most the size, so search and insert take at
most `n` comparisons on a valid tree of `n` keys. -/
theorem within_size :
    (tree : SearchTree α (BST α)).Within searchM (fun n => n) ∧
      (tree : SearchTree α (BST α)).Within insertM (fun n => n) :=
  ⟨fun a t h _ => by
      simpa [tree_size h] using (time_searchM_le_height a t).trans (height_le_size t),
    fun a t h _ => by
      simpa [tree_size h] using (time_insertM_le_height a t).trans (height_le_size t)⟩

/-- The library's operations, as the box names them; `searchM` and `insertM` are its counting. -/
def ops : Ops α where
  empty := leaf
  insert := insert
  delete := delete
  search := search
  Valid := Valid
  searchM := searchM
  insertM := insertM
  counted a t := ⟨ret_searchM a t, ret_insertM a t⟩
  emptyValid := trivial
  insertKeeps a _ h := sorted_insert h a
  deleteKeeps a _ h := sorted_delete h a

/-- The search tree the library's operations make is `tree`. -/
theorem tree_ops : (ops : Ops α).tree = tree := rfl

/-- **The library's BST meets its contract** (`Contract` in `BST/Spec.lean`). -/
theorem contract : Contract (ops : Ops α) where
  promise := promise
  invariants _ := Iff.rfl
  cost := ⟨time_searchM_le_height, time_insertM_le_height, within_size.1, within_size.2⟩

end BST

end AlgoDesign.Searching
