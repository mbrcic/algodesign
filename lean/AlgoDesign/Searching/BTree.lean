/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Spec
public import AlgoDesign.Searching.BTree.Decide
public import AlgoDesign.Searching.BTree.Basic
public import AlgoDesign.Searching.BTree.Search
public import AlgoDesign.Searching.BTree.Balance
public import AlgoDesign.Searching.BTree.Insert
public import AlgoDesign.Searching.BTree.Delete
public import AlgoDesign.Searching.BTree.Cost
public import AlgoDesign.Searching.BTree.IO

/-! The B-tree. Its contract is in `BTree/Spec.lean`; this file imports
the whole structure. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## The library's BTree meets its contract

`Contract` in `BTree/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The B-tree as a search tree, its empty tree of minimum degree `deg`: its operations, and its
invariants as `Valid`. -/
def tree (deg : ℕ) (hdeg : DegreeAtLeastTwo deg := by decide) : SearchTree α (BTree α) where
  empty := ⟨deg, hdeg, .leaf []⟩
  insert := insert
  delete a t := (delete a t).1
  search := search
  toList := toList
  Valid := Valid

theorem valid_empty {deg : ℕ} (h : DegreeAtLeastTwo deg) :
    Valid (⟨deg, h, .leaf []⟩ : BTree α) := by
  refine valid_iff_legal.2 ⟨?_, ?_, ?_, h⟩ <;>
    simp_all [Node.Bounded, Node.BoundedKeys, Node.SameDepth, Node.depth?, Node.KeyCountOk]

/-- **Promise:** the search tree's, at every minimum degree from 2 on. -/
theorem promise {deg : ℕ} (hdeg : DegreeAtLeastTwo deg) :
    (tree deg hdeg : SearchTree α (BTree α)).Promise :=
  SearchTree.Promise.of_mem (tree deg hdeg) Mem (fun a t => mem_toList a t)
    rfl
    (fun a b _ h => insertMem h a b) (fun a b _ h => deleteMem h a b)
    (fun a _ h => search_correct_valid h a) (fun _ h => sorted_toList h)

/-- On a valid tree, the search tree's `size` is the tree's own. -/
theorem tree_size {deg : ℕ} (hdeg : DegreeAtLeastTwo deg) {t : BTree α} (h : Valid t) :
    (tree deg hdeg : SearchTree α (BTree α)).size t = size t := by
  rw [(promise hdeg).size_eq_length h]; exact length_toList t

/-- The B-tree's range query is the search tree's, `SearchTree.range`, at every degree. -/
theorem range_eq (deg : ℕ) (hdeg : DegreeAtLeastTwo deg) (lo hi : RangeBound α) (t : BTree α) :
    range lo hi t = (tree deg hdeg : SearchTree α (BTree α)).range t lo hi := rfl

/-- The library's operations, as the box names them;
`searchM`, `insertM` and `deleteM` are its counting. The library's `deleteM` also says whether the
key was there; the box does not ask for that, so `ops` keeps the tree. -/
def ops : Ops α where
  empty deg hdeg := ⟨deg, hdeg, .leaf []⟩
  insert := insert
  delete a t := (delete a t).1
  search := search
  Valid := Valid
  searchM := searchM
  insertM := insertM
  deleteM a t := Prod.fst <$> deleteM a t
  counted a t := ⟨ret_searchM a t, ret_insertM a t, by simp [ret_deleteM]⟩
  emptyDeg _ _ := rfl
  emptyValid _ hdeg := valid_empty hdeg
  insertKeeps a _ h := insertValid h a
  deleteKeeps a _ h := deleteValid h a
  keepsDeg _ _ := ⟨rfl, rfl⟩

/-- The search tree the library's operations make from the empty tree of degree `deg` is
`tree deg`. -/
theorem tree_ops (deg : ℕ) (hdeg : DegreeAtLeastTwo deg) :
    (ops : Ops α).tree deg hdeg = tree deg hdeg := rfl

/-- **The library's B-tree meets its contract** (`Contract` in `BTree/Spec.lean`) at every minimum
degree from 2. -/
theorem contract : Contract (ops : Ops α) where
  promise _ hdeg := promise hdeg
  invariants _ := Iff.rfl
  cost := by
    refine ⟨?_, ?_, ?_⟩
    · intro a t h hs
      rw [tree_ops] at hs ⊢; rw [tree_size t.two_le_deg h] at hs ⊢
      exact time_searchM_le_log h hs a
    · intro a t h hs
      rw [tree_ops] at hs ⊢; rw [tree_size t.two_le_deg h] at hs ⊢
      exact time_insertM_le_log h hs a
    · intro a t h hs
      rw [tree_ops] at hs ⊢; rw [tree_size t.two_le_deg h] at hs ⊢
      exact time_deleteM_le_log h hs a

/-- `log_deg((n + 1) / 2) + 2 ≤ 3 log₂(n + 1)` for `n ≥ 1` and `deg ≥ 2`: the B-tree's bounds fit
the shared target. -/
theorem log_bound_le {deg n : ℕ} (hdeg : 2 ≤ deg) (hn : 0 < n) :
    Nat.log deg ((n + 1) / 2) + 2 ≤ 3 * Nat.log2 (n + 1) := by
  have h1 : Nat.log deg ((n + 1) / 2) ≤ Nat.log 2 ((n + 1) / 2) :=
    Nat.log_anti_left Nat.one_lt_two hdeg
  have h2 : Nat.log 2 ((n + 1) / 2) ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (Nat.div_le_self _ _)
  have h3 : 1 ≤ Nat.log 2 (n + 1) := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
  rw [Nat.log2_eq_log_two]
  omega

/-- **The design target "short", met:** search, insert and delete each in at most
`3 log₂(n + 1)` block reads, at every minimum degree from 2. -/
theorem logarithmic {deg : ℕ} (hdeg : DegreeAtLeastTwo deg) :
    (tree deg hdeg : SearchTree α (BTree α)).Logarithmic 3 searchM insertM deleteM := by
  refine ⟨fun a t h hs => ?_, fun a t h hs => ?_, fun a t h hs => ?_⟩ <;>
    rw [tree_size hdeg h] at hs ⊢ <;> beta_reduce <;>
    have hb := log_bound_le t.two_le_deg hs
  · have := time_searchM_le_log h hs a; omega
  · have := time_insertM_le_log h hs a; omega
  · have := time_deleteM_le_log h hs a; omega

end BTree

end AlgoDesign.Searching
