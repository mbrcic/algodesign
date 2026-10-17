/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Workbench.Spec

/-! The design project's contract. It is in `Workbench/Spec.lean`; this file imports it and proves
that the plainest candidate meets it (`reference_contract`) and that a candidate meeting it keeps
the search tree's promise (`Contract.isSearchTree`). -/

@[expose] public section

namespace AlgoDesign.Searching.Workbench

/-- The smallest key of `m` above `k`, if any: `Finset.min` of the keys above `k`. -/
def nextLargerOf (m : Finset ℤ) (k : ℤ) : Option ℤ :=
  if h : (m.filter (k < ·)).Nonempty then some ((m.filter (k < ·)).min' h) else none

/-- The promise written as plainly as it can be: the state is the set itself, and `Valid` asks
nothing. The bench's `Reference` is this, over a sorted list. -/
def reference : Ops (Finset ℤ) where
  meaning := id
  empty := ∅
  insert k s := (decide (k ∉ s), insert k s)
  delete k s := (decide (k ∈ s), s.erase k)
  contains k s := decide (k ∈ s)
  nextLarger k s := nextLargerOf s k
  Valid _ := True

/-- A candidate read as a search tree: its operations without their answers, `contains` as
search, and its keys listed in increasing order, read off `meaning`. The listing is the sorted
`meaning`, not anything the candidate computes, so it is in order by construction.

Cost is not stated on a candidate in Lean. A counted operation reports its own ticks, and a
wrapper that counts nothing meets every `SearchTree.Within`; a candidate's cost is what the bench
(`python/algodesign/searching/workbench.py`) measures, in a memory the candidate does not
control. -/
def Ops.asTree {S : Type} (o : Ops S) : SearchTree ℤ S where
  empty := o.empty
  insert k s := (o.insert k s).2
  delete k s := (o.delete k s).2
  search := o.contains
  toList s := (o.meaning s).sort (· ≤ ·)
  Valid := o.Valid

/-- `nextLargerOf` gives the smallest key above, or nothing. -/
theorem nextLargerOf_spec (m : Finset ℤ) (k : ℤ) : NextLargerSpec m k (nextLargerOf m k) := by
  unfold nextLargerOf
  by_cases h : (m.filter (k < ·)).Nonempty
  · simp only [h, ↓reduceDIte]
    have hmem := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hmem
    refine ⟨hmem.1, hmem.2, fun b hb hkb => ?_⟩
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hb, hkb⟩)
  · simp only [h, ↓reduceDIte]
    intro b hb
    by_contra hlt
    exact h ⟨b, Finset.mem_filter.mpr ⟨hb, not_le.mp hlt⟩⟩

/-- The contract can be met. -/
theorem reference_contract : Contract reference where
  promise :=
    ⟨rfl,
      ⟨fun _ _ _ => by ext; simp [reference], fun _ _ _ => rfl⟩,
      ⟨fun _ _ _ => by ext; simp [reference, and_comm], fun _ _ _ => rfl⟩,
      fun _ _ _ => by simp [reference],
      fun k s _ => nextLargerOf_spec s k,
      trivial, fun _ _ _ => trivial, fun _ _ _ => trivial⟩

/-- **A candidate that meets the contract is a search tree** in the chapter's sense: its set laws
are `SetLaws`, and its listing is ordered by construction. Its own "next larger" is held by
`Ops.NextLargerGives`, not here. -/
theorem Contract.isSearchTree {S : Type} {o : Ops S} (h : Contract o) : o.asTree.Promise := by
  obtain ⟨hempty, ⟨hins, -⟩, ⟨hdel, -⟩, hcont, -, hv0, hvi, hvd⟩ := h.promise
  have hk : ∀ s, o.asTree.keys s = o.meaning s := fun s => by
    simp [SearchTree.keys, Ops.asTree]
  exact
    { valid_empty := hv0
      keys_empty := by rw [hk]; exact hempty
      valid_insert := hvi
      valid_delete := hvd
      insert_adds := fun a s hv => by rw [hk, hk]; exact hins a s hv
      delete_takes := fun a s hv => by rw [hk, hk]; exact hdel a s hv
      search_says := fun a s hv => by rw [hk]; exact hcont a s hv
      in_order := fun s _ => by rw [hk]; rfl }

end AlgoDesign.Searching.Workbench
