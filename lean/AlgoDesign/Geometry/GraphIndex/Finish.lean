/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Decide
public import Mathlib.Data.List.Sort

/-!
# The graph index: the search's last step

The walk ends with a beam of nodes; the search measures each exactly, sorts them by squared
distance (ties by node) and keeps `k`. Proved here: that step keeps the box's promise for any
beam of stored nodes, each once (`promise_finish`), so it reports only stored points
(`finish_stored`). The walk is modeled in `Search.lean`, which proves what it owes,
`Ops.WalksToBeam` (`Spec.lean`).
Rust: `Hnsw::search`, which ends with `finish`; a separate Lean–Rust check
tests this step on the beams the Rust's walks end with, and the walk itself hop by hop.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

omit [CommRing α] [IsStrictOrderedRing α] in
theorem byDistance_total (a b : Neighbor α) : ByDistance a b ∨ ByDistance b a := by
  unfold ByDistance
  rcases lt_trichotomy a.sqDist b.sqDist with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.id b.id with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

omit [CommRing α] [IsStrictOrderedRing α] in
theorem byDistance_trans {a b c : Neighbor α} (hab : ByDistance a b) (hbc : ByDistance b c) :
    ByDistance a c := by
  unfold ByDistance at *
  rcases hab with h1 | ⟨h1, h1'⟩ <;> rcases hbc with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

instance : Std.Total (ByDistance (α := α)) := ⟨byDistance_total⟩

instance : IsTrans (Neighbor α) ByDistance := ⟨fun _ _ _ => byDistance_trans⟩

/-- The search's last step: measure every node of the beam exactly, sort by `ByDistance`, keep
`k`. Rust: `finish` in `hnsw.rs`. -/
def finish (pts : List (Point d α)) (q : Point d α) (k : ℕ) (beam : List ℕ) :
    List (Neighbor α) :=
  ((beam.map fun i => { sqDist := sqDist pts[i]! q, id := i }).insertionSort ByDistance).take k

omit [IsStrictOrderedRing α] in
/-- **The last step keeps the promise**: on a beam of stored nodes, each once, `k` of them (all if
fewer), each once, each with its exact squared distance, sorted nearest first, none left out ahead
of one reported. -/
theorem promise_finish (pts : List (Point d α)) (q : Point d α) (k : ℕ) (beam : List ℕ)
    (hnd : beam.Nodup) (hb : ∀ i ∈ beam, i < pts.length) :
    Promise pts q k beam (finish pts q k beam) := by
  set sorted := (beam.map fun i => (⟨sqDist pts[i]! q, i⟩ : Neighbor α)).insertionSort ByDistance
  have hmem : ∀ x, x ∈ sorted ↔ ∃ i ∈ beam, ⟨sqDist pts[i]! q, i⟩ = x := by
    intro x
    rw [List.mem_insertionSort, List.mem_map]
  have hsorted : sorted.Pairwise ByDistance := List.pairwise_insertionSort _ _
  have hids : (sorted.map Neighbor.id).Perm beam := by
    have := (List.perm_insertionSort ByDistance
      (beam.map fun i => (⟨sqDist pts[i]! q, i⟩ : Neighbor α))).map
      Neighbor.id
    rwa [List.map_map,
      show (Neighbor.id ∘ fun i => (⟨sqDist pts[i]! q, i⟩ : Neighbor α)) = id from rfl,
      List.map_id] at this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [finish, List.length_insertionSort]
  · simp only [finish, List.map_take]
    exact (hids.nodup_iff.mpr hnd).sublist (List.take_sublist _ _)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := (hmem x).mp (List.mem_of_mem_take hx)
    exact ⟨hi, hb i hi, by rw [getElem!_pos pts i (hb i hi)]⟩
  · exact hsorted.sublist (List.take_sublist _ _)
  · intro x hx i hi hout hlt
    rw [← getElem!_pos pts i hlt]
    have hy : (⟨sqDist pts[i]! q, i⟩ : Neighbor α) ∈ sorted := (hmem _).mpr ⟨i, hi, rfl⟩
    rw [← List.take_append_drop k sorted] at hsorted hy
    have hdrop : (⟨sqDist pts[i]! q, i⟩ : Neighbor α) ∈ sorted.drop k := by
      rcases List.mem_append.mp hy with h | h
      · exact absurd (List.mem_map_of_mem (f := Neighbor.id) h) hout
      · exact h
    exact (List.pairwise_append.mp hsorted).2.2 x hx _ hdrop

omit [IsStrictOrderedRing α] in
/-- Each a stored point: when the beam holds only stored nodes, each once, so does the answer. -/
theorem finish_stored (pts : List (Point d α)) (q : Point d α) (k : ℕ) (beam : List ℕ)
    (hnd : beam.Nodup) (h : ∀ i ∈ beam, i < pts.length) :
    ∀ a ∈ finish pts q k beam, a.id < pts.length :=
  fun a ha => h _ ((promise_finish pts q k beam hnd h).2.2.1 a ha).1

end HNSW

end AlgoDesign.Geometry
