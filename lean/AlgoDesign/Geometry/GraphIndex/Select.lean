/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Decide

/-!
# The graph index: the picking rule

The rule (Malkov–Yashunin Alg. 4, the relative neighborhood graph's test, Toussaint 1980): scan
the candidates nearest first, and skip `c` if a neighbor already kept is strictly nearer to it
than the base point is; keep at most `M`. On a tie `c` is kept, as in hnswlib, the paper's
reference implementation; the paper's wording, "if e is closer to q compared to any element from
R", would drop it. The paper's two options are off (`extendCandidates`, `keepPrunedConnections`).

Proved here: the rule meets box invariant 2 (`picksDiverse_selectNeighbors`); its defining
property, that no neighbor kept before a kept neighbor is strictly nearer to it than the base
is (`selectNeighbors_diverse`); and its output bounds (at most `M`, all candidates, the nearest
candidate kept first). Rust: `hnsw::select_neighbors`.
-/

@[expose] public section

namespace AlgoDesign.Geometry.HNSW

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

namespace Picking

/-- **A picking step's invariant**: `PicksDiverse` (box invariant 2). It is checked at every
picking the insertion makes, a new node's list and the re-pick of an overfull one.
Rust: `is_picking_valid`. -/
def Valid (p : Picking d α) : Prop := PicksDiverse p

instance (p : Picking d α) : Decidable (Valid p) := by
  unfold Valid; infer_instance

end Picking

/-- Keep `c` (candidates in the given order, assumed nearest-to-`base` first) unless a neighbor
already kept is strictly nearer to it than `base` is, up to `M` kept. -/
def selectNeighbors (M : ℕ) (base : Point d α) :
    List (Point d α) → List (Point d α) → List (Point d α)
  | kept, [] => kept
  | kept, c :: cs =>
      if kept.length < M ∧ kept.all (fun k => decide (sqDist base c ≤ sqDist k c)) then
        selectNeighbors M base (kept ++ [c]) cs
      else selectNeighbors M base kept cs

omit [IsStrictOrderedRing α] in
/-- At most `M` neighbors are kept. -/
theorem selectNeighbors_length_le (M : ℕ) (base : Point d α) (kept cs : List (Point d α))
    (h : kept.length ≤ M) : (selectNeighbors M base kept cs).length ≤ M := by
  induction cs generalizing kept with
  | nil => exact h
  | cons c cs ih =>
    simp only [selectNeighbors]
    split_ifs with hc
    · exact ih _ (by simp only [List.length_append, List.length_singleton]; omega)
    · exact ih _ h

omit [IsStrictOrderedRing α] in
/-- Every kept neighbor was a candidate (or already kept). -/
theorem selectNeighbors_subset (M : ℕ) (base : Point d α) (kept cs : List (Point d α)) :
    ∀ x ∈ selectNeighbors M base kept cs, x ∈ kept ∨ x ∈ cs := by
  induction cs generalizing kept with
  | nil => intro x hx; exact Or.inl hx
  | cons c cs ih =>
    intro x hx
    simp only [selectNeighbors] at hx
    split_ifs at hx with hc
    · rcases ih _ x hx with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))
      · exact Or.inr (List.mem_cons_of_mem c h)
    · rcases ih _ x hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem c h)

omit [IsStrictOrderedRing α] in
/-- Neighbors once kept stay kept, in front. -/
theorem selectNeighbors_prefix (M : ℕ) (base : Point d α) (kept cs : List (Point d α)) :
    kept <+: selectNeighbors M base kept cs := by
  induction cs generalizing kept with
  | nil => exact List.prefix_refl _
  | cons c cs ih =>
    simp only [selectNeighbors]
    split_ifs with hc
    · exact (List.prefix_append _ _).trans (ih _)
    · exact ih _

omit [IsStrictOrderedRing α] in
/-- The first candidate is always kept (when there is room). -/
theorem selectNeighbors_head_first (M : ℕ) (base c : Point d α) (cs : List (Point d α))
    (hM : 0 < M) : (selectNeighbors M base [] (c :: cs)).head? = some c := by
  simp only [selectNeighbors, List.length_nil, List.all_nil, and_true, hM, ↓reduceIte,
    List.nil_append]
  obtain ⟨t, ht⟩ := selectNeighbors_prefix M base [c] cs
  rw [← ht]
  rfl

omit [IsStrictOrderedRing α] in
/-- **The nearest candidate is always kept** (when there is room): with the candidates given
nearest-first, as Alg. 4 extracts them, the first neighbor kept is at least as near the base as
every candidate. -/
theorem selectNeighbors_head (M : ℕ) (base c : Point d α) (cs : List (Point d α)) (hM : 0 < M)
    (hfirst : ∀ x ∈ cs, sqDist base c ≤ sqDist base x) :
    ∃ y, (selectNeighbors M base [] (c :: cs)).head? = some y ∧
      ∀ x ∈ c :: cs, sqDist base y ≤ sqDist base x := by
  refine ⟨c, selectNeighbors_head_first M base c cs hM, fun x hx => ?_⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact le_rfl
  · exact hfirst x hx

omit [IsStrictOrderedRing α] in
/-- What the rule keeps stays diverse: no neighbor kept earlier is strictly nearer to a later
one than the base is. -/
theorem selectNeighbors_pairwise (M : ℕ) (base : Point d α) (kept cs : List (Point d α))
    (h : kept.Pairwise (fun k c => sqDist base c ≤ sqDist k c)) :
    (selectNeighbors M base kept cs).Pairwise (fun k c => sqDist base c ≤ sqDist k c) := by
  induction cs generalizing kept with
  | nil => exact h
  | cons c cs ih =>
    simp only [selectNeighbors]
    split_ifs with hc
    · apply ih
      refine List.pairwise_append.mpr ⟨h, List.pairwise_singleton _ _, fun k hk y hy => ?_⟩
      rw [List.mem_singleton.mp hy]
      have := List.all_eq_true.mp hc.2 k hk
      simpa using this
    · exact ih _ h

omit [IsStrictOrderedRing α] in
/-- **The rule's defining property** (what separates it from keeping the first `M`): no
neighbor kept earlier is strictly nearer to a later one than the base is. -/
theorem selectNeighbors_diverse (M : ℕ) (base : Point d α) (cs : List (Point d α)) :
    (selectNeighbors M base [] cs).Pairwise (fun k c => sqDist base c ≤ sqDist k c) :=
  selectNeighbors_pairwise M base [] cs List.Pairwise.nil

omit [IsStrictOrderedRing α] in
/-- What the rule adds to `kept` is what box invariant 2's rule picks, given `kept` already
picked. -/
theorem selectNeighbors_picksFrom (M : ℕ) (base : Point d α) (kept cs : List (Point d α)) :
    ∃ X, selectNeighbors M base kept cs = kept ++ X ∧ HNSW.PicksFrom M base kept cs X := by
  induction cs generalizing kept with
  | nil => exact ⟨[], by simp [selectNeighbors], rfl⟩
  | cons c cs ih =>
    have hiff : (kept.length < M ∧ kept.all (fun k => decide (sqDist base c ≤ sqDist k c))) ↔
        (kept.length < M ∧ ∀ k ∈ kept, sqDist base c ≤ sqDist k c) := by
      simp [List.all_eq_true]
    by_cases hc : kept.length < M ∧ ∀ k ∈ kept, sqDist base c ≤ sqDist k c
    · obtain ⟨X, hX, hP⟩ := ih (kept ++ [c])
      refine ⟨c :: X, ?_, ?_⟩
      · unfold selectNeighbors
        split_ifs with h
        · rw [hX, List.append_assoc, List.singleton_append]
        · exact absurd (hiff.mpr hc) h
      · unfold HNSW.PicksFrom
        split_ifs
        exact ⟨rfl, hP⟩
    · obtain ⟨X, hX, hP⟩ := ih kept
      refine ⟨X, ?_, ?_⟩
      · unfold selectNeighbors
        split_ifs with h
        · exact absurd (hiff.mp h) hc
        · exact hX
      · unfold HNSW.PicksFrom
        split_ifs
        exact hP

omit [IsStrictOrderedRing α] in
/-- **The rule meets box invariant 2**: given candidates nearest `base` first, what
`selectNeighbors` keeps is what the box's picking rule picks. -/
theorem picksDiverse_selectNeighbors (M : ℕ) (base : Point d α) (cs : List (Point d α))
    (hs : cs.Pairwise (fun a b => sqDist base a ≤ sqDist base b)) :
    HNSW.PicksDiverse ⟨M, base, cs, selectNeighbors M base [] cs⟩ := by
  obtain ⟨X, hX, hP⟩ := selectNeighbors_picksFrom M base [] cs
  rw [hX, List.nil_append]
  exact ⟨hs, hP⟩

end AlgoDesign.Geometry.HNSW
