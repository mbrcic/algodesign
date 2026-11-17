/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Workbench.Spec
public import AlgoDesign.Geometry.Workbench.Decide
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Rat.Defs

/-! The design project's contract. It is in `Workbench/Spec.lean`; this file imports it and proves
that the scan, as a candidate, meets it (`reference_contract`), with recall 1
(`reference_recall`, through `recall_eq_one_of_scan`) at one tick per stored point
(`time_referenceM`): the count every other candidate must beat. -/

@[expose] public section

namespace AlgoDesign.Geometry.Workbench

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- How many points recall is out of: `k`, or every stored point if there are fewer. -/
def wanted (k : ℕ) (ps : List (Point d α)) : ℕ := min k ps.length

/-- The scan's `wanted k ps`-th least squared distance from `q`: how near a point must be to
count as one of the true nearest. -/
def kth (k : ℕ) (ps : List (Point d α)) (q : Point d α) : α :=
  (dists q ps).getD (wanted k ps - 1) 0

/-- `a` is among the true `k` nearest: a stored point no farther from `q` than `kth`. A tie at that
distance counts whichever point is answered. -/
def AmongTrueNearest (k : ℕ) (ps : List (Point d α)) (q : Point d α) (a : Neighbor α) : Prop :=
  ∃ h : a.id < ps.length, sqDist ps[a.id] q ≤ kth k ps q

instance (k : ℕ) (ps : List (Point d α)) (q : Point d α) (a : Neighbor α) :
    Decidable (AmongTrueNearest k ps q a) := by
  unfold AmongTrueNearest; infer_instance

/-- The points answered that are among the true nearest. -/
def hits (k : ℕ) (ps : List (Point d α)) (q : Point d α) (ans : Answer α) : ℕ :=
  (ans.filter (AmongTrueNearest k ps q ·)).length

/-- **Recall@k, measured, not promised**: the share of the true `k` nearest that an answer found,
`hits` out of `wanted`, and 1 when nothing is wanted. The bench holds it to at least 0.9. -/
def recallAt (k : ℕ) (ps : List (Point d α)) (q : Point d α) (ans : Answer α) : ℚ :=
  if wanted k ps = 0 then 1 else (hits k ps q ans : ℚ) / wanted k ps

/-- The squared distance from `q` of each id in the list, with the id, in the list's order. -/
def measured (ps : List (Point d α)) (q : Point d α) : List ℕ → Answer α
  | [] => []
  | i :: is => { sqDist := sqDist ps[i]! q, id := i } :: measured ps q is

/-- `measured`, counted: one tick per distance computed. -/
def measuredM (ps : List (Point d α)) (q : Point d α) : List ℕ → TimeM ℕ (Answer α)
  | [] => pure []
  | i :: is => do
      tick 1
      let rest ← measuredM ps q is
      pure ({ sqDist := sqDist ps[i]! q, id := i } :: rest)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem ret_measuredM (ps : List (Point d α)) (q : Point d α) (is : List ℕ) :
    (measuredM ps q is).ret = measured ps q is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [measuredM, measured, ih]

/-- Nearest first: a stable sort on the distance. -/
def rank (l : Answer α) : Answer α := l.insertionSort (fun a b => a.sqDist ≤ b.sqDist)

/-- **The scan as a candidate**: it stores the list itself, measures every point, and keeps the
`k` nearest. -/
def reference : Ops d α (List (Point d α)) where
  build ps := ps
  query k q ps := (rank (measured ps q (List.range ps.length))).take k
  queryM k q ps := do
    let l ← measuredM ps q (List.range ps.length)
    pure ((rank l).take k)
  counted k q ps := by simp [ret_measuredM]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem time_measuredM (ps : List (Point d α)) (q : Point d α) (is : List ℕ) :
    (measuredM ps q is).time = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [measuredM, ih]; omega

omit [IsStrictOrderedRing α] in
/-- **The scan's cost**: one tick per stored point, whatever `k`. -/
theorem time_referenceM (ps : List (Point d α)) (k : ℕ) (q : Point d α) :
    ((reference (d := d) (α := α)).queryM k q ps).time = ps.length := by
  simp [reference, time_measuredM]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem measured_eq_map (ps : List (Point d α)) (q : Point d α) (is : List ℕ) :
    measured ps q is = is.map fun i => { sqDist := sqDist ps[i]! q, id := i } := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [measured, ih]

omit [IsStrictOrderedRing α] in
/-- The scan's measured distances, ranked, are `dists`. -/
theorem map_fst_rank_measured (ps : List (Point d α)) (q : Point d α) :
    (rank (measured ps q (List.range ps.length))).map Neighbor.sqDist = dists q ps := by
  have : Std.Total (fun a b : Neighbor α => a.sqDist ≤ b.sqDist) := ⟨fun x y => le_total _ _⟩
  have : IsTrans (Neighbor α) (fun a b => a.sqDist ≤ b.sqDist) := ⟨fun _ _ _ => le_trans⟩
  have hrange : (List.range ps.length).map (fun i => sqDist ps[i]! q) = ps.map (sqDist · q) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < ps.length := by simpa using h1
    simp [List.getElem?_eq_getElem hi]
  unfold dists rank
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) ?_
    (List.pairwise_insertionSort _ _) ?_
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  · refine ((List.perm_insertionSort _ _).map _).trans ?_
    rw [measured_eq_map, List.map_map]
    have h : ((List.range ps.length).map
        (Neighbor.sqDist ∘ fun i => (⟨sqDist ps[i]! q, i⟩ : Neighbor α))) = ps.map (sqDist · q) :=
      hrange
    rw [h]
    exact (List.perm_insertionSort _ _).symm

omit [IsStrictOrderedRing α] in
/-- What the scan answers is a stored point with its own distance. -/
theorem mem_reference {ps : List (Point d α)} {k : ℕ} {q : Point d α} {a : Neighbor α}
    (h : a ∈ (reference (d := d) (α := α)).query k q (reference.build ps)) :
    a.id < ps.length ∧ a.sqDist = sqDist ps[a.id]! q := by
  simp only [reference, rank] at h
  have h' := (List.perm_insertionSort _ _).mem_iff.1 (List.mem_of_mem_take h)
  rw [measured_eq_map] at h'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h'
  exact ⟨List.mem_range.1 hi, rfl⟩

omit [IsStrictOrderedRing α] in
/-- **The scan meets the contract.** -/
theorem reference_contract : Contract (reference (d := d) (α := α)) where
  promise := by
    refine ⟨⟨fun ps k q => ?_, fun _ _ _ _ ha => (mem_reference ha).1, fun ps k q => ?_⟩,
      fun ps k q => ?_, fun ps _ _ a ha => ?_⟩
    · simp [UpToK, reference]
    · simp only [EachOnce, reference, List.map_take]
      refine (List.Nodup.perm ?_ ((List.perm_insertionSort _ _).map Neighbor.id).symm).sublist
        (List.take_sublist _ _)
      rw [measured_eq_map, List.map_map]
      have : (Neighbor.id ∘ fun i : ℕ => (⟨sqDist ps[i]! q, i⟩ : Neighbor α)) = id := rfl
      rw [this, List.map_id]
      exact List.nodup_range
    · simp only [NearestFirst, reference, List.map_take, map_fst_rank_measured]
      exact (List.pairwise_insertionSort _ _).sublist (List.take_sublist _ _)
    · obtain ⟨hlt, he⟩ := mem_reference ha
      exact ⟨hlt, by rw [he, getElem!_pos ps a.id hlt]⟩

omit [IsStrictOrderedRing α] in
/-- **An answer with the scan's distances has recall 1**: one keeping the contract whose
distances, in order, are the `k` least of the stored points', the law `Nearest.Promise` states
for the k nearest. -/
theorem recall_eq_one_of_scan {ps : List (Point d α)} {q : Point d α} {k : ℕ} {ans : Answer α}
    (hexact : ExactDistance ps q ans) (hscan : ans.map Neighbor.sqDist = (dists q ps).take k) :
    recallAt k ps q ans = 1 := by
  have hlen : (dists q ps).length = ps.length := by
    simp [dists, List.length_insertionSort]
  have hsort : (dists q ps).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hans : ans.length = wanted k ps := by
    rw [← List.length_map (f := Neighbor.sqDist), hscan, List.length_take, hlen, wanted]
  unfold recallAt
  split_ifs with h0
  · rfl
  have hm : 0 < wanted k ps := Nat.pos_of_ne_zero h0
  have hmn : wanted k ps - 1 < (dists q ps).length := by
    rw [hlen]; have := Nat.min_le_right k ps.length; unfold wanted at hm ⊢; omega
  have hall : ∀ a ∈ ans, AmongTrueNearest k ps q a := by
    intro a ha
    obtain ⟨hlt, he⟩ := hexact a ha
    refine ⟨hlt, ?_⟩
    rw [← he]
    have hmem : a.sqDist ∈ (dists q ps).take k := hscan ▸ List.mem_map_of_mem ha
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hmem
    rw [List.length_take, hlen] at hj
    rw [← hjeq, List.getElem_take, kth, List.getD_eq_getElem _ _ hmn]
    have hjm : j ≤ wanted k ps - 1 := by unfold wanted; omega
    rcases Nat.lt_or_eq_of_le hjm with hlt | heq
    · exact List.pairwise_iff_getElem.1 hsort j _ _ hmn hlt
    · simp [heq]
  have hhits : hits k ps q ans = wanted k ps := by
    rw [hits, List.filter_eq_self.2 (fun a ha => decide_eq_true (hall a ha)), hans]
  rw [hhits]
  exact div_self (by exact_mod_cast h0)

omit [IsStrictOrderedRing α] in
/-- **The scan's recall is 1.** -/
theorem reference_recall (ps : List (Point d α)) (k : ℕ) (q : Point d α) :
    recallAt k ps q ((reference (d := d) (α := α)).query k q (reference.build ps)) = 1 :=
  recall_eq_one_of_scan (reference_contract.promise.2.2 ps k q)
    (by simp only [reference, List.map_take, map_fst_rank_measured])

end AlgoDesign.Geometry.Workbench
