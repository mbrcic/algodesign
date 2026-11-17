/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.Spec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Assignment: adding the labels up

Labels that fit every pair and are exact on the chosen pairs bound every other choice: summed
over the people, the chosen pairs cost exactly the person labels plus the labels of the chosen
objects, and any other choice costs at least the person labels plus the labels of its objects
(`cost_ge_labels`). When every object is chosen, both sides hold the same object labels; when
only some people are placed, the object labels at most 0, and 0 on every free object, make the
chosen objects' labels the smallest (`cheapest_of_labels`).
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

open Finset

theorem sum_list_range_eq (m : ℕ) (g : ℕ → ℤ) :
    ((List.range m).map g).sum = ∑ i ∈ range m, g i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_succ, ih]
    simp

theorem assignmentCost_eq (P : Problem) (l : List ℕ) :
    assignmentCost P l = ∑ i ∈ range l.length, P.costAt i (l.getD i 0) :=
  sum_list_range_eq _ _

/-- Summed over the places of a list with no repeats, a value of the entries is the sum over its
entries. -/
theorem sum_places {l : List ℕ} (hl : l.Nodup) (g : ℕ → ℤ) :
    ∑ i ∈ range l.length, g (l.getD i 0) = ∑ x ∈ l.toFinset, g x := by
  have e : l.toFinset = (range l.length).image fun i => l.getD i 0 := by
    ext x
    simp only [List.mem_toFinset, mem_image, mem_range, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi]⟩
  rw [e, sum_image]
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at h
  exact (hl.getElem_inj_iff).1 h

/-- **A choice costs at least the labels**: when the labels fit every pair, a choice of
different objects for the people `0 … k − 1` costs at least their labels plus its objects'. -/
theorem cost_ge_labels {P : Problem} {o : List ℕ} {u v : Labels} (ho : IsAssignmentOf P o)
    (hfit : ∀ i < o.length, ∀ j < P.n, u.at i + v.at j ≤ P.costAt i j) :
    ∑ i ∈ range o.length, u.at i + ∑ x ∈ o.toFinset, v.at x ≤ assignmentCost P o := by
  rw [assignmentCost_eq, ← sum_places ho.2, ← sum_add_distrib]
  refine sum_le_sum fun i hi => hfit i (mem_range.1 hi) _ (ho.1 _ ?_)
  have hi := mem_range.1 hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-- **A chosen assignment costs exactly the labels** when they are exact on its pairs. -/
theorem cost_eq_labels {P : Problem} {o : List ℕ} {u v : Labels} (ho : IsAssignmentOf P o)
    (hexact : ∀ i < o.length, u.at i + v.at (o.getD i 0) = P.costAt i (o.getD i 0)) :
    assignmentCost P o = ∑ i ∈ range o.length, u.at i + ∑ x ∈ o.toFinset, v.at x := by
  rw [assignmentCost_eq, ← sum_places ho.2, ← sum_add_distrib]
  exact sum_congr rfl fun i hi => (hexact i (mem_range.1 hi)).symm

/-- **Adding the labels up**: labels that fit every pair of the people `0 … k − 1` and are exact
on the pairs of `obj` make `obj` no costlier than any choice `o` whose objects' labels add up to
at least those of `obj`. -/
theorem cheapest_of_sums {P : Problem} {obj o : List ℕ} {u v : Labels}
    (hobj : IsAssignmentOf P obj) (ho : IsAssignmentOf P o) (hlen : o.length = obj.length)
    (hfit : ∀ i < obj.length, ∀ j < P.n, u.at i + v.at j ≤ P.costAt i j)
    (hexact : ∀ i < obj.length, u.at i + v.at (obj.getD i 0) = P.costAt i (obj.getD i 0))
    (hsum : ∑ x ∈ obj.toFinset, v.at x ≤ ∑ x ∈ o.toFinset, v.at x) :
    assignmentCost P obj ≤ assignmentCost P o := by
  rw [cost_eq_labels hobj hexact]
  refine le_trans ?_ (cost_ge_labels ho (by rw [hlen]; exact hfit))
  rw [hlen]
  linarith

theorem toFinset_eq_range {P : Problem} {o : List ℕ} (ho : IsAssignmentOf P o)
    (hlen : o.length = P.n) : o.toFinset = range P.n := by
  refine eq_of_subset_of_card_le (fun x hx => mem_range.2 (ho.1 x (List.mem_toFinset.1 hx))) ?_
  rw [card_range, List.toFinset_card_of_nodup ho.2, hlen]

/-- **When only some people are placed**: labels that fit every pair of the people placed, are
exact on their pairs, at most 0 on every object and 0 on every free object, make the choice
cheapest for these people. -/
theorem cheapest_of_labels {P : Problem} {obj : List ℕ} {u v : Labels}
    (hobj : IsAssignmentOf P obj)
    (hfit : ∀ i < obj.length, ∀ j < P.n, u.at i + v.at j ≤ P.costAt i j)
    (hexact : ∀ i < obj.length, u.at i + v.at (obj.getD i 0) = P.costAt i (obj.getD i 0))
    (hneg : ∀ j < P.n, v.at j ≤ 0) (hfree : ∀ j < P.n, j ∉ obj → v.at j = 0) :
    ∀ o, o.length = obj.length → IsAssignmentOf P o →
      assignmentCost P obj ≤ assignmentCost P o := by
  intro o hlen ho
  refine cheapest_of_sums hobj ho hlen hfit hexact ?_
  have h1 : ∑ x ∈ obj.toFinset, v.at x = ∑ x ∈ range P.n, v.at x := by
    refine sum_subset (fun x hx => mem_range.2 (hobj.1 x (List.mem_toFinset.1 hx))) ?_
    intro x hx hnx
    exact hfree x (mem_range.1 hx) (fun h => hnx (List.mem_toFinset.2 h))
  have h2 : ∑ x ∈ range P.n, v.at x ≤ ∑ x ∈ o.toFinset, v.at x := by
    have hs : o.toFinset ⊆ range P.n :=
      fun x hx => mem_range.2 (ho.1 x (List.mem_toFinset.1 hx))
    rw [← sum_sdiff hs]
    have : ∑ x ∈ range P.n \ o.toFinset, v.at x ≤ 0 :=
      sum_nonpos fun x hx => hneg x (mem_range.1 (mem_sdiff.1 hx).1)
    linarith
  rw [h1]; exact h2

end AlgoDesign.Flows.Assignment
