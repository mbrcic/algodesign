/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Spec
public import AlgoDesign.Flows.MaxFlow.Loop

/-!
# Cheapest flow of a given amount: fitting heights prove the flow cheapest

Source: Ahuja, Magnanti and Orlin, *Network Flows* (1993), §9.3, the reduced cost optimality
conditions (p. 309), with the opposite sign convention.

Heights add nothing to a flow's cost difference: summed over the arrows, the amount times the
height at the tail less the height at the head is the flow amount times the source's height
less the sink's (`sum_heights`). So for two flows of the same amount, the cost difference is the
sum of the changed costs times the difference of the amounts. Where the other flow carries more,
the arrow has room; where it carries less, the arrow's way back has room; under fitting heights
both have a changed cost of at least zero, so every term is at least zero
(`cheapest_of_heightsFit`).
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

theorem sum_list_range (m : ℕ) (g : ℕ → ℤ) :
    ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
                 simp

/-- Summed over the arrows, each arrow's amount times its tail's value less its head's is the sum
over the vertices of each vertex's value times what leaves it less what enters it. -/
theorem sum_tail_head {N : Network} (hN : N.WellFormed) (f : Flow) (H : ℕ → ℤ) :
    ∑ i ∈ Finset.range N.g.arrows.length, (f.on i : ℤ) * (H (N.tail i) - H (N.head i)) =
      ∑ v ∈ Finset.range N.g.n, H v * netOut N f v := by
  simp_rw [netOut_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨ht, hh⟩ := Network.endpoints_lt hN (Finset.mem_range.1 hi)
  have e : ∀ v, H v * ((f.on i : ℤ) * ((if N.tail i = v then 1 else 0) -
      (if N.head i = v then 1 else 0))) =
      (f.on i : ℤ) * ((if N.tail i = v then H v else 0) - (if N.head i = v then H v else 0)) := by
    intro v; split_ifs <;> ring
  simp_rw [e, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp [ht, hh]

/-- **Heights add nothing but the amount at the two ends**: summed over the arrows, a flow
amount times the height at the tail less the height at the head is the flow amount times the
source's height less the sink's. -/
theorem sum_heights {N : Network} (hN : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    (H : ℕ → ℤ) :
    ∑ i ∈ Finset.range N.g.arrows.length, (f.on i : ℤ) * (H (N.tail i) - H (N.head i)) =
      (H N.source - H N.sink) * value N f := by
  have hs : N.source ∈ Finset.range N.g.n := Finset.mem_range.2 hN.2.2.1
  have ht : N.sink ∈ Finset.range N.g.n := Finset.mem_range.2 hN.2.2.2.1
  have hst : N.source ≠ N.sink := hN.2.2.2.2
  have zero : ∀ v ∈ Finset.range N.g.n, v ≠ N.source ∧ v ≠ N.sink → netOut N f v = 0 := by
    intro v hv ⟨h1, h2⟩
    have := hf.2.1 v (Finset.mem_range.1 hv) h1 h2
    simp [netOut, this]
  have two : ∀ G : ℕ → ℤ, ∑ v ∈ Finset.range N.g.n, G v * netOut N f v =
      G N.source * netOut N f N.source + G N.sink * netOut N f N.sink :=
    fun G => Finset.sum_eq_add_of_mem _ _ hs ht hst fun v hv hne => by rw [zero v hv hne, mul_zero]
  have hsum := sum_tail_head hN f fun _ => 1
  simp only [sub_self, mul_zero, Finset.sum_const_zero] at hsum
  rw [two, one_mul, one_mul] at hsum
  rw [sum_tail_head hN f H, two]
  have hv : value N f = netOut N f N.source := rfl
  rw [hv]
  have : netOut N f N.sink = -netOut N f N.source := by linarith
  rw [this]; ring

theorem flowCost_eq (P : Problem) (f : Flow) :
    P.flowCost f = ∑ i ∈ Finset.range P.net.g.arrows.length, P.costOf i * (f.on i : ℤ) := by
  rw [Problem.flowCost, Network.ids, sum_list_range]

theorem changedCost_along (P : Problem) (h : Heights) (i : ℕ) :
    changedCost P h (.along i) = P.costOf i + h.at (P.net.tail i) - h.at (P.net.head i) := rfl

theorem changedCost_back (P : Problem) (h : Heights) (i : ℕ) :
    changedCost P h (.back i) = -changedCost P h (.along i) := by
  simp only [changedCost, Problem.residualCost, ResidualArrow.tail, ResidualArrow.head]
  ring

/-- **Fitting heights prove a flow cheapest for its amount.** -/
theorem cheapest_of_heightsFit {P : Problem} (hN : P.net.WellFormed) {f : Flow} {h : Heights}
    (hf : IsFlow P.net f) (hfit : HeightsFitEverywhere ⟨P, f, h⟩) :
    CheapestForAmount ⟨P, f, h⟩ := by
  intro g hg hval
  simp only at hval ⊢
  have key : P.flowCost g - P.flowCost f =
      ∑ i ∈ Finset.range P.net.g.arrows.length,
        changedCost P h (.along i) * ((g.on i : ℤ) - f.on i) := by
    have eg := sum_heights hN hg fun v => h.at v
    have ef := sum_heights hN hf fun v => h.at v
    rw [hval] at eg
    rw [flowCost_eq, flowCost_eq, ← Finset.sum_sub_distrib]
    have : ∑ i ∈ Finset.range P.net.g.arrows.length,
        changedCost P h (.along i) * ((g.on i : ℤ) - f.on i) =
        ∑ i ∈ Finset.range P.net.g.arrows.length, (P.costOf i * g.on i - P.costOf i * f.on i) +
          (∑ i ∈ Finset.range P.net.g.arrows.length,
              (g.on i : ℤ) * (h.at (P.net.tail i) - h.at (P.net.head i)) -
            ∑ i ∈ Finset.range P.net.g.arrows.length,
              (f.on i : ℤ) * (h.at (P.net.tail i) - h.at (P.net.head i))) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [changedCost_along]; ring
    rw [this, eg, ef, sub_self, add_zero]
  have hnn : 0 ≤ ∑ i ∈ Finset.range P.net.g.arrows.length,
      changedCost P h (.along i) * ((g.on i : ℤ) - f.on i) := by
    refine Finset.sum_nonneg fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rcases lt_trichotomy (g.on i) (f.on i) with hlt | heq | hgt
    · have := hfit (.back i) hi' (by simp only [ResidualArrow.residualCapacity]; omega)
      rw [changedCost_back] at this
      have : ((g.on i : ℤ) - f.on i) ≤ 0 := by omega
      nlinarith
    · rw [heq]; simp
    · have hc : g.on i ≤ P.net.capOf i := hg.1 i hi'
      have := hfit (.along i) hi' (by simp only [ResidualArrow.residualCapacity]; omega)
      have : 0 ≤ ((g.on i : ℤ) - f.on i) := by omega
      positivity
  linarith

end AlgoDesign.Flows.MinCostFlow
