/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.StepKeeps

/-!
# Cheapest flow of a given amount: the steps keep the invariants

From a flow with fitting heights, every step sends along an augmenting path an amount that fits
it, at least one unit and no more than is left, and leaves fitting heights (`StepKeeps.lean`).
So along the steps the flow stays a flow and the heights fit, the amounts sent add up to at most
the amount requested, and the steps end either with all of it sent or with no augmenting path
left (`runSteps_spec`). The zero heights fit the zero flow when no arrow costs less than 0
(`start_fit`).
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

variable {P : Problem}

/-- The heights after the first `k` of the records `rs`; `h` before the first. -/
def heightsIn (h : Heights) (rs : List RoundRecord) (k : ℕ) : Heights :=
  ((rs.take k).getLast?.map (·.heights)).getD h

theorem heightsIn_succ (h : Heights) (r : RoundRecord) (rs : List RoundRecord) (k : ℕ) :
    heightsIn h (r :: rs) (k + 1) = heightsIn r.heights rs k := by
  simp only [heightsIn, List.take_succ_cons, List.getLast?_cons]
  cases (List.take k rs).getLast? <;> rfl

/-- A flow with heights that fit it. -/
def Fits (P : Problem) (f : Flow) (h : Heights) : Prop :=
  IsFlow P.net f ∧ HeightsFitEverywhere ⟨P, f, h⟩

/-- **What the steps keep**: each sends along an augmenting path, in turn; each sends at least one
unit; together no more than is left; after every one the flow is a flow with fitting heights; and
with enough fuel they end with all of it sent or with no augmenting path left. -/
theorem runSteps_spec (hP : P.WellFormed) : ∀ fuel left f h, Fits P f h →
    FitInTurn P.net f ((runSteps P fuel left f h).map (·.sent)) ∧
      (∀ x ∈ runSteps P fuel left f h, 1 ≤ x.sent.amount) ∧
      (((runSteps P fuel left f h).map (·.sent)).map (·.amount)).sum ≤ left ∧
      (∀ k ≤ (runSteps P fuel left f h).length,
        Fits P (applyAll f (((runSteps P fuel left f h).map (·.sent)).take k))
          (heightsIn h (runSteps P fuel left f h) k)) ∧
      (left < fuel → (((runSteps P fuel left f h).map (·.sent)).map (·.amount)).sum = left ∨
        ∀ p, ¬ IsAugmentingPath P.net
          (applyAll f ((runSteps P fuel left f h).map (·.sent))) p)
  | 0, left, f, h, hF => by
    refine ⟨trivial, by simp [runSteps], by simp [runSteps], fun k hk => ?_, fun h => by omega⟩
    simp only [runSteps, List.length_nil, Nat.le_zero] at hk
    subst hk
    exact hF
  | fuel + 1, left, f, h, hF => by
    by_cases hl : left = 0
    · have e : runSteps P (fuel + 1) left f h = [] := by simp [runSteps, hl]
      rw [e]
      refine ⟨trivial, by simp, by simp, fun k hk => ?_, fun _ => Or.inl (by simp [hl])⟩
      simp only [List.length_nil, Nat.le_zero] at hk
      subst hk
      exact hF
    cases hs : step P left f h with
    | none =>
      have e : runSteps P (fuel + 1) left f h = [] := by simp [runSteps, hl, hs]
      rw [e]
      refine ⟨trivial, by simp, by simp, fun k hk => ?_, fun _ => Or.inr ?_⟩
      · simp only [List.length_nil, Nat.le_zero] at hk
        subst hk
        exact hF
      · exact step_none hP hF.2 hs
    | some r =>
      have e : runSteps P (fuel + 1) left f h =
          r :: runSteps P fuel (left - r.sent.amount) (r.sent.apply f) r.heights := by
        simp [runSteps, hl, hs]
      rw [e]
      obtain ⟨hfit, h1, h2, hH⟩ := step_some hP hF.1 hF.2 (Nat.pos_of_ne_zero hl) hs
      have hF' : Fits P (r.sent.apply f) r.heights := ⟨(apply_isFlow hP.1 hF.1 hfit).1, hH⟩
      obtain ⟨i1, i2, i3, i4, i5⟩ := runSteps_spec hP fuel (left - r.sent.amount) _ _ hF'
      refine ⟨⟨hfit, i1⟩, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · exact i2 x hx
      · simp only [List.map_cons, List.sum_cons]
        omega
      · intro k hk
        cases k with
        | zero => exact hF
        | succ k =>
          rw [heightsIn_succ]
          simp only [List.map_cons, List.take_succ_cons]
          exact i4 k (by simpa using hk)
      · intro hlt
        rcases i5 (by omega) with hsum | hnone
        · left
          simp only [List.map_cons, List.sum_cons]
          omega
        · right
          simpa [applyAll] using hnone

/-- **The zero heights fit the zero flow**, when no arrow costs less than 0. -/
theorem start_fit (hc : P.NoArrowBelowZero) : Fits P (Flow.zero P.net) (startHeights P) := by
  refine ⟨zero_isFlow P.net, fun a _ hr => ?_⟩
  have h0 : ∀ v, (startHeights P).at v = 0 := fun v => by
    simp only [Heights.at, startHeights, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  cases a with
  | along i =>
    simp only [changedCost, Problem.residualCost, h0, add_zero, sub_zero]
    simp only [Problem.costOf, List.getD_eq_getElem?_getD]
    cases hi : P.cost[i]? with
    | none => simp
    | some c => exact hc c (List.mem_of_getElem? hi)
  | back i =>
    simp [ResidualArrow.residualCapacity, Flow.on_zero] at hr

end AlgoDesign.Flows.MinCostFlow
