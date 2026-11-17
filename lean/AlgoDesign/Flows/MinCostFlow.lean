/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Spec
public import AlgoDesign.Flows.MinCostFlow.Steps
public import AlgoDesign.Flows.MinCostFlow.Walk
public import AlgoDesign.Flows.MinCostFlow.Cheapest
public import AlgoDesign.Flows.MinCostFlow.StepKeeps
public import AlgoDesign.Flows.MinCostFlow.Run

/-! Cheapest flow of a given amount: the max-flow loop with the cheapest path rule, stopped at the
requested amount. The contract is in `MinCostFlow/Spec.lean`; the steps in
`MinCostFlow/Steps.lean`; what chapter 6's walk to the sink leaves behind in
`MinCostFlow/Walk.lean`; why fitting heights prove a flow cheapest in
`MinCostFlow/Cheapest.lean`; why one step keeps the heights fitting in
`MinCostFlow/StepKeeps.lean`; and the steps together in `MinCostFlow/Run.lean`.
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

/-! ## What the library's procedures owe -/

/-- The steps start from zero heights. -/
theorem heightsAfter_zero (P : Problem) : heightsAfter P 0 = List.replicate P.net.g.n 0 := rfl

/-- A flow with fitting heights keeps the invariants: fitting heights prove it cheapest. -/
theorem valid_of_fits {P : Problem} (hP : P.WellFormed) {f : Flow} {h : Heights}
    (hF : Fits P f h) : Valid ⟨P, f, h⟩ :=
  ⟨⟨hF.1.1, hF.1.2.1⟩, cheapest_of_heightsFit hP.1 hF.1 hF.2, hF.2⟩

/-- The zero flow with zero heights keeps the invariants, when no arrow costs less than 0. -/
theorem startValid (P : Problem) (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    Valid ⟨P, Flow.zero P.net, heightsAfter P 0⟩ :=
  valid_of_fits hP (start_fit hc)

/-- What the run keeps, from the zero flow and the zero heights. -/
theorem run_spec {P : Problem} (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    FitInTurn P.net (Flow.zero P.net) (steps P) ∧ (∀ x ∈ run P, 1 ≤ x.sent.amount) ∧
      ((steps P).map (·.amount)).sum ≤ P.amount ∧
      (∀ k ≤ (run P).length,
        Fits P (applyAll (Flow.zero P.net) ((steps P).take k)) (heightsAfter P k)) ∧
      (((steps P).map (·.amount)).sum = P.amount ∨
        ∀ p, ¬ IsAugmentingPath P.net (applyAll (Flow.zero P.net) (steps P)) p) := by
  have := runSteps_spec hP (P.amount + 1) P.amount (Flow.zero P.net) (startHeights P)
    (start_fit hc)
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2 (by omega)⟩

theorem length_steps (P : Problem) : (steps P).length = (run P).length := List.length_map _

/-- After every step the flow is a flow with fitting heights. -/
theorem fits_after {P : Problem} (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    ∀ k ≤ (steps P).length,
      Fits P (applyAll (Flow.zero P.net) ((steps P).take k)) (heightsAfter P k) := by
  intro k hk
  rw [length_steps] at hk
  exact (run_spec hP hc).2.2.2.1 k hk

/-- Every step keeps the invariants. -/
theorem stepsKeep (P : Problem) (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    ∀ k ≤ (steps P).length,
      Valid ⟨P, applyAll (Flow.zero P.net) ((steps P).take k), heightsAfter P k⟩ :=
  fun k hk => valid_of_fits hP (fits_after hP hc k hk)

/-- The answer's flow is a flow with heights that fit it. -/
theorem fits_answer {P : Problem} (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    Fits P (minCostFlow P).flow (minCostFlow P).heights := by
  have := fits_after hP hc _ le_rfl
  rwa [List.take_length] at this

/-- The answer's amount is what the steps sent. -/
theorem value_answer {P : Problem} (hP : P.WellFormed) (hc : P.NoArrowBelowZero) :
    value P.net (minCostFlow P).flow = (((steps P).map (·.amount)).sum : ℕ) := by
  have := (applyAll_isFlow hP.1 (zero_isFlow P.net) (run_spec hP hc).1).2
  rw [value_zero, zero_add] at this
  exact this

/-! ## The library's cheapest flow meets its contract -/

/-- The library's procedures: the steps of `MinCostFlow/Steps.lean`. -/
def ops : Ops where
  minCostFlow := minCostFlow
  rounds := steps
  heightsAfter := heightsAfter
  Valid := Valid
  walks _ := ⟨rfl, rfl⟩
  startsLevel := heightsAfter_zero
  startValid := startValid
  roundsKeep := stepsKeep
  augments P hP hc := ⟨(run_spec hP hc).1, fun x hx => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact (run_spec hP hc).2.1 r hr⟩

/-- **A flow of the requested amount.** -/
theorem sendsAFlow : ops.SendsAFlow := fun P hP hc => by
  refine ⟨(fits_answer hP hc).1, ?_⟩
  change value P.net (minCostFlow P).flow ≤ P.amount
  rw [value_answer hP hc]
  exact_mod_cast (run_spec hP hc).2.2.1

/-- **Cheapest among all flows of that amount.** -/
theorem cheapestForItsAmount : ops.CheapestForItsAmount := fun _ hP hc =>
  cheapest_of_heightsFit hP.1 (fits_answer hP hc).1 (fits_answer hP hc).2

/-- **Heights under which no arrow with room has a negative changed cost.** -/
theorem heightsFit : ops.HeightsFit := fun _ hP hc => (fits_answer hP hc).2

/-- **Short only at a cut that proves the amount.** -/
theorem shortOnlyAtACut : ops.ShortOnlyAtACut := fun P hP hc hlt => by
  change P.net.source ∈ reached P.net (minCostFlow P).flow ∧
    P.net.sink ∉ reached P.net (minCostFlow P).flow ∧
    (cutCapacity P.net (reached P.net (minCostFlow P).flow) : ℤ) = value P.net (minCostFlow P).flow
  change value P.net (minCostFlow P).flow < P.amount at hlt
  rw [value_answer hP hc] at hlt
  rcases (run_spec hP hc).2.2.2.2 with hsum | hnone
  · exact absurd hsum (by intro e; omega)
  · exact reached_cut hP.1 (fits_answer hP hc).1 hnone

/-- **At most as many rounds as the requested amount.** -/
theorem stepsAtMostAmount : ops.RoundsAtMostAmount := fun P hP hc => by
  change (steps P).length ≤ P.amount
  have h1 := length_le_sum_amount (steps P) fun x hx => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact (run_spec hP hc).2.1 r hr
  have h2 := (run_spec hP hc).2.2.1
  omega

/-- **The library's cheapest flow meets its contract.** -/
theorem contract : Contract ops :=
  ⟨⟨sendsAFlow, cheapestForItsAmount, heightsFit, shortOnlyAtACut⟩, fun _ => Iff.rfl,
    stepsAtMostAmount⟩

end AlgoDesign.Flows.MinCostFlow
