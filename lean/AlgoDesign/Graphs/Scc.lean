/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Spec
public import AlgoDesign.Graphs.Scc.Decide
public import AlgoDesign.Graphs.Scc.Basic
public import AlgoDesign.Graphs.Scc.Reach
public import AlgoDesign.Graphs.Scc.Check
public import AlgoDesign.Graphs.Scc.AlgorithmT
public import AlgoDesign.Graphs.Scc.Kosaraju
public import AlgoDesign.Graphs.Scc.Condensation
public import AlgoDesign.Graphs.Scc.Correct

/-! Strong components, the condensation and the checker. The contract is in `Scc/Spec.lean`; this
file imports the whole of it. -/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

/-! ## The library meets its contract

`Contract` in `Scc/Spec.lean` is the part of the contract that Lean checks. Algorithm T meets its
promise by proof (`algorithmTPromise`, `Scc/Correct.lean`), and the condensation meets
`Ops.condenses`. -/

/-- The library's procedures, as the box names them: Algorithm T's walk and its answer, and the
condensation. -/
def ops : Ops where
  start := AlgorithmT.start
  step := AlgorithmT.step
  components := algorithmT
  condensation := condensation
  Valid := Valid
  walks g := by
    change AlgorithmT.read g (AlgorithmT.run g (AlgorithmT.steps g) (AlgorithmT.start g)) = _
    rw [AlgorithmT.run_eq_iterate]; rfl
  carries _ := rfl
  keepsGraph := AlgorithmT.step_g
  stepKeeps g hg k := by
    rw [← AlgorithmT.run_eq_iterate]
    exact validAlong g hg k
  lists g hg := by
    obtain ⟨-, -, ⟨hlen, hmem, hall⟩, -⟩ := algorithmTPromise g hg
    refine ⟨hlen, fun i hi => ⟨(hmem i hi).1, fun v => ⟨(hmem i hi).2 v, ?_⟩⟩⟩
    rintro ⟨hv, he⟩
    have := hall v hv
    rwa [he, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
  condenses g hg := by
    obtain ⟨hs, hi, hm, -⟩ := algorithmTPromise _ hg
    exact ⟨hi, condensation_spec hg hs.1.1 hm⟩

/-- **The library meets its contract.** -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hg => (algorithmTPromise _ hg).1,
      fun _ hg _ hu _ hv => reaches_iff_quotient hg (algorithmTPromise _ hg).1 hu hv,
      fun _ hg => quotientAcyclic_of_isScc hg (algorithmTPromise _ hg).1⟩
  invariants _ := Iff.rfl
  cost g hg := by
    change Over g ((AlgorithmT.step g)^[AlgorithmT.steps g] (AlgorithmT.start g))
    rw [← AlgorithmT.run_eq_iterate]
    exact (AlgorithmT.ends_final hg).over

end AlgoDesign.Graphs.Scc
