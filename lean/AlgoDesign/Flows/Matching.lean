/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Matching.Spec
public import AlgoDesign.Flows.Matching.Read

/-! Matching people with objects: the library's max flow on the matching network, the pairs that
carry the unit, and König's cover and Hall's blocked group read from its last search. The contract
is in `Matching/Spec.lean`; the network's arrows and what the last search says in
`Matching/Read.lean`. -/

@[expose] public section

namespace AlgoDesign.Flows.Matching

open AlgoDesign.Flows

/-- The library's max flow on the matching network: its flow and the vertices its last search
reached. -/
def flowAnswer (P : Problem) : Flows.Answer := MaxFlow.ops.maxFlow P.network

/-- **The library's matching**: the answer read from max flow on the matching network. -/
def maxMatching (P : Problem) : Answer :=
  answerOf P (flowAnswer P).flow (flowAnswer P).side

/-- The last search of max flow is the one the answer is read from. -/
theorem side_flowAnswer (P : Problem) :
    (flowAnswer P).side = reached P.network (flowAnswer P).flow := rfl

theorem isFlow_flowAnswer {P : Problem} (hP : P.WellFormed) :
    IsFlow P.network (flowAnswer P).flow :=
  MaxFlow.contract.promise.1 _ (network_wellFormed hP)

theorem sink_not_reached {P : Problem} (hP : P.WellFormed) :
    P.network.sink ∉ reached P.network (flowAnswer P).flow :=
  (MaxFlow.contract.promise.2.1 _ (network_wellFormed hP)).2.1

/-! ## The library's matching meets its contract -/

/-- The library's procedures: max flow on the matching network, the answer read from it. -/
def ops : Ops where
  maxMatching := maxMatching
  rounds P := MaxFlow.ops.rounds P.network
  Valid := Valid
  walks P := congrArg (carried P) (MaxFlow.ops.walks P.network)
  startValid _ hP := MaxFlow.ops.startValid _ (network_wellFormed hP)
  roundsKeep _ hP := MaxFlow.ops.roundsKeep _ (network_wellFormed hP)
  augments _ hP := MaxFlow.ops.augments _ (network_wellFormed hP)

/-- **A maximum matching.** -/
theorem maximumMatching : ops.MaximumMatching := fun P hP => by
  refine ⟨carried_isMatching hP (isFlow_flowAnswer hP), fun M hM => ?_⟩
  have := matching_le_cover hM (isCover_read hP (isFlow_flowAnswer hP))
  have := cover_le_carried hP (isFlow_flowAnswer hP) (sink_not_reached hP)
  change M.length ≤ (carried P (flowAnswer P).flow).length
  omega

/-- **Beside it a cover as large, with every acceptable pair incident to it.** -/
theorem coverAsLarge : ops.CoverAsLarge := fun P hP => by
  have hc := isCover_read hP (isFlow_flowAnswer hP)
  have := matching_le_cover (carried_isMatching hP (isFlow_flowAnswer hP)) hc
  have := cover_le_carried hP (isFlow_flowAnswer hP) (sink_not_reached hP)
  refine ⟨hc, ?_⟩
  change (coverPeopleOf P (reached P.network (flowAnswer P).flow)).length +
    (coverObjectsOf P (reached P.network (flowAnswer P).flow)).length =
      (carried P (flowAnswer P).flow).length
  omega

/-- **If some person stays unmatched, a blocked group.** -/
theorem blockedGroupWhenShort : ops.BlockedGroupWhenShort := fun P hP hlt => by
  change (carried P (flowAnswer P).flow).length < P.people at hlt
  refine ⟨groupOf P (flowAnswer P).side, by simp [ops, maxMatching, answerOf, hlt], ?_⟩
  exact isBlocked_read hP (isFlow_flowAnswer hP) (sink_not_reached hP) hlt

/-- No flow on the matching network carries more than one unit per person. -/
theorem value_le_people {P : Problem} (hP : P.WellFormed) {f : Flow}
    (hf : IsFlow P.network f) : value P.network f ≤ P.people := by
  have hN := network_wellFormed hP
  refine (value_le_cutCapacity hN hf (List.mem_singleton_self _)
    (by rw [network_sink, network_source]; simp)).trans ?_
  have hsub : ∀ i ∈ P.network.ids.filter (fun i => P.network.tail i ∈ [P.network.source] ∧
      P.network.head i ∉ [P.network.source]), i < P.network.g.arrows.length ∧ i < P.people :=
    fun i hi => by
      simp only [List.mem_filter, Network.ids, List.mem_range, List.mem_singleton,
        decide_eq_true_eq] at hi
      exact ⟨hi.1, tail_eq_source hi.1 hi.2.1⟩
  have h1 := sum_le_length (g := P.network.capOf) fun i hi => (capOf_eq (hsub i hi).1).le
  have h2 := (List.Nodup.subperm (nodup_filter_ids _ _) (l₂ := List.range P.people)
    fun i hi => List.mem_range.2 (hsub i hi).2).length_le
  rw [List.length_range] at h2
  unfold cutCapacity
  exact_mod_cast h1.trans h2

/-- **At most one step per person.** -/
theorem stepsAtMostPeople : ops.StepsAtMostPeople := fun P hP => by
  have h1 := MaxFlow.contract.cost.1 _ (network_wellFormed hP)
  have h2 := value_le_people hP (isFlow_flowAnswer hP)
  change (((MaxFlow.ops.rounds P.network).flatten.length : ℕ) : ℤ) ≤ _ at h1
  change (MaxFlow.ops.rounds P.network).flatten.length ≤ P.people
  have : value P.network (MaxFlow.ops.maxFlow P.network).flow ≤ P.people := h2
  omega

/-- **The library's matching meets its contract.** -/
theorem contract : Contract ops :=
  ⟨⟨maximumMatching, coverAsLarge, blockedGroupWhenShort⟩, fun _ => Iff.rfl, stepsAtMostPeople⟩

end AlgoDesign.Flows.Matching
