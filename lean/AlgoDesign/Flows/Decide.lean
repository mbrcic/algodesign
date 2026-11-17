/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Spec
public import AlgoDesign.Flows.Matching.Spec

/-! Deciding the Flows contracts' checks on a given network: a well-formed network, a flow, and
heights that fit, so tests can judge an answer with `decide`. -/

@[expose] public section

namespace AlgoDesign.Flows

instance (N : Network) : Decidable N.WellFormed := by
  unfold Network.WellFormed; infer_instance

instance (N : Network) (f : Flow) : Decidable (IsFlow N f) := by
  unfold IsFlow WithinCapacity Conserved WellFormed; infer_instance

instance (st : State) : Decidable (WithinCapacity st) := by
  unfold WithinCapacity; infer_instance

instance (st : State) : Decidable (Conserved st) := by
  unfold Conserved; infer_instance

instance (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

instance (st : State) : Decidable (Valid st) := by
  unfold Valid; infer_instance

namespace MinCostFlow

/-- `HeightsFitEverywhere`, arrow by arrow: along and back each arrow of the network. -/
def heightsFitB (P : Problem) (f : Flow) (h : Heights) : Bool :=
  (List.range P.net.g.arrows.length).all fun i =>
    [ResidualArrow.along i, ResidualArrow.back i].all fun a =>
      !decide (0 < a.residualCapacity P.net f) || decide (0 ≤ changedCost P h a)

/-- `heightsFitB` decides `HeightsFitEverywhere`. -/
theorem heightsFit_iff (P : Problem) (f : Flow) (h : Heights) :
    HeightsFitEverywhere ⟨P, f, h⟩ ↔ heightsFitB P f h = true := by
  unfold HeightsFitEverywhere heightsFitB
  simp only [List.all_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt,
    decide_eq_true_eq, forall_eq_or_imp, forall_eq]
  constructor
  · intro H i hi
    exact ⟨(Nat.eq_zero_or_pos _).elim (fun h0 => Or.inl h0.le) fun hr => Or.inr (H _ hi hr),
      (Nat.eq_zero_or_pos _).elim (fun h0 => Or.inl h0.le) fun hr => Or.inr (H _ hi hr)⟩
  · intro H a ha hr
    cases a with
    | along i => exact ((H i ha).1.resolve_left (by omega))
    | back i => exact ((H i ha).2.resolve_left (by omega))

instance (P : Problem) (f : Flow) (h : Heights) : Decidable (HeightsFitEverywhere ⟨P, f, h⟩) :=
  decidable_of_iff' _ (heightsFit_iff P f h)

instance (st : State) : Decidable (HeightsFitEverywhere st) :=
  decidable_of_iff' _ (heightsFit_iff st.prob st.flow st.heights)

instance (st : State) : Decidable (FlowRespected st) := by
  unfold FlowRespected; infer_instance


/-- Every list as long as `caps` whose entry at each place is at most the one of `caps` there:
the candidate flows of a network, with `caps` its capacities by arrow id. -/
def boundedFlows : List ℕ → List Flow
  | [] => [[]]
  | c :: cs => (List.range (c + 1)).flatMap fun x => (boundedFlows cs).map (x :: ·)

/-- A list is in `boundedFlows caps` when it is as long as `caps` and below it place by place. -/
theorem mem_boundedFlows {caps : List ℕ} {g : Flow} :
    g ∈ boundedFlows caps ↔ List.Forall₂ (· ≤ ·) g caps := by
  induction caps generalizing g with
  | nil => cases g <;> simp [boundedFlows]
  | cons c cs ih =>
    cases g with
    | nil => simp [boundedFlows]
    | cons x g => simp [boundedFlows, ih, Nat.lt_succ_iff]

/-- Every flow of a network is among the candidates under its capacities. -/
theorem mem_boundedFlows_of_isFlow {N : Network} {g : Flow} (hg : IsFlow N g) :
    g ∈ boundedFlows (N.ids.map N.capOf) := by
  obtain ⟨hc, -, hw⟩ := hg
  change g.length = N.g.arrows.length at hw
  rw [mem_boundedFlows, List.forall₂_iff_get]
  refine ⟨by simp [Network.ids, hw], fun i h1 h2 => ?_⟩
  have := hc i (hw ▸ h1)
  simpa [Network.ids, Flow.on, List.getElem?_eq_getElem h1] using this

/-- `CheapestForAmount`, over the candidate flows: every one that is a flow of the same amount
costs at least as much as the current flow. -/
def cheapestB (st : State) : Bool :=
  (boundedFlows (st.prob.net.ids.map st.prob.net.capOf)).all fun g =>
    !decide (IsFlow st.prob.net g) ||
      !decide (value st.prob.net g = value st.prob.net st.flow) ||
      decide (st.prob.flowCost st.flow ≤ st.prob.flowCost g)

/-- `cheapestB` decides `CheapestForAmount`. -/
theorem cheapest_iff (st : State) : CheapestForAmount st ↔ cheapestB st = true := by
  unfold CheapestForAmount cheapestB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · intro H g _
    by_cases hf : IsFlow st.prob.net g
    · by_cases hv : value st.prob.net g = value st.prob.net st.flow
      · exact Or.inr (H g hf hv)
      · exact Or.inl (Or.inr hv)
    · exact Or.inl (Or.inl hf)
  · intro H g hf hv
    exact (H g (mem_boundedFlows_of_isFlow hf)).resolve_left (by simp [hf, hv])

instance (st : State) : Decidable (CheapestForAmount st) :=
  decidable_of_iff' _ (cheapest_iff st)

instance (st : State) : Decidable (Valid st) := by
  unfold Valid; infer_instance

instance (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

end MinCostFlow

namespace MatchingDecide

open Matching

instance (P : Problem) : Decidable P.WellFormed := by
  unfold Problem.WellFormed; infer_instance

instance (P : Problem) (M : List (ℕ × ℕ)) : Decidable (IsMatching P M) := by
  unfold IsMatching; infer_instance

instance (P : Problem) (cp co : List ℕ) : Decidable (IsCover P cp co) := by
  unfold IsCover; infer_instance

/-- `IsBlocked`, its objects' clause read over the lists both ways: every object listed is
accepted by someone of the group, and every pair of someone of the group has its object listed. -/
def isBlockedB (P : Problem) (g : Group) : Bool :=
  decide g.people.Nodup && g.people.all (· < P.people) && decide g.objects.Nodup &&
    g.objects.all (fun o => g.people.any fun p => (p, o) ∈ P.pairs) &&
    P.pairs.all (fun e => !decide (e.1 ∈ g.people) || decide (e.2 ∈ g.objects)) &&
    decide (g.objects.length < g.people.length)

/-- `isBlockedB` decides `IsBlocked`. -/
theorem isBlockedB_iff (P : Problem) (g : Group) : IsBlocked P g ↔ isBlockedB P g = true := by
  unfold IsBlocked isBlockedB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, fun o ho => (h4 o).1 ho⟩, fun e he => ?_⟩, h5⟩
    by_cases hp : e.1 ∈ g.people
    · exact Or.inr ((h4 e.2).2 ⟨e.1, hp, he⟩)
    · exact Or.inl hp
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    refine ⟨h1, h2, h3, fun o => ⟨h4 o, ?_⟩, h6⟩
    rintro ⟨p, hp, hpo⟩
    exact (h5 _ hpo).resolve_left (by simpa using hp)

instance (P : Problem) (g : Group) : Decidable (IsBlocked P g) :=
  decidable_of_iff' _ (isBlockedB_iff P g)

instance (st : Matching.State) : Decidable (FlowRespected st) := by
  unfold FlowRespected; infer_instance

instance (st : Matching.State) : Decidable (Matching.Valid st) := by
  unfold Matching.Valid; infer_instance

end MatchingDecide

end AlgoDesign.Flows
