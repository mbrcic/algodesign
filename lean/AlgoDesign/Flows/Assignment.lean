/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.Spec
public import AlgoDesign.Flows.Assignment.Steps
public import AlgoDesign.Flows.Assignment.Labels
public import AlgoDesign.Flows.Assignment.SearchKeeps
public import AlgoDesign.Flows.Assignment.Walk
public import AlgoDesign.Flows.Assignment.Run

/-! Assignment: the cheapest path rule, one person at a time, with labels on both sides. The
contract is in `Assignment/Spec.lean`; the steps in `Assignment/Steps.lean`; why labels that fit
and are exact prove a choice cheapest in `Assignment/Labels.lean` and `least_of_labels` below;
what one person's search keeps in `Assignment/SearchKeeps.lean`, and why the library's search,
labels moved once, ends as that per-pick search in `Assignment/Probe.lean`; the walk back in
`Assignment/Walk.lean`; and the steps together in `Assignment/Run.lean`.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-- **Adding the labels up**: labels that fit every pair and are exact on an assignment's pairs
make it least-cost. Summed over the people, the assignment costs exactly the labels of all people
and all objects; any other assignment costs at least that. -/
theorem least_of_labels {P : Problem} {obj : List ℕ} {u v : Labels}
    (hobj : IsAssignmentOf P obj) (hlen : obj.length = P.n)
    (hfit : ∀ i < P.n, ∀ j < P.n, u.at i + v.at j ≤ P.costAt i j)
    (hexact : ∀ i < P.n, u.at i + v.at (obj.getD i 0) = P.costAt i (obj.getD i 0)) :
    ∀ σ, σ.length = P.n → IsAssignmentOf P σ →
      assignmentCost P obj ≤ assignmentCost P σ := by
  intro σ hσ hσa
  refine cheapest_of_sums hobj hσa (hσ.trans hlen.symm) (by rw [hlen]; exact hfit)
    (by rw [hlen]; exact hexact) ?_
  rw [toFinset_eq_range hobj hlen, toFinset_eq_range hσa hσ]

/-! ## What the library's procedures owe -/

/-- The state after the last person: everybody placed, with labels that fit and are exact. -/
theorem answer_placed (P : Problem) :
    Placed (after P P.n) ∧ (after P P.n).prob = P ∧ (after P P.n).obj.length = P.n :=
  after_spec P P.n le_rfl

/-- The library's procedures: the steps of `Assignment/Steps.lean`. -/
def ops : Ops where
  assign := assign
  after := after
  Valid := Valid
  walks _ := ⟨rfl, rfl, rfl⟩
  adds P _ k hk := ⟨(after_spec P k hk).2.1, (after_spec P k hk).2.2⟩
  startValid P _ := valid_after P 0 (Nat.zero_le _)
  stepsKeep P _ := valid_after P

/-- **A least-cost assignment.** -/
theorem leastCost : ops.LeastCost := fun P _ => by
  obtain ⟨h, hp, hl⟩ := answer_placed P
  have ha := h.assign
  have hf := h.fit
  have he := h.exact
  rw [hp] at ha hf he
  refine ⟨ha, hl, least_of_labels (u := (after P P.n).personLabel)
    (v := (after P P.n).objectLabel) ha hl ?_ ?_⟩
  · intro i hi j hj; exact hf i (by rw [hl]; exact hi) j hj
  · intro i hi; exact he i (by rw [hl]; exact hi)

/-- **On every pair the two labels add up to at most the pair's cost.** -/
theorem labelsFit : ops.LabelsFit := fun P _ i hi j hj => by
  obtain ⟨h, hp, hl⟩ := answer_placed P
  have hf := h.fit
  rw [hp] at hf
  exact hf i (by rw [hl]; exact hi) j hj

/-- **On every chosen pair exactly to it.** -/
theorem exactOnChosen : ops.ExactOnChosen := fun P _ i hi => by
  obtain ⟨h, hp, hl⟩ := answer_placed P
  have he := h.exact
  rw [hp] at he
  exact he i (by rw [hl]; exact hi)

/-- **Read as prices, every person's object is their favorite after price.** -/
theorem favoriteAfterPrice : ops.FavoriteAfterPrice := fun P hP i hi j hj => by
  have h1 := labelsFit P hP i hi j hj
  have h2 := exactOnChosen P hP i hi
  change _ - _ ≤ _ - _
  linarith

/-- **One best-first search per person.** -/
theorem oneSearchPerPerson : ops.OneSearchPerPerson := fun P _ k hk => by
  change (after P (k + 1)).obj.length = (after P k).obj.length + 1
  rw [(after_spec P (k + 1) hk).2.2, (after_spec P k hk.le).2.2]

/-- **The library's assignment meets its contract.** -/
theorem contract : Contract ops :=
  ⟨⟨leastCost, labelsFit, exactOnChosen, favoriteAfterPrice⟩, fun _ => Iff.rfl,
    oneSearchPerPerson⟩

end AlgoDesign.Flows.Assignment
