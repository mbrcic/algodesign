/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.Walk
public import AlgoDesign.Flows.Assignment.Probe
public import AlgoDesign.Flows.Assignment.Labels

/-!
# Assignment: the steps keep the invariants

Each step places one more person (`step_spec`): its search ends at a free object
(`SearchKeeps.lean`, for the per-pick form, which the library's search agrees with by
`Probe.lean`), and its walk back gives every person a different object, exact with them
(`Walk.lean`). The labels the search moved fit every pair of a person placed, the new one
included; the object labels stay at most 0, and 0 on every free object, since only visited
objects, all held, lose a value, and every object held before is held after. So after every
step the labels prove the people placed so far cheapest (`valid_after`, by adding the labels up,
`Labels.lean`).
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-- **One step places one more person** and keeps the labels fitting and exact. -/
theorem step_spec {st : State} (hst : Placed st) (hk : st.obj.length < st.prob.n) :
    Placed (step st) ∧ (step st).prob = st.prob ∧ (step st).obj.length = st.obj.length + 1 := by
  obtain ⟨s, j, hs, hF⟩ := pickSearch_spec hst hk
  have W := walk_spec hF
  -- the search the library runs ends as the per-pick one (`search_agrees`)
  have hag := search_agrees st hk
  rw [hs] at hag
  have he : step st = ⟨st.prob, (walk st s j).1, s.u, s.v⟩ := by
    cases h : search st with
    | none => rw [h] at hag; exact absurd hag (by simp)
    | some x =>
      rw [h] at hag
      simp only [Option.map_some, Option.some.injEq, key, Prod.mk.injEq] at hag
      obtain ⟨hu, hv, hvia, -, hj⟩ := hag
      simp only [step, h, walk, hu, hv, hvia, hj]
  rw [he]
  refine ⟨⟨W.assign, ?_, fun i hi => W.exact i (W.len ▸ hi), hF.inv.nonpos, ?_⟩, rfl, W.len⟩
  · intro i hi j' hj'
    change i < (walk st s j).1.length at hi
    change s.u.at i + s.v.at j' ≤ st.prob.costAt i j'
    rw [show (walk st s j).1.length = st.obj.length + 1 from W.len] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hF.inv.fit i hi j' hj'
    · exact hF.curFit j' hj'
  · intro j' hj' hno
    exact hF.inv.free j' hj' fun h => hno (W.keep j' h)

/-- The state before the first person: nobody placed, all labels 0. -/
theorem start_placed (P : Problem) : Placed (start P) :=
  ⟨⟨by simp [start], List.nodup_nil⟩, by simp [start], by simp [start],
    fun j hj => le_of_eq (at_build _ hj), fun j hj _ => at_build _ hj⟩

/-- **The state after `k` people**, for `k` up to the number of people: `k` placed, with labels
that fit and are exact. -/
theorem after_spec (P : Problem) :
    ∀ k ≤ P.n, Placed (after P k) ∧ (after P k).prob = P ∧ (after P k).obj.length = k
  | 0, _ => ⟨start_placed P, rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨h1, h2, h3⟩ := after_spec P k (by omega)
    obtain ⟨g1, g2, g3⟩ := step_spec h1 (by rw [h2, h3]; omega)
    exact ⟨g1, g2.trans h2, g3.trans (by rw [h3])⟩

/-- **The invariants hold after every step.** -/
theorem valid_after (P : Problem) : ∀ k ≤ P.n, Valid (after P k) := by
  intro k hk
  obtain ⟨h, -, -⟩ := after_spec P k hk
  exact ⟨⟨h.assign, cheapest_of_labels h.assign h.fit h.exact h.nonpos h.free⟩, h.fit, h.exact⟩

end AlgoDesign.Flows.Assignment
