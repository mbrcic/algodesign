/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Goal
public import Mathlib.Tactic.Linarith

/-!
# Cheapest flow of a given amount: what the walk to the sink leaves behind

Three more facts chapter 6's walk keeps when no arrow costs less than 0, which the heights after a
step rest on (`Ordered`): every settled vertex's known cost is at most every unsettled one's
(`SettledBelow`); along an arrow between two settled vertices the cost does not drop by more than
the arrow's (`SettledTriangle`); and a vertex's previous vertex is settled, and its known cost is
the previous vertex's plus the cost of an arrow between them (`PreviousTight`).

From them, `goal_settled` states what the walk to a goal leaves when it settles the goal: every
settled vertex costs at most the goal, and every arrow out of a settled vertex costs at least the
difference the heights after a step need. `goal_unsettled`: when it does not settle the goal, no
path leads there.
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

open AlgoDesign.Paths AlgoDesign.Paths.Dijkstra AlgoDesign.Paths.Network

variable {N : Network} {s : ℕ}

/-- Every settled vertex's known cost is at most every unsettled vertex's. -/
def SettledBelow (st : State) : Prop :=
  ∀ v ∈ st.settled, ∀ y < st.net.g.n, y ∉ st.settled → ∀ dv ∈ st.known v, ∀ dy ∈ st.known y,
    dv ≤ dy

/-- Along an arrow between two settled vertices, the known cost grows by at most the arrow's. -/
def SettledTriangle (st : State) : Prop :=
  ∀ u ∈ st.settled, ∀ v ∈ st.settled, ∀ i, st.net.g.arrows[i]? = some (u, v) →
    ∀ du ∈ st.known u, ∀ dv ∈ st.known v, dv ≤ du + st.net.arrowCost i

/-- A vertex's previous vertex is settled, and the vertex's known cost is the previous vertex's
plus the cost of an arrow between them. -/
def PreviousTight (st : State) : Prop :=
  ∀ w u, st.prev w = some u → u ∈ st.settled ∧ ∃ du dw i, st.known u = some du ∧
    st.known w = some dw ∧ st.net.g.arrows[i]? = some (u, w) ∧ dw = du + st.net.arrowCost i

/-- The three facts together. -/
def Ordered (st : State) : Prop := SettledBelow st ∧ SettledTriangle st ∧ PreviousTight st

theorem arrowCost_nonneg (hnn : N.NoArrowBelowZero) (i : ℕ) : 0 ≤ N.arrowCost i := by
  have := pathCost_nonneg hnn [i]
  simpa [pathCost] using this

theorem ordered_start : Ordered (start N s) := by
  refine ⟨fun v hv => by simp [start] at hv, fun u hu => by simp [start] at hu, fun w u h => ?_⟩
  simp [start] at h

theorem ordered_step (hnn : N.NoArrowBelowZero) {st : State} (hn : st.net = N) (hS : Steady st)
    (h : Ordered st) (hne : st.queue ≠ []) : Ordered (step N st) := by
  subst hn
  obtain ⟨⟨k, u⟩, q, hq⟩ := List.exists_cons_of_ne_nil hne
  by_cases hu : u ∈ st.settled
  · rw [step_skip hq hu]; exact h
  rw [step_settle hq hu]
  obtain ⟨h1, h2, h3⟩ := h
  have hR := hS.2.2.1
  obtain ⟨hun, hku, hlow⟩ := front_spec hS.2.2.2.1 hq hu
  have R := relaxes_foldl st.net u k (st.net.g.out u)
    { st with settled := st.settled ++ [u], queue := q } fun e he => (mem_out.1 he).1
  set st' := (st.net.g.out u).foldl (tryArrow st.net u k)
    { st with settled := st.settled ++ [u], queue := q }
  have hset : st'.settled = st.settled ++ [u] := R.settled
  have hnet : st'.net = st.net := R.net
  have KP : ∀ x ∈ st.settled ++ [u], st'.known x = st.known x ∧ st'.prev x = st.prev x := by
    intro x hx
    rcases R.known_prev x with h | ⟨hx', -⟩
    · exact h
    · exact absurd hx hx'
  have hc := arrowCost_nonneg (N := st.net) hnn
  refine ⟨?_, ?_, ?_⟩
  · intro v hv y hy hyS dv hdv dy hdy
    rw [hset] at hv hyS
    rw [hnet] at hy
    rw [(KP v hv).1] at hdv
    have hyu : y ∉ st.settled := fun h => hyS (List.mem_append_left _ h)
    -- every known cost after the step is at least `k`, and `v` costs at most `k`
    have hv_le : dv ≤ k := by
      rcases List.mem_append.1 hv with hv | hv
      · exact h1 v hv u hun hu dv hdv k hku
      · rw [List.mem_singleton.1 hv, hku] at hdv
        exact le_of_eq (Option.some.inj hdv).symm
    rcases R.known_prev y with ⟨hk, -⟩ | ⟨-, -, e, he, -, hk⟩
    · rw [hk] at hdy
      rcases List.mem_append.1 hv with hv | hv
      · exact h1 v hv y hy hyu dv hdv dy hdy
      · exact hv_le.trans (hlow y hy hyu dy hdy)
    · rw [hk] at hdy
      have := hc e.2
      have hd : dy = k + st.net.arrowCost e.2 := (Option.some.inj hdy).symm
      linarith
  · intro a ha b hb i hi da hda db hdb
    rw [hset] at ha hb
    rw [hnet] at hi ⊢
    rw [(KP a ha).1] at hda
    rw [(KP b hb).1] at hdb
    have hci := hc i
    rcases List.mem_append.1 ha with ha | ha <;> rcases List.mem_append.1 hb with hb | hb
    · exact h2 a ha b hb i hi da hda db hdb
    · -- `b` is `u`: the arrow out of `a` was tried when `a` was settled
      rw [List.mem_singleton.1 hb] at hi hdb
      have hlt : u < st.net.g.n := hun
      have := hR a ha (u, i) (mem_out.2 ⟨hlt, hi⟩) hu da hda
      rw [hku] at this hdb
      simp only [AtMost] at this
      rw [← Option.some.inj hdb]; exact this
    · rw [List.mem_singleton.1 ha] at hda
      rw [hku] at hda
      have := h1 b hb u hun hu db hdb k hku
      have hk' : da = k := (Option.some.inj hda).symm
      linarith
    · obtain rfl := List.mem_singleton.1 ha
      obtain rfl := List.mem_singleton.1 hb
      rw [hku] at hda hdb
      rw [← Option.some.inj hda, ← Option.some.inj hdb]
      linarith
  · intro w v hw
    rw [hset, hnet]
    rcases R.known_prev w with ⟨hk, hp⟩ | ⟨-, hp, e, he, hew, hk⟩
    · rw [hp] at hw
      obtain ⟨hv, dv, dw, i, h1', h2', h3', h4'⟩ := h3 w v hw
      refine ⟨List.mem_append_left _ hv, dv, dw, i, ?_, by rw [hk]; exact h2', h3', h4'⟩
      rw [(KP v (List.mem_append_left _ hv)).1]; exact h1'
    · rw [hp] at hw
      obtain rfl := Option.some.inj hw
      have hm := (mem_out.1 he).2
      rw [hew] at hm
      exact ⟨by simp, k, _, e.2, by rw [(KP u (by simp)).1]; exact hku, hk, hm, rfl⟩

theorem ordered_runSteps (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) (f : ℕ) :
    Ordered (runSteps (step N) f (start N s)) :=
  (runSteps_induct (fun st => st.net = N ∧ Steady st ∧ Ordered st) _
    (fun _ h hq => ⟨(step_net _ _).trans h.1, steady_step h.1 h.2.1 hq,
      ordered_step hnn h.1 h.2.1 h.2.2 hq⟩) _ _ ⟨rfl, steady_start hs, ordered_start⟩).2.2

/-- **Either the walk to `t` never settles `t` and is the whole walk, or it stopped where the
whole walk settles `t`.** -/
theorem runTo_cases_settled (N : Network) (t : ℕ) : ∀ f st, t ∉ st.settled →
    (runTo N t f st = runSteps (step N) f st ∧ t ∉ (runSteps (step N) f st).settled) ∨
      ∃ k < f, ∃ key q, (runSteps (step N) k st).queue = (key, t) :: q ∧
        t ∉ (runSteps (step N) k st).settled ∧
        runTo N t f st = { runSteps (step N) k st with
          settled := (runSteps (step N) k st).settled ++ [t], queue := q }
  | 0, _, ht => Or.inl ⟨rfl, ht⟩
  | f + 1, st, ht => by
    unfold runTo
    split
    · rename_i hq
      rw [runSteps_of_queue_nil hq]
      exact Or.inl ⟨rfl, ht⟩
    · rename_i key u q hq
      have hne : st.queue ≠ [] := by simp [hq]
      split_ifs with hu
      · obtain ⟨rfl, hu⟩ := hu
        exact Or.inr ⟨0, by omega, key, q, hq, hu, rfl⟩
      · have ht' : t ∉ (step N st).settled := by
          by_cases hus : u ∈ st.settled
          · rw [step_skip hq hus]; exact ht
          · rw [(step_settle_known (N := N) hq hus).2]
            simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨ht, fun e => hu ⟨e.symm, e ▸ hus⟩⟩
        rw [runSteps_succ_of_ne hne]
        rcases runTo_cases_settled N t f (step N st) ht' with h | ⟨k, hk, key', q', h1, h2, h3⟩
        · exact Or.inl h
        · refine Or.inr ⟨k + 1, by omega, key', q', ?_, ?_, ?_⟩ <;>
            rw [runSteps_succ_of_ne hne] <;> assumption

/-- **When the walk to `t` does not settle `t`, no path leads from `s` to `t`.** -/
theorem goal_unsettled (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) {t : ℕ}
    (ht : t ∉ (finalTo N s t).settled) : ¬ N.g.Reaches s t := by
  intro hr
  rcases runTo_cases_settled N t (N.g.arrows.length + 1) (start N s) (by simp [start]) with
    ⟨h, -⟩ | ⟨k, -, key, q, -, -, h⟩
  · apply ht
    simp only [finalTo, h]
    exact mem_settled_of_reaches hN hs (final_net N s).1 (final_net N s).2
      (final_valid hN hnn hs) (final_queue N s) hr
  · apply ht
    simp only [finalTo, h]
    simp

/-- **What the walk to `t` leaves when it settles `t`**, at cost `dt`: every settled vertex costs at
most `dt`; along an arrow out of a settled vertex, a settled head costs at most the tail plus the
arrow, an unsettled head means `dt` is at most the tail plus the arrow; and the previous vertices
are tight. -/
theorem goal_settled (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) {t : ℕ}
    (ht : t ∈ (finalTo N s t).settled) :
    ∃ dt, (finalTo N s t).known t = some dt ∧
      (∀ v ∈ (finalTo N s t).settled, ∃ dv, (finalTo N s t).known v = some dv ∧ dv ≤ dt) ∧
      (∀ u ∈ (finalTo N s t).settled, ∀ v i, N.g.arrows[i]? = some (u, v) →
        ∀ du ∈ (finalTo N s t).known u,
          (∀ dv ∈ (finalTo N s t).known v, v ∈ (finalTo N s t).settled →
            dv ≤ du + N.arrowCost i) ∧
          (v ∉ (finalTo N s t).settled → dt ≤ du + N.arrowCost i)) ∧
      PreviousTight (finalTo N s t) ∧ (finalTo N s t).net = N := by
  rcases runTo_cases_settled N t (N.g.arrows.length + 1) (start N s) (by simp [start]) with
    ⟨h, hn⟩ | ⟨k, -, key, q, hq, htX, h⟩
  · exact absurd (by simpa [finalTo, h] using ht) hn
  set X := runSteps (step N) k (start N s) with hX
  have hXn : X.net = N := (net_runSteps N k _).1
  have hS : Steady X := steady_runSteps hs k
  have hV := (valid_runSteps hN hnn hs k).1
  obtain ⟨o1, o2, o3⟩ := ordered_runSteps hnn hs k (N := N)
  rw [← hX] at o1 o2 o3
  obtain ⟨htn, hkt, hlow⟩ := front_spec hS.2.2.2.1 hq htX
  rw [hXn] at htn hlow
  have hc := arrowCost_nonneg hnn
  have hF : finalTo N s t = { X with settled := X.settled ++ [t], queue := q } := h
  rw [hF]
  simp only
  refine ⟨key, hkt, ?_, ?_, ?_, hXn⟩
  · intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · obtain ⟨dv, hdv⟩ := Option.ne_none_iff_exists'.1 (hV.1.2 v hv).1
      exact ⟨dv, hdv, o1 v hv t (hXn ▸ htn) htX dv hdv key hkt⟩
    · rw [List.mem_singleton.1 hv]; exact ⟨key, hkt, le_rfl⟩
  · intro u hu v i hi du hdu
    have hvn : v < N.g.n := (hN.1 _ (List.mem_of_getElem? hi)).2
    have hci := hc i
    rcases List.mem_append.1 hu with hu | hu
    · refine ⟨fun dv hdv hv => ?_, fun hv => ?_⟩
      · rcases List.mem_append.1 hv with hv | hv
        · exact o2 u hu v hv i (hXn ▸ hi) du hdu dv hdv |>.trans_eq (by rw [hXn])
        · rw [List.mem_singleton.1 hv] at hdv hi hvn
          have := hS.2.2.1 u hu (t, i) (hXn ▸ mem_out.2 ⟨hvn, hi⟩) htX du hdu
          rw [hkt] at this hdv
          simp only [AtMost] at this
          rw [← Option.some.inj hdv]; simpa [hXn] using this
      · have hvX : v ∉ X.settled := fun h => hv (List.mem_append_left _ h)
        have := hS.2.2.1 u hu (v, i) (hXn ▸ mem_out.2 ⟨hvn, hi⟩) hvX du hdu
        obtain ⟨dv, hdv, hle⟩ := atMost_iff.1 this
        have := hlow v hvn hvX dv hdv
        rw [hXn] at hle
        exact this.trans hle
    · rw [List.mem_singleton.1 hu] at hdu
      rw [hkt] at hdu
      have hk' : du = key := (Option.some.inj hdu).symm
      refine ⟨fun dv hdv hv => ?_, fun _ => by linarith⟩
      rcases List.mem_append.1 hv with hv | hv
      · have := o1 v hv t (hXn ▸ htn) htX dv hdv key hkt
        linarith
      · rw [List.mem_singleton.1 hv, hkt] at hdv
        have : dv = key := (Option.some.inj hdv).symm
        linarith
  · intro w u hw
    obtain ⟨hu, rest⟩ := o3 w u hw
    exact ⟨List.mem_append_left _ hu, rest⟩

end AlgoDesign.Flows.MinCostFlow
