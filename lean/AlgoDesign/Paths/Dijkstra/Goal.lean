/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Walk

/-!
# Cheapest paths: the walk to one goal

Source: Hart, Nilsson and Raphael, "A Formal Basis for the Heuristic Determination of Minimum Cost
Paths", IEEE Trans. SSC 4 (1968), p. 102: the search ends when the goal is the vertex chosen.

The walk to a goal is the walk of `dijkstra`, stopped the moment the goal comes off the queue and
is settled, before the arrows out of it are tried. Its last state is not one a `step` gives (the
goal's row is untried), so what it promises is stated of its answer: the goal's cost is its
cheapest, every recorded previous vertex leads back along a path of exactly the known cost, a goal
that cannot be reached is reported as unreachable, and the vertices it settles are the first ones
the whole walk settles, in the same order.
-/

@[expose] public section

namespace AlgoDesign.Paths.Dijkstra

open Network

variable {N : Network} {s : ℕ}

/-! ## The walk -/

/-- Take steps while the queue is not empty, at most `f` of them, but stop as soon as the goal `t`
comes off the queue unsettled: settle it, and try none of its arrows. -/
def runTo (N : Network) (t : ℕ) : ℕ → State → State
  | 0, st => st
  | f + 1, st =>
    match st.queue with
    | [] => st
    | (_, u) :: q =>
      if u = t ∧ u ∉ st.settled then { st with settled := st.settled ++ [u], queue := q }
      else runTo N t f (step N st)

/-- The state the walk to `t` ends in. -/
abbrev finalTo (N : Network) (s t : ℕ) : State :=
  runTo N t (N.g.arrows.length + 1) (start N s)

/-- **The walk to one goal**: each settled vertex's cost, and the costs found so far; the previous
vertices. -/
def dijkstraTo (N : Network) (s t : ℕ) : Answer := answer (finalTo N s t)

/-! ## The walk to a goal is the whole walk, stopped -/

theorem runSteps_of_queue_nil {step : State → State} {st : State} (h : st.queue = []) :
    ∀ f, runSteps step f st = st
  | 0 => rfl
  | _ + 1 => by simp [runSteps, h]

theorem runSteps_succ_of_ne {step : State → State} {st : State} (h : st.queue ≠ []) (f : ℕ) :
    runSteps step (f + 1) st = runSteps step f (step st) := by
  simp [runSteps, h]

theorem runSteps_add (step : State → State) :
    ∀ a b st, runSteps step (a + b) st = runSteps step b (runSteps step a st)
  | 0, _, _ => by simp [runSteps]
  | a + 1, b, st => by
    by_cases h : st.queue = []
    · rw [runSteps_of_queue_nil h, runSteps_of_queue_nil h, runSteps_of_queue_nil h]
    · rw [show a + 1 + b = (a + b) + 1 by omega, runSteps_succ_of_ne h, runSteps_succ_of_ne h,
        runSteps_add step a b]

/-- **Either the walk to `t` never met `t`, or it stopped where the whole walk settles `t`**: after
`k` steps of the whole walk, with `t` unsettled at the front of the queue. -/
theorem runTo_cases (N : Network) (t : ℕ) : ∀ f st,
    runTo N t f st = runSteps (step N) f st ∨
      ∃ k < f, ∃ key q, (runSteps (step N) k st).queue = (key, t) :: q ∧
        t ∉ (runSteps (step N) k st).settled ∧
        runTo N t f st = { runSteps (step N) k st with
          settled := (runSteps (step N) k st).settled ++ [t], queue := q }
  | 0, _ => Or.inl rfl
  | f + 1, st => by
    unfold runTo
    split
    · rename_i hq
      exact Or.inl (runSteps_of_queue_nil hq _).symm
    · rename_i key u q hq
      have hne : st.queue ≠ [] := by simp [hq]
      split_ifs with hu
      · obtain ⟨rfl, hu⟩ := hu
        exact Or.inr ⟨0, by omega, key, q, hq, hu, rfl⟩
      · rw [runSteps_succ_of_ne hne]
        rcases runTo_cases N t f (step N st) with h | ⟨k, hk, key', q', h1, h2, h3⟩
        · exact Or.inl h
        · refine Or.inr ⟨k + 1, by omega, key', q', ?_, ?_, ?_⟩ <;>
            rw [runSteps_succ_of_ne hne] <;> assumption

/-! ## What the walk to a goal promises -/

theorem steady_runSteps (hs : s < N.g.n) (f : ℕ) : Steady (runSteps (step N) f (start N s)) :=
  (runSteps_induct (fun st => st.net = N ∧ Steady st) _
    (fun _ h hq => ⟨(step_net _ _).trans h.1, steady_step h.1 h.2 hq⟩) _ _
    ⟨rfl, steady_start hs⟩).2

theorem valid_runSteps (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) (f : ℕ) :
    Valid (runSteps (step N) f (start N s)) ∧ WellFormed (runSteps (step N) f (start N s)) :=
  (runSteps_induct (fun st => (st.net = N ∧ st.source = s) ∧ Valid st ∧ WellFormed st) _
    (fun _ h hq => ⟨⟨(step_net _ _).trans h.1.1, (step_source _ _).trans h.1.2⟩,
      valid_step hN hnn hs h.1.1 h.1.2 h.2 hq⟩) _ _ ⟨⟨rfl, rfl⟩, valid_start hs⟩).2

/-- Settling the front vertex keeps its known cost, and settles it after the vertices settled
before. -/
theorem step_settle_known {st : State} {k : ℤ} {u : ℕ} {q : List (ℤ × ℕ)}
    (hq : st.queue = (k, u) :: q) (hu : u ∉ st.settled) :
    (step N st).known u = st.known u ∧ (step N st).settled = st.settled ++ [u] := by
  rw [step_settle hq hu]
  have R := relaxes_foldl N u k (N.g.out u) { st with settled := st.settled ++ [u], queue := q }
    fun e he => (mem_out.1 he).1
  refine ⟨?_, R.settled⟩
  rcases R.known_prev u with h | ⟨hx, -⟩
  · exact h.1
  · exact absurd (List.mem_append_right _ (List.mem_singleton_self u)) hx

/-- The walk to `t` ends with the steady pieces of a state of the whole walk: the same known
costs and previous vertices. -/
theorem finalTo_steady (hs : s < N.g.n) (t : ℕ) :
    ∃ X, (X.net = N ∧ X.source = s ∧ Steady X) ∧ (finalTo N s t).known = X.known ∧
      (finalTo N s t).prev = X.prev := by
  rcases runTo_cases N t (N.g.arrows.length + 1) (start N s) with h | ⟨k, _, _, _, _, _, h⟩
  · exact ⟨_, ⟨(final_net N s).1, (final_net N s).2, final_steady hs⟩, by simp only [finalTo, h],
      by simp only [finalTo, h]⟩
  · exact ⟨_, ⟨(net_runSteps N k _).1, (net_runSteps N k _).2, steady_runSteps hs k⟩,
      by simp only [finalTo, h], by simp only [finalTo, h]⟩

/-- **The goal gets the cost of its cheapest path**, when it can be reached and no arrow is
negative. -/
theorem dijkstraTo_goal (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) {t : ℕ}
    (ht : N.g.Reaches s t) :
    ∃ d, (dijkstraTo N s t).cost t = some d ∧ N.Cheapest s t (some d) := by
  rcases runTo_cases N t (N.g.arrows.length + 1) (start N s) with h | ⟨k, -, key, q, hq, hu, h⟩
  · have := reached_of_valid hN hs (final_net N s).1 (final_net N s).2 (final_valid hN hnn hs)
      (final_queue N s) ht
    simpa [dijkstraTo, finalTo, answer, h] using this
  · set X := runSteps (step N) k (start N s)
    have hV := valid_step hN hnn hs (net_runSteps N k _).1 (net_runSteps N k _).2
      (valid_runSteps hN hnn hs k) (by simp [X, hq])
    obtain ⟨hk, hS⟩ := step_settle_known (N := N) hq hu
    obtain ⟨hne, hc⟩ := hV.1.1.2 t (by rw [hS]; simp)
    rw [step_net, step_source, (net_runSteps N k _).1, (net_runSteps N k _).2] at hc
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hne
    refine ⟨d, ?_, hd ▸ hc⟩
    simp only [dijkstraTo, finalTo, answer, h]
    rw [← hk]; exact hd

/-- **Following each recorded previous vertex back to the start gives a path of exactly the known
cost**, whatever the arrows cost. -/
theorem dijkstraTo_previous (hs : s < N.g.n) (t : ℕ) {v : ℕ} (hv : v < N.g.n) :
    ∀ d ∈ (dijkstraTo N s t).cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
      LeadsBack (dijkstraTo N s t).prev s (N.visits s p) := by
  obtain ⟨X, ⟨hn, hsrc, hX⟩, hk, hp⟩ := finalTo_steady hs t
  simp only [dijkstraTo, answer, hk, hp]
  exact previous_of_steady hn hsrc hX hv

/-- **A vertex that cannot be reached is reported as unreachable**, whatever the arrows cost. -/
theorem dijkstraTo_unreached (hs : s < N.g.n) (t : ℕ) {v : ℕ} (hv : v < N.g.n)
    (hr : ¬ N.g.Reaches s v) : (dijkstraTo N s t).cost v = none := by
  obtain ⟨X, ⟨hn, hsrc, hX⟩, hk, -⟩ := finalTo_steady hs t
  simp only [dijkstraTo, answer, hk]
  exact unreached_of_steady hn hsrc hX hv hr

theorem settled_step_prefix (st : State) : st.settled <+: (step N st).settled := by
  unfold step
  split
  · exact List.prefix_refl _
  · rename_i k u q hq
    split_ifs with hu
    · exact List.prefix_refl _
    · have := (step_settle_known (N := N) hq hu).2
      unfold step at this
      rw [hq] at this
      simp only [hu, ite_false] at this
      rw [this]
      exact List.prefix_append _ _

theorem settled_runSteps_prefix : ∀ f st, st.settled <+: (runSteps (step N) f st).settled
  | 0, _ => List.prefix_refl _
  | f + 1, st => by
    unfold runSteps
    split_ifs
    · exact List.prefix_refl _
    · exact (settled_step_prefix st).trans (settled_runSteps_prefix f _)

/-- **The walk to a goal settles the first vertices the whole walk settles, in the same order.** -/
theorem settled_finalTo_prefix (N : Network) (s t : ℕ) :
    (finalTo N s t).settled <+: (final N s).settled := by
  rcases runTo_cases N t (N.g.arrows.length + 1) (start N s) with h | ⟨k, hk, key, q, hq, hu, h⟩
  · simp only [finalTo, h, List.prefix_refl]
  · simp only [finalTo, h]
    set X := runSteps (step N) k (start N s)
    have hne : X.queue ≠ [] := by simp [hq]
    have hstep : runSteps (step N) (k + 1) (start N s) = step N X := by
      rw [show k + 1 = k + 1 from rfl, runSteps_add (step N) k 1]
      exact (runSteps_succ_of_ne hne 0)
    have hfin : final N s = runSteps (step N) (N.g.arrows.length + 1 - (k + 1)) (step N X) := by
      rw [← hstep, ← runSteps_add, show k + 1 + (N.g.arrows.length + 1 - (k + 1)) =
        N.g.arrows.length + 1 by omega]
    rw [hfin]
    change X.settled ++ [t] <+: _
    rw [← (step_settle_known (N := N) hq hu).2]
    exact settled_runSteps_prefix _ _

end AlgoDesign.Paths.Dijkstra
