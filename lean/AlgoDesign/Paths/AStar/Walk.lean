/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.AStar.Spec
public import AlgoDesign.Paths.Dijkstra.Goal

/-!
# Heading for the goal: the search and its proofs

The search is the cheapest-paths walk to one goal with each queue entry's key the known cost plus
the estimate at its vertex: take the smallest entry (key, then vertex id) off the queue, skip its
vertex if settled, else settle it, stop if it is the goal, and otherwise try every arrow out of it
to an unsettled vertex, lowering the known cost if the arrow gives less and recording the vertex
as previous. A settled vertex is never reopened.

The proof follows the chapter: read on the changed costs (`changed`), with every known cost and key
moved by the estimate (`shifted`), each step of the search is a step of the cheapest-paths walk
(`shifted_step`), so the search is that walk to the goal (`shifted_final`). Box invariant 1 makes
every changed cost at least zero (`noArrowBelowZero_changed`), and along a path the changes cancel
but for the two ends (`pathCost_changed`), so the cheapest paths are the same.
-/

@[expose] public section

namespace AlgoDesign.Paths.AStar

open Network Dijkstra

/-! ## The search -/

/-- **Try one arrow** `(w, i)` out of `u`, settled at cost `du`: unless `w` is settled, if `w` has
no known cost or the arrow gives less, record the new cost and `u`, and queue the new cost plus
the estimate at `w`. -/
def tryArrow (N : Network) (est : List ℤ) (u : ℕ) (du : ℤ) (st : State) (e : ℕ × ℕ) : State :=
  if e.1 ∈ st.settled then st
  else if (st.known e.1).all (du + N.arrowCost e.2 < ·) then
    { st with
      known := Function.update st.known e.1 (some (du + N.arrowCost e.2))
      prev := Function.update st.prev e.1 (some u)
      queue := insertEntry (du + N.arrowCost e.2 + estimate est e.1, e.1) st.queue
      pushed := st.pushed + 1 }
  else st

/-- **The start**: nothing settled; the start vertex known at cost 0, queued with its estimate;
the search heads for the goal `t`. -/
def start (N : Network) (est : List ℤ) (s t : ℕ) : State :=
  { net := N, source := s, settled := [], known := Function.update (fun _ => none) s (some 0),
    prev := fun _ => none, queue := [(estimate est s, s)], pushed := 1, est := est, goal := t }

/-- **One step**: take the smallest entry off the queue; skip its vertex if it is settled, else
settle it and try every arrow out of it, in its row's order, from its known cost, the key less
its estimate. -/
def step (N : Network) (st : State) : State :=
  match st.queue with
  | [] => st
  | (f, u) :: q =>
    if u ∈ st.settled then { st with queue := q }
    else (N.g.out u).foldl (tryArrow N st.est u (f - estimate st.est u))
      { st with settled := st.settled ++ [u], queue := q }

/-- **The search** from `s` to the goal `t`. -/
def astar (N : Network) (est : List ℤ) (s t : ℕ) : Answer :=
  answer (runTo (step N) t (N.g.arrows.length + 1) (start N est s t)).toState

/-! ## On the changed costs, the search is the cheapest-paths walk -/

variable {N : Network} {est : List ℤ}

/-- The search's state read on the changed costs for the estimate `est`, each known cost and key
moved down by `h₀`; `shifted` is this for the state's own estimate and the estimate at its start. -/
def shiftedBy (est : List ℤ) (h₀ : ℤ) (st : State) : Dijkstra.State :=
  { st.toState with
    net := changed st.net est
    known := fun v => (st.known v).map (· + estimate est v - h₀)
    queue := st.queue.map fun e => (e.1 - h₀, e.2) }

theorem shifted_eq (st : State) :
    shifted st = shiftedBy st.est (estimate st.est st.source) st := rfl

theorem arrowCost_changed {i : ℕ} (hi : i < N.g.arrows.length) :
    (changed N est).arrowCost i =
      N.arrowCost i + estimate est (N.target i) - estimate est (N.source i) := by
  simp [changed, arrowCost, List.getD_eq_getElem?_getD, hi]

theorem entryLe_shift (h₀ : ℤ) (a b : ℤ × ℕ) :
    EntryLe (a.1 - h₀, a.2) (b.1 - h₀, b.2) ↔ EntryLe a b := by
  unfold EntryLe; simp only; omega

theorem insertEntry_shift (h₀ : ℤ) (e : ℤ × ℕ) (q : List (ℤ × ℕ)) :
    insertEntry (e.1 - h₀, e.2) (q.map fun e => (e.1 - h₀, e.2)) =
      (insertEntry e q).map fun e => (e.1 - h₀, e.2) := by
  induction q with
  | nil => rfl
  | cons f q ih =>
    simp only [List.map_cons, insertEntry]
    by_cases h : EntryLe e f
    · have h' := (entryLe_shift h₀ e f).2 h
      simp [h, h']
    · have h' : ¬ EntryLe (e.1 - h₀, e.2) (f.1 - h₀, f.2) :=
        fun h' => h ((entryLe_shift h₀ e f).1 h')
      simp [h, h', ih]

/-- **One arrow tried by the search is one arrow tried by the walk on the changed costs.** -/
theorem shifted_tryArrow (h₀ : ℤ) {u w i : ℕ} (he : (w, i) ∈ N.g.out u) (f : ℤ) (st : State) :
    shiftedBy est h₀ (tryArrow N est u (f - estimate est u) st (w, i)) =
      Dijkstra.tryArrow (changed N est) u (f - h₀) (shiftedBy est h₀ st) (w, i) := by
  have hi := (mem_out.1 he).2
  have hlt : i < N.g.arrows.length := (List.getElem?_eq_some_iff.1 hi).1
  have hc : (changed N est).arrowCost i =
      N.arrowCost i + estimate est w - estimate est u := by
    rw [arrowCost_changed hlt, target_eq hi]
    simp [source, List.getD_eq_getElem?_getD, hi]
  have hS : (shiftedBy est h₀ st).settled = st.settled := rfl
  have hK : (shiftedBy est h₀ st).known w = (st.known w).map (· + estimate est w - h₀) := rfl
  unfold tryArrow Dijkstra.tryArrow
  dsimp only
  rw [hS, hc, hK]
  -- the new cost on the changed costs is the new cost plus the estimate at `w`, less `h₀`
  have key : f - h₀ + (N.arrowCost i + estimate est w - estimate est u) =
      f - estimate est u + N.arrowCost i + estimate est w - h₀ := by omega
  have hlow : ((st.known w).all fun x => decide (f - estimate est u + N.arrowCost i < x)) =
      (((st.known w).map (· + estimate est w - h₀)).all fun x =>
        decide (f - h₀ + (N.arrowCost i + estimate est w - estimate est u) < x)) := by
    cases st.known w with
    | none => rfl
    | some d =>
      simp only [Option.all_some, Option.map_some, decide_eq_decide]
      omega
  rw [← hlow]
  split_ifs
  · rfl
  · simp only [shiftedBy]
    congr 1
    · funext v
      by_cases hv : v = w
      · subst hv; simp only [Function.update_self, Option.map_some]; rw [key]
      · simp [Function.update_of_ne hv]
    · rw [key, ← insertEntry_shift]
  · rfl

theorem shifted_foldl (h₀ : ℤ) (u : ℕ) (f : ℤ) :
    ∀ (l : List (ℕ × ℕ)), (∀ e ∈ l, e ∈ N.g.out u) → ∀ st : State,
      shiftedBy est h₀ (l.foldl (tryArrow N est u (f - estimate est u)) st) =
        l.foldl (Dijkstra.tryArrow (changed N est) u (f - h₀)) (shiftedBy est h₀ st)
  | [], _, _ => rfl
  | ⟨w, i⟩ :: l, h, st => by
    simp only [List.foldl_cons]
    rw [shifted_foldl h₀ u f l (fun e he => h e (by simp [he])),
      shifted_tryArrow h₀ (h _ (by simp))]

/-- **A try keeps the search's network, estimate, start vertex and goal.** -/
theorem tryArrow_fields (u : ℕ) (du : ℤ) (st : State) (e : ℕ × ℕ) :
    (tryArrow N est u du st e).net = st.net ∧ (tryArrow N est u du st e).est = st.est ∧
      (tryArrow N est u du st e).source = st.source ∧
        (tryArrow N est u du st e).goal = st.goal := by
  unfold tryArrow
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem foldl_fields (u : ℕ) (du : ℤ) :
    ∀ (l : List (ℕ × ℕ)) (st : State), (l.foldl (tryArrow N est u du) st).net = st.net ∧
      (l.foldl (tryArrow N est u du) st).est = st.est ∧
        (l.foldl (tryArrow N est u du) st).source = st.source ∧
          (l.foldl (tryArrow N est u du) st).goal = st.goal
  | [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | e :: l, st => by
    obtain ⟨h1, h2, h3, h4⟩ := foldl_fields u du l (tryArrow N est u du st e)
    obtain ⟨g1, g2, g3, g4⟩ := tryArrow_fields (N := N) (est := est) u du st e
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

/-- **A step keeps the search's network, estimate, start vertex and goal.** -/
theorem step_fields (N : Network) (st : State) :
    (step N st).net = st.net ∧ (step N st).est = st.est ∧ (step N st).source = st.source ∧
      (step N st).goal = st.goal := by
  unfold step
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split_ifs
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact foldl_fields _ _ _ _

/-- **One step of the search is one step of the walk on the changed costs.** -/
theorem shifted_step (h₀ : ℤ) (st : State) (hest : st.est = est) :
    shiftedBy est h₀ (step N st) = Dijkstra.step (changed N est) (shiftedBy est h₀ st) := by
  subst hest
  cases hq : st.queue with
  | nil =>
    have hq' : (shiftedBy st.est h₀ st).queue = [] := by simp [shiftedBy, hq]
    unfold step Dijkstra.step
    rw [hq, hq']
  | cons e q =>
    obtain ⟨f, u⟩ := e
    have hq' : (shiftedBy st.est h₀ st).queue = (f - h₀, u) :: q.map fun e => (e.1 - h₀, e.2) := by
      simp [shiftedBy, hq]
    have hS : (shiftedBy st.est h₀ st).settled = st.settled := rfl
    unfold step Dijkstra.step
    rw [hq, hq']
    dsimp only
    rw [hS]
    split_ifs
    · rfl
    · exact shifted_foldl (est := st.est) (N := N) h₀ u f (N.g.out u) (fun e he => he)
        { st with settled := st.settled ++ [u], queue := q }

theorem shifted_start (s t : ℕ) :
    shiftedBy est (estimate est s) (start N est s t) = Dijkstra.start (changed N est) s := by
  simp only [shiftedBy, start, Dijkstra.start, List.map_cons, List.map_nil, sub_self]
  congr 1
  funext v
  by_cases hv : v = s
  · subst hv; simp
  · simp [Function.update_of_ne hv]

/-- **Stopped at the goal, the search is the cheapest-paths walk to the goal on the changed
costs.** -/
theorem shifted_runTo (h₀ : ℤ) (t : ℕ) :
    ∀ f st, st.est = est → shiftedBy est h₀ (runTo (step N) t f st) =
      Dijkstra.runTo (changed N est) t f (shiftedBy est h₀ st)
  | 0, _, _ => rfl
  | f + 1, st, hest => by
    cases hq : st.queue with
    | nil =>
      have hq' : (shiftedBy est h₀ st).queue = [] := by simp [shiftedBy, hq]
      unfold runTo Dijkstra.runTo
      rw [hq, hq']
    | cons e q =>
      obtain ⟨k, u⟩ := e
      have hq' : (shiftedBy est h₀ st).queue = (k - h₀, u) :: q.map fun e => (e.1 - h₀, e.2) := by
        simp [shiftedBy, hq]
      have hS : (shiftedBy est h₀ st).settled = st.settled := rfl
      unfold runTo Dijkstra.runTo
      rw [hq, hq']
      dsimp only
      rw [hS]
      split_ifs
      · rfl
      · rw [← shifted_step h₀ st hest]
        exact shifted_runTo h₀ t f (step N st) ((step_fields N st).2.1.trans hest)

theorem shifted_final (s t : ℕ) :
    shiftedBy est (estimate est s) (runTo (step N) t (N.g.arrows.length + 1) (start N est s t)) =
      finalTo (changed N est) s t := by
  rw [shifted_runTo (est := est) _ _ _ (start N est s t) rfl, shifted_start]
  rfl

/-! ## The changed costs -/

theorem wellFormed_changed (hN : N.WellFormed) : (changed N est).WellFormed :=
  ⟨hN.1, by simp [changed]⟩

/-- **Box invariant 1 makes every changed cost at least zero.** -/
theorem noArrowBelowZero_changed {t : ℕ} (h : Consistent N t est) :
    (changed N est).NoArrowBelowZero := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  have := h.2.2 i (List.mem_range.1 hi)
  omega

/-- **Along a path, the changed costs cancel but for the two ends**: a path from `u` to `v` costs
its cost plus the estimate at `v` minus the estimate at `u`. -/
theorem pathCost_changed {u : ℕ} {p : List ℕ} {v : ℕ} (h : N.ends u p = some v) :
    (changed N est).pathCost p = N.pathCost p + estimate est v - estimate est u := by
  induction p generalizing u with
  | nil =>
    simp only [ends, Option.some.injEq] at h
    subst h; simp [pathCost]
  | cons j p ih =>
    simp only [ends] at h
    split at h
    · rename_i a b hj
      split_ifs at h with hau
      subst hau
      have hlt : j < N.g.arrows.length := (List.getElem?_eq_some_iff.1 hj).1
      have := ih h
      have hc := arrowCost_changed (est := est) hlt
      rw [target_eq hj, show N.source j = a by simp [source, List.getD_eq_getElem?_getD, hj]]
        at hc
      simp only [pathCost, List.map_cons, List.sum_cons] at this ⊢
      rw [hc, this]
      omega
    · exact absurd h (by simp)

theorem ends_changed : ∀ (u : ℕ) (p : List ℕ), (changed N est).ends u p = N.ends u p
  | _, [] => rfl
  | u, i :: p => by
    simp only [ends, show (changed N est).g = N.g from rfl]
    split
    · split_ifs
      · exact ends_changed _ p
      · rfl
    · rfl

theorem isPath_changed {s : ℕ} {p : List ℕ} {v : ℕ} :
    (changed N est).IsPath s p v ↔ N.IsPath s p v := by
  simp only [IsPath, ends_changed]
  rfl

/-- **The cheapest paths are the same on the changed costs**, their costs moved by the estimates at
the two ends. -/
theorem cheapest_changed {s t : ℕ} {d : ℤ} :
    (changed N est).Cheapest s t (some (d + estimate est t - estimate est s)) ↔
      N.Cheapest s t (some d) := by
  unfold Cheapest CheapestAmong
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp _ => ?_, fun d' hd' => ?_⟩
    · have := h1 p (isPath_changed.2 hp) trivial
      rw [pathCost_changed hp.1] at this
      change d + _ - _ ≤ _ at this
      change d ≤ _
      omega
    · rw [Option.mem_def, Option.some.injEq] at hd'
      subst hd'
      obtain ⟨p, hp, -, hc⟩ := h2 _ rfl
      have hp := isPath_changed.1 hp
      rw [pathCost_changed hp.1] at hc
      exact ⟨p, hp, trivial, by omega⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp _ => ?_, fun d' hd' => ?_⟩
    · have hp := isPath_changed.1 hp
      have := h1 p hp trivial
      change d ≤ _ at this
      change _ ≤ (changed N est).pathCost p
      rw [pathCost_changed hp.1]
      omega
    · rw [Option.mem_def, Option.some.injEq] at hd'
      subst hd'
      obtain ⟨p, hp, -, hc⟩ := h2 _ rfl
      refine ⟨p, isPath_changed.2 hp, trivial, ?_⟩
      rw [pathCost_changed hp.1, hc]

/-! ## What the search promises -/

/-- The search's answer, read off the walk to the goal on the changed costs. -/
theorem astar_cost (s t v : ℕ) :
    (dijkstraTo (changed N est) s t).cost v =
      ((astar N est s t).cost v).map (· + estimate est v - estimate est s) ∧
    (dijkstraTo (changed N est) s t).prev = (astar N est s t).prev := by
  have := shifted_final (N := N) (est := est) s t
  simp only [dijkstraTo, astar, answer]
  rw [← this]
  exact ⟨rfl, rfl⟩

theorem astar_goal (hN : N.WellFormed) {s t : ℕ} (h : Consistent N t est)
    (hs : s < N.g.n) (hr : N.g.Reaches s t) :
    ∃ d, (astar N est s t).cost t = some d ∧ N.Cheapest s t (some d) := by
  obtain ⟨d', hd', hc⟩ := dijkstraTo_goal (wellFormed_changed hN) (noArrowBelowZero_changed h)
    hs hr
  rw [(astar_cost s t t).1] at hd'
  cases ha : (astar N est s t).cost t with
  | none => rw [ha] at hd'; exact absurd hd' (by simp)
  | some d =>
    rw [ha, Option.map_some, Option.some.injEq] at hd'
    subst hd'
    exact ⟨d, rfl, cheapest_changed.1 hc⟩

theorem astar_previous {s t : ℕ} (hs : s < N.g.n) {v : ℕ} (hv : v < N.g.n) :
    ∀ d ∈ (astar N est s t).cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
      LeadsBack (astar N est s t).prev s (N.visits s p) := by
  intro d hd
  have := dijkstraTo_previous (N := changed N est) hs t hv (d + estimate est v - estimate est s)
    (by rw [(astar_cost s t v).1, Option.mem_def.1 hd]; rfl)
  obtain ⟨p, hp, hc, hl⟩ := this
  have hp := isPath_changed.1 hp
  rw [pathCost_changed hp.1] at hc
  rw [(astar_cost (N := N) (est := est) s t v).2] at hl
  exact ⟨p, hp, by omega, hl⟩

theorem astar_unreached {s t : ℕ} (hs : s < N.g.n) {v : ℕ} (hv : v < N.g.n)
    (hr : ¬ N.g.Reaches s v) : (astar N est s t).cost v = none := by
  have := dijkstraTo_unreached (N := changed N est) hs t hv hr
  rw [(astar_cost s t v).1] at this
  cases h : (astar N est s t).cost v with
  | none => rfl
  | some d => rw [h] at this; exact absurd this (by simp)

/-! ## The search stays legal -/

theorem valid_start {s t : ℕ} (h : Consistent N t est) (hs : s < N.g.n) :
    Valid (start N est s t) ∧ WellFormed (start N est s t) := by
  refine ⟨h, ?_⟩
  change Dijkstra.Valid (shiftedBy est (estimate est s) (start N est s t)) ∧
    Dijkstra.WellFormed (shiftedBy est (estimate est s) (start N est s t))
  rw [shifted_start]
  exact Dijkstra.valid_start hs

theorem valid_step (hN : N.WellFormed) {st : State} (hn : st.net = N) (hs : st.source < N.g.n)
    (h : Valid st ∧ WellFormed st) (hne : st.queue ≠ []) :
    Valid (step N st) ∧ WellFormed (step N st) := by
  obtain ⟨hnet, hest, hsrc, hgoal⟩ := step_fields N st
  have h1 : Consistent N st.goal st.est := hn ▸ h.1
  refine ⟨?_, ?_⟩
  · unfold Valid EstimateIsConsistent
    rw [hnet, hest, hgoal]
    exact h.1
  · unfold WellFormed WalkIsCheapestPathsOnChangedCosts
    rw [shifted_eq, hest, hsrc, shifted_step _ st rfl]
    exact Dijkstra.valid_step (wellFormed_changed hN) (noArrowBelowZero_changed h1) hs
      (by simp [shiftedBy, hn]) rfl h.2 (by simpa [shiftedBy] using hne)

/-- **`Valid` and `WellFormed` together are the search's two pieces**, the box's one and the one
the search needs beyond it. -/
theorem valid_and_wellFormed_iff (st : State) :
    Valid st ∧ WellFormed st ↔ EstimateIsConsistent st ∧ WalkIsCheapestPathsOnChangedCosts st :=
  Iff.rfl

/-! ## Cost -/

theorem final_counted (N : Network) (est : List ℤ) (s t : ℕ) :
    Counted N (runTo (step N) t (N.g.arrows.length + 1) (start N est s t)).toState := by
  have hfin := shifted_final (N := N) (est := est) s t
  have key : Counted (changed N est) (finalTo (changed N est) s t) := by
    change Counted (changed N est) (Dijkstra.runTo (changed N est) t (N.g.arrows.length + 1)
      (Dijkstra.start (changed N est) s))
    rcases runTo_cases (changed N est) t (N.g.arrows.length + 1)
      (Dijkstra.start (changed N est) s) with h | ⟨k, -, key, q, hq, hu, h⟩
    · rw [h]; exact Dijkstra.final_counted _ _
    · rw [h]
      have hc := runSteps_induct (Counted (changed N est)) _ (fun _ h hq => (counted_step h hq).1)
        k _ (counted_start (s := s))
      refine ⟨hc.1.append (List.nodup_singleton t) (by simpa using hu), ?_⟩
      have := hc.2
      unfold tried at this ⊢
      simp only [List.flatMap_append, List.length_append, List.flatMap_singleton] at this ⊢
      omega
  rw [← hfin] at key
  exact key

end AlgoDesign.Paths.AStar
