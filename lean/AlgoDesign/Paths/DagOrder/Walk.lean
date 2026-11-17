/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.DagOrder.Decide
public import AlgoDesign.Paths.Dijkstra.Basic
public import AlgoDesign.Graphs.TopoOrder

/-!
# Cheapest paths in a graph with no cycle: the walk

Source: Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §22.2,
DAG-SHORTEST-PATHS (p. 617), and Lemma 22.15 (p. 635), path relaxation: relaxing a path's arrows
in order makes its end's cost exact. In a topological order every path's arrows come in order.

The walk takes the vertices in Kahn's order (`TopoOrder.kahn`). A vertex with no known cost is
taken without trying its row. An arrow's end gets a new cost, and the vertex as its previous one,
only when its cost drops or was unknown.
-/

@[expose] public section

namespace AlgoDesign.Paths.DagOrder

open Network Graphs
open Dijkstra (Through LeadsBack Answer)

/-! ## The walk -/

/-- **Try one arrow** `(w, i)` out of `u`, known at cost `du`: if `w` has no known cost or the
arrow gives less, record the new cost and `u`. -/
def tryArrow (N : Network) (u : ℕ) (du : ℤ) (st : State) (e : ℕ × ℕ) : State :=
  if (st.known e.1).all (du + N.arrowCost e.2 < ·) then
    { st with
      known := Function.update st.known e.1 (some (du + N.arrowCost e.2))
      prev := Function.update st.prev e.1 (some u) }
  else st

/-- **The start**, given an order: nothing taken; the start vertex known at cost 0. -/
def start (_ : Network) (s : ℕ) (l : List ℕ) : State :=
  ⟨[], l, Function.update (fun _ => none) s (some 0), fun _ => none⟩

/-- **One step**: take the next vertex of the order; if its cost is known, try every arrow out of
it, in its row's order. -/
def step (N : Network) (st : State) : State :=
  match st.todo with
  | [] => st
  | u :: rest =>
    match st.known u with
    | none => { st with done := st.done ++ [u], todo := rest }
    | some du =>
      (N.g.out u).foldl (tryArrow N u du) { st with done := st.done ++ [u], todo := rest }

/-- **The walk**: Kahn's order, or its stuck set; then one step per vertex. -/
def dagPaths (N : Network) (s : ℕ) : Except (List ℕ) Answer :=
  (TopoOrder.kahn N.g).map fun l => answer (runSteps (step N) N.g.n (start N s l))

/-! ## The order -/

variable {N : Network} {s : ℕ}

theorem not_mem_left_of_isTopoOrder {D R : List ℕ} {u : ℕ}
    (h : TopoOrder.IsTopoOrder N.g (D ++ u :: R)) : u ∉ D := by
  have hnd := h.nodup
  rw [List.nodup_append] at hnd
  exact fun hu => hnd.2.2 u hu u List.mem_cons_self rfl

/-- **In a topological order, every arrow out of a vertex points to a vertex after it.** -/
theorem mem_rest_of_arrow {D R : List ℕ} {u x : ℕ} (h : TopoOrder.IsTopoOrder N.g (D ++ u :: R))
    (hx : (u, x) ∈ N.g.arrows) : x ∈ R := by
  have hb : TopoOrder.Before (D ++ u :: R) u x := h.2 _ hx
  have hnd := h.nodup
  rcases List.mem_append.1 hb.mem_right with hxD | hxR
  · exfalso
    obtain ⟨as, bs, rfl⟩ := List.append_of_mem hxD
    have hb' : TopoOrder.Before (as ++ x :: (bs ++ u :: R)) u x := by simpa using hb
    have hnd' : (as ++ x :: (bs ++ u :: R)).Nodup := by simpa using hnd
    have hu := TopoOrder.mem_prefix_of_before hnd' hb'
    exact not_mem_left_of_isTopoOrder h (List.mem_append_left _ hu)
  · rcases List.mem_cons.1 hxR with rfl | hxR
    · exfalso
      have := hb.nodup hnd
      simp at this
    · exact hxR

/-! ## Walks and paths -/

theorem mem_visits_of_ends {u : ℕ} {p : List ℕ} {v : ℕ} (h : N.ends u p = some v) :
    v ∈ N.visits u p := by
  induction p using List.reverseRecOn generalizing v with
  | nil => simp only [ends, Option.some.injEq] at h; subst h; simp [visits]
  | append_singleton q j _ =>
    obtain ⟨x, -, hj⟩ := ends_append_singleton.1 h
    rw [visits_append_singleton, target_eq hj]
    simp

/-- **A walk that passes `u` and ends among the vertices taken before it never passed `u`**: in a
topological order, no arrow leads back from `u` to a vertex before it. -/
theorem not_mem_visits {D R : List ℕ} {u : ℕ} (h : TopoOrder.IsTopoOrder N.g (D ++ u :: R)) :
    ∀ {q : List ℕ} {x : ℕ}, N.ends s q = some x → (∀ y ∈ N.visits s q, y ∈ D ++ [u]) → x ∈ D →
      u ∉ N.visits s q := by
  intro q
  induction q using List.reverseRecOn with
  | nil =>
    intro x hx _ hxD hu
    simp only [ends, Option.some.injEq] at hx
    subst hx
    simp only [visits, List.map_nil, List.mem_singleton] at hu
    exact not_mem_left_of_isTopoOrder h (hu ▸ hxD)
  | append_singleton q j ih =>
    intro x hx hall hxD hu
    obtain ⟨y, hy, hj⟩ := ends_append_singleton.1 hx
    rw [visits_append_singleton, target_eq hj] at hall hu
    have hyq := mem_visits_of_ends hy
    rcases List.mem_append.1 (hall y (List.mem_append_left _ hyq)) with hyD | hyu
    · rcases List.mem_append.1 hu with hu | hu
      · exact ih hy (fun z hz => hall z (List.mem_append_left _ hz)) hyD hu
      · rw [← List.mem_singleton.1 hu] at hxD
        exact not_mem_left_of_isTopoOrder h hxD
    · rw [List.mem_singleton.1 hyu] at hj
      have hxR := mem_rest_of_arrow h (List.mem_of_getElem? hj)
      have hnd := h.nodup
      rw [List.nodup_append] at hnd
      exact hnd.2.2 x hxD x (List.mem_cons_of_mem _ hxR) rfl

/-- **A path through the vertices taken, the last of them `u`, that passes `u` ends one arrow after
it**: it is a path to `u` through the vertices taken before `u`, then an arrow out of `u`. -/
theorem split_at_last {D R : List ℕ} {u : ℕ} (h : TopoOrder.IsTopoOrder N.g (D ++ u :: R))
    {p : List ℕ} {v : ℕ} (hp : N.IsPath s p v) (ht : Through N (D ++ [u]) s p)
    (hu : u ∈ (N.visits s p).dropLast) :
    ∃ q i, p = q ++ [i] ∧ N.IsPath s q u ∧ Through N D s q ∧ N.g.arrows[i]? = some (u, v) := by
  have hne : p ≠ [] := by
    rintro rfl
    simp [visits] at hu
  obtain ⟨q, i, x, rfl, hq, hi, -, hv⟩ := hp.eq_snoc hne
  rw [hv, List.dropLast_concat] at hu
  have hall : ∀ y ∈ N.visits s q, y ∈ D ++ [u] := by
    intro y hy
    exact ht y (by rw [hv, List.dropLast_concat]; exact hy)
  have hxu : x = u := by
    by_contra hxu
    have hxD : x ∈ D := by
      rcases List.mem_append.1 (hall x hq.mem_visits) with hx | hx
      · exact hx
      · exact absurd (List.mem_singleton.1 hx) hxu
    exact not_mem_visits h hq.1 hall hxD hu
  subst hxu
  refine ⟨q, i, rfl, hq, fun y hy => ?_, hi⟩
  rcases List.mem_append.1 (hall y (List.dropLast_subset _ hy)) with hy' | hy'
  · exact hy'
  · exact absurd (List.mem_singleton.1 hy') (hq.ne_of_mem_dropLast hy)

/-! ## Trying the arrows out of a vertex -/

theorem atMost_trans_le {c : Option ℤ} {b b' : ℤ} (h : AtMost c b) (hb : b ≤ b') :
    AtMost c b' := by
  cases c with
  | none => exact h
  | some d => exact le_trans (α := ℤ) h hb

/-- A cost at most `b` stays at most `b` when it is lowered. -/
theorem atMost_lower {c c' : Option ℤ} {b : ℤ} (h : AtMost c b) (hl : ∀ d ∈ c, AtMost c' d) :
    AtMost c' b := by
  cases c with
  | none => exact absurd h id
  | some d => exact atMost_trans_le (hl d rfl) h

/-- What trying the arrows `l` out of `u`, known at cost `du`, does to a state `st`, giving
`st'`. -/
structure Relaxes (N : Network) (u : ℕ) (du : ℤ) (l : List (ℕ × ℕ)) (st st' : State) : Prop where
  done : st'.done = st.done
  todo : st'.todo = st.todo
  known_prev : ∀ x, (st'.known x = st.known x ∧ st'.prev x = st.prev x) ∨
    (st'.prev x = some u ∧ ∃ e ∈ l, e.1 = x ∧ st'.known x = some (du + N.arrowCost e.2))
  lowers : ∀ x, ∀ d ∈ st.known x, AtMost (st'.known x) d
  tried : ∀ e ∈ l, AtMost (st'.known e.1) (du + N.arrowCost e.2)

theorem Relaxes.same {u : ℕ} {du : ℤ} {l : List (ℕ × ℕ)} {st : State}
    (h : ∀ e ∈ l, AtMost (st.known e.1) (du + N.arrowCost e.2)) : Relaxes N u du l st st where
  done := rfl
  todo := rfl
  known_prev _ := Or.inl ⟨rfl, rfl⟩
  lowers _ d hd := by rw [Option.mem_def] at hd; rw [hd]; exact le_refl d
  tried := h

theorem relaxes_tryArrow (u : ℕ) (du : ℤ) (st : State) (e : ℕ × ℕ) :
    Relaxes N u du [e] st (tryArrow N u du st e) := by
  unfold tryArrow
  split_ifs with hlow
  · refine
      { done := rfl
        todo := rfl
        known_prev := fun x => ?_
        lowers := fun x d hd => ?_
        tried := fun e' he' => ?_ }
    · by_cases hx : x = e.1
      · subst hx
        exact Or.inr ⟨by simp, e, by simp, rfl, by simp⟩
      · exact Or.inl ⟨by simp [hx], by simp [hx]⟩
    · by_cases hx : x = e.1
      · subst hx
        rw [Option.mem_def] at hd
        rw [hd] at hlow
        simp only [Option.all_some, decide_eq_true_eq] at hlow
        simp only [Function.update_self, AtMost]
        exact le_of_lt hlow
      · simp only [Function.update_of_ne hx]
        rw [Option.mem_def] at hd; rw [hd]; exact le_refl d
    · rw [List.mem_singleton.1 he']
      simp only [Function.update_self, AtMost, le_refl]
  · refine Relaxes.same fun e' he' => ?_
    rw [List.mem_singleton.1 he']
    cases hk : st.known e.1 with
    | none => rw [hk] at hlow; simp at hlow
    | some d =>
      rw [hk] at hlow
      simp only [Option.all_some, decide_eq_true_eq, not_lt] at hlow
      exact hlow

theorem Relaxes.append {u : ℕ} {du : ℤ} {l₁ l₂ : List (ℕ × ℕ)} {st st₁ st₂ : State}
    (h₁ : Relaxes N u du l₁ st st₁) (h₂ : Relaxes N u du l₂ st₁ st₂) :
    Relaxes N u du (l₁ ++ l₂) st st₂ where
  done := h₂.done.trans h₁.done
  todo := h₂.todo.trans h₁.todo
  known_prev x := by
    rcases h₂.known_prev x with ⟨hk, hp⟩ | ⟨hp, e, he, hex, hk⟩
    · rcases h₁.known_prev x with ⟨hk', hp'⟩ | ⟨hp', e, he, hex, hk'⟩
      · exact Or.inl ⟨hk.trans hk', hp.trans hp'⟩
      · exact Or.inr ⟨hp.trans hp', e, List.mem_append_left _ he, hex, hk.trans hk'⟩
    · exact Or.inr ⟨hp, e, List.mem_append_right _ he, hex, hk⟩
  lowers x d hd := atMost_lower (h₁.lowers x d hd) (h₂.lowers x)
  tried e he := by
    rcases List.mem_append.1 he with he | he
    · exact atMost_lower (h₁.tried e he) (h₂.lowers e.1)
    · exact h₂.tried e he

theorem relaxes_foldl (u : ℕ) (du : ℤ) :
    ∀ (l : List (ℕ × ℕ)) (st : State), Relaxes N u du l st (l.foldl (tryArrow N u du) st)
  | [], _ => Relaxes.same (by simp)
  | e :: l, st => by
    rw [List.foldl_cons]
    exact (relaxes_tryArrow u du st e).append (relaxes_foldl u du l _)

/-! ## The invariants along the walk -/

theorem mem_known_start {l : List ℕ} {v : ℕ} {d : ℤ} :
    d ∈ (start N s l).known v ↔ v = s ∧ d = 0 := by
  by_cases hv : v = s
  · subst hv; simp [start, eq_comm]
  · simp [start, hv]

theorem valid_start {l : List ℕ} (hl : TopoOrder.IsTopoOrder N.g l) : Valid N s (start N s l) := by
  refine ⟨by simpa [InOrder, start] using hl, fun v _ => ⟨fun p hp ht => ?_, fun d hd => ?_⟩,
    rfl, fun v _ d hd => ?_⟩
  · have hp0 := Dijkstra.eq_nil_of_through_nil ht
    subst hp0
    rw [isPath_nil_iff.1 hp]
    simp [start, pathCost, AtMost]
  · obtain ⟨rfl, rfl⟩ := mem_known_start.1 hd
    exact ⟨[], isPath_nil v, Dijkstra.through_nil _ _, rfl⟩
  · obtain ⟨rfl, rfl⟩ := mem_known_start.1 hd
    exact ⟨[], isPath_nil v, rfl, Dijkstra.through_nil _ _, rfl, by simp [visits]⟩

/-- A vertex of a topological order is a vertex of the graph. -/
theorem lt_of_mem_order {l : List ℕ} (hl : TopoOrder.IsTopoOrder N.g l) {u : ℕ} (hu : u ∈ l) :
    u < N.g.n :=
  List.mem_range.1 (hl.1.subset hu)

/-- Following the previous vertices back still works when no vertex of the list changed its
previous vertex. -/
theorem leadsBack_congr {prev prev' : ℕ → Option ℕ} {l : List ℕ} (h : LeadsBack prev s l)
    (hs : s ∈ l) (hkeep : ∀ x ∈ l, prev' x = prev x) : LeadsBack prev' s l :=
  ⟨(hkeep s hs).trans h.1,
    h.2.imp_of_mem_imp fun a b _ hb hab => by rw [hkeep b hb]; exact hab⟩

theorem step_cons {st : State} {u : ℕ} {rest : List ℕ} (ht : st.todo = u :: rest) :
    step N st = match st.known u with
      | none => { st with done := st.done ++ [u], todo := rest }
      | some du =>
        (N.g.out u).foldl (tryArrow N u du) { st with done := st.done ++ [u], todo := rest } := by
  unfold step; rw [ht]

/-- **A step keeps the walk legal**: the next vertex's paths are the old ones and those that end
with one arrow out of it. -/
theorem valid_step {st : State} (h : Valid N s st) (hne : st.todo ≠ []) :
    Valid N s (step N st) := by
  obtain ⟨hO, hK, hP⟩ := h
  obtain ⟨u, rest, ht⟩ := List.exists_cons_of_ne_nil hne
  have hO' : TopoOrder.IsTopoOrder N.g (st.done ++ u :: rest) := by
    unfold InOrder at hO; rwa [ht] at hO
  have hun : u < N.g.n := lt_of_mem_order hO' (by simp)
  -- the state with `u` taken, before its row is tried
  set st₁ : State := { st with done := st.done ++ [u], todo := rest } with hst₁
  have hO₁ : InOrder N st₁ := by simpa [InOrder, st₁] using hO'
  -- a path through the vertices taken now either was one before, or ends one arrow after `u`
  have hsplit : ∀ {p v}, N.IsPath s p v → Through N (st.done ++ [u]) s p →
      Through N st.done s p ∨ ∃ q i, p = q ++ [i] ∧ N.IsPath s q u ∧ Through N st.done s q ∧
        N.g.arrows[i]? = some (u, v) := by
    intro p v hp htp
    by_cases hu : u ∈ (N.visits s p).dropLast
    · exact Or.inr (split_at_last hO' hp htp hu)
    · refine Or.inl fun y hy => ?_
      rcases List.mem_append.1 (htp y hy) with hy' | hy'
      · exact hy'
      · exact absurd (List.mem_singleton.1 hy' ▸ hy) hu
  rw [step_cons ht]
  cases hku : st.known u with
  | none =>
    refine ⟨hO₁, fun v hv => ⟨fun p hp htp => ?_, fun d hd => ?_⟩, hP.1, fun v hv d hd => ?_⟩
    · rcases hsplit hp htp with htp | ⟨q, i, -, hq, htq, -⟩
      · exact (hK v hv).1 p hp htp
      · have := (hK u hun).1 q hq htq
        rw [hku] at this
        exact absurd this id
    · obtain ⟨p, hp, hc, htp, -⟩ := hP.2 v hv d hd
      exact ⟨p, hp, Dijkstra.through_mono htp (fun x hx => List.mem_append_left _ hx), hc⟩
    · obtain ⟨p, hp, hc, htp, hl⟩ := hP.2 v hv d hd
      exact ⟨p, hp, hc, Dijkstra.through_mono htp (fun x hx => List.mem_append_left _ hx), hl⟩
  | some du =>
    have R := relaxes_foldl (N := N) u du (N.g.out u) st₁
    set st' := (N.g.out u).foldl (tryArrow N u du) st₁
    have hdone : st'.done = st.done ++ [u] := R.done
    -- a vertex whose cost changed is the end of an arrow out of `u`, so after `u` in the order
    have keep : ∀ x ∈ st.done ++ [u], st'.known x = st.known x ∧ st'.prev x = st.prev x := by
      intro x hx
      rcases R.known_prev x with hk | ⟨-, e, he, rfl, -⟩
      · exact hk
      · have hxR := mem_rest_of_arrow hO' (List.mem_of_getElem? (mem_out.1 he).2)
        have hnd := hO'.nodup
        rw [← List.singleton_append, ← List.append_assoc, List.nodup_append] at hnd
        exact absurd rfl (hnd.2.2 e.1 hx e.1 hxR)
    -- the path to `u` that its previous vertices give
    obtain ⟨pu, hpu, hcu, htu, hlu⟩ := hP.2 u hun du hku
    have hvu : ∀ y ∈ N.visits s pu, y ∈ st.done ++ [u] := by
      intro y hy
      rw [hpu.visits_eq] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ (htu y hy)
      · exact List.mem_append_right _ hy
    have hsu : s ∈ st.done ++ [u] := hvu s (List.mem_cons_self)
    have hprev_s : st'.prev s = none := (keep s hsu).2.trans hP.1
    have hP' : PreviousLeadsBack N s st' := by
      refine ⟨hprev_s, fun v hv d hd => ?_⟩
      rcases R.known_prev v with ⟨hkv, hpv⟩ | ⟨hpv, e, he, hev, hkv⟩
      · rw [hkv] at hd
        obtain ⟨p, hp, hc, htp, hl⟩ := hP.2 v hv d hd
        have htp' : Through N st'.done s p := by
          rw [hdone]; exact Dijkstra.through_mono htp fun x hx => List.mem_append_left _ hx
        refine ⟨p, hp, hc, htp', leadsBack_congr hl (by simp [visits]) fun b hb => ?_⟩
        rw [hp.visits_eq] at hb
        rcases List.mem_append.1 hb with hb | hb
        · exact (keep b (List.mem_append_left _ (htp b hb))).2
        · rw [List.mem_singleton.1 hb]; exact hpv
      · subst hev
        rw [hkv, Option.mem_def, Option.some.injEq] at hd
        subst hd
        have hi := (mem_out.1 he).2
        have hwR := mem_rest_of_arrow hO' (List.mem_of_getElem? hi)
        have hnd := hO'.nodup
        rw [← List.singleton_append, ← List.append_assoc, List.nodup_append] at hnd
        have hwp : e.1 ∉ N.visits s pu := fun hm => hnd.2.2 e.1 (hvu _ hm) e.1 hwR rfl
        obtain ⟨hp', hv'⟩ := hpu.snoc hi hwp
        refine ⟨pu ++ [e.2], hp', by rw [pathCost_append, hcu]; simp [pathCost],
          fun x hx => ?_, ?_⟩
        · rw [hdone]
          rw [hv', List.dropLast_concat] at hx
          exact hvu x hx
        · rw [hv']
          refine ⟨hprev_s, List.IsChain.append
            (hlu.2.imp_of_mem_imp fun a b _ hb hab => ?_) (List.isChain_singleton _) ?_⟩
          · rw [(keep b (hvu b hb)).2]; exact hab
          · intro x hx y hy
            rw [hpu.visits_eq] at hx
            simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
              Option.mem_def, Option.some.injEq] at hx
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            rw [← hx, ← hy, hpv]
    change Valid N s st'
    refine ⟨by simpa [InOrder, hdone, R.todo, st₁] using hO', fun v hv => ⟨fun p hp htp => ?_,
      fun d hd => ?_⟩, hP'⟩
    · rw [hdone] at htp
      rcases hsplit hp htp with htp | ⟨q, i, rfl, hq, htq, hi⟩
      · exact atMost_lower ((hK v hv).1 p hp htp) (R.lowers v)
      · have hdu := (hK u hun).1 q hq htq
        rw [hku] at hdu
        have := R.tried (v, i) (mem_out.2 ⟨hv, hi⟩)
        refine atMost_trans_le this ?_
        have hi1 : N.pathCost [i] = N.arrowCost i := by simp [pathCost]
        rw [pathCost_append, hi1]
        simp only [AtMost] at hdu
        change du + N.arrowCost i ≤ _
        omega
    · obtain ⟨p, hp, hc, htp, -⟩ := hP'.2 v hv d hd
      exact ⟨p, hp, htp, hc⟩

theorem step_done_todo {st : State} {u : ℕ} {rest : List ℕ} (ht : st.todo = u :: rest) :
    (step N st).done = st.done ++ [u] ∧ (step N st).todo = rest := by
  rw [step_cons ht]
  cases st.known u with
  | none => exact ⟨rfl, rfl⟩
  | some du =>
    have R := relaxes_foldl (N := N) u du (N.g.out u)
      { st with done := st.done ++ [u], todo := rest }
    exact ⟨R.done, R.todo⟩

/-- Enough steps from a legal state take every vertex left, and keep the state legal. -/
theorem runSteps_spec (f : ℕ) {st : State} (h : Valid N s st) (hf : st.todo.length ≤ f) :
    Valid N s (runSteps (step N) f st) ∧ (runSteps (step N) f st).todo = [] := by
  induction f generalizing st with
  | zero => exact ⟨h, List.eq_nil_of_length_eq_zero (by simp only [runSteps]; omega)⟩
  | succ f ih =>
    unfold runSteps
    split_ifs with h0
    · exact ⟨h, h0⟩
    · obtain ⟨u, rest, ht⟩ := List.exists_cons_of_ne_nil h0
      refine ih (valid_step h h0) ?_
      rw [(step_done_todo ht).2]
      rw [ht, List.length_cons] at hf
      omega

/-- The state the walk ends in, in the order `l`. -/
abbrev final (N : Network) (s : ℕ) (l : List ℕ) : State := runSteps (step N) N.g.n (start N s l)

theorem final_spec {l : List ℕ} (hl : TopoOrder.IsTopoOrder N.g l) :
    Valid N s (final N s l) ∧ (final N s l).todo = [] :=
  runSteps_spec _ (valid_start hl) (by simp [start, hl.1.length_eq])

/-- In the end every vertex is taken, so the cheapest through the vertices taken is the
cheapest. -/
theorem final_cheapest (hN : N.WellFormed) (hs : s < N.g.n) {l : List ℕ}
    (hl : TopoOrder.IsTopoOrder N.g l) {v : ℕ} (hv : v < N.g.n) :
    N.Cheapest s v ((final N s l).known v) := by
  obtain ⟨⟨hO, hK, -⟩, hT⟩ := final_spec (s := s) hl
  unfold InOrder at hO
  rw [hT, List.append_nil] at hO
  have hall : ∀ {p w}, N.IsPath s p w → Through N (final N s l).done s p := fun hp x hx =>
    hO.1.mem_iff.2 (List.mem_range.2 (hp.lt_of_mem hN hs (List.dropLast_subset _ hx)))
  exact ⟨fun p hp _ => (hK v hv).1 p hp (hall hp), fun d hd => by
    obtain ⟨p, hp, -, hc⟩ := (hK v hv).2 d hd
    exact ⟨p, hp, trivial, hc⟩⟩

/-! ## A vertex that can be reached has a path -/

theorem exists_take_ends {u : ℕ} {p : List ℕ} {v c : ℕ} (h : N.ends u p = some v)
    (hc : c ∈ N.visits u p) : ∃ k, N.ends u (p.take k) = some c := by
  induction p generalizing u with
  | nil =>
    simp only [visits, List.map_nil, List.mem_singleton] at hc
    exact ⟨0, by simp [ends, hc]⟩
  | cons j p ih =>
    simp only [ends] at h
    split at h
    · rename_i a b hj
      split_ifs at h with hau
      subst hau
      have hv : N.visits a (j :: p) = a :: N.visits b p := by
        simp [visits, target_eq hj]
      rw [hv] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨0, by simp [ends]⟩
      · obtain ⟨k, hk⟩ := ih h hc
        exact ⟨k + 1, by simp [ends, hj, hk]⟩
    · exact absurd h (by simp)

/-- **A vertex that can be reached has a path to it**: cut a walk at the first return to its end. -/
theorem exists_isPath_of_reaches {u v : ℕ} (h : N.g.Reaches u v) : ∃ p, N.IsPath u p v := by
  induction h with
  | refl => exact ⟨[], isPath_nil _⟩
  | @tail b c _ hbc ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (show (b, c) ∈ N.g.arrows from hbc)
    by_cases hcq : c ∈ N.visits u q
    · obtain ⟨k, hk⟩ := exists_take_ends hq.1 hcq
      refine ⟨q.take k, hk, ?_⟩
      have : N.visits u (q.take k) = (N.visits u q).take (k + 1) := by
        simp [visits, List.map_take]
      rw [this]
      exact (List.take_sublist _ _).nodup hq.2
    · exact ⟨_, (hq.snoc hi hcq).1⟩

/-! ## The promise -/

theorem dagPaths_ok {a : Answer} (h : dagPaths N s = .ok a) :
    ∃ l, TopoOrder.kahn N.g = .ok l ∧ a = answer (final N s l) := by
  unfold dagPaths at h
  cases hk : TopoOrder.kahn N.g with
  | error t => rw [hk] at h; cases h
  | ok l =>
    rw [hk] at h
    exact ⟨l, rfl, (Except.ok.inj h).symm⟩

theorem isTopoOrder_of_kahn (hN : N.WellFormed) {l : List ℕ} (hk : TopoOrder.kahn N.g = .ok l) :
    TopoOrder.IsTopoOrder N.g l := by
  have := TopoOrder.kahn_spec hN.1
  rw [hk] at this
  exact this

theorem dagPaths_reached (hN : N.WellFormed) (hs : s < N.g.n) {a : Answer}
    (h : dagPaths N s = .ok a) {v : ℕ} (hv : v < N.g.n) (hr : N.g.Reaches s v) :
    ∃ d, a.cost v = some d ∧ N.Cheapest s v (some d) := by
  obtain ⟨l, hk, rfl⟩ := dagPaths_ok h
  have hc := final_cheapest hN hs (isTopoOrder_of_kahn hN hk) hv
  obtain ⟨p, hp⟩ := exists_isPath_of_reaches hr
  cases hd : (final N s l).known v with
  | none =>
    have := hc.1 p hp trivial
    rw [hd] at this
    exact absurd this id
  | some d => exact ⟨d, hd, hd ▸ hc⟩

theorem dagPaths_previous (hN : N.WellFormed) {a : Answer} (h : dagPaths N s = .ok a) {v : ℕ}
    (hv : v < N.g.n) : ∀ d ∈ a.cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
      LeadsBack a.prev s (N.visits s p) := by
  intro d hd
  obtain ⟨l, hk, rfl⟩ := dagPaths_ok h
  obtain ⟨p, hp, hc, -, hl⟩ := (final_spec (s := s) (isTopoOrder_of_kahn hN hk)).1.2.2.2 v hv d hd
  exact ⟨p, hp, hc, hl⟩

theorem dagPaths_unreached (hN : N.WellFormed) {a : Answer} (h : dagPaths N s = .ok a) {v : ℕ}
    (hv : v < N.g.n) (hr : ¬ N.g.Reaches s v) : a.cost v = none := by
  by_contra hne
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨p, hp, -⟩ := dagPaths_previous hN h hv d hd
  exact hr (reaches_of_ends hp.1)

theorem dagPaths_stuck (hN : N.WellFormed) {t : List ℕ} (h : dagPaths N s = .error t) :
    TopoOrder.IsStuck N.g t := by
  unfold dagPaths at h
  have := TopoOrder.kahn_spec hN.1
  cases hk : TopoOrder.kahn N.g with
  | ok l => rw [hk] at h; cases h
  | error t' =>
    rw [hk] at h this
    cases h
    exact this

/-! ## The cost -/

/-- **One look at every vertex and every arrow**: over the whole walk, the vertices it takes and
the row entries it walks number at most `n + m`. -/
theorem dagPaths_cost (N : Network) (s : ℕ) {l : List ℕ} (hl : TopoOrder.IsTopoOrder N.g l) :
    looks N (final N s l) ≤ N.g.n + N.g.arrows.length := by
  obtain ⟨⟨hO, -⟩, hT⟩ := final_spec (N := N) (s := s) hl
  unfold InOrder at hO
  rw [hT, List.append_nil] at hO
  unfold looks
  set done := (final N s l).done
  have hlen : done.length = N.g.n := by simpa using hO.1.length_eq
  have hsum : (done.map fun v => (N.g.out v).length + 1).sum =
      (done.map fun v => (N.g.out v).length).sum + done.length := by
    clear_value done
    clear hO hlen
    induction done with
    | nil => simp
    | cons b L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  have hle := TopoOrder.sum_countP_le N.g.n N.g.arrows done hO.nodup
  simp only [← TopoOrder.length_out] at hle
  omega

end AlgoDesign.Paths.DagOrder
