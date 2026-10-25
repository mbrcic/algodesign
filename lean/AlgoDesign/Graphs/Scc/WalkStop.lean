/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkPostorder

/-!
# Algorithm T: the stop when done

Tarjan–Zwick p. 12: once every vertex has been entered and the current vertex's low value equals
the root's, everything not yet out is one whole group, the root's strong component
(`mem_stopGroup_iff`). The current vertex gets back to the root, since its low value is the root's
entry number; every vertex on the path lies between the two, so it shares their component; every
vertex waiting on the open list shares its component with a vertex on the path; and every vertex of
the root's component is waiting or on the path, because every vertex has been entered and no group
out holds a vertex that reaches the root. So the stopped walk keeps the box's three invariants
(`valid_stopAll`), and its vertices finish in the order the moves alone finish them
(`finished_runMove_of_all`), which is `finishOrder`.

Up to the step at which it stops, the walk is the run of moves; after it, the walk stands still
(`run_cases`). At its end it holds what the proof of correctness reads (`Ends`, `ends_final`), and
every state of it is `Valid` (`validAlong`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-! ## The run with the stop -/

theorem run_succ (k : ℕ) (w : Walk) : run g (k + 1) w = step g (run g k w) := by
  rw [run_eq_iterate, run_eq_iterate, Function.iterate_succ_apply']

theorem runMove_succ : ∀ (k : ℕ) (w : Walk), runMove g (k + 1) w = move g (runMove g k w)
  | 0, _ => rfl
  | k + 1, w => runMove_succ k (move g w)

/-- The group the stop takes out: the open list from its bottom, then the path from the top
down. -/
def stopGroup (w : Walk) : List ℕ := w.followers.dropLast.reverse ++ vertices w

section StopFields

variable (w : Walk)

@[simp] theorem stopAll_pre : (stopAll g w).pre = w.pre := rfl
@[simp] theorem stopAll_path : (stopAll g w).path = [] := rfl
@[simp] theorem stopAll_next : (stopAll g w).next = g.n := rfl
@[simp] theorem stopAll_followers : (stopAll g w).followers = [guard g] := rfl
@[simp] theorem stopAll_finished : (stopAll g w).finished = w.finished ++ vertices w := rfl
@[simp] theorem stopAll_groups : (stopAll g w).groups = w.groups ++ [stopGroup w] := rfl
@[simp] theorem stopAll_low (u : ℕ) :
    (stopAll g w).low u = if u ∈ stopGroup w then done g else w.low u := rfl
@[simp] theorem stopAll_emitted (u : ℕ) :
    (stopAll g w).emitted u = if u ∈ stopGroup w then w.groups.length else w.emitted u := rfl

end StopFields

/-- After the stop, a step changes nothing. -/
theorem step_stopAll (w : Walk) : step g (stopAll g w) = stopAll g w := by
  simp [step, stops, move]

theorem run_stopAll (w : Walk) : ∀ k, run g k (stopAll g w) = stopAll g w
  | 0 => rfl
  | k + 1 => by simp only [run, step_stopAll, run_stopAll w k]

/-- **The walk is the run of moves until a move calls for the stop, and then stands still.** -/
theorem run_cases (w : Walk) : ∀ k, run g k w = runMove g k w ∨
    ∃ j < k, stops g (runMove g j w) (runMove g (j + 1) w) = true ∧
      run g k w = stopAll g (runMove g (j + 1) w)
  | 0 => Or.inl rfl
  | k + 1 => by
    rw [run_succ]
    rcases run_cases w k with h | ⟨j, hj, hs, h⟩
    · rw [h, runMove_succ]
      by_cases hs : stops g (runMove g k w) (move g (runMove g k w)) = true
      · exact Or.inr ⟨k, by omega, by rw [runMove_succ]; exact hs,
          by simp [step, hs, runMove_succ]⟩
      · left
        simp [step, hs]
    · rw [h, step_stopAll]
      exact Or.inr ⟨j, by omega, hs, rfl⟩

theorem doneAtRoot_iff {w : Walk} : doneAtRoot g w = true ↔ ∃ v i rest, w.path = (v, i) :: rest ∧
    w.time = g.n ∧ w.low v = w.low (rest.getLastD (v, i)).1 := by
  unfold doneAtRoot
  split <;> simp_all

/-- A move that calls for the stop leaves the walk with every vertex entered and the current
vertex back at the root's low value. -/
theorem doneAtRoot_of_stops {w w' : Walk} (hs : stops g w w' = true) : doneAtRoot g w' = true := by
  unfold stops at hs
  split at hs <;> simp_all

/-- The last frame of a path whose entry numbers fall from the top holds the least of them. -/
theorem le_getLastD (f : ℕ → ℕ) : ∀ (l : List (ℕ × ℕ)) (a : ℕ × ℕ),
    ((a :: l).map Prod.fst).Pairwise (fun x y => f y < f x) →
    ∀ p ∈ (a :: l).map Prod.fst, f (l.getLastD a).1 ≤ f p
  | [], a, _, p, hp => by
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hp
    subst hp
    exact le_rfl
  | b :: l, a, hs, p, hp => by
    rw [List.getLastD_cons]
    rw [List.map_cons, List.pairwise_cons] at hs
    rw [List.map_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (hs.1 _ (List.mem_map_of_mem List.getLastD_mem_cons)).le
    · exact le_getLastD f l b hs.2 p hp

/-! ## Everything not yet out is the root's component -/

section Stop

variable {w : Walk} (h : Inv g w) {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest)
include h hs

omit h in
theorem root_mem_vertices : (rest.getLastD (v, i)).1 ∈ vertices w := by
  rw [vertices, hs]
  exact List.mem_map_of_mem List.getLastD_mem_cons

theorem Inv.root_le {p : ℕ} (hp : p ∈ vertices w) : w.pre (rest.getLastD (v, i)).1 ≤ w.pre p := by
  have hsort := h.sorted
  rw [vertices, hs] at hsort hp
  exact le_getLastD w.pre rest (v, i) hsort p hp

/-- The root's low value is its entry number: nothing in its component was entered before it. -/
theorem Inv.low_root : w.low (rest.getLastD (v, i)).1 = w.pre (rest.getLastD (v, i)).1 := by
  set r := (rest.getLastD (v, i)).1
  have hrp : r ∈ vertices w := root_mem_vertices hs
  rw [h.low_eq (h.path_entered hrp) (h.not_out_of_path hrp)]
  refine le_antisymm (climbBack_le_pre _ _) (le_climbBack_iff.2 ⟨le_rfl, fun x hx => ?_⟩)
  have hx0 : w.pre x ≠ 0 := by
    rcases head_of_mem_reachList hx with rfl | ⟨a, ha⟩
    · exact h.path_entered hrp
    · exact (h.retreat_ent _ ha).2
  obtain ⟨q, hq, -, hqx⟩ :=
    h.gray_min r hrp x hx0 (mutual_of_mem_reachList hx).symm
  exact (h.root_le hs hq).trans hqx

variable (hl : w.low v = w.low (rest.getLastD (v, i)).1)
include hl

/-- **The current vertex shares the root's component**: its climb-back number is the root's entry
number. -/
theorem Inv.mutual_top_root : Mutual g v (rest.getLastD (v, i)).1 := by
  set r := (rest.getLastD (v, i)).1
  have hrp : r ∈ vertices w := root_mem_vertices hs
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hr0 := h.path_entered hrp
  have hlv : climbBack (g := g) w v = w.pre r := by
    rw [← h.low_eq (h.path_entered hvp) (h.not_out_of_path hvp), hl, h.low_root hs]
  rcases exists_climbBack (g := g) w v with h1 | ⟨x, hx, h1⟩
  · have : v = r := h.pre_inj v r (h.path_entered hvp) (h1.symm.trans hlv)
    rw [this]
    exact mutual_refl _
  · have : x = r := h.pre_inj x r (by rw [← h1, hlv]; exact hr0) (h1.symm.trans hlv)
    rw [← this]
    exact mutual_of_mem_reachList hx

theorem Inv.mutual_path_root {p : ℕ} (hp : p ∈ vertices w) :
    Mutual g p (rest.getLastD (v, i)).1 := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hrp := root_mem_vertices hs
  exact ⟨ReflTransGen.trans
      (h.reach p hp v (h.path_entered hvp) (h.pre_le_top hs hp)) (h.mutual_top_root hs hl).1,
    h.reach _ hrp p (h.path_entered hp) (h.root_le hs hp)⟩

end Stop

section Group

variable {w : Walk} (h : Inv g w)
include h

/-- The open list above the guard, from its bottom: the finished vertices whose group is not out,
in the order they finished. -/
theorem Inv.waiting_eq :
    w.followers.dropLast.reverse = w.finished.filter fun v => v ∉ w.groups.flatten := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  rw [hval.1, List.dropLast_concat, List.reverse_reverse]

theorem Inv.stopGroup_eq :
    stopGroup w = (w.finished.filter fun v => v ∉ w.groups.flatten) ++ vertices w := by
  rw [stopGroup, h.waiting_eq]

theorem Inv.not_out_of_stopGroup {x : ℕ} (hx : x ∈ stopGroup w) : x ∉ w.groups.flatten := by
  rw [h.stopGroup_eq] at hx
  rcases List.mem_append.1 hx with hx | hx
  · simpa using (List.mem_filter.1 hx).2
  · exact h.not_out_of_path hx

theorem Inv.lt_n_of_stopGroup {x : ℕ} (hx : x ∈ stopGroup w) : x < g.n := by
  rw [h.stopGroup_eq] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact h.lt_n x (h.fin_entered (List.mem_filter.1 hx).1)
  · exact h.lt_n x (h.path_entered hx)

theorem Inv.all_entered (ht : w.time = g.n) : ∀ u < g.n, w.pre u ≠ 0 := by
  intro u hu
  have hc := h.time_eq
  rw [ht] at hc
  have := List.countP_eq_length.1 (by rw [List.length_range]; exact hc.symm) u
    (List.mem_range.2 hu)
  simpa using this

/-- With every vertex entered, each is out already or in the group the stop takes out. -/
theorem Inv.out_or_stopGroup (ht : w.time = g.n) {u : ℕ} (hu : u < g.n) :
    u ∈ w.groups.flatten ∨ u ∈ stopGroup w := by
  rw [h.stopGroup_eq]
  rcases (h.entered u).1 (h.all_entered ht u hu) with hp | hf
  · exact Or.inr (List.mem_append_right _ hp)
  · by_cases ho : u ∈ w.groups.flatten
    · exact Or.inl ho
    · exact Or.inr (List.mem_append_left _ (List.mem_filter.2 ⟨hf, by simpa using ho⟩))

end Group

section StopGroup

variable {w : Walk} (h : Inv g w) {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest)
  (ht : w.time = g.n) (hl : w.low v = w.low (rest.getLastD (v, i)).1)
include h hs ht hl

/-- **The group the stop takes out is the root's whole strong component.** -/
theorem Inv.mem_stopGroup_iff (x : ℕ) :
    x ∈ stopGroup w ↔ x < g.n ∧ Mutual g x (rest.getLastD (v, i)).1 := by
  set r := (rest.getLastD (v, i)).1
  have hrp : r ∈ vertices w := root_mem_vertices hs
  constructor
  · intro hx
    refine ⟨h.lt_n_of_stopGroup hx, ?_⟩
    rw [h.stopGroup_eq] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨hf, ho⟩ := List.mem_filter.1 hx
      obtain ⟨q, hq, hqx⟩ := h.open_gray x hf (by simpa using ho)
      exact hqx.symm.trans (h.mutual_path_root hs hl hq)
    · exact h.mutual_path_root hs hl hx
  · rintro ⟨hx, hxr⟩
    rcases h.out_or_stopGroup ht hx with ho | hg
    · exact absurd (h.out_closed x ho r hxr.1).1 (h.not_out_of_path hrp)
    · exact hg

end StopGroup

/-! ## The stopped walk -/

/-- Among the vertices with a property, one has the least value of `f`. -/
theorem exists_min_of (f : ℕ → ℕ) (P : ℕ → Prop) :
    ∀ k u, f u ≤ k → P u → ∃ x, P x ∧ ∀ y, P y → f x ≤ f y
  | 0, u, hk, hu => ⟨u, hu, fun y _ => by omega⟩
  | k + 1, u, hk, hu => by
    by_cases hmin : ∀ y, P y → f u ≤ f y
    · exact ⟨u, hu, hmin⟩
    · obtain ⟨y, hy⟩ := Classical.not_forall.1 hmin
      have hPy : P y := Classical.byContradiction fun hn => hy fun hp => absurd hp hn
      have hlt : ¬ f u ≤ f y := fun hle => hy fun _ => hle
      exact exists_min_of f P k y (by omega) hPy

section Stopped

variable {w : Walk} (h : Inv g w) (hst : doneAtRoot g w = true)
include h hst

omit h in
theorem time_of_stops : w.time = g.n := by
  obtain ⟨v, i, rest, -, ht, -⟩ := doneAtRoot_iff.1 hst
  exact ht

theorem Inv.out_stopAll {u : ℕ} (hu : u < g.n) : u ∈ (stopAll g w).groups.flatten := by
  simp only [stopAll_groups, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.mem_append]
  exact h.out_or_stopGroup (time_of_stops hst) hu

/-- After the stop every vertex's leader has finished. -/
theorem Inv.leaderOut_stopAll {u : ℕ} (hu : u < g.n) : LeaderOut (g := g) (stopAll g w) u := by
  have hall := h.all_entered (time_of_stops hst)
  obtain ⟨x, ⟨hx, hxu⟩, hmin⟩ :=
    exists_min_of w.pre (fun x => x < g.n ∧ Mutual g x u) _ u le_rfl ⟨hu, mutual_refl u⟩
  refine ⟨x, hx, hxu, ?_, fun y hy hyu => Or.inr (hmin y ⟨hy, hyu⟩)⟩
  rw [stopAll_finished]
  rcases (h.entered x).1 (hall x hx) with hp | hf
  · exact List.mem_append_right _ hp
  · exact List.mem_append_left _ hf

/-- **The stopped walk keeps the box's three invariants.** -/
theorem valid_stopAll : Valid (stopAll g w) := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  obtain ⟨v, i, rest, hs, ht, hl⟩ := doneAtRoot_iff.1 hst
  have hg' : (stopAll g w).g = g := by simp [h.graph]
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut
  rw [hg']
  refine ⟨?_, fun u hu _ hno => absurd (h.leaderOut_stopAll hst hu) hno, ?_, ?_⟩
  · -- 1: nothing waits
    rw [stopAll_followers, List.filter_eq_nil_iff.2, List.reverse_nil, List.nil_append]
    intro a ha
    have ha0 : w.pre a ≠ 0 := by
      rw [stopAll_finished] at ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h.fin_entered ha
      · exact h.path_entered ha
    exact fun hc => of_decide_eq_true hc (h.out_stopAll hst (h.lt_n a ha0))
  · intro u hu
    refine ⟨iff_of_true ?_ (h.leaderOut_stopAll hst hu),
      iff_of_true (h.out_stopAll hst hu) (h.leaderOut_stopAll hst hu)⟩
    rw [stopAll_low]
    split_ifs with hg'
    · rfl
    · rcases h.out_or_stopGroup ht hu with ho | ho
      · exact (h.low_done_iff hu).2 ho
      · exact absurd ho hg'
  · intro m hm u hu x hx
    rw [stopAll_groups, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact hval.2.2.2 m hm u hu x hx
    · have hu' := (h.mem_stopGroup_iff hs ht hl u).1 hu
      rw [h.mem_stopGroup_iff hs ht hl x]
      exact ⟨fun hxr => hxr.2.trans hu'.2.symm, fun hxu => ⟨hx, hxu.trans hu'.2⟩⟩

end Stopped

/-! ## The order vertices finish in after the stop -/

/-- With every vertex entered, a move keeps the entry numbers, and the vertices finished followed by
the path from the top down. -/
theorem move_of_all {w : Walk} (h : Inv g w) (hall : ∀ u < g.n, w.pre u ≠ 0) :
    (move g w).pre = w.pre ∧
      (move g w).finished ++ vertices (move g w) = w.finished ++ vertices w := by
  rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
  · obtain ⟨gw, t, lo, le, pa, fo, gr, em, ne, pr, fi, re⟩ := w
    simp only at hs
    subst hs
    simp only [move]
    split_ifs with hn hl
    · exact absurd ((h.low_zero _).1 hl) (hall _ hn)
    · simp [vertices]
    · simp
  · rcases hi : (g.out v)[i]? with _ | ⟨x, id⟩
    · simp only [move, hs, hi]
      rcases rest with _ | ⟨⟨u, j⟩, rest'⟩
      · simp [postvisit_pre, postvisit_finished, postvisit_path, vertices, hs]
      · simp [postvisit_pre, postvisit_finished, postvisit_path, vertices, hs]
    · simp only [move, hs, hi]
      have hx : w.low x ≠ 0 := (h.low_zero x).not.2 (hall x (lt_of_out hi))
      simp [hx, vertices, hs]

theorem finished_runMove_of_all (hg : g.WellFormed) : ∀ (k : ℕ) {w : Walk}, Inv g w →
    (∀ u < g.n, w.pre u ≠ 0) →
    (runMove g k w).finished ++ vertices (runMove g k w) = w.finished ++ vertices w
  | 0, _, _, _ => rfl
  | k + 1, w, h, hall => by
    obtain ⟨hp, hf⟩ := move_of_all h hall
    rw [show runMove g (k + 1) w = runMove g k (move g w) from rfl,
      finished_runMove_of_all hg k (inv_step hg h) (by rw [hp]; exact hall), hf]

/-- **Stopped at a state of the moves, the vertices finish in `finishOrder`.** -/
theorem finishOrder_of_stop (hg : g.WellFormed) {j : ℕ} (hj : j ≤ steps g)
    (ht : (runMove g j (start g)).time = g.n) :
    (runMove g j (start g)).finished ++ vertices (runMove g j (start g)) = finishOrder g := by
  have h := inv_run hg j (inv_start g)
  have hfin := finished_runMove_of_all hg (steps g - j) h (h.all_entered ht)
  rw [← run_add, show j + (steps g - j) = steps g by omega] at hfin
  rw [← hfin, show runMove g (steps g) (start g) = finalMove g from rfl, final_finished hg,
    vertices, (final_done hg).1, List.map_nil, List.append_nil]

/-! ## The end of the walk -/

/-- **What holds at the end of the walk**: the box's invariants; the walk is over; every vertex is
in a group out, each group a non-empty list of vertices without repeats, numbered by when it came
out and listed in postorder; and a group out reaches only groups out no later. -/
structure Ends (g : Digraph) (w : Walk) : Prop where
  valid : Valid w
  over : Over g w
  out : ∀ v < g.n, v ∈ w.groups.flatten
  lt_n : ∀ m ∈ w.groups, ∀ v ∈ m, v < g.n
  out_closed : ∀ x ∈ w.groups.flatten, ∀ y, g.Reaches x y →
    y ∈ w.groups.flatten ∧ w.emitted y ≤ w.emitted x
  grp_idx : ∀ i (h : i < w.groups.length), ∀ v ∈ w.groups[i], w.emitted v = i
  grp_ne : ∀ m ∈ w.groups, m ≠ []
  grp_nodup : ∀ m ∈ w.groups, m.Nodup
  grp_sub : ∀ m ∈ w.groups, m.Sublist (finishOrder g)

theorem ends_finalMove (hg : g.WellFormed) : Ends g (finalMove g) where
  valid := (inv_final hg).valid
  over := final_done hg
  out _ hv := final_out hg hv
  lt_n m hm v hv :=
    (inv_final hg).lt_n v ((inv_final hg).fin_entered (((inv_final hg).grp_sub m hm).subset hv))
  out_closed := (inv_final hg).out_closed
  grp_idx := (inv_final hg).grp_idx
  grp_ne := (inv_final hg).grp_ne
  grp_nodup := (inv_final hg).grp_nodup
  grp_sub m hm := final_finished hg ▸ (inv_final hg).grp_sub m hm

/-- **The stopped walk is at its end.** -/
theorem ends_stopAll (hg : g.WellFormed) {w : Walk} (h : Inv g w) (hst : doneAtRoot g w = true)
    (hfin : w.finished ++ vertices w = finishOrder g) : Ends g (stopAll g w) := by
  obtain ⟨v, i, rest, hs, ht, hl⟩ := doneAtRoot_iff.1 hst
  have hmem := h.mem_stopGroup_iff hs ht hl
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hgrp_lt : ∀ x ∈ stopGroup w, x < g.n := fun x hx => h.lt_n_of_stopGroup hx
  have hold_lt : ∀ x ∈ w.groups.flatten, x < g.n := fun x hx => h.lt_n x (h.out_entered hx)
  have hmem_out : ∀ x, x ∈ (stopAll g w).groups.flatten ↔ x ∈ w.groups.flatten ∨
      x ∈ stopGroup w := by
    intro x
    simp only [stopAll_groups, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append]
  refine ⟨valid_stopAll h hst, ⟨rfl, le_rfl⟩, fun u hu => h.out_stopAll hst hu, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- members are vertices
    intro m hm x hx
    rw [stopAll_groups, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact hold_lt x (List.mem_flatten.2 ⟨m, hm, hx⟩)
    · exact hgrp_lt x hx
  · -- a group out reaches only groups out no later
    intro x hx y hxy
    have hxn : x < g.n := by
      rcases (hmem_out x).1 hx with hx | hx
      · exact hold_lt x hx
      · exact hgrp_lt x hx
    refine ⟨h.out_stopAll hst (lt_of_reaches hg hxn hxy), ?_⟩
    rw [stopAll_emitted, stopAll_emitted]
    rcases (hmem_out x).1 hx with hx' | hx'
    · have hxg : x ∉ stopGroup w := fun hg' => h.not_out_of_stopGroup hg' hx'
      obtain ⟨hyo, hle⟩ := h.out_closed x hx' y hxy
      have hyg : y ∉ stopGroup w := fun hg' => h.not_out_of_stopGroup hg' hyo
      simp only [hxg, hyg, ↓reduceIte]
      exact hle
    · simp only [hx', ↓reduceIte]
      split_ifs with hyg
      · exact le_rfl
      · rcases h.out_or_stopGroup ht (lt_of_reaches hg hxn hxy) with hyo | hyo
        · exact (h.emitted_lt hyo).le
        · exact absurd hyo hyg
  · -- numbered by when they came out
    intro k hk u hu
    rw [stopAll_emitted]
    by_cases hkl : k < w.groups.length
    · have hu' : u ∈ w.groups[k] := by
        simpa [stopAll_groups, List.getElem_append_left hkl] using hu
      have hug : u ∉ stopGroup w := fun hg' =>
        h.not_out_of_stopGroup hg' (List.mem_flatten.2 ⟨_, List.getElem_mem hkl, hu'⟩)
      simp only [hug, ↓reduceIte]
      exact h.grp_idx k hkl u hu'
    · have hk' : k = w.groups.length := by
        simp only [stopAll_groups, List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have hu' : u ∈ stopGroup w := by
        simpa [stopAll_groups] using hu
      simp [hu']
  · -- not empty
    intro m hm
    rw [stopAll_groups, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.grp_ne m hm
    · exact List.ne_nil_of_mem (List.mem_append_right _ hvp)
  · -- no repeats
    intro m hm
    rw [stopAll_groups, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h.grp_nodup m hm
    · rw [h.stopGroup_eq]
      refine List.nodup_append.2 ⟨h.fin_nodup.filter _, ?_, ?_⟩
      · exact h.sorted.imp fun hab hEq => by subst hEq; exact lt_irrefl _ hab
      · intro a ha b hb hab
        subst hab
        exact h.path_fin a hb (List.mem_filter.1 ha).1
  · -- in postorder
    intro m hm
    rw [← hfin]
    rw [stopAll_groups, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact (h.grp_sub m hm).trans (List.sublist_append_left _ _)
    · rw [h.stopGroup_eq]
      exact List.filter_sublist.append (List.Sublist.refl _)

/-- **The walk run to its end is at its end**, whether it stopped early or not. -/
theorem ends_final (hg : g.WellFormed) : Ends g (final g) := by
  unfold final
  rcases run_cases (start g) (steps g) with h | ⟨j, hj, hs, h⟩
  · rw [h]
    exact ends_finalMove hg
  · rw [h]
    have hinv := inv_run hg (j + 1) (inv_start g)
    have hd := doneAtRoot_of_stops hs
    exact ends_stopAll hg hinv hd (finishOrder_of_stop hg hj (time_of_stops hd))

/-- **Every state of the walk keeps the box's three invariants.** -/
theorem valid_run (hg : g.WellFormed) (k : ℕ) : Valid (run g k (start g)) := by
  rcases run_cases (start g) k with h | ⟨j, -, hs, h⟩
  · rw [h]
    exact (inv_run hg k (inv_start g)).valid
  · rw [h]
    exact valid_stopAll (inv_run hg (j + 1) (inv_start g)) (doneAtRoot_of_stops hs)

end AlgorithmT

/-- **Algorithm T keeps its invariants**, proved: every state of the walk on a well-formed graph
is `Valid`. -/
theorem validAlong : ValidAlong := fun _ hg k => AlgorithmT.valid_run hg k

end AlgoDesign.Graphs.Scc
