/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkFacts

/-!
# Algorithm T: the walk's whole invariant

`Inv` holds the three box invariants (`Valid`) together with the facts about the depth-first walk
their proofs use (Tarjan–Zwick 2024, §2 and §3): the entry numbers count the vertices entered, are
different and grow up the current path; a vertex is entered exactly when it is on the path or has
finished; the arrows of a finished vertex, and those of a vertex on the path up to where it has got,
have been come back over; every vertex on the path reaches every vertex entered after it (the
vertices entered after it are its descendants); a finished vertex whose group is not out has its low
value below its entry number; a group out reaches only groups out no later; a
finished vertex whose group is not out shares its strong component with a vertex on the path; the
first-entered member of the component of a vertex on the path is on the path; a vertex on the path
leads exactly while its low value is its entry number; the climb-back number of an arrow's tail is
at most the entry number of its head (when the two reach each other), and at most the climb-back
number of every finished descendant whose branch the walk has come back from.

The rest of this file derives what the steps need from `Inv`: a vertex on the path has no finished
leader, a vertex is out exactly when its leader has finished, and from an entered vertex every
vertex reachable is entered or reached through a vertex on the path.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-- The vertices of the current path, the current vertex first. -/
def vertices (w : Walk) : List ℕ := w.path.map Prod.fst

/-- The first `k` arrows of `v`'s row have been come back over. -/
def RowRetreated (g : Digraph) (log : List (ℕ × ℕ)) (v k : ℕ) : Prop :=
  ∀ j < k, ∀ e, (g.out v)[j]? = some e → (v, e.1) ∈ log

/-- **The frames, current first, are where the walk left them.** Each frame's position is within
its row and every arrow before it has been come back over, except that below the current frame
the last arrow looked at leads to the vertex of the frame just above (`above`), and the walk has
not yet come back over it. -/
def FramesRetreated (g : Digraph) (log : List (ℕ × ℕ)) : Option ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | none, (v, i) :: rest =>
    i ≤ (g.out v).length ∧ RowRetreated g log v i ∧ FramesRetreated g log (some v) rest
  | some x, (v, i) :: rest =>
    0 < i ∧ i ≤ (g.out v).length ∧ ((g.out v)[i - 1]?).map Prod.fst = some x ∧
      RowRetreated g log v (i - 1) ∧ FramesRetreated g log (some v) rest

/-- `x` is a finished descendant of `z` whose branch the walk has come back from: `x` was entered
after `z`, and either `z` has finished after `x`, or `z` is on the path and `x` was entered before
the vertex above `z` on the path. -/
def Folded (w : Walk) (z x : ℕ) : Prop :=
  w.pre z < w.pre x ∧ ((z ∈ w.finished ∧ [x, z].Sublist w.finished) ∨
    (z ∈ vertices w ∧ ∀ p ∈ vertices w, w.pre z < w.pre p → w.pre x < w.pre p))

/-- **Algorithm T's whole invariant**: the box's three (`valid`), and the facts about the walk
their proofs use. -/
structure Inv (g : Digraph) (w : Walk) : Prop where
  graph : w.g = g
  valid : Valid w
  lt_n : ∀ v, w.pre v ≠ 0 → v < g.n
  pre_le : ∀ v, w.pre v ≤ w.time
  pre_inj : ∀ u v, w.pre u ≠ 0 → w.pre u = w.pre v → u = v
  time_eq : w.time = (List.range g.n).countP fun v => w.pre v ≠ 0
  low_zero : ∀ v, w.low v = 0 ↔ w.pre v = 0
  entered : ∀ v, w.pre v ≠ 0 ↔ v ∈ vertices w ∨ v ∈ w.finished
  path_fin : ∀ v ∈ vertices w, v ∉ w.finished
  fin_nodup : w.finished.Nodup
  sorted : (vertices w).Pairwise fun a b => w.pre b < w.pre a
  frames : FramesRetreated g w.retreats none w.path
  fin_rows : ∀ x ∈ w.finished, RowRetreated g w.retreats x (g.out x).length
  retreat_ent : ∀ a ∈ w.retreats, w.pre a.1 ≠ 0 ∧ w.pre a.2 ≠ 0
  roots : ∀ r < w.next, w.pre r ≠ 0
  reach : ∀ p ∈ vertices w, ∀ x, w.pre x ≠ 0 → w.pre p ≤ w.pre x → g.Reaches p x
  out_fin : ∀ v ∈ w.groups.flatten, v ∈ w.finished
  out_closed : ∀ x ∈ w.groups.flatten, ∀ y, g.Reaches x y →
    y ∈ w.groups.flatten ∧ w.emitted y ≤ w.emitted x
  grp_idx : ∀ i (h : i < w.groups.length), ∀ v ∈ w.groups[i], w.emitted v = i
  grp_ne : ∀ m ∈ w.groups, m ≠ []
  grp_nodup : ∀ m ∈ w.groups, m.Nodup
  grp_sub : ∀ m ∈ w.groups, m.Sublist w.finished
  open_low : ∀ v ∈ w.finished, v ∉ w.groups.flatten → w.low v < w.pre v
  lead_iff : ∀ v ∈ vertices w, w.lead v = true ↔ w.low v = w.pre v
  open_gray : ∀ x ∈ w.finished, x ∉ w.groups.flatten → ∃ q ∈ vertices w, Mutual g q x
  gray_min : ∀ p ∈ vertices w, ∀ u, w.pre u ≠ 0 → Mutual g u p →
    ∃ q ∈ vertices w, Mutual g q p ∧ w.pre q ≤ w.pre u
  fin_split : ∀ p ∈ vertices w, w.finished =
    w.finished.filter (fun x => w.pre x < w.pre p) ++ w.finished.filter (fun x => w.pre p < w.pre x)
  retreat_low : ∀ a ∈ w.retreats, Mutual g a.1 a.2 → climbBack (g := g) w a.1 ≤ w.pre a.2
  folded : ∀ z x, x ∈ w.finished → w.pre z ≠ 0 → Folded w z x → Mutual g z x →
    climbBack (g := g) w z ≤ climbBack (g := g) w x

/-! ## What `Inv` gives -/

section Derived

variable {w : Walk} (h : Inv g w)
include h

theorem Inv.fin_entered {v : ℕ} (hv : v ∈ w.finished) : w.pre v ≠ 0 :=
  (h.entered v).2 (Or.inr hv)

theorem Inv.path_entered {v : ℕ} (hv : v ∈ vertices w) : w.pre v ≠ 0 :=
  (h.entered v).2 (Or.inl hv)

theorem Inv.out_entered {v : ℕ} (hv : v ∈ w.groups.flatten) : w.pre v ≠ 0 :=
  h.fin_entered (h.out_fin v hv)

theorem Inv.leaderOut_iff {v : ℕ} (hv : v < g.n) :
    LeaderOut (g := g) w v ↔ v ∈ w.groups.flatten := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  exact ((hval.2.2.1 v hv).2).symm

theorem Inv.low_done_iff {v : ℕ} (hv : v < g.n) : w.low v = done g ↔ v ∈ w.groups.flatten := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  exact ((hval.2.2.1 v hv).1).trans (h.leaderOut_iff hv)

/-- A vertex on the path has no finished leader: the first-entered member of its component is on
the path. -/
theorem Inv.not_leaderOut_of_path {p : ℕ} (hp : p ∈ vertices w) : ¬ LeaderOut (g := g) w p := by
  rintro ⟨u, hu, hup, huf, hmin⟩
  obtain ⟨q, hq, hqp, hqu⟩ := h.gray_min p hp u (h.fin_entered huf) hup
  have hqn : q < g.n := h.lt_n q (h.path_entered hq)
  rcases hmin q hqn hqp with h0 | h1
  · exact h.path_entered hq h0
  · have : q = u := h.pre_inj q u (h.path_entered hq) (by omega)
    subst this
    exact h.path_fin q hq huf

theorem Inv.not_out_of_path {p : ℕ} (hp : p ∈ vertices w) : p ∉ w.groups.flatten := fun ho =>
  h.not_leaderOut_of_path hp ((h.leaderOut_iff (h.lt_n p (h.path_entered hp))).2 ho)

/-- An entered vertex whose group is not out has its low value at its climb-back number. -/
theorem Inv.low_eq {v : ℕ} (hv : w.pre v ≠ 0) (ho : v ∉ w.groups.flatten) :
    w.low v = climbBack (g := g) w v := by
  have hn := h.lt_n v hv
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  exact hval.2.1 v hn hv fun hl => ho ((h.leaderOut_iff hn).1 hl)

/-- Every arrow of a finished vertex leads to an entered vertex. -/
theorem Inv.entered_of_fin_arrow (hg : g.WellFormed) {x y : ℕ} (hx : x ∈ w.finished)
    (hxy : g.Arrow x y) : w.pre y ≠ 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hxy
  have hm : (y, i) ∈ g.out x := mem_out.2 ⟨(hg _ (List.mem_of_getElem? hi)).2, hi⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
  have hjl : j < (g.out x).length := (List.getElem?_eq_some_iff.1 hj).1
  exact (h.retreat_ent _ (h.fin_rows x hx j hjl _ hj)).2

/-- From an entered vertex, every vertex reachable is entered, or reachable through a vertex on the
path. -/
theorem Inv.entered_or_path (hg : g.WellFormed) {u z : ℕ} (hu : w.pre u ≠ 0)
    (huz : g.Reaches u z) : w.pre z ≠ 0 ∨ ∃ p ∈ vertices w, g.Reaches u p := by
  induction huz with
  | refl => exact Or.inl hu
  | tail hux hxy ih =>
    rename_i x y
    rcases ih with hx | hp
    · rcases (h.entered x).1 hx with hx | hx
      · exact Or.inr ⟨x, hx, hux⟩
      · exact Or.inl (h.entered_of_fin_arrow hg hx hxy)
    · exact Or.inr hp

theorem Inv.time_le : w.time ≤ g.n := by
  rw [h.time_eq]
  exact List.countP_le_length.trans (by simp)

theorem Inv.time_lt {x : ℕ} (hx : x < g.n) (h0 : w.pre x = 0) : w.time < g.n := by
  rw [h.time_eq, List.countP_eq_length_filter]
  have := (List.length_filter_lt_length_iff_exists
    (p := fun v => decide (w.pre v ≠ 0)) (l := List.range g.n)).2
    ⟨x, List.mem_range.2 hx, by simp [h0]⟩
  simpa using this

theorem Inv.pre_le_n (v : ℕ) : w.pre v ≤ g.n := (h.pre_le v).trans h.time_le

/-- The current vertex was entered last of the vertices on the path. -/
theorem Inv.pre_lt_top {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest) {p : ℕ}
    (hp : p ∈ rest.map Prod.fst) : w.pre p < w.pre v := by
  have := h.sorted
  simp only [vertices, hs, List.map_cons, List.pairwise_cons] at this
  exact this.1 p hp

theorem Inv.pre_le_top {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest) {p : ℕ}
    (hp : p ∈ vertices w) : w.pre p ≤ w.pre v := by
  simp only [vertices, hs, List.map_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact le_rfl
  · exact (h.pre_lt_top hs hp).le

theorem Inv.top_not_mem_rest {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest) :
    v ∉ rest.map Prod.fst := fun hv => lt_irrefl _ (h.pre_lt_top hs hv)

/-- A vertex whose group is out is not on the path. -/
theorem Inv.low_lt_done {v : ℕ} (hv : w.pre v ≠ 0) (ho : v ∉ w.groups.flatten) :
    w.low v < done g := by
  rw [h.low_eq hv ho]
  have := climbBack_le_pre (g := g) w v
  have := h.pre_le_n v
  unfold done
  omega

end Derived

theorem LeaderOut.of_mutual {w : Walk} {v y : ℕ} (hl : LeaderOut (g := g) w v)
    (hvy : Mutual g v y) : LeaderOut (g := g) w y := by
  obtain ⟨u, hu, huv, huf, hmin⟩ := hl
  exact ⟨u, hu, huv.trans hvy, huf, fun x hx hxy => hmin x hx (hxy.trans hvy.symm)⟩

/-! ## The start -/

theorem inv_start (g : Digraph) : Inv g (start g) where
  graph := rfl
  valid := valid_start g
  lt_n _ h := absurd rfl h
  pre_le _ := le_rfl
  pre_inj _ _ h := absurd rfl h
  time_eq := by simp [start]
  low_zero _ := by simp [start]
  entered _ := by simp [start, vertices]
  path_fin _ h := by simp [start, vertices] at h
  fin_nodup := List.nodup_nil
  sorted := List.Pairwise.nil
  frames := trivial
  fin_rows _ h := by simp [start] at h
  retreat_ent _ h := by simp [start] at h
  roots _ h := by simp [start] at h
  reach _ h := by simp [start, vertices] at h
  out_fin _ h := by simp [start] at h
  out_closed _ h := by simp [start] at h
  grp_idx _ h := by simp [start] at h
  grp_ne _ h := by simp [start] at h
  grp_nodup _ h := by simp [start] at h
  grp_sub _ h := by simp [start] at h
  open_low _ h := by simp [start] at h
  lead_iff _ h := by simp [start, vertices] at h
  open_gray _ h := by simp [start] at h
  gray_min _ h := by simp [start, vertices] at h
  fin_split _ h := by simp [start, vertices] at h
  retreat_low _ h := by simp [start] at h
  folded _ _ h := by simp [start] at h

end AlgorithmT

end AlgoDesign.Graphs.Scc
