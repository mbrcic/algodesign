/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkPrevisit

/-!
# Algorithm T: coming back over an arrow keeps the invariant

`inv_retreat`: when the current vertex `v` looks at an arrow to a vertex `x` already entered, the
walk comes back over it at once, and `Inv` holds after. If `v` and `x` reach each other, `x`'s
group is not out and its low value is its climb-back number, so `v`'s new low value is the smaller
of the two, which is `v`'s new climb-back number (Tarjan–Zwick Lemma 3.8, first case). If not,
`x`'s group is out: `x` is neither on the path nor waiting on `F`, since either would put `x` in
`v`'s component; so `x`'s low value is `done`, and `v`'s does not change (Lemma 3.8, second case).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

theorem arrow_of_out {v x id i : ℕ} (h : (g.out v)[i]? = some (x, id)) : g.Arrow v x :=
  List.mem_of_getElem? (mem_out.1 (List.mem_of_getElem? h)).2

theorem lt_of_out {v x id i : ℕ} (h : (g.out v)[i]? = some (x, id)) : x < g.n :=
  (mem_out.1 (List.mem_of_getElem? h)).1

/-- An arrow from the current vertex leads to a vertex in its component, or to one whose group is
out; never both. -/
theorem Inv.mutual_iff_not_out {w : Walk} (h : Inv g w) {v i : ℕ} {rest : List (ℕ × ℕ)}
    (hs : w.path = (v, i) :: rest) {x : ℕ} (hvx : g.Arrow v x) (hx : w.pre x ≠ 0) :
    Mutual g v x ↔ x ∉ w.groups.flatten := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  constructor
  · intro hm ho
    exact h.not_out_of_path hvp (h.out_closed x ho v hm.2).1
  · intro ho
    rcases (h.entered x).1 hx with hxp | hxf
    · exact ⟨reaches_of_arrow hvx, h.reach x hxp v (h.path_entered hvp) (h.pre_le_top hs hxp)⟩
    · obtain ⟨q, hq, hqx⟩ := h.open_gray x hxf ho
      exact ⟨reaches_of_arrow hvx,
        hqx.2.trans (h.reach q hq v (h.path_entered hvp) (h.pre_le_top hs hq))⟩

/-- After a retreat from `v` to `x`, `v`'s low value is its climb-back number, given that it was,
that `x`'s was when they reach each other, and that `x`'s was not smaller when they do not. -/
theorem low_retreat_eq {w : Walk} {v x : ℕ} (hxn : x < g.n) (hv : w.low v = climbBack (g := g) w v)
    (hm : Mutual g v x → w.low x = climbBack (g := g) w x)
    (hnm : ¬ Mutual g v x → w.low v ≤ w.low x) (hvn : v < g.n) :
    (retreat w v x).low v = climbBack (g := g) (retreat w v x) v := by
  simp only [retreat_low_apply, ↓reduceIte]
  by_cases hvx : Mutual g v x
  · rw [climbBack_add_self (retreat_pre w v x) (retreat_retreats w v x) hxn hvx hvn, ← hv,
      ← hm hvx]
  · rw [climbBack_add_of_not_mutual (retreat_pre w v x) (retreat_retreats w v x) hxn hvx, ← hv,
      min_eq_left (hnm hvx)]

/-- A retreat keeps "`v` leads exactly while its low value is its entry number". -/
theorem lead_retreat_iff {w : Walk} {v x : ℕ} (hle : w.low v ≤ w.pre v)
    (hv : w.lead v = true ↔ w.low v = w.pre v) :
    (retreat w v x).lead v = true ↔ (retreat w v x).low v = (retreat w v x).pre v := by
  simp only [retreat_lead_apply, retreat_low_apply, retreat_pre, ↓reduceIte, true_and]
  by_cases hlt : w.low x < w.low v
  · simp only [hlt, ↓reduceIte, Bool.false_eq_true, false_iff]
    omega
  · simp only [hlt, ↓reduceIte, min_eq_left (Nat.le_of_not_lt hlt), hv]

/-- **Coming back over an arrow to an entered vertex keeps the invariant.** -/
theorem inv_retreat {w : Walk} (h : Inv g w) {v i : ℕ}
    {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest) {x id : ℕ}
    (hi : (g.out v)[i]? = some (x, id)) (hx : w.pre x ≠ 0) :
    Inv g (retreat { w with path := (v, i + 1) :: rest } v x) := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  set w0 : Walk := { w with path := (v, i + 1) :: rest } with hw0
  set w' := retreat w0 v x with hw'
  have hvx : g.Arrow v x := arrow_of_out hi
  have hxn : x < g.n := lt_of_out hi
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  have hvn := h.lt_n v hv0
  have hvo := h.not_out_of_path hvp
  have hvertices : vertices w' = vertices w := by simp [hw', hw0, vertices, hs]
  have hpre : w'.pre = w.pre := by simp [hw', hw0]
  have hfin : w'.finished = w.finished := by simp [hw', hw0]
  have hgr : w'.groups = w.groups := by simp [hw', hw0]
  have hlog : w'.retreats = w.retreats ++ [(v, x)] := by simp [hw', hw0]
  have hlow : ∀ y, y ≠ v → w'.low y = w.low y := fun y hy => by
    simp [hw', hw0, retreat_low_apply, hy]
  have hlead : ∀ y, y ≠ v → w'.lead y = w.lead y := fun y hy => by
    simp [hw', hw0, retreat_lead_apply, hy]
  have hcb : ∀ y, y ≠ v → climbBack (g := g) w' y = climbBack (g := g) w y :=
    fun y hy => climbBack_add_of_ne (w := w0) hpre hlog hxn hy
  have hcble : ∀ y, climbBack (g := g) w' y ≤ climbBack (g := g) w y :=
    fun y => climbBack_add_le (w := w0) hpre hlog hxn y
  have hLO : ∀ y, LeaderOut (g := g) w' y ↔ LeaderOut (g := g) w y := by
    intro y
    unfold LeaderOut
    rw [hfin, hpre]
  have hlowv : w'.low v = climbBack (g := g) w' v := by
    refine low_retreat_eq (w := w0) hxn (h.low_eq hv0 hvo) (fun hm => ?_) (fun hm => ?_) hvn
    · exact h.low_eq hx ((h.mutual_iff_not_out hs hvx hx).1 hm)
    · have ho : x ∈ w.groups.flatten := by
        by_contra ho
        exact hm ((h.mutual_iff_not_out hs hvx hx).2 ho)
      exact ((h.low_done_iff hxn).2 ho).symm ▸ (h.low_lt_done hv0 hvo).le
  have hlowv_lt : w'.low v < done g := by
    rw [hlowv]
    have := hcble v
    have := climbBack_le_pre (g := g) w v
    have := h.pre_le_n v
    unfold done
    omega
  have hg' : w'.g = g := by simp [hw', hw0, h.graph]
  refine
    { graph := hg'
      valid := ?_
      lt_n := by rw [hpre]; exact h.lt_n
      pre_le := by rw [hpre]; simpa [hw', hw0] using h.pre_le
      pre_inj := by rw [hpre]; exact h.pre_inj
      time_eq := by rw [hpre]; simpa [hw', hw0] using h.time_eq
      low_zero := ?_
      entered := by rw [hpre, hvertices, hfin]; exact h.entered
      path_fin := by rw [hvertices, hfin]; exact h.path_fin
      fin_nodup := by rw [hfin]; exact h.fin_nodup
      sorted := by rw [hvertices, hpre]; exact h.sorted
      frames := ?_
      fin_rows := ?_
      retreat_ent := ?_
      roots := by rw [hpre]; simpa [hw', hw0] using h.roots
      reach := by rw [hvertices, hpre]; exact h.reach
      out_fin := by rw [hgr, hfin]; exact h.out_fin
      out_closed := by simpa [hw', hw0] using h.out_closed
      grp_idx := by simpa [hw', hw0] using h.grp_idx
      grp_ne := by rw [hgr]; exact h.grp_ne
      grp_nodup := by rw [hgr]; exact h.grp_nodup
      grp_sub := by rw [hgr, hfin]; exact h.grp_sub
      open_low := ?_
      lead_iff := ?_
      open_gray := by rw [hfin, hgr, hvertices]; exact h.open_gray
      gray_min := by rw [hvertices, hpre]; exact h.gray_min
      fin_split := by rw [hvertices, hfin, hpre]; exact h.fin_split
      retreat_low := ?_
      folded := ?_ }
  on_goal 1 =>
    unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut
    rw [hg']
    refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hw', hw0, FollowersInFinishOrder] using hval.1
  · intro y hy hy0 hyl
    by_cases hyv : y = v
    · subst hyv
      exact hlowv
    · rw [hlow y hyv, hcb y hyv]
      exact hval.2.1 y hy (by rwa [hpre] at hy0) fun hl => hyl ((hLO y).2 hl)
  · intro y hy
    rw [hLO y, hgr]
    by_cases hyv : y = v
    · subst hyv
      have := hval.2.2.1 y hy
      refine ⟨⟨fun he => absurd he (Nat.ne_of_lt hlowv_lt), fun hl => ?_⟩, this.2⟩
      exact absurd ((h.leaderOut_iff hy).1 hl) hvo
    · rw [hlow y hyv]
      exact hval.2.2.1 y hy
  · rw [hgr]
    exact hval.2.2.2
  · intro y
    rw [hpre]
    by_cases hyv : y = v
    · subst hyv
      have hmin : w'.low y = min (w.low y) (w.low x) := by
        rw [hw', retreat_low_apply]
        simp only [↓reduceIte, hw0]
      rw [hmin]
      constructor
      · intro h0
        have h1 := (h.low_zero y).not.2 hv0
        have h2 := (h.low_zero x).not.2 hx
        omega
      · intro h0
        exact absurd h0 hv0
    · rw [hlow y hyv]
      exact h.low_zero y
  · have hf := h.frames
    rw [hs] at hf
    rw [hw', retreat_path, retreat_retreats]
    simp only [hw0]
    refine ⟨(List.getElem?_eq_some_iff.1 hi).1, fun j hj e he => ?_,
      hf.2.2.mono fun a ha => List.mem_append_left _ ha⟩
    by_cases hji : j < i
    · exact List.mem_append_left _ (hf.2.1 j hji e he)
    · have : j = i := by omega
      subst this
      rw [hi] at he
      cases he
      simp
  · rw [hfin, hlog]
    exact fun y hy => (h.fin_rows y hy).mono fun a ha => List.mem_append_left _ ha
  · intro a ha
    rw [hlog] at ha
    rw [hpre]
    rcases List.mem_append.1 ha with ha | ha
    · exact h.retreat_ent a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨hv0, hx⟩
  · intro y hy hyo
    rw [hfin] at hy
    rw [hgr] at hyo
    have hyv : y ≠ v := fun he => h.path_fin v hvp (he ▸ hy)
    rw [hlow y hyv, hpre]
    exact h.open_low y hy hyo
  · intro y hy
    rw [hvertices] at hy
    by_cases hyv : y = v
    · subst hyv
      have hle : w0.low y ≤ w0.pre y := by
        simp only [hw0]
        rw [h.low_eq hv0 hvo]
        exact climbBack_le_pre w y
      exact lead_retreat_iff hle (h.lead_iff y hy)
    · rw [hlead y hyv, hlow y hyv, hpre]
      exact h.lead_iff y hy
  · intro a ha hm
    rw [hlog] at ha
    rw [hpre]
    rcases List.mem_append.1 ha with ha | ha
    · exact (hcble a.1).trans (h.retreat_low a ha hm)
    · simp only [List.mem_singleton] at ha
      subst ha
      rw [climbBack_add_self (w := w0) hpre hlog hxn hm hvn]
      exact (min_le_right _ _).trans (climbBack_le_pre w x)
  · intro z y hy hz hzy hm
    rw [hfin] at hy
    have hyv : y ≠ v := fun he => h.path_fin v hvp (he ▸ hy)
    rw [hcb y hyv]
    refine (hcble z).trans (h.folded z y hy (by rwa [hpre] at hz) ?_ hm)
    unfold Folded at hzy ⊢
    rwa [hpre, hfin, hvertices] at hzy

end AlgorithmT

end AlgoDesign.Graphs.Scc
