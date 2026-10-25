/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkMoves

/-!
# Algorithm T: entering a vertex keeps the invariant

`inv_previsit`: entering an unvisited vertex `x`, reached from every vertex on the path, keeps
`Inv`. The new vertex gets the largest entry number, so it goes on top of the path in order; it
leads, its low value and climb-back number are its entry number, and no leader has finished for
it: a finished vertex reaching it reaches it through the path (Tarjan–Zwick Lemma 2.4, the white
path theorem, in the form the walk keeps), so its component's first-entered member is on the path.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

theorem countP_update_ne_zero {f : ℕ → ℕ} {x k : ℕ} (hfx : f x = 0) (hk : k ≠ 0) :
    ∀ l : List ℕ, l.Nodup → x ∈ l →
      l.countP (fun v => Function.update f x k v ≠ 0) = l.countP (fun v => f v ≠ 0) + 1
  | [], _, hx => absurd hx List.not_mem_nil
  | a :: l, hnd, hx => by
    rw [List.countP_cons, List.countP_cons]
    by_cases hax : a = x
    · subst hax
      have hal : a ∉ l := (List.nodup_cons.1 hnd).1
      have : l.countP (fun v => Function.update f a k v ≠ 0) = l.countP (fun v => f v ≠ 0) :=
        List.countP_congr fun y hy => by
          have : y ≠ a := fun h => hal (h ▸ hy)
          rw [Function.update_of_ne this]
      simpa [hfx, hk] using this
    · have := countP_update_ne_zero hfx hk l (List.nodup_cons.1 hnd).2
        (by simpa [Ne.symm hax] using hx)
      simp only [Function.update_of_ne hax]
      omega

/-- No finished leader for an unvisited vertex reached from every vertex on the path. -/
theorem Inv.not_leaderOut_unvisited (hg : g.WellFormed) {w : Walk} (h : Inv g w) {x : ℕ}
    (hreach : ∀ p ∈ vertices w, g.Reaches p x) (hx0 : w.pre x = 0) :
    ¬ LeaderOut (g := g) w x := by
  rintro ⟨u, hu, hux, huf, hmin⟩
  rcases h.entered_or_path hg (h.fin_entered huf) hux.1 with hx | ⟨p, hp, hup⟩
  · exact hx hx0
  · have hpx : Mutual g p x := ⟨hreach p hp, hux.2.trans hup⟩
    obtain ⟨q, hq, hqp, hqu⟩ :=
      h.gray_min p hp u (h.fin_entered huf) ⟨hup, (hreach p hp).trans hux.2⟩
    rcases hmin q (h.lt_n q (h.path_entered hq)) (hqp.trans hpx) with h0 | h1
    · exact h.path_entered hq h0
    · have : q = u := h.pre_inj q u (h.path_entered hq) (by omega)
      subst this
      exact h.path_fin q hq huf

/-- **Entering a vertex keeps the invariant**: an unvisited vertex `x`, reached from every vertex on
the path, entered on top of frames `P` with the path's vertices, where the frame below has just
looked at the arrow to `x`. -/
theorem inv_previsit (hg : g.WellFormed) {w : Walk} (h : Inv g w) {P : List (ℕ × ℕ)} {x : ℕ}
    (hP : P.map Prod.fst = vertices w) (hF : FramesRetreated g w.retreats (some x) P)
    (hreach : ∀ p ∈ vertices w, g.Reaches p x) (hx0 : w.pre x = 0) (hxn : x < g.n) :
    Inv g (previsit { w with path := P } x) := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  set w' := previsit { w with path := P } x with hw'
  have hxf : x ∉ w.finished := fun hf => h.fin_entered hf hx0
  have hxp : x ∉ vertices w := fun hp => h.path_entered hp hx0
  have hxo : x ∉ w.groups.flatten := fun ho => h.out_entered ho hx0
  have hsrc : ∀ a ∈ w.retreats, a.1 ≠ x := fun a ha he => (h.retreat_ent a ha).1 (he ▸ hx0)
  have hhead : ∀ a ∈ w.retreats, a.2 ≠ x := fun a ha he => (h.retreat_ent a ha).2 (he ▸ hx0)
  have hpre : ∀ y, y ≠ x → w'.pre y = w.pre y := fun y hy => by
    simp [hw', Function.update_of_ne hy]
  have hprex : w'.pre x = w.time + 1 := by simp [hw']
  have hlow : ∀ y, y ≠ x → w'.low y = w.low y := fun y hy => by
    simp [hw', Function.update_of_ne hy]
  have hlowx : w'.low x = w.time + 1 := by simp [hw']
  have hvertices : vertices w' = x :: vertices w := by simpa [hw', vertices] using hP
  have hent : ∀ y, w'.pre y ≠ 0 ↔ y = x ∨ w.pre y ≠ 0 := fun y => by
    by_cases hy : y = x
    · simp [hy, hprex]
    · simp [hy, hpre y hy]
  have htime := h.time_lt hxn hx0
  have hcb : ∀ y, y ≠ x → climbBack (g := g) w' y = climbBack (g := g) w y :=
    fun y hy => climbBack_previsit_of_ne (w := { w with path := P }) hhead hy
  have hcbx : climbBack (g := g) w' x = w.time + 1 := by
    rw [climbBack_of_no_source (w := w') (by simpa [hw'] using hsrc), hprex]
  have hLO : ∀ y, LeaderOut (g := g) w' y ↔ LeaderOut (g := g) w y := by
    intro y
    constructor
    · rintro ⟨u, hu, huy, huf, hmin⟩
      have hux : u ≠ x := fun he => hxf (he ▸ huf)
      refine ⟨u, hu, huy, huf, fun z hz hzy => ?_⟩
      rcases hmin z hz hzy with h0 | h1
      · by_cases hzx : z = x
        · exact Or.inl (hzx ▸ hx0)
        · exact Or.inl (by rwa [hpre z hzx] at h0)
      · by_cases hzx : z = x
        · exact Or.inl (hzx ▸ hx0)
        · exact Or.inr (by rwa [hpre z hzx, hpre u hux] at h1)
    · rintro ⟨u, hu, huy, huf, hmin⟩
      have hux : u ≠ x := fun he => hxf (he ▸ huf)
      refine ⟨u, hu, huy, huf, fun z hz hzy => ?_⟩
      by_cases hzx : z = x
      · subst hzx
        have := h.pre_le u
        exact Or.inr (by rw [hprex, hpre u hux]; omega)
      · rw [hpre z hzx, hpre u hux]
        exact hmin z hz hzy
  have hnLx : ¬ LeaderOut (g := g) w x := h.not_leaderOut_unvisited hg hreach hx0
  have hg' : w'.g = g := h.graph
  refine
    { graph := hg'
      valid := ?_
      lt_n := ?_
      pre_le := ?_
      pre_inj := ?_
      time_eq := ?_
      low_zero := ?_
      entered := ?_
      path_fin := ?_
      fin_nodup := by simpa [hw'] using h.fin_nodup
      sorted := ?_
      frames := ?_
      fin_rows := by simpa [hw'] using h.fin_rows
      retreat_ent := ?_
      roots := ?_
      reach := ?_
      out_fin := by simpa [hw'] using h.out_fin
      out_closed := by simpa [hw'] using h.out_closed
      grp_idx := by simpa [hw'] using h.grp_idx
      grp_ne := by simpa [hw'] using h.grp_ne
      grp_nodup := by simpa [hw'] using h.grp_nodup
      grp_sub := by simpa [hw'] using h.grp_sub
      open_low := ?_
      lead_iff := ?_
      open_gray := ?_
      gray_min := ?_
      fin_split := ?_
      retreat_low := ?_
      folded := ?_ }
  on_goal 1 =>
    unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut
    rw [hg']
    refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hw', FollowersInFinishOrder] using hval.1
  · intro v hv hv0 hvl
    by_cases hvx : v = x
    · subst hvx
      rw [hlowx, hcbx]
    · rw [hlow v hvx, hcb v hvx]
      exact hval.2.1 v hv (by rwa [hpre v hvx] at hv0) fun hl => hvl ((hLO v).2 hl)
  · intro v hv
    rw [hLO v]
    by_cases hvx : v = x
    · subst hvx
      simp only [hlowx, hnLx, iff_false, done]
      exact ⟨by omega, by simpa [hw'] using hxo⟩
    · rw [hlow v hvx]
      simpa [hw'] using hval.2.2.1 v hv
  · simpa [hw'] using hval.2.2.2
  · intro v hv
    rcases (hent v).1 hv with rfl | hv
    · exact hxn
    · exact h.lt_n v hv
  · intro v
    by_cases hvx : v = x
    · subst hvx
      rw [hprex]
      exact le_rfl
    · rw [hpre v hvx]
      have := h.pre_le v
      simp only [hw', previsit_time]
      omega
  · intro u v hu huv
    by_cases hux : u = x
    · subst hux
      by_contra hne
      have hvx : v ≠ u := Ne.symm hne
      rw [hprex, hpre v hvx] at huv
      have := h.pre_le v
      omega
    · by_cases hvx : v = x
      · subst hvx
        rw [hprex, hpre u hux] at huv
        have := h.pre_le u
        omega
      · rw [hpre u hux, hpre v hvx] at huv
        exact h.pre_inj u v (by rwa [hpre u hux] at hu) huv
  · simp only [hw', previsit_time, previsit_pre, h.time_eq]
    exact (countP_update_ne_zero hx0 (Nat.succ_ne_zero _) _ List.nodup_range
      (List.mem_range.2 hxn)).symm
  · intro v
    by_cases hvx : v = x
    · subst hvx
      rw [hlowx, hprex]
    · rw [hlow v hvx, hpre v hvx]
      exact h.low_zero v
  · intro v
    rw [hent v, hvertices]
    simp only [List.mem_cons, hw', previsit_finished]
    constructor
    · rintro (rfl | hv)
      · exact Or.inl (Or.inl rfl)
      · rcases (h.entered v).1 hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
    · rintro ((rfl | hv) | hv)
      · exact Or.inl rfl
      · exact Or.inr (h.path_entered hv)
      · exact Or.inr (h.fin_entered hv)
  · intro v hv
    rw [hvertices] at hv
    simp only [hw', previsit_finished]
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hxf
    · exact h.path_fin v hv
  · rw [hvertices]
    refine List.Pairwise.cons (fun b hb => ?_) (h.sorted.imp_of_mem fun ha hb hab => ?_)
    · have hbx : b ≠ x := fun he => hxp (he ▸ hb)
      rw [hprex, hpre b hbx]
      have := h.pre_le b
      omega
    · rename_i a b
      have hax : a ≠ x := fun he => hxp (he ▸ ha)
      have hbx : b ≠ x := fun he => hxp (he ▸ hb)
      rwa [hpre a hax, hpre b hbx]
  · simp only [hw', previsit_path, previsit_retreats]
    exact ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j), hF⟩
  · intro a ha
    simp only [hw', previsit_retreats] at ha
    have := h.retreat_ent a ha
    exact ⟨(hent _).2 (Or.inr this.1), (hent _).2 (Or.inr this.2)⟩
  · intro r hr
    exact (hent r).2 (Or.inr (h.roots r (by simpa [hw'] using hr)))
  · intro p hp y hy hpy
    rw [hvertices] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · by_cases hyx : y = p
      · exact hyx ▸ ReflTransGen.refl
      · rw [hprex, hpre y hyx] at hpy
        have := h.pre_le y
        omega
    · have hpx : p ≠ x := fun he => hxp (he ▸ hp)
      by_cases hyx : y = x
      · exact hyx ▸ hreach p hp
      · rw [hpre p hpx, hpre y hyx] at hpy
        exact h.reach p hp y (by rwa [hpre y hyx] at hy) hpy
  · intro v hv hvo
    simp only [hw', previsit_finished, previsit_groups] at hv hvo
    have hvx : v ≠ x := fun he => hxf (he ▸ hv)
    rw [hlow v hvx, hpre v hvx]
    exact h.open_low v hv hvo
  · intro v hv
    rw [hvertices] at hv
    rcases List.mem_cons.1 hv with rfl | hv
    · simp [hw']
    · have hvx : v ≠ x := fun he => hxp (he ▸ hv)
      rw [hlow v hvx, hpre v hvx]
      simpa [hw', Function.update_of_ne hvx] using h.lead_iff v hv
  · intro v hv hvo
    simp only [hw', previsit_finished, previsit_groups] at hv hvo
    obtain ⟨q, hq, hqv⟩ := h.open_gray v hv hvo
    exact ⟨q, by rw [hvertices]; exact List.mem_cons_of_mem _ hq, hqv⟩
  · intro p hp u hu hup
    rw [hvertices] at hp ⊢
    rcases List.mem_cons.1 hp with hpx | hp'
    · rw [hpx] at hup ⊢
      by_cases hux : u = x
      · exact ⟨x, List.mem_cons_self, mutual_refl x, by rw [hux]⟩
      · have hu' : w.pre u ≠ 0 := by rwa [hpre u hux] at hu
        rcases h.entered_or_path hg hu' hup.1 with hx | ⟨p', hp', hup'⟩
        · exact absurd hx0 hx
        · have hp'x : Mutual g p' x := ⟨hreach p' hp', hup.2.trans hup'⟩
          obtain ⟨q, hq, hqp', hqu⟩ :=
            h.gray_min p' hp' u hu' ⟨hup', hp'x.1.trans hup.2⟩
          have hqx : q ≠ x := fun he => hxp (he ▸ hq)
          exact ⟨q, List.mem_cons_of_mem _ hq, hqp'.trans hp'x,
            by rw [hpre q hqx, hpre u hux]; exact hqu⟩
    · have hpx : p ≠ x := fun he => hxp (he ▸ hp')
      by_cases hux : u = x
      · refine ⟨p, List.mem_cons_of_mem _ hp', mutual_refl p, ?_⟩
        rw [hpre p hpx, hux, hprex]
        have := h.pre_le p
        omega
      · obtain ⟨q, hq, hqp, hqu⟩ :=
          h.gray_min p hp' u (by rwa [hpre u hux] at hu) hup
        have hqx : q ≠ x := fun he => hxp (he ▸ hq)
        exact ⟨q, List.mem_cons_of_mem _ hq, hqp, by rw [hpre q hqx, hpre u hux]; exact hqu⟩
  · intro p hp
    rw [hvertices] at hp
    have hfin : w'.finished = w.finished := rfl
    rw [hfin]
    have hfx : ∀ y ∈ w.finished, y ≠ x := fun y hy he => hxf (he ▸ hy)
    rcases List.mem_cons.1 hp with hpx | hp'
    · rw [hpx, List.filter_eq_self.2 fun y hy => ?_, List.filter_eq_nil_iff.2 fun y hy => ?_,
        List.append_nil]
      · rw [hpre y (hfx y hy), hprex]
        have := h.pre_le y
        simp only [decide_eq_true_eq]
        omega
      · rw [hpre y (hfx y hy), hprex]
        have := h.pre_le y
        simp only [decide_eq_true_eq]
        omega
    · have hpx : p ≠ x := fun he => hxp (he ▸ hp')
      have e1 : (w.finished.filter fun y => decide (w'.pre y < w'.pre p)) =
          w.finished.filter fun y => decide (w.pre y < w.pre p) :=
        List.filter_congr fun y hy => by rw [hpre y (hfx y hy), hpre p hpx]
      have e2 : (w.finished.filter fun y => decide (w'.pre p < w'.pre y)) =
          w.finished.filter fun y => decide (w.pre p < w.pre y) :=
        List.filter_congr fun y hy => by rw [hpre y (hfx y hy), hpre p hpx]
      rw [e1, e2]
      exact h.fin_split p hp'
  · intro a ha hm
    simp only [hw', previsit_retreats] at ha
    rw [hcb a.1 (hsrc a ha), hpre a.2 (hhead a ha)]
    exact h.retreat_low a ha hm
  · intro z y hy hz hzy hm
    simp only [hw', previsit_finished] at hy
    have hyx : y ≠ x := fun he => hxf (he ▸ hy)
    have hzx : z ≠ x := by
      rintro rfl
      have := hzy.1
      rw [hprex, hpre y hyx] at this
      have := h.pre_le y
      omega
    rw [hcb z hzx, hcb y hyx]
    refine h.folded z y hy (by rwa [hpre z hzx] at hz) ⟨?_, ?_⟩ hm
    · have := hzy.1
      rwa [hpre z hzx, hpre y hyx] at this
    · rcases hzy.2 with ⟨hzf, hs⟩ | ⟨hzp, hall⟩
      · exact Or.inl ⟨by simpa [hw'] using hzf, by simpa [hw'] using hs⟩
      · rw [hvertices] at hzp hall
        refine Or.inr ⟨(List.mem_cons.1 hzp).resolve_left hzx, fun p hp hzp' => ?_⟩
        have hpx : p ≠ x := fun he => hxp (he ▸ hp)
        have := hall p (List.mem_cons_of_mem _ hp)
        rw [hpre z hzx, hpre p hpx, hpre y hyx] at this
        exact this hzp'

end AlgorithmT

end AlgoDesign.Graphs.Scc
