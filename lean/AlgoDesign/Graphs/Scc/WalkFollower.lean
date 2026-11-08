/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkFinish

/-!
# Algorithm T: a vertex that does not lead finishes

`inv_finish_follower`: the current vertex `v` has looked at its whole row and does not lead. A
member of its component was entered earlier, so the first-entered member is below it on the path;
`v` goes on top of `F`, and the walk comes back over the arrow from the vertex `u` below it. The
two reach each other, so `u`'s low value becomes the smaller of the two (Tarjan–Zwick Lemma 3.8).
Every vertex `v`'s branch reached is now folded into `u`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-- **A vertex that does not lead finishes, and the walk comes back to the vertex below it.** -/
theorem inv_finish_follower (hg : g.WellFormed) {w : Walk} (h : Inv g w) {v i u j : ℕ}
    {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: (u, j) :: rest)
    (hi : (g.out v)[i]? = none) (hl : w.lead v = false) :
    Inv g (retreat (postvisit g { w with path := (u, j) :: rest } v) u v) := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  set w2 := postvisit g { w with path := (u, j) :: rest } v with hw2def
  have hw2 : w2 =
      { w with path := (u, j) :: rest, finished := w.finished ++ [v],
               followers := v :: w.followers } := by
    rw [hw2def, postvisit_of_not_lead (by exact hl)]
  set w' := retreat w2 u v with hw'
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hup : u ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  have hu0 := h.path_entered hup
  have hvn := h.lt_n v hv0
  have hun := h.lt_n u hu0
  have hvo := h.not_out_of_path hvp
  have huo := h.not_out_of_path hup
  have hpl' : vertices w' = u :: rest.map Prod.fst := by simp [hw', hw2, vertices]
  have hpl : vertices w = v :: vertices w' := by rw [hpl']; simp [vertices, hs]
  have hvR : v ∉ vertices w' := by
    rw [hpl']
    exact h.top_not_mem_rest hs
  have hRsub : ∀ p ∈ vertices w', p ∈ vertices w := fun p hp => by
    rw [hpl]
    exact List.mem_cons_of_mem _ hp
  have hRlt : ∀ p ∈ vertices w', w.pre p < w.pre v := fun p hp =>
    h.pre_lt_top hs (by rwa [hpl'] at hp)
  have hRle : ∀ p ∈ vertices w', w.pre p ≤ w.pre u := by
    intro p hp
    rw [hpl'] at hp
    have hsr := h.sorted
    simp only [vertices, hs, List.map_cons, List.pairwise_cons] at hsr
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_rfl
    · exact (hsr.2.1 p hp).le
  have hpre : w'.pre = w.pre := by simp [hw', hw2]
  have hfin : w'.finished = w.finished ++ [v] := by simp [hw', hw2]
  have hgr : w'.groups = w.groups := by simp [hw', hw2]
  have hlog : w'.retreats = w.retreats ++ [(u, v)] := by simp [hw', hw2]
  have hlow : ∀ y, y ≠ u → w'.low y = w.low y := fun y hy => by
    simp [hw', hw2, retreat_low_apply, hy]
  have hlead : ∀ y, y ≠ u → w'.lead y = w.lead y := fun y hy => by
    simp [hw', hw2, retreat_lead_apply, hy]
  have hvf : v ∉ w.finished := h.path_fin v hvp
  -- a member of `v`'s component entered earlier, and the first is below `v` on the path
  have hnf : ¬ First (g := g) w v := fun hf => by
    rw [← h.lead_iff_first hs hi hg] at hf
    simp [hl] at hf
  obtain ⟨u0, hu00, hu0v, hu0lt⟩ : ∃ u0, w.pre u0 ≠ 0 ∧ Mutual g u0 v ∧ w.pre u0 < w.pre v := by
    by_contra hne
    exact hnf fun u0 h0 hm => by
      by_contra hlt
      exact hne ⟨u0, h0, hm, Nat.lt_of_not_le hlt⟩
  obtain ⟨q, hq, hqv, hqu0⟩ := h.gray_min v hvp u0 hu00 hu0v
  have hqR : q ∈ vertices w' := by
    rw [hpl] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · omega
    · exact hq
  have hmuv : Mutual g u v :=
    ⟨h.reach u hup v hv0 (hRlt u (by simp [hpl'])).le,
      hqv.2.trans (h.reach q hq u hu0 (hRle q hqR))⟩
  -- climb-back numbers
  have hcb2 : ∀ y, climbBack (g := g) w2 y = climbBack (g := g) w y := fun y => by
    rw [hw2]; rfl
  have hp2 : w'.pre = w2.pre := by simp [hw']
  have hr2 : w'.retreats = w2.retreats ++ [(u, v)] := by simp [hw']
  have hcb : ∀ y, y ≠ u → climbBack (g := g) w' y = climbBack (g := g) w y := fun y hy => by
    rw [climbBack_add_of_ne hp2 hr2 hvn hy, hcb2]
  have hcbu : climbBack (g := g) w' u =
      min (climbBack (g := g) w u) (climbBack (g := g) w v) := by
    rw [climbBack_add_self hp2 hr2 hvn hmuv hun, hcb2, hcb2]
  have hcble : ∀ y, climbBack (g := g) w' y ≤ climbBack (g := g) w y := fun y => by
    rw [← hcb2]
    exact climbBack_add_le hp2 hr2 hvn y
  have hLO : ∀ y, LeaderOut (g := g) w' y ↔ LeaderOut (g := g) w y := by
    intro y
    constructor
    · rintro ⟨x, hx, hxy, hxf, hmin⟩
      rw [hfin] at hxf
      rcases List.mem_append.1 hxf with hxf | hxv
      · exact ⟨x, hx, hxy, hxf, fun z hz hzy => by rw [← hpre]; exact hmin z hz hzy⟩
      · simp only [List.mem_singleton] at hxv
        subst hxv
        rcases hmin u0 (h.lt_n u0 hu00) (hu0v.trans hxy) with h0 | h1
        · exact absurd (by rwa [hpre] at h0) hu00
        · rw [hpre] at h1
          omega
    · rintro ⟨x, hx, hxy, hxf, hmin⟩
      exact ⟨x, hx, hxy, by rw [hfin]; exact List.mem_append_left _ hxf,
        fun z hz hzy => by rw [hpre]; exact hmin z hz hzy⟩
  have hlowu : w'.low u = climbBack (g := g) w' u := by
    refine low_retreat_eq (w := w2) hvn ?_ (fun _ => ?_) (fun hm => absurd hmuv hm) hun
    · rw [hcb2, hw2]
      exact h.low_eq hu0 huo
    · rw [hcb2, hw2]
      exact h.low_eq hv0 hvo
  have hlowv : w.low v < w.pre v := by
    have := (h.lead_iff v hvp).not.1 (by simp [hl])
    have := climbBack_le_pre (g := g) w v
    rw [h.low_eq hv0 hvo] at *
    omega
  have hg' : w'.g = g := by simp [hw', hw2, h.graph]
  refine
    { graph := hg'
      valid := ?_
      lt_n := by rw [hpre]; exact h.lt_n
      pre_le := by rw [hpre]; simpa [hw', hw2] using h.pre_le
      pre_inj := by rw [hpre]; exact h.pre_inj
      time_eq := by rw [hpre]; simpa [hw', hw2] using h.time_eq
      low_zero := ?_
      entered := ?_
      path_fin := ?_
      fin_nodup := by rw [hfin]; exact List.nodup_append.2 ⟨h.fin_nodup, by simp,
        fun a ha b hb => by
          simp only [List.mem_singleton] at hb
          exact hb ▸ ne_of_mem_of_not_mem ha hvf⟩
      sorted := ?_
      frames := ?_
      fin_rows := ?_
      retreat_ent := ?_
      roots := by rw [hpre]; simpa [hw', hw2] using h.roots
      reach := fun p hp => by rw [hpre]; exact h.reach p (hRsub p hp)
      out_fin := fun y hy => by
        rw [hfin]
        rw [hgr] at hy
        exact List.mem_append_left _ (h.out_fin y hy)
      out_closed := by simpa [hw', hw2] using h.out_closed
      grp_idx := by simpa [hw', hw2] using h.grp_idx
      grp_ne := by rw [hgr]; exact h.grp_ne
      grp_nodup := by rw [hgr]; exact h.grp_nodup
      grp_sub := fun m hm => by
        rw [hfin]
        rw [hgr] at hm
        exact (h.grp_sub m hm).trans (List.sublist_append_left _ _)
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
  · -- box invariant 1
    simp only [hw', hw2, retreat_followers, retreat_finished, retreat_groups]
    rw [hval.1, List.filter_append]
    have hvo' : decide (v ∉ w.groups.flatten) = true := decide_eq_true hvo
    simp only [List.filter_cons, List.filter_nil, hvo', ↓reduceIte, List.reverse_append,
      List.reverse_singleton, List.cons_append, List.nil_append]
  · -- box invariant 2
    intro y hy hy0 hyl
    by_cases hyu : y = u
    · subst hyu
      exact hlowu
    · rw [hlow y hyu, hcb y hyu]
      exact hval.2.1 y hy (by rwa [hpre] at hy0) fun hl' => hyl ((hLO y).2 hl')
  · -- box invariant 3
    intro y hy
    rw [hLO y, hgr]
    by_cases hyu : y = u
    · subst hyu
      refine ⟨⟨fun he => ?_, fun hl' => absurd ((h.leaderOut_iff hy).1 hl') huo⟩,
        (hval.2.2.1 y hy).2⟩
      have := hcble y
      have := climbBack_le_pre (g := g) w y
      have := h.pre_le_n y
      rw [hlowu] at he
      unfold done at he
      omega
    · rw [hlow y hyu]
      exact hval.2.2.1 y hy
  · rw [hgr]
    exact hval.2.2.2
  · intro y
    rw [hpre]
    by_cases hyu : y = u
    · subst hyu
      have hmin : w'.low y = min (w.low y) (w.low v) := by
        rw [hw', retreat_low_apply, hw2]
        simp only [↓reduceIte]
      rw [hmin]
      have h1 := (h.low_zero y).not.2 hu0
      have h2 := (h.low_zero v).not.2 hv0
      constructor
      · intro h0
        omega
      · intro h0
        exact absurd h0 hu0
    · rw [hlow y hyu]
      exact h.low_zero y
  · intro y
    rw [hpre, hfin, h.entered y, hpl]
    simp only [List.mem_cons, List.mem_append]
    tauto
  · intro y hy
    rw [hfin]
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨h.path_fin y (hRsub y hy), fun he => hvR (he ▸ hy)⟩
  · rw [hpre, hpl']
    have hsr := h.sorted
    simp only [vertices, hs, List.map_cons] at hsr
    exact (List.pairwise_cons.1 hsr).2
  · have hf := h.frames
    rw [hs] at hf
    have := hf.2.2.pop (log := w.retreats)
    simp only [hw', hw2, retreat_path, retreat_retreats]
    exact this
  · intro y hy
    rw [hfin] at hy
    rw [hlog]
    rcases List.mem_append.1 hy with hy | hy
    · exact (h.fin_rows y hy).mono fun a ha => List.mem_append_left _ ha
    · simp only [List.mem_singleton] at hy
      subst hy
      exact (h.row_done hs hi).mono fun a ha => List.mem_append_left _ ha
  · intro a ha
    rw [hlog] at ha
    rw [hpre]
    rcases List.mem_append.1 ha with ha | ha
    · exact h.retreat_ent a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨hu0, hv0⟩
  · intro y hy hyo
    rw [hfin] at hy
    rw [hgr] at hyo
    rw [hpre]
    rcases List.mem_append.1 hy with hy | hy
    · have hyu : y ≠ u := fun he => h.path_fin u hup (he ▸ hy)
      rw [hlow y hyu]
      exact h.open_low y hy hyo
    · simp only [List.mem_singleton] at hy
      subst hy
      have hyu : y ≠ u := fun he => hvR (he ▸ by simp [hpl'])
      rw [hlow y hyu]
      exact hlowv
  · intro y hy
    by_cases hyu : y = u
    · subst hyu
      have hle : w2.low y ≤ w2.pre y := by
        rw [hw2]
        dsimp only
        rw [h.low_eq hu0 huo]
        exact climbBack_le_pre w y
      have := lead_retreat_iff (x := v) hle (by rw [hw2]; exact h.lead_iff y hup)
      exact this
    · rw [hlead y hyu, hlow y hyu, hpre]
      exact h.lead_iff y (hRsub y hy)
  · intro y hy hyo
    rw [hfin] at hy
    rw [hgr] at hyo
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨q', hq', hq'y⟩ := h.open_gray y hy hyo
      rw [hpl] at hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨q, hqR, hqv.trans hq'y⟩
      · exact ⟨q', hq', hq'y⟩
    · simp only [List.mem_singleton] at hy
      subst hy
      exact ⟨q, hqR, hqv⟩
  · intro p hp y hy hyp
    rw [hpre] at hy ⊢
    obtain ⟨q', hq', hq'p, hq'y⟩ := h.gray_min p (hRsub p hp) y hy hyp
    rw [hpl] at hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact ⟨p, hp, mutual_refl p, (hRlt p hp).le.trans hq'y⟩
    · exact ⟨q', hq', hq'p, hq'y⟩
  · intro p hp
    have hpv := hRlt p hp
    have e1 : ([v].filter fun x => decide (w.pre x < w.pre p)) = [] := by
      simp [Nat.not_lt.2 hpv.le]
    have e2 : ([v].filter fun x => decide (w.pre p < w.pre x)) = [v] := by simp [hpv]
    rw [hfin, hpre, List.filter_append, List.filter_append, e1, e2, List.append_nil,
      ← List.append_assoc, ← h.fin_split p (hRsub p hp)]
  · intro a ha hm
    rw [hlog] at ha
    rw [hpre]
    rcases List.mem_append.1 ha with ha | ha
    · exact (hcble a.1).trans (h.retreat_low a ha hm)
    · simp only [List.mem_singleton] at ha
      subst ha
      dsimp only
      rw [hcbu]
      exact (min_le_right _ _).trans (climbBack_le_pre w v)
  · intro z x hx hz hzx hm
    rw [hfin] at hx
    rw [hpre] at hz
    have hvu : v ≠ u := fun he => hvR (he ▸ by simp [hpl'])
    have hxu : x ≠ u := by
      rintro rfl
      rcases List.mem_append.1 hx with hx | hx
      · exact h.path_fin x hup hx
      · simp only [List.mem_singleton] at hx
        exact hvu hx.symm
    rw [hcb x hxu]
    obtain ⟨hzxp, hcase⟩ := hzx
    rw [hpre] at hzxp
    have hfv : ∀ y, w.pre v < w.pre y → Folded w v y := fun y hy =>
      ⟨hy, Or.inr ⟨hvp, fun p hp hvp' => absurd (h.pre_le_top hs hp) (by omega)⟩⟩
    have hRu : ∀ y ∈ vertices w', y ≠ u → w.pre y < w.pre u := fun y hy hyu =>
      lt_of_le_of_ne (hRle y hy) fun he => hyu (h.pre_inj y u (h.path_entered (hRsub y hy)) he)
    have hup' : u ∈ vertices w' := by simp [hpl']
    rcases List.mem_append.1 hx with hxf | hxv
    · have hxv : x ≠ v := fun he => hvf (he ▸ hxf)
      rcases hcase with ⟨hzf, hsub⟩ | ⟨hzp, hall⟩
      · rw [hfin] at hzf hsub
        by_cases hzv : z = v
        · rw [hzv, hcb v hvu]
          rw [hzv] at hzxp hm
          exact h.folded v x hxf hv0 (hfv x hzxp) hm
        · have hzf' : z ∈ w.finished :=
            (List.mem_append.1 hzf).resolve_right (by simpa using hzv)
          exact (hcble z).trans
            (h.folded z x hxf hz ⟨hzxp, Or.inl ⟨hzf', pair_sublist_of_append hsub hzv⟩⟩ hm)
      · by_cases hzu : z = u
        · rw [hzu] at hzxp hm hz ⊢
          by_cases hxlt : w.pre x < w.pre v
          · refine (hcble u).trans
              (h.folded u x hxf hz ⟨hzxp, Or.inr ⟨hup, fun p hp hup' => ?_⟩⟩ hm)
            rw [hpl] at hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact hxlt
            · have := hall p hp
              rw [hpre, hzu] at this
              exact this hup'
          · have hvx : w.pre v < w.pre x :=
              lt_of_le_of_ne (Nat.le_of_not_lt hxlt) fun he => hxv (h.pre_inj v x hv0 he).symm
            have hmvx : Mutual g v x :=
              ⟨h.reach v hvp x (h.fin_entered hxf) hvx.le, hm.2.trans hmuv.1⟩
            rw [hcbu]
            exact (min_le_right _ _).trans (h.folded v x hxf hv0 (hfv x hvx) hmvx)
        · have hzu' := hRu z hzp hzu
          rw [hcb z hzu]
          refine h.folded z x hxf hz ⟨hzxp, Or.inr ⟨hRsub z hzp, fun p hp hzp' => ?_⟩⟩ hm
          rw [hpl] at hp
          rcases List.mem_cons.1 hp with rfl | hp
          · have := hall u hup'
            rw [hpre] at this
            have := this hzu'
            have := hRlt u hup'
            omega
          · have := hall p hp
            rw [hpre] at this
            exact this hzp'
    · simp only [List.mem_singleton] at hxv
      subst hxv
      rcases hcase with ⟨-, hsub⟩ | ⟨hzp, hall⟩
      · rw [hfin] at hsub
        exact absurd hsub (not_pair_sublist_append hvf)
      · by_cases hzu : z = u
        · rw [hzu, hcbu]
          exact min_le_right _ _
        · have := hall u hup'
          rw [hpre] at this
          have := this (hRu z hzp hzu)
          have := hRlt u hup'
          omega

end AlgorithmT

end AlgoDesign.Graphs.Scc
