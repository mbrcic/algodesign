/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkFollower

/-!
# Algorithm T: a leader finishes and its group comes out

`inv_finish_leader`: the current vertex `v` has looked at its whole row and leads, so it was entered
first in its component. `F` holds, above the vertices that finished before `v` was entered, exactly
the finished vertices entered after `v` whose group is not out; these are the rest of `v`'s
component, their low values are at least `v`'s entry number, and the vertices below them have low
values under it (Tarjan–Zwick Lemma 3.9). So popping `F` takes exactly the rest of the component,
in the order the vertices finished, and the group out is the whole component, marked done. Every
vertex `v` reaches is in it or in a group out before, so the groups come out sinks first
(Theorem 3.5). Coming back over the arrow from the vertex below changes no low value.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

theorem Inv.emitted_lt {w : Walk} (h : Inv g w) {y : ℕ} (hy : y ∈ w.groups.flatten) :
    w.emitted y < w.groups.length := by
  obtain ⟨m, hm, hym⟩ := List.mem_flatten.1 hy
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hm
  rw [h.grp_idx k hk y hym]
  exact hk

theorem retreat_eq_of_not_lt {w : Walk} {v x : ℕ} (h : ¬ w.low x < w.low v) :
    retreat w v x = { w with retreats := w.retreats ++ [(v, x)] } := by
  unfold retreat
  simp [h]

/-- Adding retreats between vertices that do not reach each other changes no climb-back
number. -/
theorem climbBack_append_of_not_mutual :
    ∀ (E : List (ℕ × ℕ)) {w w' : Walk}, (∀ a ∈ E, ¬ Mutual g a.1 a.2 ∧ a.2 < g.n) →
      w'.pre = w.pre → w'.retreats = w.retreats ++ E → ∀ y,
        climbBack (g := g) w' y = climbBack (g := g) w y
  | [], w, w', _, hp, hr, y => climbBack_congr (by rw [hr, List.append_nil]) (by rw [hp])
      (fun x _ => by rw [hp])
  | a :: E, w, w', hE, hp, hr, y => by
    set w1 : Walk := { w with retreats := w.retreats ++ [a] }
    have h1 : climbBack (g := g) w1 y = climbBack (g := g) w y :=
      climbBack_add_of_not_mutual (w := w) (w' := w1) (v := a.1) (x := a.2) rfl rfl
        (hE a List.mem_cons_self).2 (hE a List.mem_cons_self).1 y
    rw [← h1]
    exact climbBack_append_of_not_mutual E (w := w1)
      (fun b hb => hE b (List.mem_cons_of_mem _ hb)) hp
      (by rw [hr]; change w.retreats ++ a :: E = (w.retreats ++ [a]) ++ E; simp) y

/-- **A leader finishes and its group comes out**; the log then gains `E`, the arrow back to the
vertex below if there is one. -/
theorem inv_finish_leader (hg : g.WellFormed) {w : Walk} (h : Inv g w) {v i : ℕ}
    {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest) (hi : (g.out v)[i]? = none)
    (hl : w.lead v = true) (E : List (ℕ × ℕ))
    (hE : ∀ a ∈ E, a.1 ∈ rest.map Prod.fst ∧ a.2 = v)
    (hEF : FramesRetreated g (w.retreats ++ E) none rest) :
    Inv g { postvisit g { w with path := rest } v with retreats := w.retreats ++ E } := by
  have hval := h.valid
  unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut at hval
  rw [h.graph] at hval
  set w1 : Walk := { w with path := rest } with hw1
  have hl1 : w1.lead v = true := hl
  have hpv := postvisit_of_lead (g := g) hl1
  set r := popFollowers w.low (w.low v) w.followers with hrdef
  set grp := r.1.reverse ++ [v] with hgrpdef
  set w' : Walk := { postvisit g w1 v with retreats := w.retreats ++ E } with hw'
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  have hvn := h.lt_n v hv0
  have hvo := h.not_out_of_path hvp
  have hvf : v ∉ w.finished := h.path_fin v hvp
  have hfirst : First (g := g) w v := (h.lead_iff_first hs hi hg).1 hl
  have hlowv : w.low v = w.pre v := (h.lead_iff v hvp).1 hl
  -- the fields after the step
  have hpre : w'.pre = w.pre := by rw [hw', hpv]
  have hfin : w'.finished = w.finished ++ [v] := by rw [hw', hpv]
  have hgr : w'.groups = w.groups ++ [grp] := by rw [hw', hpv]
  have hlog : w'.retreats = w.retreats ++ E := by rw [hw']
  have hlead : w'.lead = w.lead := by rw [hw', hpv]
  have hfol : w'.followers = r.2 := by rw [hw', hpv]
  have hlow : ∀ y, w'.low y = if y ∈ grp then done g else w.low y := fun y => by
    rw [hw', hpv]
  have hem : ∀ y, w'.emitted y = if y ∈ grp then w.groups.length else w.emitted y := fun y => by
    rw [hw', hpv]
  have hpl' : vertices w' = rest.map Prod.fst := by rw [hw', hpv]; rfl
  have hpl : vertices w = v :: vertices w' := by rw [hpl']; simp [vertices, hs]
  have hvR : v ∉ vertices w' := by
    rw [hpl']
    exact h.top_not_mem_rest hs
  have hRsub : ∀ p ∈ vertices w', p ∈ vertices w := fun p hp => by
    rw [hpl]
    exact List.mem_cons_of_mem _ hp
  have hRlt : ∀ p ∈ vertices w', w.pre p < w.pre v := fun p hp =>
    h.pre_lt_top hs (by rwa [hpl'] at hp)
  have hnm : ∀ y, w.pre y ≠ 0 → w.pre y < w.pre v → ¬ Mutual g y v := fun y hy hlt hm => by
    have := hfirst y hy hm
    omega
  -- `F` splits at `v`'s entry
  set Flt := w.finished.filter fun x => decide (w.pre x < w.pre v) with hFlt
  set Fgt := w.finished.filter fun x => decide (w.pre v < w.pre x) with hFgt
  set A := Flt.filter fun x => decide (x ∉ w.groups.flatten) with hA
  set B := Fgt.filter fun x => decide (x ∉ w.groups.flatten) with hB
  have hsplit : w.finished = Flt ++ Fgt := h.fin_split v hvp
  have hmemB : ∀ x, x ∈ B ↔ x ∈ w.finished ∧ w.pre v < w.pre x ∧ x ∉ w.groups.flatten := by
    intro x
    simp only [hB, hFgt, List.mem_filter, decide_eq_true_eq]
    tauto
  have hmemA : ∀ x, x ∈ A ↔ x ∈ w.finished ∧ w.pre x < w.pre v ∧ x ∉ w.groups.flatten := by
    intro x
    simp only [hA, hFlt, List.mem_filter, decide_eq_true_eq]
    tauto
  have hfolw : w.followers = B.reverse ++ (A.reverse ++ [guard g]) := by
    rw [hval.1, hsplit, List.filter_append]
    simp [hA, hB]
  have hBlow : ∀ x ∈ B, w.pre v ≤ w.low x := by
    intro x hx
    obtain ⟨hxf, hxv, hxo⟩ := (hmemB x).1 hx
    have hxm := h.mutual_of_waiting hs hfirst hxf hxo hxv
    rw [h.low_eq (h.fin_entered hxf) hxo]
    refine le_climbBack_iff.2 ⟨hxv.le, fun z hz => ?_⟩
    have hz0 : w.pre z ≠ 0 := by
      rcases head_of_mem_reachList hz with rfl | ⟨a, ha⟩
      · exact h.fin_entered hxf
      · exact (h.retreat_ent _ ha).2
    exact hfirst z hz0 ((mutual_of_mem_reachList hz).symm.trans hxm)
  have hAlow : ∀ c ∈ A.reverse ++ [guard g], w.low c < w.pre v := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨hcf, hcv, hco⟩ := (hmemA c).1 (List.mem_reverse.1 hc)
      have := h.open_low c hcf hco
      omega
    · simp only [List.mem_singleton] at hc
      subst hc
      have hg0 : w.pre (guard g) = 0 := by
        by_contra hne
        have := h.lt_n _ hne
        simp [guard] at this
      rw [(h.low_zero _).2 hg0]
      omega
  have hr : r = (B.reverse, A.reverse ++ [guard g]) := by
    rw [hrdef, hfolw, hlowv]
    exact popFollowers_append _ _ (fun c hc => hAlow c (List.mem_of_mem_head? hc)) _
      fun x hx => hBlow x (List.mem_reverse.1 hx)
  have hgrp : grp = B ++ [v] := by rw [hgrpdef, hr, List.reverse_reverse]
  have hmem : ∀ y, y ∈ grp ↔ Mutual g y v := by
    intro y
    rw [hgrp, h.mutual_iff_of_first hs hi hg hfirst y, List.mem_append, hmemB y,
      List.mem_singleton]
    tauto
  have hdisj : ∀ y, Mutual g y v → y ∉ w.groups.flatten := fun y hy ho =>
    hvo (h.out_closed y ho v hy.1).1
  have hlowin : ∀ y, Mutual g y v → w'.low y = done g := fun y hy => by
    simp [hlow, (hmem y).2 hy]
  have hlowout : ∀ y, ¬ Mutual g y v → w'.low y = w.low y := fun y hy => by
    simp [hlow, show y ∉ grp from fun h' => hy ((hmem y).1 h')]
  have hemin : ∀ y, Mutual g y v → w'.emitted y = w.groups.length := fun y hy => by
    simp [hem, (hmem y).2 hy]
  have hemout : ∀ y, ¬ Mutual g y v → w'.emitted y = w.emitted y := fun y hy => by
    simp [hem, show y ∉ grp from fun h' => hy ((hmem y).1 h')]
  have hflat : ∀ y, y ∈ w'.groups.flatten ↔ y ∈ w.groups.flatten ∨ Mutual g y v := by
    intro y
    rw [hgr, List.flatten_append, List.mem_append, ← hmem y]
    simp
  have hLO : ∀ y, LeaderOut (g := g) w' y ↔ LeaderOut (g := g) w y ∨ Mutual g y v := by
    intro y
    constructor
    · rintro ⟨x, hx, hxy, hxf, hmin⟩
      rw [hfin] at hxf
      rcases List.mem_append.1 hxf with hxf | hxv
      · exact Or.inl ⟨x, hx, hxy, hxf, fun z hz hzy => by rw [← hpre]; exact hmin z hz hzy⟩
      · simp only [List.mem_singleton] at hxv
        subst hxv
        exact Or.inr hxy.symm
    · rintro (⟨x, hx, hxy, hxf, hmin⟩ | hyv)
      · exact ⟨x, hx, hxy, by rw [hfin]; exact List.mem_append_left _ hxf,
          fun z hz hzy => by rw [hpre]; exact hmin z hz hzy⟩
      · refine ⟨v, hvn, hyv.symm, by rw [hfin]; simp, fun z _ hzy => ?_⟩
        rw [hpre]
        by_cases hz0 : w.pre z = 0
        · exact Or.inl hz0
        · exact Or.inr (hfirst z hz0 (hzy.trans hyv))
  have hEnm : ∀ a ∈ E, ¬ Mutual g a.1 a.2 ∧ a.2 < g.n := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := hE a ha
    have hap : a.1 ∈ vertices w' := by rw [hpl']; exact ha1
    refine ⟨?_, ha2 ▸ hvn⟩
    rw [ha2]
    exact hnm a.1 (h.path_entered (hRsub _ hap)) (hRlt _ hap)
  have hcb : ∀ y, climbBack (g := g) w' y = climbBack (g := g) w y :=
    climbBack_append_of_not_mutual E hEnm hpre hlog
  have hfv : ∀ y, w.pre v < w.pre y → Folded w v y := fun y hy =>
    ⟨hy, Or.inr ⟨hvp, fun p hp hvp' => absurd (h.pre_le_top hs hp) (by omega)⟩⟩
  have hg' : w'.g = g := by simp [hw', hw1, h.graph]
  refine
    { graph := hg'
      valid := ?_
      lt_n := by rw [hpre]; exact h.lt_n
      pre_le := by rw [hpre]; simpa [hw', hpv] using h.pre_le
      pre_inj := by rw [hpre]; exact h.pre_inj
      time_eq := by rw [hpre]; simpa [hw', hpv] using h.time_eq
      low_zero := ?_
      entered := ?_
      path_fin := ?_
      fin_nodup := by
        rw [hfin]
        exact List.nodup_append.2 ⟨h.fin_nodup, by simp, fun a ha b hb => by
          simp only [List.mem_singleton] at hb
          exact hb ▸ ne_of_mem_of_not_mem ha hvf⟩
      sorted := ?_
      frames := by rw [hlog, hw', hpv]; exact hEF
      fin_rows := ?_
      retreat_ent := ?_
      roots := by rw [hpre]; simpa [hw', hpv] using h.roots
      reach := fun p hp => by rw [hpre]; exact h.reach p (hRsub p hp)
      out_fin := ?_
      out_closed := ?_
      grp_idx := ?_
      grp_ne := ?_
      grp_nodup := ?_
      grp_sub := ?_
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
    rw [hfol, hr]
    rw [hfin, hsplit, List.filter_append, List.filter_append]
    have e1 : (Flt.filter fun y => decide (y ∉ w'.groups.flatten)) = A := by
      refine List.filter_congr fun y hy => ?_
      have hy' := List.mem_filter.1 hy
      have hyv : w.pre y < w.pre v := by simpa using hy'.2
      have := hnm y (h.fin_entered hy'.1) hyv
      simp [hflat, this]
    have e2 : (Fgt.filter fun y => decide (y ∉ w'.groups.flatten)) = [] := by
      refine List.filter_eq_nil_iff.2 fun y hy => ?_
      have hy' := List.mem_filter.1 hy
      have hyv : w.pre v < w.pre y := by simpa using hy'.2
      rw [decide_eq_true_eq, not_not, hflat]
      by_cases hyo : y ∈ w.groups.flatten
      · exact Or.inl hyo
      · exact Or.inr ((h.mutual_iff_of_first hs hi hg hfirst y).2 (Or.inr ⟨hy'.1, hyo, hyv⟩))
    have e3 : ([v].filter fun y => decide (y ∉ w'.groups.flatten)) = [] := by
      simp [hflat, mutual_refl]
    rw [e1, e2, e3, List.append_nil, List.append_nil]
  · -- box invariant 2
    intro y hy hy0 hyl
    rw [hLO y, not_or] at hyl
    rw [hlowout y hyl.2, hcb y]
    exact hval.2.1 y hy (by rwa [hpre] at hy0) hyl.1
  · -- box invariant 3
    intro y hy
    rw [hLO y, hflat y]
    by_cases hyv : Mutual g y v
    · simp [hyv, hlowin y hyv]
    · rw [hlowout y hyv]
      simp only [hyv, or_false]
      exact hval.2.2.1 y hy
  · intro m hm u hu x hx
    rw [hgr] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hval.2.2.2 m hm u hu x hx
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [hmem x]
      have := (hmem u).1 hu
      exact ⟨fun hxv => hxv.trans this.symm, fun hxu => hxu.trans this⟩
  · intro y
    rw [hpre]
    by_cases hyv : Mutual g y v
    · rw [hlowin y hyv]
      have hy0 : w.pre y ≠ 0 := by
        rcases (h.mutual_iff_of_first hs hi hg hfirst y).1 hyv with rfl | ⟨hyf, -⟩
        · exact hv0
        · exact h.fin_entered hyf
      simp [done, hy0]
    · rw [hlowout y hyv]
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
    · obtain ⟨ha1, ha2⟩ := hE a ha
      have hap : a.1 ∈ vertices w' := by rw [hpl']; exact ha1
      exact ⟨h.path_entered (hRsub _ hap), ha2 ▸ hv0⟩
  · intro y hy
    rw [hfin]
    rcases (hflat y).1 hy with hy | hy
    · exact List.mem_append_left _ (h.out_fin y hy)
    · rcases (h.mutual_iff_of_first hs hi hg hfirst y).1 hy with rfl | ⟨hyf, -⟩
      · simp
      · exact List.mem_append_left _ hyf
  · intro x hx y hxy
    rcases (hflat x).1 hx with hxo | hxv
    · have hxn : ¬ Mutual g x v := fun hm => hdisj x hm hxo
      obtain ⟨hyo, hyx⟩ := h.out_closed x hxo y hxy
      have hyn : ¬ Mutual g y v := fun hm => hdisj y hm hyo
      exact ⟨(hflat y).2 (Or.inl hyo), by rw [hemout y hyn, hemout x hxn]; exact hyx⟩
    · refine ⟨(hflat y).2 (h.out_or_mutual_of_first hs hi hg hfirst (hxv.2.trans hxy)), ?_⟩
      rw [hemin x hxv]
      rcases h.out_or_mutual_of_first hs hi hg hfirst (hxv.2.trans hxy) with hyo | hyv
      · rw [hemout y fun hm => hdisj y hm hyo]
        exact (h.emitted_lt hyo).le
      · rw [hemin y hyv]
  · intro k hk y hy
    have key : ∀ (L : List (List ℕ)), L = w.groups ++ [grp] → ∀ (hk : k < L.length),
        y ∈ L[k] → w'.emitted y = k := by
      intro L hL hk hy
      subst hL
      by_cases hkl : k < w.groups.length
      · rw [List.getElem_append_left hkl] at hy
        have hyo : y ∈ w.groups.flatten :=
          List.mem_flatten.2 ⟨_, List.getElem_mem hkl, hy⟩
        rw [hemout y fun hm => hdisj y hm hyo]
        exact h.grp_idx k hkl y hy
      · have hk' : k = w.groups.length := by
          simp only [List.length_append, List.length_singleton] at hk
          omega
        subst hk'
        simp only [List.getElem_concat_length] at hy
        exact hemin y ((hmem y).1 hy)
    exact key _ hgr hk hy
  · intro m hm
    rw [hgr] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact h.grp_ne m hm
    · simp only [List.mem_singleton] at hm
      subst hm
      simp [grp]
  · intro m hm
    rw [hgr] at hm
    rcases List.mem_append.1 hm with hm | hm
    · exact h.grp_nodup m hm
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [hgrp]
      refine List.nodup_append.2 ⟨?_, by simp, fun a ha b hb => ?_⟩
      · exact (h.fin_nodup.sublist List.filter_sublist).sublist List.filter_sublist
      · simp only [List.mem_singleton] at hb
        exact hb ▸ ne_of_mem_of_not_mem ((hmemB a).1 ha).1 hvf
  · intro m hm
    rw [hgr] at hm
    rw [hfin]
    rcases List.mem_append.1 hm with hm | hm
    · exact (h.grp_sub m hm).trans (List.sublist_append_left _ _)
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [hgrp]
      refine List.Sublist.append ?_ (List.Sublist.refl _)
      exact List.filter_sublist.trans List.filter_sublist
  · intro y hy hyo
    rw [hfin] at hy
    rw [hflat, not_or] at hyo
    rw [hlowout y hyo.2, hpre]
    rcases List.mem_append.1 hy with hy | hy
    · exact h.open_low y hy hyo.1
    · simp only [List.mem_singleton] at hy
      exact absurd (by rw [hy]; exact mutual_refl v) hyo.2
  · intro y hy
    have hyn : ¬ Mutual g y v := hnm y (h.path_entered (hRsub y hy)) (hRlt y hy)
    rw [hlead, hlowout y hyn, hpre]
    exact h.lead_iff y (hRsub y hy)
  · intro y hy hyo
    rw [hfin] at hy
    rw [hflat, not_or] at hyo
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨q, hq, hqy⟩ := h.open_gray y hy hyo.1
      rw [hpl] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact absurd hqy.symm hyo.2
      · exact ⟨q, hq, hqy⟩
    · simp only [List.mem_singleton] at hy
      exact absurd (by rw [hy]; exact mutual_refl v) hyo.2
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
    rw [hpre, hcb]
    rcases List.mem_append.1 ha with ha | ha
    · exact h.retreat_low a ha hm
    · exact absurd hm (hEnm a ha).1
  · intro z x hx hz hzx hm
    rw [hfin] at hx
    rw [hpre] at hz
    rw [hcb, hcb]
    obtain ⟨hzxp, hcase⟩ := hzx
    rw [hpre] at hzxp
    rcases List.mem_append.1 hx with hxf | hxv
    · have hxv : x ≠ v := fun he => hvf (he ▸ hxf)
      rcases hcase with ⟨hzf, hsub⟩ | ⟨hzp, hall⟩
      · rw [hfin] at hzf hsub
        by_cases hzv : z = v
        · rw [hzv] at hzxp hm ⊢
          exact h.folded v x hxf hv0 (hfv x hzxp) hm
        · have hzf' : z ∈ w.finished :=
            (List.mem_append.1 hzf).resolve_right (by simpa using hzv)
          exact h.folded z x hxf hz ⟨hzxp, Or.inl ⟨hzf', pair_sublist_of_append hsub hzv⟩⟩ hm
      · refine h.folded z x hxf hz ⟨hzxp, Or.inr ⟨hRsub z hzp, fun p hp hzp' => ?_⟩⟩ hm
        rw [hpl] at hp
        rcases List.mem_cons.1 hp with rfl | hp
        · by_contra hle
          have hpx : w.pre p < w.pre x :=
            lt_of_le_of_ne (Nat.le_of_not_lt hle) fun he => hxv (h.pre_inj p x hv0 he).symm
          have hzp0 := h.path_entered (hRsub z hzp)
          refine hnm z hzp0 (hRlt z hzp) ⟨h.reach z (hRsub z hzp) p hv0 (hRlt z hzp).le, ?_⟩
          exact (h.reach p hvp x (h.fin_entered hxf) hpx.le).trans hm.2
        · have := hall p hp
          rw [hpre] at this
          exact this hzp'
    · simp only [List.mem_singleton] at hxv
      subst hxv
      exact absurd hm (hnm z hz hzxp)

end AlgorithmT

end AlgoDesign.Graphs.Scc
