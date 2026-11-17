/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkRetreat

/-!
# Algorithm T: what holds when the current vertex finishes

When the current vertex `v` has looked at its whole row, every arrow from it has been come back
over (`Inv.row_done`). Then `v` leads exactly when it is the first-entered member of its
component (`Inv.lead_iff_first`, Tarjan–Zwick Lemma 3.7 with Lemma 3.6): if a member entered
earlier, a path to it leaves the vertices entered since `v` along an arrow from a finished
descendant (or `v`) whose branch has been come back from, to a vertex entered before `v`; that
arrow gives the descendant a climb-back number below `v`'s entry number, and so `v`. Back the other
way, a climb-back number below the entry number is the entry number of a member entered earlier.

When `v` is first in its component, the component is `v` and the vertices waiting on `F` entered
after `v` (`Inv.mutual_iff_of_first`), and every vertex reachable from `v` is in a group out or in
`v`'s component (`Inv.out_or_mutual_of_first`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-- `v` was entered first of the entered members of its component. -/
def First (w : Walk) (v : ℕ) : Prop := ∀ u, w.pre u ≠ 0 → Mutual g u v → w.pre v ≤ w.pre u

/-- An arrow of a vertex whose whole row has been come back over is in the log. -/
theorem retreated_of_row (hg : g.WellFormed) {log : List (ℕ × ℕ)} {x y : ℕ}
    (hrow : RowRetreated g log x (g.out x).length) (hxy : g.Arrow x y) : (x, y) ∈ log := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hxy
  have hm : (y, i) ∈ g.out x := mem_out.2 ⟨(hg _ (List.mem_of_getElem? hi)).2, hi⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm
  exact hrow j (List.getElem?_eq_some_iff.1 hj).1 _ hj

section Top

variable {w : Walk} (h : Inv g w) {v i : ℕ} {rest : List (ℕ × ℕ)} (hs : w.path = (v, i) :: rest)
  (hi : (g.out v)[i]? = none)
include h hs hi

theorem Inv.row_done : RowRetreated g w.retreats v (g.out v).length := by
  have hf := h.frames
  rw [hs] at hf
  have := List.getElem?_eq_none_iff.1 hi
  have : i = (g.out v).length := le_antisymm hf.1 this
  exact this ▸ hf.2.1

/-- Every arrow of a finished vertex or of the current vertex has been come back over. -/
theorem Inv.retreated_of_closed (hg : g.WellFormed) {x y : ℕ} (hx : x ∈ w.finished ∨ x = v)
    (hxy : g.Arrow x y) : (x, y) ∈ w.retreats := by
  rcases hx with hx | rfl
  · exact retreated_of_row hg (h.fin_rows x hx) hxy
  · exact retreated_of_row hg (h.row_done hs hi) hxy

/-- From the current vertex, every vertex reachable is entered, or reachable through a vertex
below it on the path. -/
theorem Inv.entered_or_below (hg : g.WellFormed) {z : ℕ} (hvz : g.Reaches v z) :
    w.pre z ≠ 0 ∨ ∃ p ∈ vertices w, p ≠ v ∧ g.Reaches v p := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  induction hvz with
  | refl => exact Or.inl (h.path_entered hvp)
  | tail hva hab ih =>
    rename_i a b
    rcases ih with ha | hp
    · by_cases hav : a = v
      · exact Or.inl (h.retreat_ent _ (h.retreated_of_closed hs hi hg (Or.inr hav) hab)).2
      · rcases (h.entered a).1 ha with ha | ha
        · exact Or.inr ⟨a, ha, hav, hva⟩
        · exact Or.inl (h.retreat_ent _ (h.retreated_of_closed hs hi hg (Or.inl ha) hab)).2
    · exact Or.inr hp

/-- **The current vertex leads exactly when it was entered first in its component** (Tarjan–Zwick
Lemma 3.7). -/
theorem Inv.lead_iff_first (hg : g.WellFormed) : w.lead v = true ↔ First (g := g) w v := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  have hvo := h.not_out_of_path hvp
  have hlow := h.low_eq hv0 hvo
  rw [h.lead_iff v hvp, hlow]
  constructor
  · intro hcb u hu huv
    by_contra hle
    have hlt : w.pre u < w.pre v := Nat.lt_of_not_le hle
    obtain ⟨x, y, hvx, hx, hxy, hy, hyu⟩ :=
      exists_cross (fun y => w.pre y ≠ 0 ∧ w.pre v ≤ w.pre y) huv.2 ⟨hv0, le_rfl⟩
        (fun h' => by omega)
    have hxc : x ∈ w.finished ∨ x = v := by
      rcases (h.entered x).1 hx.1 with hxp | hxf
      · exact Or.inr (h.pre_inj x v hx.1 (le_antisymm (h.pre_le_top hs hxp) hx.2))
      · exact Or.inl hxf
    have hlog := h.retreated_of_closed hs hi hg hxc hxy
    have hy0 := (h.retreat_ent _ hlog).2
    have hyv : w.pre y < w.pre v := by
      by_contra h'
      exact hy ⟨hy0, Nat.le_of_not_lt h'⟩
    have hmxy : Mutual g x y :=
      ⟨reaches_of_arrow hxy, hyu.trans (huv.1.trans hvx)⟩
    have hcx := h.retreat_low _ hlog hmxy
    rcases hxc with hxf | rfl
    · have hxv : x ≠ v := fun he => h.path_fin v hvp (he ▸ hxf)
      have hpre : w.pre v < w.pre x :=
        lt_of_le_of_ne hx.2 fun he => hxv (h.pre_inj v x hv0 he).symm
      have hfold : Folded w v x :=
        ⟨hpre, Or.inr ⟨hvp, fun p hp hvp' => absurd (h.pre_le_top hs hp) (by omega)⟩⟩
      have := h.folded v x hxf hv0 hfold
        ⟨hvx, (reaches_of_arrow hxy).trans (hyu.trans huv.1)⟩
      dsimp only at hcx
      omega
    · dsimp only at hcx
      omega
  · intro hfirst
    rcases exists_climbBack (g := g) w v with he | ⟨z, hz, he⟩
    · exact he
    · rcases head_of_mem_reachList hz with rfl | ⟨a, ha⟩
      · exact he
      · have := hfirst z (h.retreat_ent _ ha).2 (mutual_of_mem_reachList hz).symm
        have := climbBack_le_pre (g := g) w v
        omega

section First

variable (hg : g.WellFormed) (hfirst : First (g := g) w v)
include hg hfirst

omit hi hg in
/-- A finished vertex waiting on `F`, entered after the current vertex, is in its component. -/
theorem Inv.mutual_of_waiting {x : ℕ} (hxf : x ∈ w.finished) (hxo : x ∉ w.groups.flatten)
    (hx : w.pre v < w.pre x) : Mutual g x v := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  obtain ⟨q, hq, hqx⟩ := h.open_gray x hxf hxo
  have hqv := h.reach q hq v hv0 (h.pre_le_top hs hq)
  have hvx := h.reach v hvp x (h.fin_entered hxf) hx.le
  have hmq : Mutual g q v := ⟨hqv, hvx.trans hqx.2⟩
  have := hfirst q (h.path_entered hq) hmq
  have hqe : q = v := h.pre_inj q v (h.path_entered hq) (le_antisymm (h.pre_le_top hs hq) this)
  exact hqe ▸ hqx.symm

/-- **The current vertex's component, when it leads**: itself, and the finished vertices waiting on
`F` that were entered after it. -/
theorem Inv.mutual_iff_of_first (y : ℕ) : Mutual g y v ↔
    y = v ∨ (y ∈ w.finished ∧ y ∉ w.groups.flatten ∧ w.pre v < w.pre y) := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  have hv0 := h.path_entered hvp
  constructor
  · intro hyv
    have hy0 : w.pre y ≠ 0 := by
      rcases h.entered_or_below hs hi hg hyv.2 with hy | ⟨p, hp, hpv, hvp'⟩
      · exact hy
      · have hpv' := h.reach p hp v hv0 (h.pre_le_top hs hp)
        have := hfirst p (h.path_entered hp) ⟨hpv', hvp'⟩
        exact absurd (h.pre_inj p v (h.path_entered hp)
          (le_antisymm (h.pre_le_top hs hp) this)) hpv
    by_cases hye : y = v
    · exact Or.inl hye
    · have hle := hfirst y hy0 hyv
      have hlt : w.pre v < w.pre y :=
        lt_of_le_of_ne hle fun he => hye (h.pre_inj v y hv0 he).symm
      have hyf : y ∈ w.finished := by
        rcases (h.entered y).1 hy0 with hyp | hyf
        · exact absurd (h.pre_le_top hs hyp) (by omega)
        · exact hyf
      refine Or.inr ⟨hyf, fun ho => ?_, hlt⟩
      exact h.not_out_of_path hvp (h.out_closed y ho v hyv.1).1
  · rintro (rfl | ⟨hyf, hyo, hlt⟩)
    · exact mutual_refl y
    · exact h.mutual_of_waiting hs hfirst hyf hyo hlt

/-- **Everything the current vertex reaches, when it leads, is in a group out or in its
component.** -/
theorem Inv.out_or_mutual_of_first {z : ℕ} (hvz : g.Reaches v z) :
    z ∈ w.groups.flatten ∨ Mutual g z v := by
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  induction hvz with
  | refl => exact Or.inr (mutual_refl v)
  | tail hva hab ih =>
    rename_i a b
    rcases ih with ha | ha
    · exact Or.inl (h.out_closed a ha b (reaches_of_arrow hab)).1
    · have hac : a ∈ w.finished ∨ a = v := by
        rcases (h.mutual_iff_of_first hs hi hg hfirst a).1 ha with rfl | ⟨haf, -⟩
        · exact Or.inr rfl
        · exact Or.inl haf
      have hb0 := (h.retreat_ent _ (h.retreated_of_closed hs hi hg hac hab)).2
      by_cases hbo : b ∈ w.groups.flatten
      · exact Or.inl hbo
      · refine Or.inr ⟨?_, hva.tail hab⟩
        rcases (h.entered b).1 hb0 with hbp | hbf
        · exact h.reach b hbp v (h.path_entered hvp) (h.pre_le_top hs hbp)
        · obtain ⟨q, hq, hqb⟩ := h.open_gray b hbf hbo
          exact hqb.2.trans (h.reach q hq v (h.path_entered hvp) (h.pre_le_top hs hq))

end First

end Top

/-! ## Finishing a vertex, unfolded -/

theorem postvisit_of_not_lead {w : Walk} {v : ℕ} (hl : w.lead v = false) :
    postvisit g w v = { w with finished := w.finished ++ [v], followers := v :: w.followers } := by
  simp [postvisit, hl]

theorem postvisit_of_lead {w : Walk} {v : ℕ} (hl : w.lead v = true) :
    postvisit g w v =
      { w with finished := w.finished ++ [v],
               low := fun u => if u ∈ (popFollowers w.low (w.low v) w.followers).1.reverse ++ [v]
                 then done g else w.low u,
               emitted := fun u =>
                 if u ∈ (popFollowers w.low (w.low v) w.followers).1.reverse ++ [v]
                 then w.groups.length else w.emitted u,
               followers := (popFollowers w.low (w.low v) w.followers).2,
               groups :=
                 w.groups ++ [(popFollowers w.low (w.low v) w.followers).1.reverse ++ [v]] } := by
  simp [postvisit, hl]

end AlgorithmT

end AlgoDesign.Graphs.Scc
