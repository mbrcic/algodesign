/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Report

/-!
# Bridges, cut vertices and blocks: who separates whom, read off the tree

On the finished walk, deleting a vertex `v` cuts off exactly the subtrees of its *closed* children:
the children whose subtree cannot climb above `v`, or every child when `v` is a root. Everything
else in `v`'s piece stays together, joined to the root (`separates_iff_tree`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

/-- `c` is a child of `v` whose subtree is cut off when `v` fails: `v` is a root, or the subtree
cannot climb above `v`. -/
def ClosedChild (w : Walk) (v c : ℕ) : Prop :=
  Child w v c ∧ (w.arrival v = none ∨ w.entry v ≤ w.low c)

theorem joins_of_link {x y : ℕ} (hl : g.Link x y) : ∃ i, Joins g i x y := by
  rcases hl with h | h
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact ⟨i, Or.inr hi⟩

theorem link_of_joins {i x y : ℕ} (h : Joins g i x y) : g.Link x y := by
  rcases h with h | h
  · exact Or.inl (List.mem_of_getElem? h)
  · exact Or.inr (List.mem_of_getElem? h)

section Done

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hD : Done (g := g) w)
include hS hO hD

include hg in
/-- **A closed child's subtree is cut off when `v` fails.** -/
theorem not_connected_closed {v c z₁ z₂ : ℕ} (hc : ClosedChild w v c) (h₁ : Above w c z₁)
    (h₂ : ¬ Above w c z₂) : ¬ (isolate g v).Connected z₁ z₂ := by
  obtain ⟨⟨hce, hca, hcu⟩, hcl⟩ := hc
  have hcn := lt_n_of_entered hO hce
  have hcf := (done_finished hS hD hcn).2
  have hve : w.entry v ≠ 0 := by
    have := (hangs hS hO c hca).2.2.2.1
    rwa [hcu] at this
  have hclosed : ∀ z z', (isolate g v).Link z z' → Above w c z → Above w c z' := by
    intro z z' hl hz
    by_contra hz'
    obtain ⟨hl', -, hz'v⟩ := link_isolate.mp hl
    obtain ⟨i, hi⟩ := joins_of_link hl'
    rcases leave_sub hg hS hO hcf hca hi hz hz' with ⟨-, h, -⟩ | ⟨h1, h2⟩
    · exact hz'v (h.trans hcu)
    · rw [hcu] at h1
      rcases hcl with hva | hle
      · exact hz'v (above_root hva h1)
      · have hz'e := (entry_le_of_above hS hO h1 hve).1
        have := entry_le_of_above' hS hO h1 hz'e
        exact hz'v (entry_inj hS hO hz'e (by omega))
  intro hcon
  exact h₂ (mem_of_connected_closed hclosed hcon h₁)

omit hD in
/-- Below a root, a vertex not under `v` reaches the root avoiding `v`. -/
theorem connected_up_isolate {v r z : ℕ} (hrz : Above w r z) (hvz : ¬ Above w v z) :
    (isolate g v).Connected r z := by
  refine connected_down_isolate hS hO hrz fun t h1 h2 h3 => ⟨fun h => hvz (h ▸ h2),
    fun h => hvz ?_⟩
  have hta : w.arrival t ≠ none := ((above_iff.mp h1).resolve_left (Ne.symm h3)).1
  exact h ▸ (Above.up hta).trans h2

include hg in
/-- Under a child of `v` that is not closed, every vertex reaches the root avoiding `v`. -/
theorem connected_open {v c r z : ℕ} (hc : Child w v c) (hva : w.arrival v ≠ none)
    (hopen : w.low c < w.entry v) (hra : w.arrival r = none) (hrv : Above w r v)
    (hcz : Above w c z) : (isolate g v).Connected z r := by
  obtain ⟨hce, hca, hcu⟩ := hc
  have hcn := lt_n_of_entered hO hce
  have hve : w.entry v ≠ 0 := (hangs hS hO v hva).2.1
  have hvlt : w.entry v < w.entry c := by
    have := (hangs hS hO c hca).2.2.2.2.1
    rwa [hcu] at this
  rw [shape_low_eq hS hcn hce, climb_lt_iff] at hopen
  rcases hopen with h | ⟨z0, hz0n, hex, ⟨y0, h0⟩, hs, -, hy0⟩
  · omega
  simp only at hy0
  have hcz0 := above_of_explored hS hO hex
  have hz0e := entered_of_above hS hO hcz0 hce
  have hz0f := (done_finished hS hD hz0n).2
  have hj : Joins g h0 z0 y0 := joins_of_adj_mem (List.mem_of_mem_take hs)
  have hcz0le := entry_le_of_above' hS hO hcz0 hce
  have hyz : y0 ≠ z0 := fun h => by rw [h] at hy0; omega
  obtain ⟨-, hyz' | hzy⟩ := link_of_finished hg hS hO hz0n hz0f hj hyz
  swap
  · have := entry_le_of_above' hS hO hzy hz0e
    omega
  have hnvy : ¬ Above w v y0 := fun h => by
    have := entry_le_of_above' hS hO h hve
    omega
  have hry0 : Above w r y0 := by
    have hrz0 : Above w r z0 := hrv.trans ((hcu ▸ Above.up hca).trans hcz0)
    rcases above_total hyz' hrz0 with h | h
    · exact (above_root hra h) ▸ Above.refl w r
    · exact h
  have hy0v : y0 ≠ v := fun h => hnvy (h ▸ Above.refl w v)
  have hz0v : z0 ≠ v := fun h => by rw [h] at hcz0le; omega
  have c0 := connected_below_isolate hS hO hcz hce hvlt
  have c1 := connected_below_isolate hS hO hcz0 hce hvlt
  have c2 : (isolate g v).Connected z0 y0 :=
    connected_of_link (link_isolate.mpr ⟨link_of_joins hj, hz0v, hy0v⟩)
  have c3 := connected_symm (connected_up_isolate hS hO hry0 hnvy)
  exact connected_trans (connected_symm c0) (connected_trans c1 (connected_trans c2 c3))

include hg in
/-- **Who separates whom**: on the finished walk, `v` separates two vertices of one piece, neither
`v`, exactly when one of them lies under a closed child of `v` and the other does not. -/
theorem separates_iff_tree {v x y : ℕ} (hxn : x < g.n) (hvx : v ≠ x) (hvy : v ≠ y)
    (hcxy : g.Connected x y) :
    Separates g v x y ↔ ∃ c, ClosedChild w v c ∧ (Above w c x ↔ ¬ Above w c y) := by
  constructor
  swap
  · rintro ⟨c, hc, hiff⟩
    refine ⟨hvx, hvy, hcxy, ?_⟩
    by_cases hx : Above w c x
    · exact not_connected_closed hg hS hO hD hc hx (hiff.mp hx)
    · have hy : Above w c y := by
        by_contra hy
        exact hx (hiff.mpr hy)
      exact fun h => not_connected_closed hg hS hO hD hc hy hx (connected_symm h)
  · rintro ⟨-, -, -, hncon⟩
    by_contra hnot'
    have hnot : ∀ c, ClosedChild w v c → (Above w c x ↔ Above w c y) := by
      intro c hc
      by_contra h
      exact hnot' ⟨c, hc, by tauto⟩
    apply hncon
    have hxe := (done_finished hS hD hxn).1
    obtain ⟨r, hrx, hra, -⟩ := exists_root hS hO _ x le_rfl hxe
    have hry : Above w r y := above_of_connected hg hS hO hD hra hrx hcxy
    by_cases hrv : Above w r v
    swap
    · have hclosed : ∀ z z', g.Link z z' →
          (Above w r z ∧ (isolate g v).Connected x z) →
          (Above w r z' ∧ (isolate g v).Connected x z') := by
        intro z z' hl ⟨hz, hxz⟩
        have hz' : Above w r z' := above_of_connected hg hS hO hD hra hz (connected_of_link hl)
        exact ⟨hz', hxz.tail (link_isolate.mpr ⟨hl, fun h => hrv (h ▸ hz),
          fun h => hrv (h ▸ hz')⟩)⟩
      exact (mem_of_connected_closed hclosed hcxy ⟨hrx, ReflTransGen.refl⟩).2
    have hchild : ∀ z, Above w v z → z ≠ v → ∃ c, Child w v c ∧ Above w c z := by
      intro z hvz hzv
      obtain ⟨c, hcz, hca, hcu⟩ := exists_child_of_above hvz (Ne.symm hzv)
      exact ⟨c, ⟨(hangs hS hO c hca).2.1, hca, hcu⟩, hcz⟩
    -- two vertices under one closed child stay together
    have hsame : ∀ c, Child w v c → Above w c x → Above w c y →
        (isolate g v).Connected x y := by
      intro c ⟨hce, hca, hcu⟩ hx hy
      have hvlt : w.entry v < w.entry c := by
        have := (hangs hS hO c hca).2.2.2.2.1
        rwa [hcu] at this
      exact connected_trans (connected_symm (connected_below_isolate hS hO hx hce hvlt))
        (connected_below_isolate hS hO hy hce hvlt)
    by_cases hva : w.arrival v = none
    · have hrv' : r = v := above_root hva hrv
      subst hrv'
      obtain ⟨c, hc, hcx⟩ := hchild x hrx (Ne.symm hvx)
      exact hsame c hc hcx ((hnot c ⟨hc, Or.inl hva⟩).mp hcx)
    · -- every vertex not under a closed child reaches the root avoiding `v`
      have hreach : ∀ z < g.n, z ≠ v → Above w r z →
          (∀ c, ClosedChild w v c → ¬ Above w c z) → (isolate g v).Connected z r := by
        intro z hzn hzv hrz hnc
        by_cases hvz : Above w v z
        · obtain ⟨c, hc, hcz⟩ := hchild z hvz hzv
          have hopen : w.low c < w.entry v := by
            by_contra h
            exact hnc c ⟨hc, Or.inr (by omega)⟩ hcz
          exact connected_open hg hS hO hD hc hva hopen hra hrv hcz
        · exact connected_symm (connected_up_isolate hS hO hrz hvz)
      by_cases hxc : ∃ c, ClosedChild w v c ∧ Above w c x
      · obtain ⟨c, hc, hcx⟩ := hxc
        exact hsame c hc.1 hcx ((hnot c hc).mp hcx)
      · push Not at hxc
        have hyc : ∀ c, ClosedChild w v c → ¬ Above w c y :=
          fun c hc hcy => hxc c hc ((hnot c hc).mpr hcy)
        have hyn : y < g.n := lt_n_of_entered hO
          (entered_of_above hS hO hry (entered_of_above hS hO (Above.refl w r)
            (entry_le_of_above hS hO hrx hxe).1))
        exact connected_trans (hreach x hxn (Ne.symm hvx) hrx hxc)
          (connected_symm (hreach y hyn (Ne.symm hvy) hry hyc))

end Done

end Walk

end AlgoDesign.Graphs.Blocks
