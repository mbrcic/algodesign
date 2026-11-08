/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Final
public import AlgoDesign.Graphs.Blocks.Forest

/-!
# Bridges, cut vertices and blocks: the finished walk's report

On the finished walk every link that is not a loop has a deeper end, and that end a first block
top above it (`exists_head`): every child of a root is a block top, since nothing in a tree
climbs above its root. So every such link is in exactly one emitted block, which is a whole block
of the network (`Groups.lean`), and the report is the specification's answer
(`report_promise`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

/-- In lists with no element twice across them, an element is in at most one. -/
theorem index_unique {L : List (List ℕ)} (hL : L.flatten.Nodup) {e j k : ℕ} (hj : j < L.length)
    (hk : k < L.length) (hej : e ∈ L[j]) (hek : e ∈ L[k]) : j = k := by
  rw [List.nodup_flatten, List.pairwise_iff_getElem] at hL
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact List.disjoint_left.mp (hL.2 j k hj hk h) hej hek
  · exact List.disjoint_left.mp (hL.2 k j hk hj h) hek hej

/-- The first list holding `e`, when no element is in two. -/
theorem findIdx_eq_some_iff {L : List (List ℕ)} (hL : L.flatten.Nodup) {e k : ℕ} :
    L.findIdx? (fun b => decide (e ∈ b)) = some k ↔ ∃ h : k < L.length, e ∈ L[k] := by
  rw [List.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨h, he, -⟩
    exact ⟨h, by simpa using he⟩
  · rintro ⟨h, he⟩
    refine ⟨h, by simpa using he, fun j hj hej => ?_⟩
    have := index_unique (j := j) (k := k) hL (by omega) h (by simpa using hej) he
    omega

theorem findIdx_eq_none_iff {L : List (List ℕ)} {e : ℕ} :
    L.findIdx? (fun b => decide (e ∈ b)) = none ↔ ∀ b ∈ L, e ∉ b := by
  rw [List.findIdx?_eq_none_iff]
  simp

section Done

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hD : Done (g := g) w)
include hS hO hD

omit hD in
/-- Nothing in a tree climbs above its root. -/
theorem root_le_low {r x : ℕ} (hra : w.arrival r = none) (hrx : Above w r x)
    (hxe : w.entry x ≠ 0) : w.entry r ≤ w.low x := by
  have hxn := lt_n_of_entered hO hxe
  rw [shape_low_eq hS hxn hxe, le_climb_iff]
  refine ⟨entry_le_of_above' hS hO hrx (entry_le_of_above hS hO hrx hxe).1,
    fun z hzn hex s hs _ => ?_⟩
  have hxz := above_of_explored hS hO hex
  have hrz := hrx.trans hxz
  have hre := (entry_le_of_above hS hO hrx hxe).1
  obtain ⟨hse, hrel⟩ := hS.2.2.2.2.2.1 z hzn s hs
  by_cases hsz : s.1 = z
  · rw [hsz]
    exact entry_le_of_above' hS hO hrz hre
  · rcases hrel hsz with h | h
    · rw [anc_iff hS hO] at h
      rcases above_total h hrz with h' | h'
      · rw [above_root hra h']
      · exact entry_le_of_above' hS hO h' hre
    · rw [anc_iff hS hO] at h
      exact entry_le_of_above' hS hO (hrz.trans h) hre

/-- **Every vertex below a root has a first block top above it.** -/
theorem exists_head : ∀ k x, w.entry x ≤ k → w.entry x ≠ 0 → w.arrival x ≠ none →
    ∃ c, HeadIs (g := g) w x c
  | 0, x, hk, hx, _ => absurd (by omega) hx
  | k + 1, x, hk, hx, hxa => by
    have hxn := lt_n_of_entered hO hx
    have hxf := (done_finished hS hD hxn).2
    obtain ⟨-, -, hun, hue, hlt, -⟩ := hangs hS hO x hxa
    by_cases hbt : BlockTop w x
    · refine ⟨x, (headIs_iff hS hO).mpr ⟨Above.refl w x, hbt, fun c' h1 h2 h3 => ?_⟩⟩
      exact absurd (above_antisymm hS hO h1 h2) h3
    · have hua : w.arrival (w.up x) ≠ none := by
        intro hua
        exact hbt ⟨hxf, hxa, root_le_low hS hO hua (Above.up hxa) hx⟩
      obtain ⟨c, hc⟩ := exists_head k (w.up x) (by omega) hue hua
      obtain ⟨hcu, hct, hbet⟩ := (headIs_iff hS hO).mp hc
      refine ⟨c, (headIs_iff hS hO).mpr ⟨hcu.trans (Above.up hxa), hct, fun c' h1 h2 h3 => ?_⟩⟩
      by_cases hc'x : c' = x
      · exact hc'x ▸ hbt
      · exact hbet c' ((above_iff.mp h1).resolve_left hc'x).2 h2 h3

omit hD in
theorem head_unique {x c c' : ℕ} (h : HeadIs (g := g) w x c) (h' : HeadIs (g := g) w x c') :
    c = c' := by
  obtain ⟨h1, h2, h3⟩ := (headIs_iff hS hO).mp h
  obtain ⟨h1', h2', h3'⟩ := (headIs_iff hS hO).mp h'
  by_contra hne
  rcases above_total h1 h1' with h'' | h''
  · exact h3 c' h1' h'' (Ne.symm hne) h2'
  · exact h3' c h1 h'' hne h2

omit hD in
theorem inGroup_unique {c c' f : ℕ} (h : InGroup (g := g) w c f)
    (h' : InGroup (g := g) w c' f) : c = c' := by
  obtain ⟨-, x, -, hx, hhx⟩ := h
  obtain ⟨-, x', -, hx', hhx'⟩ := h'
  obtain ⟨l, hl, hl1, hl2⟩ := hx
  obtain ⟨l', hl', hl1', hl2'⟩ := hx'
  have hxx : x = x' := by
    have hc := ((headIs_iff hS hO).mp hhx)
    have hce := entered_of_finished hS hO hc.2.1.1
    have hxe := entered_of_above hS hO hc.1 hce
    exact entry_inj hS hO hxe (hl2.trans hl2'.symm)
  subst hxx
  exact head_unique hS hO hhx hhx'

include hg in
/-- **Every link that is not a loop is in a block top's group.** -/
theorem exists_inGroup {f : ℕ} (hf : NonLoop g f) : ∃ c, InGroup (g := g) w c f := by
  obtain ⟨⟨a, b⟩, hab, hne⟩ := hf
  simp only [Option.mem_def] at hab
  simp only at hne
  have han : a < g.n := (hg _ (List.mem_of_getElem? hab)).1
  have hbn : b < g.n := (hg _ (List.mem_of_getElem? hab)).2
  have hae := (done_finished hS hD han).1
  have hbe := (done_finished hS hD hbn).1
  obtain ⟨x, y, hxy, hxe, hyx, hxdeep, hxab⟩ : ∃ x y, Joins g f x y ∧ w.entry x ≠ 0 ∧ y ≠ x ∧
      w.entry x = max (w.entry a) (w.entry b) ∧ (a = x ∨ b = x) := by
    rcases le_or_gt (w.entry a) (w.entry b) with h | h
    · exact ⟨b, a, Or.inr hab, hbe, hne, by omega, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl hab, hae, Ne.symm hne, by omega, Or.inl rfl⟩
  have hxn := lt_n_of_entered hO hxe
  have hxf := (done_finished hS hD hxn).2
  obtain ⟨hye, hyx' | hxy'⟩ := link_of_finished hg hS hO hxn hxf hxy hyx
  swap
  · have := (entry_le_of_above hS hO hxy' hye).2.2 (Ne.symm hyx)
    have hyab : y = a ∨ y = b := by
      rcases Joins.ends (Or.inl hab) hxy with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inr h
      · exact Or.inl h
    rcases hyab with rfl | rfl <;> omega
  have hxa : w.arrival x ≠ none := ((above_iff.mp hyx').resolve_left hyx).1
  obtain ⟨c, hc⟩ := exists_head hS hO hD _ x le_rfl hxe hxa
  refine ⟨c, ⟨⟨(a, b), hab, hne⟩, x, hxn, (y, f), ?_, rfl⟩, x, hxn, ?_, hc⟩
  · rw [looked_of_finished hS hxn hxf]
    exact adj_mem_of_joins hg hxy
  · exact (deep_iff hab).mpr ⟨hxab, hxdeep⟩

/-- An isolated vertex is a finished root with no children. -/
theorem loneRoot_of_isolated {v : ℕ} (hv : IsolatedVertex g v) : LoneRoot (g := g) w v := by
  obtain ⟨hvn, hiso⟩ := hv
  have hjoin : ∀ i y, Joins g i v y → y = v := by
    intro i y h
    rcases h with h | h
    · exact (hiso _ (List.mem_of_getElem? h) (Or.inl rfl)).symm
    · exact hiso _ (List.mem_of_getElem? h) (Or.inr rfl)
  refine ⟨(done_finished hS hD hvn).2, ?_, ?_⟩
  · by_contra hva
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hva
    obtain ⟨-, -, -, -, hlt, hj⟩ := hangs hS hO v hva
    have := hjoin e _ (hj e (by simp [he])).symm
    rw [this] at hlt
    omega
  · unfold numChildren
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    rintro t - ht
    obtain ⟨-, hta, rfl⟩ : Child w v t := of_decide_eq_true ht
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hta
    obtain ⟨-, -, -, -, hlt, hj⟩ := hangs hS hO t hta
    have := congrArg w.entry (hjoin e _ (hj e (by simp [he])))
    omega

include hg in
/-- **The finished walk's report is the specification's answer**: exactly the bridges and the cut
vertices, and the network's blocks with their vertices. -/
theorem report_promise :
    (∀ e, e ∈ (report g w).bridges ↔ IsBridge g e) ∧
    (∀ v, v ∈ (report g w).cutVertices ↔ IsCutVertex g v) ∧
    BlocksAgree g (report g w) ∧ VerticesAgree g (report g w) ∧ (report g w).cutVertices.Nodup := by
  have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBr := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCut := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hflat := hBO.2.2.2.2.2.2.2.1
  have hbl : ∀ e < g.links.length, (report g w).blockOfLink.getD e none =
      w.blocks.findIdx? (fun b => decide (e ∈ b)) := by
    intro e he
    simp [report, he]
  have hgetD : ∀ k (hk : k < w.blocks.length), w.blocks.getD k [] = w.blocks[k] := by
    intro k hk
    simp [hk]
  -- a link in a block is in that block's group
  have hgrp : ∀ k (hk : k < w.blocks.length) e, e ∈ w.blocks[k] →
      ∃ c, ∀ f < g.links.length, f ∈ w.blocks[k] ↔ InGroup (g := g) w c f := by
    intro k hk e he
    obtain ⟨c, -, -, -, hiff⟩ := hBO.2.2.1 k hk (by rw [hgetD k hk]; exact List.ne_nil_of_mem he)
    exact ⟨c, by rwa [hgetD k hk] at hiff⟩
  have hlt : ∀ k (hk : k < w.blocks.length) e, e ∈ w.blocks[k] → e < g.links.length :=
    fun k hk e he => hBO.2.2.2.2.2.2.2.2 _ (List.getElem_mem hk) e he
  have hnl : ∀ k (hk : k < w.blocks.length) e, e ∈ w.blocks[k] → NonLoop g e := by
    intro k hk e he
    obtain ⟨c, hiff⟩ := hgrp k hk e he
    exact ((hiff e (hlt k hk e he)).mp he).1.1
  have hhas : ∀ e, NonLoop g e → ∃ k, ∃ hk : k < w.blocks.length, e ∈ w.blocks[k] := by
    intro e hne
    have hem : e < g.links.length := by
      obtain ⟨l, hl, -⟩ := hne
      exact (List.getElem?_eq_some_iff.mp (Option.mem_def.mp hl)).1
    obtain ⟨c, hc⟩ := exists_inGroup hg hS hO hD hne
    obtain ⟨x, -, -, hhead⟩ := hc.2
    obtain ⟨-, hct, -⟩ := (headIs_iff hS hO).mp hhead
    obtain ⟨k, hk, -, -, hiff⟩ := hBO.2.2.2.2.1 c (finished_lt hO hct.1) hct
    rw [hgetD k hk] at hiff
    exact ⟨k, hk, (hiff e hem).mpr hc⟩
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e
    simp only [report, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hb⟩
      exact (isBridge_iff_tree hg hS hO hD he).mpr ((hBr.2.2 e he).mp hb)
    · intro h
      exact ⟨h.1, (hBr.2.2 e h.1).mpr ((isBridge_iff_tree hg hS hO hD h.1).mp h)⟩
  · intro v
    simp only [report, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hv, hc⟩
      exact (isCutVertex_iff_tree hg hS hO hD hv).mpr ((hCut v hv).mp hc)
    · intro h
      exact ⟨h.1, (hCut v h.1).mpr ((isCutVertex_iff_tree hg hS hO hD h.1).mp h)⟩
  · intro e he
    rw [hbl e he, findIdx_eq_none_iff]
    constructor
    · intro h hne
      obtain ⟨k, hk, hek⟩ := hhas e hne
      exact h _ (List.getElem_mem hk) hek
    · intro h b hb heb
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
      exact h (hnl k hk e heb)
  · intro e he f hf hne hnf
    obtain ⟨ke, hke, heke⟩ := hhas e hne
    obtain ⟨kf, hkf, hfkf⟩ := hhas f hnf
    rw [hbl e he, hbl f hf, (findIdx_eq_some_iff hflat).mpr ⟨hke, heke⟩,
      (findIdx_eq_some_iff hflat).mpr ⟨hkf, hfkf⟩, Option.some.injEq]
    obtain ⟨c, hiff⟩ := hgrp ke hke e heke
    constructor
    · rintro rfl
      exact sameBlock_of_inGroup hg hS hO ((hiff e he).mp heke) ((hiff f hf).mp hfkf)
    · intro hsb
      have hfke := (hiff f hf).mpr (inGroup_of_sameBlock hg hS hO ((hiff e he).mp heke) hsb)
      exact index_unique hflat hke hkf hfke hfkf
  · intro e he
    rw [hbl e he]
    rcases h : w.blocks.findIdx? (fun b => decide (e ∈ b)) with _ | k
    · rfl
    · obtain ⟨hk, -⟩ := (findIdx_eq_some_iff hflat).mp h
      simp only [Option.all_some]
      exact decide_eq_true hk
  · intro e he k hk
    rw [hbl e he, findIdx_eq_some_iff hflat]
    simp only [report, hgetD k hk]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩
  · intro v hv hiso
    obtain ⟨k, hk, h1, h2⟩ := hBO.2.2.2.2.2.1 v hv (loneRoot_of_isolated hS hO hD hiso)
    exact ⟨k, hk, h1, h2⟩
  · exact hBO.1
  · exact hBO.2.1
  · intro k hk hemp
    obtain ⟨r, -, ⟨-, hpl⟩, hlone⟩ := hBO.2.2.2.1 k hk hemp
    simp only [report]
    rw [hpl]
    exact ⟨rfl, fun v hv => by
      rw [List.mem_singleton] at hv
      exact hv ▸ isolated_of_loneRoot hg hS hO hlone⟩
  · intro j hj k hk hje hke hpl
    obtain ⟨r, hr, ⟨-, hplk⟩, -⟩ := hBO.2.2.2.1 k hk hke
    simp only [report] at hpl
    exact hBO.2.2.2.2.2.2.1 j hj k hk r hr ⟨hje, hpl.trans hplk⟩ ⟨hke, hplk⟩
  · exact List.nodup_range.filter _

end Done

end Walk

end AlgoDesign.Graphs.Blocks
