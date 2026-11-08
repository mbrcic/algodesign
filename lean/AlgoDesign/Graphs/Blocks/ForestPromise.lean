/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.ForestDfs

/-!
# Bridges, cut vertices and blocks: the separators the forest lists

On the finished walk, the forest lists for two vertices in one piece exactly the vertices whose
failure alone separates them, and answers `none` for vertices in different pieces
(`forest_promise`). The forest's meeting climb lists the cut vertices with a child above exactly
one end (`Forest.separators_spec`); a cut vertex's children are the blocks of the block tops that
hang from it, which are its closed children; and a block lies above a vertex's node exactly when
its top lies above the vertex (`dAnc_block_iff`), which is `separates_iff_tree`'s test.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

section Done

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hD : Done (g := g) w)
include hg hS hO hD

/-- **A cut vertex's children in the forest** are the blocks of the block tops hanging from it. -/
theorem parentOf_eq_cut_iff {q c' : ℕ} (hq : q ∈ cuts g w) :
    (parentOf (g := g) w c' = cutNodeOf (g := g) w q ∧ c' ≠ cutNodeOf (g := g) w q) ↔
      ∃ c, BlockTop w c ∧ w.up c = q ∧ c' = blockOf (g := g) w c := by
  have hlo := (cutNodeOf_lt hq).1
  constructor
  · rintro ⟨hp, hne⟩
    by_cases hsz : c' < Forest.size (report g w)
    · rcases node_classify hsz with hb | ⟨p', hp', rfl⟩
      · by_cases he : w.blocks.getD c' [] = []
        · rw [parentOf_empty hb he] at hp
          exact absurd hp hne
        · rw [parentOf_nonempty hb he] at hp
          split_ifs at hp with hcut
          · obtain ⟨-, hct, -⟩ := topOf_spec hS hb he
            obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO _ hct.2.1
            exact ⟨_, hct, cutNodeOf_inj (mem_cuts.mpr ⟨hun, hcut⟩) hq hp,
              (blockOf_topOf hg hS hO hD hb he).symm⟩
          · exact absurd hp hne
      · exfalso
        rw [parentOf_cut hp'] at hp
        split_ifs at hp with hpa
        · exact hne hp
        · have hpn := (mem_cuts.mp hp').1
          obtain ⟨-, hht, -⟩ := (headIs_iff hS hO).mp (headOf_spec hS hO hD hpn hpa)
          have := (blockOf_spec hS hO hht).1
          omega
    · exfalso
      rw [size_eq] at hsz
      have hp' : parentOf (g := g) w c' = c' := by
        unfold parentOf
        rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]
      exact hne (hp' ▸ hp)
  · rintro ⟨c, hct, hcu, rfl⟩
    obtain ⟨hb, -⟩ := blockOf_spec hS hO hct
    refine ⟨?_, by omega⟩
    rw [parentOf_blockOf hg hS hO hD hct, hcu, ite_eq_left (mem_cuts.mp hq).2]

omit hg in
/-- A closed child is a block top hanging from the vertex. -/
theorem closedChild_iff {q c : ℕ} : ClosedChild w q c ↔ BlockTop w c ∧ w.up c = q := by
  constructor
  · rintro ⟨⟨hce, hca, hcu⟩, hcl⟩
    have hcf := (done_finished hS hD (lt_n_of_entered hO hce)).2
    refine ⟨⟨hcf, hca, ?_⟩, hcu⟩
    rcases hcl with hqa | hle
    · exact hcu ▸ root_le_low hS hO hqa (hcu ▸ Above.up hca) hce
    · exact hcu ▸ hle
  · rintro ⟨hct, hcu⟩
    exact ⟨⟨entered_of_finished hS hO hct.1, hct.2.1, hcu⟩, Or.inr (hcu ▸ hct.2.2)⟩

/-- A cut vertex's node is a vertex's node only for that vertex. -/
theorem cutNode_ne_node {q u : ℕ} (hq : q ∈ cuts g w) (hu : u < g.n) :
    cutNodeOf (g := g) w q = Forest.nodeOfVertex (report g w) u ↔ q = u := by
  constructor
  · intro h
    by_cases huc : u ∈ cuts g w
    · rw [nodeOfVertex_of_cut huc] at h
      exact cutNodeOf_inj hq huc h
    · exfalso
      have hnc : w.cut u = false := by
        by_contra h'
        exact huc (mem_cuts.mpr ⟨hu, by simpa using h'⟩)
      obtain ⟨k0, hk0, he, -⟩ := node_cases hg hS hO hD hu hnc
      have := (cutNodeOf_lt hq).1
      omega
  · rintro rfl
    rw [nodeOfVertex_of_cut hq]

/-- **The forest's promise on the finished walk**: for two vertices in one piece, the forest lists
exactly the vertices whose failure alone separates them; for vertices in different pieces,
`none`. -/
theorem forest_promise (hR : RootsOk (g := g) w) {u v : ℕ} (hu : u < g.n) (hv : v < g.n) :
    (g.Connected u v → ∃ l, (forest g (report g w)).separators u v = some l ∧
      ∀ q, q ∈ l ↔ Separates g q u v) ∧
    (¬ g.Connected u v → (forest g (report g w)).separators u v = none) := by
  have h := treeSpec hg hS hO hD hR
  obtain ⟨hnone, hsome⟩ := Forest.separators_spec h rfl hu hv
  have hue := (done_finished hS hD hu).1
  have hve := (done_finished hS hD hv).1
  obtain ⟨ru, hru, hrua, hrue⟩ := exists_root hS hO _ u le_rfl hue
  obtain ⟨rv, hrv, hrva, hrve⟩ := exists_root hS hO _ v le_rfl hve
  have hrun := lt_n_of_entered hO hrue
  have hrvn := lt_n_of_entered hO hrve
  rw [top_node hg hS hO hD _ u le_rfl hu ru hru hrua,
    top_node hg hS hO hD _ v le_rfl hv rv hrv hrva] at hnone
  have hconn : g.Connected u v ↔ ru = rv := by
    constructor
    · intro hc
      have := above_of_connected hg hS hO hD hrua hru hc
      rcases above_total this hrv with h' | h'
      · exact above_root hrva h'
      · exact (above_root hrua h').symm
    · rintro rfl
      have hdown : ∀ z, Above w ru z → g.Connected ru z := fun z hz =>
        connected_of_above hS hO hz fun t h1 _ h3 =>
          link_up hS hO ((above_iff.mp h1).resolve_left (Ne.symm h3)).1
      exact connected_trans (connected_symm (hdown u hru)) (hdown v hrv)
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have hrr := hconn.mp hc
    subst hrr
    rcases hsep : (forest g (report g w)).separators u v with _ | l
    · exact absurd rfl (hnone.mp hsep)
    refine ⟨l, rfl, fun q => ?_⟩
    rw [hsome l hsep q]
    have hB : Separates g q u v ↔ q ∈ cuts g w ∧ q ≠ u ∧ q ≠ v ∧
        ∃ c, BlockTop w c ∧ w.up c = q ∧ (Above w c u ↔ ¬ Above w c v) := by
      constructor
      · intro hsepq
        obtain ⟨hqu, hqv⟩ := ne_of_separates hsepq
        obtain ⟨c, hcc, hiff⟩ := (separates_iff_tree hg hS hO hD hu hqu hqv hc).mp hsepq
        obtain ⟨hct, hcu⟩ := (closedChild_iff hS hO hD).mp hcc
        have hqn : q < g.n := hcu ▸ (hangs hS hO c hct.2.1).2.2.1
        have hcut : IsCutVertex g q := (isCutVertex_iff hg hqn).mpr ⟨u, hu, v, hv, hsepq⟩
        have := ((report_promise hg hS hO hD).2.1 q).mpr hcut
        exact ⟨this, hqu, hqv, c, hct, hcu, hiff⟩
      · rintro ⟨-, hqu, hqv, c, hct, hcu, hiff⟩
        exact (separates_iff_tree hg hS hO hD hu hqu hqv hc).mpr
          ⟨c, (closedChild_iff hS hO hD).mpr ⟨hct, hcu⟩, hiff⟩
    rw [hB]
    simp only [report_eq w]
    constructor
    · rintro ⟨k, hk, hkq, hku, hkv, c', hpc', hc'ne, hd⟩
      have hq : q ∈ cuts g w := List.mem_of_getElem? hkq
      have hkn : w.blocks.length + k = cutNodeOf (g := g) w q := by
        unfold cutNodeOf
        obtain ⟨hkl, hget⟩ := List.getElem?_eq_some_iff.mp hkq
        rw [← hget, (cuts_nodup (g := g) w).idxOf_getElem]
      rw [hkn] at hku hkv hpc' hc'ne
      obtain ⟨c, hct, hcu, rfl⟩ := (parentOf_eq_cut_iff hg hS hO hD hq).mp ⟨hpc', hc'ne⟩
      have hcuq : w.up c ∈ cuts g w := hcu ▸ hq
      refine ⟨hq, fun h' => hku ((cutNode_ne_node hg hS hO hD hq hu).mpr h'),
        fun h' => hkv ((cutNode_ne_node hg hS hO hD hq hv).mpr h'), c, hct, hcu, ?_⟩
      rwa [dAnc_block_iff hg hS hO hD hct hcuq _ u le_rfl hu,
        dAnc_block_iff hg hS hO hD hct hcuq _ v le_rfl hv] at hd
    · rintro ⟨hq, hqu, hqv, c, hct, hcu, hiff⟩
      have hcuq : w.up c ∈ cuts g w := hcu ▸ hq
      refine ⟨(cuts g w).idxOf q, List.idxOf_lt_length_of_mem hq, ?_, ?_, ?_, ?_⟩
      · rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hq), List.getElem_idxOf]
      · exact fun h' => hqu ((cutNode_ne_node hg hS hO hD hq hu).mp h')
      · exact fun h' => hqv ((cutNode_ne_node hg hS hO hD hq hv).mp h')
      · obtain ⟨hpc, hne⟩ := (parentOf_eq_cut_iff hg hS hO hD hq).mpr ⟨c, hct, hcu, rfl⟩
        refine ⟨blockOf (g := g) w c, hpc, hne, ?_⟩
        rwa [dAnc_block_iff hg hS hO hD hct hcuq _ u le_rfl hu,
          dAnc_block_iff hg hS hO hD hct hcuq _ v le_rfl hv]
  · rw [hnone]
    intro heq
    exact hc (hconn.mpr (node_root_inj hg hS hO hD hrun hrvn hrua hrva heq))

end Done

end Walk

end AlgoDesign.Graphs.Blocks
