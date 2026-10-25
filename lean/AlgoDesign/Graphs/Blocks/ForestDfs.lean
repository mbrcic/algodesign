/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.ForestRoot
public import AlgoDesign.Graphs.Blocks.Separate

/-!
# Bridges, cut vertices and blocks: the block-cut forest of the finished walk

The finished walk's report names its blocks by their block tops: a block with links is the group
of one block top `c`, and holds the vertex `c` hangs from and the vertices whose first block top is
`c` (`mem_vertices_iff`). So the block-cut forest is the walk's tree folded up: a block hangs from
the cut vertex its top hangs from, if that is a cut vertex, and a cut vertex other than a root hangs
from the block of its first block top (`parentOf`). This is the shape `TreeSpec` asks for, and a
block lies above a vertex's node exactly when its top lies above the vertex (`dAnc_iff_above`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

/-! ## Naming the nodes -/

/-- The block of block top `c`: the first block that is `c`'s group. -/
def blockOf (w : Walk) (c : ℕ) : ℕ :=
  if h : ∃ k, k < w.blocks.length ∧ IsGroupOf (g := g) w (w.blocks.getD k []) c then Nat.find h
  else 0

/-- The block top of block `k`. -/
def topOf (w : Walk) (k : ℕ) : ℕ :=
  if h : ∃ c, c < g.n ∧ IsGroupOf (g := g) w (w.blocks.getD k []) c then Nat.find h else 0

/-- The first block top above `p`. -/
def headOf (w : Walk) (p : ℕ) : ℕ :=
  if h : ∃ c, c < g.n ∧ HeadIs (g := g) w p c then Nat.find h else 0

/-- The cut vertices, increasing. -/
def cuts (g : Graph) (w : Walk) : List ℕ := (List.range g.n).filter w.cut

/-- A cut vertex's node. -/
def cutNodeOf (w : Walk) (p : ℕ) : ℕ := w.blocks.length + (cuts g w).idxOf p

/-- **The forest's parents**, read off the walk: a block hangs from the cut vertex its top hangs
from, if that is a cut vertex; a cut vertex other than a root hangs from the block of its first
block top; every other node is a root. -/
def parentOf (w : Walk) (x : ℕ) : ℕ :=
  if x < w.blocks.length then
    if w.blocks.getD x [] = [] then x
    else if w.cut (w.up (topOf (g := g) w x)) then cutNodeOf (g := g) w (w.up (topOf (g := g) w x))
    else x
  else match (cuts g w)[x - w.blocks.length]? with
    | some p => if w.arrival p = none then x else blockOf (g := g) w (headOf (g := g) w p)
    | none => x

/-- A rank dropping from each node to its parent: twice the top's entry number for a block, one
more than twice the vertex's for a cut vertex. -/
def rankOf (w : Walk) (x : ℕ) : ℕ :=
  if x < w.blocks.length then 2 * w.entry (topOf (g := g) w x)
  else match (cuts g w)[x - w.blocks.length]? with
    | some p => 2 * w.entry p + 1
    | none => 0

theorem report_eq (w : Walk) : (report g w).blocks = w.blocks ∧
    (report g w).blockVertices = w.vertices ∧ (report g w).cutVertices = cuts g w := ⟨rfl, rfl, rfl⟩

theorem mem_verticesOf {b : List ℕ} {p : ℕ} :
    p ∈ verticesOf g b ↔ p < g.n ∧ ∃ i ∈ b, ∃ l, g.links[i]? = some l ∧ (l.1 = p ∨ l.2 = p) := by
  simp [verticesOf, List.any_eq_true, Option.any_eq_true]

theorem foldl_last {N k0 : ℕ} {P : ℕ → Prop} [DecidablePred P] (hP : ∀ k < N, P k ↔ k = k0)
    (init : ℕ) : ∀ M, k0 < M → M ≤ N →
      (List.range M).foldl (fun acc k => if P k then k else acc) init = k0
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | M + 1, h, hM => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    by_cases hk : M = k0
    · subst hk
      simp [(hP M (by omega)).mpr rfl]
    · rw [ite_eq_right (fun h' => hk ((hP M (by omega)).mp h'))]
      exact foldl_last hP init M (by omega) (by omega)

theorem cuts_nodup (w : Walk) : (cuts g w).Nodup := List.nodup_range.filter _

theorem mem_cuts {w : Walk} {p : ℕ} : p ∈ cuts g w ↔ p < g.n ∧ w.cut p = true := by
  simp [cuts]

theorem cutNode_eq {w : Walk} {p : ℕ} :
    Forest.cutNode (report g w) p =
      if p ∈ cuts g w then some (cutNodeOf (g := g) w p) else none := by
  unfold Forest.cutNode cutNodeOf
  change Option.map (fun x => w.blocks.length + x) ((cuts g w).idxOf? p) = _
  split_ifs with h
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr h)
    rw [hi]
    obtain ⟨hil, hget, -⟩ := List.idxOf?_eq_some_iff.mp hi
    have hlt : (cuts g w).idxOf p < (cuts g w).length := List.idxOf_lt_length_of_mem h
    have := (cuts_nodup (g := g) w).getElem_inj_iff.mp
      (hget.trans (List.getElem_idxOf hlt).symm)
    simp [this]
  · rw [List.idxOf?_eq_none_iff.mpr h]
    rfl

/-- A vertex that is no cut vertex has, as its node, the one block holding it. -/
theorem nodeOfVertex_of_unique {w : Walk} {p k0 : ℕ} (hp : p ∉ cuts g w)
    (hk0 : k0 < w.blocks.length)
    (huniq : ∀ k < w.blocks.length, p ∈ w.vertices.getD k [] ↔ k = k0) :
    Forest.nodeOfVertex (report g w) p = k0 := by
  unfold Forest.nodeOfVertex
  rw [cutNode_eq, ite_eq_right hp]
  exact foldl_last (N := w.blocks.length) huniq 0 _ (by simpa [report] using hk0) (by simp [report])

theorem nodeOfVertex_of_cut {w : Walk} {p : ℕ} (hp : p ∈ cuts g w) :
    Forest.nodeOfVertex (report g w) p = cutNodeOf (g := g) w p := by
  unfold Forest.nodeOfVertex
  rw [cutNode_eq, ite_eq_left hp]

theorem size_eq (w : Walk) :
    Forest.size (report g w) = w.blocks.length + (cuts g w).length := rfl

theorem cutNodeOf_lt {w : Walk} {p : ℕ} (hp : p ∈ cuts g w) :
    w.blocks.length ≤ cutNodeOf (g := g) w p ∧
      cutNodeOf (g := g) w p < Forest.size (report g w) := by
  unfold cutNodeOf
  rw [size_eq]
  have := List.idxOf_lt_length_of_mem hp
  omega

theorem cuts_getElem?_cutNodeOf {w : Walk} {p : ℕ} (hp : p ∈ cuts g w) :
    (cuts g w)[cutNodeOf (g := g) w p - w.blocks.length]? = some p := by
  unfold cutNodeOf
  rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hp),
    List.getElem_idxOf]

theorem cutNodeOf_inj {w : Walk} {p q : ℕ} (hp : p ∈ cuts g w) (hq : q ∈ cuts g w)
    (h : cutNodeOf (g := g) w p = cutNodeOf (g := g) w q) : p = q := by
  have := cuts_getElem?_cutNodeOf hp
  rw [h, cuts_getElem?_cutNodeOf hq] at this
  exact Option.some.inj this.symm

theorem node_classify {w : Walk} {x : ℕ} (hx : x < Forest.size (report g w)) :
    x < w.blocks.length ∨ ∃ p ∈ cuts g w, x = cutNodeOf (g := g) w p := by
  rw [size_eq] at hx
  by_cases h : x < w.blocks.length
  · exact Or.inl h
  · right
    have hi : x - w.blocks.length < (cuts g w).length := by omega
    refine ⟨(cuts g w)[x - w.blocks.length], List.getElem_mem hi, ?_⟩
    unfold cutNodeOf
    rw [(cuts_nodup (g := g) w).idxOf_getElem]
    omega

theorem parentOf_cut {w : Walk} {p : ℕ} (hp : p ∈ cuts g w) :
    parentOf (g := g) w (cutNodeOf (g := g) w p) = if w.arrival p = none then
      cutNodeOf (g := g) w p else blockOf (g := g) w (headOf (g := g) w p) := by
  unfold parentOf
  rw [ite_eq_right (by have := (cutNodeOf_lt hp).1; omega), cuts_getElem?_cutNodeOf hp]

theorem parentOf_empty {w : Walk} {k : ℕ} (hk : k < w.blocks.length)
    (he : w.blocks.getD k [] = []) : parentOf (g := g) w k = k := by
  unfold parentOf
  rw [ite_eq_left hk, ite_eq_left he]

theorem parentOf_nonempty {w : Walk} {k : ℕ} (hk : k < w.blocks.length)
    (he : w.blocks.getD k [] ≠ []) : parentOf (g := g) w k =
      if w.cut (w.up (topOf (g := g) w k)) then cutNodeOf (g := g) w (w.up (topOf (g := g) w k))
      else k := by
  unfold parentOf
  rw [ite_eq_left hk, ite_eq_right he]

theorem mem_around_block {w : Walk} {x y : ℕ} (hx : x < w.blocks.length) :
    y ∈ Forest.around (report g w) x ↔
      ∃ p ∈ w.vertices.getD x [], p ∈ cuts g w ∧ y = cutNodeOf (g := g) w p := by
  unfold Forest.around
  rw [ite_eq_left (by simpa [report] using hx)]
  simp only [List.mem_filterMap, cutNode_eq]
  constructor
  · rintro ⟨p, hp, h⟩
    split_ifs at h with hc
    · exact ⟨p, hp, hc, (Option.some.inj h).symm⟩
  · rintro ⟨p, hp, hc, rfl⟩
    exact ⟨p, hp, by rw [ite_eq_left hc]⟩

theorem mem_around_cut {w : Walk} {p y : ℕ} (hp : p ∈ cuts g w) :
    y ∈ Forest.around (report g w) (cutNodeOf (g := g) w p) ↔
      y < w.blocks.length ∧ p ∈ w.vertices.getD y [] := by
  unfold Forest.around
  rw [ite_eq_right (by have := (cutNodeOf_lt hp).1; simp only [report]; omega)]
  simp only [List.mem_filter, List.mem_range]
  change y < w.blocks.length ∧
    ((cuts g w)[cutNodeOf (g := g) w p - w.blocks.length]?.any
      (· ∈ w.vertices.getD y [])) = true ↔ _
  rw [cuts_getElem?_cutNodeOf hp]
  simp

theorem rankOf_cut {w : Walk} {p : ℕ} (hp : p ∈ cuts g w) :
    rankOf (g := g) w (cutNodeOf (g := g) w p) = 2 * w.entry p + 1 := by
  unfold rankOf
  rw [ite_eq_right (by have := (cutNodeOf_lt hp).1; omega), cuts_getElem?_cutNodeOf hp]

theorem rankOf_block {w : Walk} {k : ℕ} (hk : k < w.blocks.length) :
    rankOf (g := g) w k = 2 * w.entry (topOf (g := g) w k) := by
  unfold rankOf
  rw [ite_eq_left hk]

section Done

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hD : Done (g := g) w)
include hS hO hD

include hg in
/-- The arrival link of a vertex whose first block top is `c` is in `c`'s group. -/
theorem inGroup_arrival {p c e : ℕ} (hh : HeadIs (g := g) w p c) (he : w.arrival p = some e) :
    InGroup (g := g) w c e := by
  have hpa : w.arrival p ≠ none := by simp [he]
  obtain ⟨hpn, hpe, hun, hue, hlt, hj⟩ := hangs hS hO p hpa
  have hje := hj e (by simp [he])
  have huf := (done_finished hS hD hun).2
  refine ⟨⟨nonLoop_arrival hS hO he, w.up p, hun, (p, e), ?_, rfl⟩, p, hpn, ?_, hh⟩
  · rw [looked_of_finished hS hun huf]
    exact adj_mem_of_joins hg hje
  · rcases hje with h | h
    · exact (deep_iff h).mpr ⟨Or.inr rfl, by omega⟩
    · exact (deep_iff h).mpr ⟨Or.inl rfl, by omega⟩

omit hD in
/-- A block top is its own first block top. -/
theorem headIs_self {c : ℕ} (hc : BlockTop w c) : HeadIs (g := g) w c c :=
  (headIs_iff hS hO).mpr ⟨Above.refl w c, hc, fun _ h1 h2 h3 =>
    absurd (above_antisymm hS hO h1 h2) h3⟩

omit hD in
theorem arrival_lt {p e : ℕ} (he : w.arrival p = some e) : e < g.links.length := by
  obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO p (by simp [he])
  rcases hj e (by simp [he]) with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1

include hg in
/-- A block is the group of one block top. -/
theorem group_unique {b : List ℕ} {c c' : ℕ} (hb : IsGroupOf (g := g) w b c)
    (hb' : IsGroupOf (g := g) w b c') : c = c' := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hb.2.1.2.1
  have hem := arrival_lt hS hO he
  have h1 := inGroup_arrival hg hS hO hD (headIs_self hS hO hb.2.1) he
  have h2 := (hb'.2.2 e hem).mp ((hb.2.2 e hem).mpr h1)
  exact inGroup_unique hS hO h1 h2

omit hD in
theorem blockOf_spec {c : ℕ} (hc : BlockTop w c) : blockOf (g := g) w c < w.blocks.length ∧
    IsGroupOf (g := g) w (w.blocks.getD (blockOf (g := g) w c) []) c := by
  have hex : ∃ k, k < w.blocks.length ∧ IsGroupOf (g := g) w (w.blocks.getD k []) c := by
    obtain ⟨k, hk, h⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1 c (finished_lt hO hc.1) hc
    exact ⟨k, hk, h⟩
  unfold blockOf
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

omit hO hD in
/-- Every block with links is the block of its top, which is a block top. -/
theorem topOf_spec {k : ℕ} (hk : k < w.blocks.length) (hne : w.blocks.getD k [] ≠ []) :
    topOf (g := g) w k < g.n ∧ BlockTop w (topOf (g := g) w k) ∧
      IsGroupOf (g := g) w (w.blocks.getD k []) (topOf (g := g) w k) := by
  have hex : ∃ c, c < g.n ∧ IsGroupOf (g := g) w (w.blocks.getD k []) c := by
    obtain ⟨c, hc, h⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1 k hk hne
    exact ⟨c, hc, h⟩
  unfold topOf
  rw [dite_eq_left hex]
  have := Nat.find_spec hex
  exact ⟨this.1, this.2.2.1, this.2⟩

include hg in
theorem blockOf_unique {c k : ℕ} (hk : k < w.blocks.length)
    (h : IsGroupOf (g := g) w (w.blocks.getD k []) c) : k = blockOf (g := g) w c := by
  obtain ⟨hb, hgb⟩ := blockOf_spec hS hO h.2.1
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp h.2.1.2.1
  have hem := arrival_lt hS hO he
  have h1 := inGroup_arrival hg hS hO hD (headIs_self hS hO h.2.1) he
  have hflat := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.1
  have m1 := (h.2.2 e hem).mpr h1
  have m2 := (hgb.2.2 e hem).mpr h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hb, Option.getD_some] at m1 m2
  exact index_unique hflat hk hb m1 m2

include hg in
theorem topOf_blockOf {c : ℕ} (hc : BlockTop w c) :
    topOf (g := g) w (blockOf (g := g) w c) = c := by
  obtain ⟨hb, hgb⟩ := blockOf_spec hS hO hc
  exact group_unique hg hS hO hD (topOf_spec hS hb hgb.1).2.2 hgb

include hg in
theorem blockOf_topOf {k : ℕ} (hk : k < w.blocks.length) (hne : w.blocks.getD k [] ≠ []) :
    blockOf (g := g) w (topOf (g := g) w k) = k :=
  (blockOf_unique hg hS hO hD hk (topOf_spec hS hk hne).2.2).symm

include hg in
/-- **A block's vertices**: the vertex its top hangs from, and the vertices whose first block top is
its top. -/
theorem mem_vertices_iff {c p : ℕ} (hc : BlockTop w c) :
    p ∈ w.vertices.getD (blockOf (g := g) w c) [] ↔ p = w.up c ∨ HeadIs (g := g) w p c := by
  obtain ⟨hb, hgb⟩ := blockOf_spec hS hO hc
  have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hBO.2.1 _ hb hgb.1, mem_verticesOf]
  have hce := entered_of_finished hS hO hc.1
  obtain ⟨-, -, hun, hue, hult, hjc⟩ := hangs hS hO c hc.2.1
  constructor
  · rintro ⟨hpn, i, hi, ⟨a, b⟩, hl, hp⟩
    have him : i < g.links.length := (List.getElem?_eq_some_iff.mp hl).1
    obtain ⟨-, x, hxn, hdeep, hhead⟩ := (hgb.2.2 i him).mp hi
    obtain ⟨hxab, hxmax⟩ := (deep_iff hl).mp hdeep
    by_cases hpx : p = x
    · exact Or.inr (hpx ▸ hhead)
    have hj : Joins g i x p := by
      simp only at hp
      rcases hxab with rfl | rfl <;> rcases hp with rfl | rfl
      · exact absurd rfl hpx
      · exact Or.inl hl
      · exact Or.inr hl
      · exact absurd rfl hpx
    have hpmax : w.entry p ≤ w.entry x := by
      simp only at hp
      rcases hp with rfl | rfl <;> omega
    obtain ⟨hcx, -, hbet⟩ := (headIs_iff hS hO).mp hhead
    have hxe := entered_of_above hS hO hcx hce
    have hxf := (done_finished hS hD hxn).2
    obtain ⟨hpe, hpx' | hxp⟩ := link_of_finished hg hS hO hxn hxf hj hpx
    · by_cases hcp : Above w c p
      · exact Or.inr ((headIs_iff hS hO).mpr ⟨hcp, hc, fun c' h1 h2 h3 =>
          hbet c' (h1.trans hpx') h2 h3⟩)
      · exact Or.inl (gate hg hS hO hc hj hcx hcp)
    · have := (entry_le_of_above hS hO hxp hpe).2.2 (Ne.symm hpx)
      omega
  · rintro (rfl | hh)
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hc.2.1
      have hem := arrival_lt hS hO he
      have hin := (hgb.2.2 e hem).mpr (inGroup_arrival hg hS hO hD (headIs_self hS hO hc) he)
      refine ⟨hun, e, hin, ?_⟩
      rcases hjc e (by simp [he]) with h | h
      · exact ⟨_, h, Or.inl rfl⟩
      · exact ⟨_, h, Or.inr rfl⟩
    · obtain ⟨hcp, -, -⟩ := (headIs_iff hS hO).mp hh
      have hpa : w.arrival p ≠ none := by
        rcases above_iff.mp hcp with h | ⟨h, -⟩
        · exact h ▸ hc.2.1
        · exact h
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hpa
      obtain ⟨hpn, -, -, -, -, hj⟩ := hangs hS hO p hpa
      have hem := arrival_lt hS hO he
      have hin := (hgb.2.2 e hem).mpr (inGroup_arrival hg hS hO hD hh he)
      refine ⟨hpn, e, hin, ?_⟩
      rcases hj e (by simp [he]) with h | h
      · exact ⟨_, h, Or.inr rfl⟩
      · exact ⟨_, h, Or.inl rfl⟩

/-- **The cut vertices, read off the tree**: a vertex other than a root from which a block top
hangs, or a root with two or more children. -/
theorem cut_iff {p : ℕ} (hp : p < g.n) : w.cut p = true ↔
    (w.arrival p ≠ none ∧ ∃ c < g.n, BlockTop w c ∧ w.up c = p) ∨
      (w.arrival p = none ∧ 2 ≤ numChildren (g := g) w p) := by
  rw [hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p hp]
  have hpf := (done_finished hS hD hp).2
  constructor
  · rintro (⟨hpa, c, hcn, ⟨hce, hca, hcu⟩, hcf, hle⟩ | ⟨hpa, -, h2⟩)
    · exact Or.inl ⟨hpa, c, hcn, ⟨hcf, hca, hcu ▸ hle⟩, hcu⟩
    · exact Or.inr ⟨hpa, h2⟩
  · rintro (⟨hpa, c, hcn, ⟨hcf, hca, hle⟩, hcu⟩ | ⟨hpa, h2⟩)
    · exact Or.inl ⟨hpa, c, hcn, ⟨entered_of_finished hS hO hcf, hca, hcu⟩, hcf, hcu ▸ hle⟩
    · exact Or.inr ⟨hpa, hpf, h2⟩

include hg in
/-- Every block is a block top's group, or a lone root's block without links. -/
theorem block_cases {k : ℕ} (hk : k < w.blocks.length) :
    (w.blocks.getD k [] ≠ [] ∧ BlockTop w (topOf (g := g) w k) ∧
      ∀ p, p ∈ w.vertices.getD k [] ↔ p = w.up (topOf (g := g) w k) ∨
        HeadIs (g := g) w p (topOf (g := g) w k)) ∨
    (w.blocks.getD k [] = [] ∧ ∃ r < g.n, w.vertices.getD k [] = [r] ∧ LoneRoot (g := g) w r) := by
  by_cases hne : w.blocks.getD k [] = []
  · obtain ⟨r, hr, ⟨-, hpl⟩, hlone⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1 k hk hne
    exact Or.inr ⟨hne, r, hr, hpl, hlone⟩
  · obtain ⟨-, hct, -⟩ := topOf_spec hS hk hne
    refine Or.inl ⟨hne, hct, fun p => ?_⟩
    have := mem_vertices_iff hg hS hO hD (p := p) hct
    rwa [blockOf_topOf hg hS hO hD hk hne] at this

theorem headOf_spec {p : ℕ} (hp : p < g.n) (hpa : w.arrival p ≠ none) :
    HeadIs (g := g) w p (headOf (g := g) w p) := by
  have hpe := (done_finished hS hD hp).1
  obtain ⟨c, hc⟩ := exists_head hS hO hD _ p le_rfl hpe hpa
  have hcn : c < g.n := finished_lt hO ((headIs_iff hS hO).mp hc).2.1.1
  have hex : ∃ c, c < g.n ∧ HeadIs (g := g) w p c := ⟨c, hcn, hc⟩
  unfold headOf
  rw [dite_eq_left hex]
  exact (Nat.find_spec hex).2

theorem headOf_eq {p c : ℕ} (hp : p < g.n) (hc : HeadIs (g := g) w p c) :
    headOf (g := g) w p = c := by
  have hpa : w.arrival p ≠ none := by
    obtain ⟨hcp, hct, -⟩ := (headIs_iff hS hO).mp hc
    rcases above_iff.mp hcp with h | ⟨h, -⟩
    · exact h ▸ hct.2.1
    · exact h
  exact head_unique hS hO (headOf_spec hS hO hD hp hpa) hc

omit hD in
/-- A vertex is not above a block top that is its own child: tops hang below the vertex. -/
theorem not_headIs_root {p c : ℕ} (hpa : w.arrival p = none) (hc : HeadIs (g := g) w p c) :
    False := by
  obtain ⟨hcp, hct, -⟩ := (headIs_iff hS hO).mp hc
  exact hct.2.1 (above_root hpa hcp ▸ hpa)

include hg in
/-- **A vertex's node**: a vertex that is no cut vertex lies in exactly one block. -/
theorem node_cases {p : ℕ} (hp : p < g.n) (hnc : w.cut p = false) :
    ∃ k0 < w.blocks.length, Forest.nodeOfVertex (report g w) p = k0 ∧
      ((w.arrival p ≠ none ∧ k0 = blockOf (g := g) w (headOf (g := g) w p)) ∨
       (w.arrival p = none ∧ ∃ c, BlockTop w c ∧ w.up c = p ∧ k0 = blockOf (g := g) w c) ∨
       (w.arrival p = none ∧ LoneRoot (g := g) w p ∧ EmptyAt w k0 p)) := by
  have hpc : p ∉ cuts g w := fun h => by simp [(mem_cuts.mp h).2] at hnc
  have hnotcut := fun h => (Bool.eq_false_iff.mp hnc) ((cut_iff hS hO hD hp).mpr h)
  -- a block top hanging from `p` makes `p` a cut vertex unless `p` is a root
  have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hpa : w.arrival p = none
  · by_cases hch : ∃ c, BlockTop w c ∧ w.up c = p
    · obtain ⟨c, hct, hcu⟩ := hch
      obtain ⟨hb, -⟩ := blockOf_spec hS hO hct
      refine ⟨blockOf (g := g) w c, hb, nodeOfVertex_of_unique hpc hb fun k hk => ?_,
        Or.inr (Or.inl ⟨hpa, c, hct, hcu, rfl⟩)⟩
      rcases block_cases hg hS hO hD hk with ⟨hne, hkt, hmem⟩ | ⟨hemp, r, -, hpl, hlone⟩
      · rw [hmem]
        constructor
        · rintro (h | h)
          · -- two block tops hanging from a root that is no cut vertex: they are one
            by_contra hkc
            have hne' : topOf (g := g) w k ≠ c := by
              intro h'
              exact hkc (by rw [← blockOf_topOf hg hS hO hD hk hne, h'])
            exact hnotcut (Or.inr ⟨hpa, two_children_iff.mpr ⟨_, finished_lt hO hkt.1, c,
              finished_lt hO hct.1, hne', ⟨entered_of_finished hS hO hkt.1, hkt.2.1, h.symm⟩,
              ⟨entered_of_finished hS hO hct.1, hct.2.1, hcu⟩⟩⟩)
          · exact (not_headIs_root hS hO hpa h).elim
        · rintro rfl
          left
          rw [topOf_blockOf hg hS hO hD hct, hcu]
      · rw [hpl, List.mem_singleton]
        constructor
        · rintro rfl
          obtain ⟨-, -, h0⟩ := hlone
          unfold numChildren at h0
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
          exact absurd (decide_eq_true ⟨entered_of_finished hS hO hct.1, hct.2.1, hcu⟩)
            (h0 c (List.mem_range.mpr (finished_lt hO hct.1)))
        · rintro rfl
          exact absurd hemp (blockOf_spec hS hO hct).2.1
    · have hlone : LoneRoot (g := g) w p := by
        refine ⟨(done_finished hS hD hp).2, hpa, ?_⟩
        unfold numChildren
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        rintro t ht htc
        obtain ⟨hte, hta, htu⟩ : Child w p t := of_decide_eq_true htc
        have htn := lt_n_of_entered hO hte
        exact hch ⟨t, ⟨(done_finished hS hD htn).2, hta,
          htu ▸ root_le_low hS hO hpa (htu ▸ Above.up hta) hte⟩, htu⟩
      obtain ⟨k0, hk0, hemp⟩ := hBO.2.2.2.2.2.1 p hp hlone
      refine ⟨k0, hk0, nodeOfVertex_of_unique hpc hk0 fun k hk => ?_,
        Or.inr (Or.inr ⟨hpa, hlone, hemp⟩)⟩
      rcases block_cases hg hS hO hD hk with ⟨hne, hkt, hmem⟩ | ⟨hemp', r, hr, hpl, -⟩
      · rw [hmem]
        constructor
        · rintro (h | h)
          · exact (hch ⟨_, hkt, h.symm⟩).elim
          · exact (not_headIs_root hS hO hpa h).elim
        · rintro rfl
          exact absurd hemp.1 hne
      · rw [hpl, List.mem_singleton]
        constructor
        · intro hpr
          exact hBO.2.2.2.2.2.2.1 k hk k0 hk0 p hp ⟨hemp', by rw [hpr]; exact hpl⟩ hemp
        · rintro rfl
          have := hemp.2
          rw [hpl] at this
          exact (List.singleton_inj.mp this).symm
  · have hh := headOf_spec hS hO hD hp hpa
    obtain ⟨-, hct, -⟩ := (headIs_iff hS hO).mp hh
    obtain ⟨hb, -⟩ := blockOf_spec hS hO hct
    refine ⟨_, hb, nodeOfVertex_of_unique hpc hb fun k hk => ?_, Or.inl ⟨hpa, rfl⟩⟩
    rcases block_cases hg hS hO hD hk with ⟨hne, hkt, hmem⟩ | ⟨hemp, r, -, hpl, hlone⟩
    · rw [hmem]
      constructor
      · rintro (h | h)
        · exact (hnotcut (Or.inl ⟨hpa, _, finished_lt hO hkt.1, hkt, h.symm⟩)).elim
        · rw [← blockOf_topOf hg hS hO hD hk hne, headOf_eq hS hO hD hp h]
      · rintro rfl
        right
        rw [topOf_blockOf hg hS hO hD hct]
        exact hh
    · rw [hpl, List.mem_singleton]
      constructor
      · rintro rfl
        exact absurd hlone.2.1 hpa
      · rintro rfl
        exact absurd hemp (blockOf_spec hS hO hct).2.1

theorem cut_up_of_top {c : ℕ} (hc : BlockTop w c) (hua : w.arrival (w.up c) ≠ none) :
    w.up c ∈ cuts g w := by
  obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO c hc.2.1
  exact mem_cuts.mpr ⟨hun, (cut_iff hS hO hD hun).mpr
    (Or.inl ⟨hua, c, finished_lt hO hc.1, hc, rfl⟩)⟩

include hg in
theorem parentOf_blockOf {c : ℕ} (hc : BlockTop w c) :
    parentOf (g := g) w (blockOf (g := g) w c) =
      if w.cut (w.up c) then cutNodeOf (g := g) w (w.up c) else blockOf (g := g) w c := by
  obtain ⟨hb, hgb⟩ := blockOf_spec hS hO hc
  rw [parentOf_nonempty hb hgb.1, topOf_blockOf hg hS hO hD hc]

theorem parent_lt {x : ℕ} (hx : x < Forest.size (report g w)) :
    parentOf (g := g) w x < Forest.size (report g w) := by
  rcases node_classify hx with hb | ⟨p, hp, rfl⟩
  · by_cases he : w.blocks.getD x [] = []
    · rw [parentOf_empty hb he]
      exact hx
    · rw [parentOf_nonempty hb he]
      split_ifs with hcut
      · obtain ⟨-, hct, -⟩ := topOf_spec hS hb he
        obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO _ hct.2.1
        exact (cutNodeOf_lt (mem_cuts.mpr ⟨hun, hcut⟩)).2
      · exact hx
  · rw [parentOf_cut hp]
    split_ifs with hpa
    · exact hx
    · have hpn := (mem_cuts.mp hp).1
      obtain ⟨-, hct, -⟩ := (headIs_iff hS hO).mp (headOf_spec hS hO hD hpn hpa)
      have := (blockOf_spec hS hO hct).1
      rw [size_eq]
      omega

include hg in
theorem parent_rank {x : ℕ} (hx : x < Forest.size (report g w))
    (hne : parentOf (g := g) w x ≠ x) :
    rankOf (g := g) w (parentOf (g := g) w x) < rankOf (g := g) w x := by
  rcases node_classify hx with hb | ⟨p, hp, rfl⟩
  · by_cases he : w.blocks.getD x [] = []
    · exact absurd (parentOf_empty hb he) hne
    · rw [parentOf_nonempty hb he] at hne ⊢
      split_ifs at hne ⊢ with hcut
      · obtain ⟨-, hct, -⟩ := topOf_spec hS hb he
        obtain ⟨-, -, hun, -, hlt, -⟩ := hangs hS hO _ hct.2.1
        rw [rankOf_cut (mem_cuts.mpr ⟨hun, hcut⟩), rankOf_block hb]
        omega
      · exact absurd rfl hne
  · rw [parentOf_cut hp] at hne ⊢
    split_ifs at hne ⊢ with hpa
    · exact absurd rfl hne
    · have hpn := (mem_cuts.mp hp).1
      have hh := headOf_spec hS hO hD hpn hpa
      obtain ⟨hcp, hct, -⟩ := (headIs_iff hS hO).mp hh
      obtain ⟨hb, -⟩ := blockOf_spec hS hO hct
      rw [rankOf_cut hp, rankOf_block hb, topOf_blockOf hg hS hO hD hct]
      have := entry_le_of_above' hS hO hcp (entered_of_finished hS hO hct.1)
      omega

/-- A lone root's block holds no cut vertex. -/
theorem lone_not_cut {r : ℕ} (hr : r < g.n) (hl : LoneRoot (g := g) w r) : r ∉ cuts g w := by
  intro h
  rcases (cut_iff hS hO hD hr).mp (mem_cuts.mp h).2 with ⟨hra, -⟩ | ⟨-, h2⟩
  · exact hra hl.2.1
  · rw [hl.2.2] at h2
    omega

omit hD in
/-- The nodes whose parent is a block are cut vertices hanging from it. -/
theorem parent_eq_block {y k : ℕ} (hy : y < Forest.size (report g w)) (hk : k < w.blocks.length)
    (hne : y ≠ k) (h : parentOf (g := g) w y = k) :
    ∃ q ∈ cuts g w, y = cutNodeOf (g := g) w q ∧ w.arrival q ≠ none ∧
      k = blockOf (g := g) w (headOf (g := g) w q) := by
  rcases node_classify hy with hb | ⟨q, hq, rfl⟩
  · exfalso
    by_cases he : w.blocks.getD y [] = []
    · rw [parentOf_empty hb he] at h
      exact hne h
    · rw [parentOf_nonempty hb he] at h
      split_ifs at h with hcut
      · obtain ⟨-, hct, -⟩ := topOf_spec hS hb he
        obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO _ hct.2.1
        have := (cutNodeOf_lt (mem_cuts.mpr ⟨hun, hcut⟩)).1
        omega
      · exact hne h
  · rw [parentOf_cut hq] at h
    split_ifs at h with hqa
    · exact (hne h).elim
    · exact ⟨q, hq, rfl, hqa, h.symm⟩

include hg in
/-- **The forest is the walk's tree folded up**: the nodes around a node are its parent and its
children. -/
theorem mem_around_iff {x : ℕ} (hx : x < Forest.size (report g w)) (y : ℕ) :
    y ∈ Forest.around (report g w) x ↔ y < Forest.size (report g w) ∧
      ((parentOf (g := g) w x ≠ x ∧ y = parentOf (g := g) w x) ∨
        (parentOf (g := g) w y = x ∧ y ≠ x)) := by
  rcases node_classify hx with hb | ⟨p, hp, rfl⟩
  · rw [mem_around_block hb]
    rcases block_cases hg hS hO hD hb with ⟨hne, hct, hmem⟩ | ⟨hemp, r, hr, hpl, hlone⟩
    · rw [parentOf_nonempty hb hne]
      set c := topOf (g := g) w x with hcdef
      have hxc : x = blockOf (g := g) w c := (blockOf_topOf hg hS hO hD hb hne).symm
      obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO c hct.2.1
      constructor
      · rintro ⟨q, hq, hqc, rfl⟩
        refine ⟨(cutNodeOf_lt hqc).2, ?_⟩
        rcases (hmem q).mp hq with rfl | hh
        · rw [ite_eq_left (mem_cuts.mp hqc).2]
          exact Or.inl ⟨fun h => by have := (cutNodeOf_lt hqc).1; omega, rfl⟩
        · right
          have hqn := (mem_cuts.mp hqc).1
          have hqa : w.arrival q ≠ none := fun h => not_headIs_root hS hO h hh
          rw [parentOf_cut hqc, ite_eq_right hqa, headOf_eq hS hO hD hqn hh, ← hxc]
          exact ⟨rfl, fun h => by have := (cutNodeOf_lt hqc).1; omega⟩
      · rintro ⟨hy, (⟨hpx, rfl⟩ | ⟨hpy, hyx⟩)⟩
        · split_ifs at hpx with hcut
          · exact ⟨_, (hmem _).mpr (Or.inl rfl), mem_cuts.mpr ⟨hun, hcut⟩, by rw [ite_eq_left hcut]⟩
          · exact absurd rfl hpx
        · obtain ⟨q, hq, rfl, hqa, hk⟩ := parent_eq_block hS hO hy hb hyx hpy
          have hqn := (mem_cuts.mp hq).1
          have hh := headOf_spec hS hO hD hqn hqa
          obtain ⟨-, hht, -⟩ := (headIs_iff hS hO).mp hh
          have hc' : c = headOf (g := g) w q := by
            have := congrArg (topOf (g := g) w) hk
            rwa [topOf_blockOf hg hS hO hD hht, ← hcdef] at this
          exact ⟨q, (hmem q).mpr (Or.inr (hc' ▸ hh)), hq, rfl⟩
    · rw [parentOf_empty hb hemp, hpl]
      constructor
      · rintro ⟨q, hq, hqc, -⟩
        rw [List.mem_singleton] at hq
        exact absurd (hq ▸ hqc) (lone_not_cut hS hO hD hr hlone)
      · rintro ⟨hy, (⟨h, -⟩ | ⟨hpy, hyx⟩)⟩
        · exact absurd rfl h
        · obtain ⟨q, hq, rfl, hqa, hk⟩ := parent_eq_block hS hO hy hb hyx hpy
          have hqn := (mem_cuts.mp hq).1
          obtain ⟨-, hht, -⟩ := (headIs_iff hS hO).mp (headOf_spec hS hO hD hqn hqa)
          have := (blockOf_spec hS hO hht).2.1
          rw [← hk] at this
          exact absurd hemp this
  · rw [mem_around_cut hp]
    have hpn := (mem_cuts.mp hp).1
    rw [parentOf_cut hp]
    constructor
    · rintro ⟨hy, hpy⟩
      refine ⟨by rw [size_eq]; omega, ?_⟩
      have hyne : y ≠ cutNodeOf (g := g) w p := fun h => by
        have := (cutNodeOf_lt hp).1
        omega
      rcases block_cases hg hS hO hD hy with ⟨hne, hct, hmem⟩ | ⟨hemp, r, hr, hpl, hlone⟩
      · rcases (hmem p).mp hpy with hpu | hh
        · right
          refine ⟨?_, hyne⟩
          rw [parentOf_nonempty hy hne, ← hpu, ite_eq_left (mem_cuts.mp hp).2]
        · left
          have hpa : w.arrival p ≠ none := fun h => not_headIs_root hS hO h hh
          rw [ite_eq_right hpa, headOf_eq hS hO hD hpn hh, blockOf_topOf hg hS hO hD hy hne]
          exact ⟨hyne, rfl⟩
      · rw [hpl, List.mem_singleton] at hpy
        exact absurd (hpy ▸ hp) (lone_not_cut hS hO hD hr hlone)
    · rintro ⟨hy, (⟨hpx, rfl⟩ | ⟨hpy, hyx⟩)⟩
      · split_ifs at hpx ⊢ with hpa
        · exact absurd rfl hpx
        · have hh := headOf_spec hS hO hD hpn hpa
          obtain ⟨-, hht, -⟩ := (headIs_iff hS hO).mp hh
          obtain ⟨hb, -⟩ := blockOf_spec hS hO hht
          refine ⟨hb, (mem_vertices_iff hg hS hO hD hht).mpr (Or.inr hh)⟩
      · rcases node_classify hy with hb | ⟨q, hq, rfl⟩
        · refine ⟨hb, ?_⟩
          by_cases he : w.blocks.getD y [] = []
          · rw [parentOf_empty hb he] at hpy
            have := (cutNodeOf_lt hp).1
            omega
          · rw [parentOf_nonempty hb he] at hpy
            split_ifs at hpy with hcut
            · obtain ⟨-, hct, hmem⟩ :=
                (block_cases hg hS hO hD hb).resolve_right (fun h => he h.1)
              obtain ⟨-, -, hun, -, -, -⟩ := hangs hS hO _ hct.2.1
              have := cutNodeOf_inj (mem_cuts.mpr ⟨hun, hcut⟩) hp hpy
              exact (hmem p).mpr (Or.inl this.symm)
            · have := (cutNodeOf_lt hp).1
              omega
        · exfalso
          rw [parentOf_cut hq] at hpy
          split_ifs at hpy with hqa
          · exact hyx hpy
          · have hqn := (mem_cuts.mp hq).1
            obtain ⟨-, hht, -⟩ := (headIs_iff hS hO).mp (headOf_spec hS hO hD hqn hqa)
            have h1 := (blockOf_spec hS hO hht).1
            have h2 := (cutNodeOf_lt hp).1
            omega

include hg in
theorem node_lt {p : ℕ} (hp : p < g.n) :
    Forest.nodeOfVertex (report g w) p < Forest.size (report g w) := by
  by_cases hc : p ∈ cuts g w
  · rw [nodeOfVertex_of_cut hc]
    exact (cutNodeOf_lt hc).2
  · have hnc : w.cut p = false := by
      by_contra h
      exact hc (mem_cuts.mpr ⟨hp, by simpa using h⟩)
    obtain ⟨k0, hk0, he, -⟩ := node_cases hg hS hO hD hp hnc
    rw [he, size_eq]
    omega

include hg in
/-- The forest without its rooting: parents, ranks and neighbours. -/
theorem treeSpec0 : Forest.TreeSpec (report g w) 0 (parentOf (g := g) w) (rankOf (g := g) w) :=
  ⟨fun _ hx => parent_lt hS hO hD hx, fun _ hx hne => parent_rank hg hS hO hD hx hne,
    fun _ hx y => mem_around_iff hg hS hO hD hx y, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

include hg in
/-- A root's node is a root of the forest. -/
theorem parent_node_root {r : ℕ} (hr : r < g.n) (hra : w.arrival r = none) :
    parentOf (g := g) w (Forest.nodeOfVertex (report g w) r) =
      Forest.nodeOfVertex (report g w) r := by
  by_cases hc : r ∈ cuts g w
  · rw [nodeOfVertex_of_cut hc, parentOf_cut hc, ite_eq_left hra]
  · have hnc : w.cut r = false := by
      by_contra h
      exact hc (mem_cuts.mpr ⟨hr, by simpa using h⟩)
    obtain ⟨k0, hk0, he, hcase⟩ := node_cases hg hS hO hD hr hnc
    rw [he]
    rcases hcase with ⟨h, -⟩ | ⟨-, c, hct, hcu, rfl⟩ | ⟨-, -, hemp⟩
    · exact absurd hra h
    · rw [parentOf_blockOf hg hS hO hD hct, hcu, hnc]
      rfl
    · exact parentOf_empty hk0 hemp.1

include hg in
/-- **The forest's root above a vertex's node is the node of the vertex's root.** -/
theorem top_node : ∀ k p, w.entry p ≤ k → p < g.n → ∀ r, Above w r p → w.arrival r = none →
    Forest.top (parentOf (g := g) w) (rankOf (g := g) w) (Forest.nodeOfVertex (report g w) p) =
      Forest.nodeOfVertex (report g w) r := by
  have h0 := treeSpec0 hg hS hO hD
  intro k
  induction k with
  | zero =>
    intro p hk hp
    have := (done_finished hS hD hp).1
    omega
  | succ k ih =>
    intro p hk hp r hrp hra
    by_cases hpa : w.arrival p = none
    · have hrp' := above_root hpa hrp
      subst hrp'
      exact Forest.top_of_root (parent_node_root hg hS hO hD hp hpa)
    have hh := headOf_spec hS hO hD hp hpa
    obtain ⟨hhp, hht, -⟩ := (headIs_iff hS hO).mp hh
    set h := headOf (g := g) w p
    obtain ⟨hb, -⟩ := blockOf_spec hS hO hht
    have hhe := entered_of_finished hS hO hht.1
    obtain ⟨-, -, hun, hue, hlt, -⟩ := hangs hS hO h hht.2.1
    have hle := entry_le_of_above' hS hO hhp hhe
    -- the forest's root above `p`'s node is the one above `h`'s block
    have hstep : Forest.top (parentOf (g := g) w) (rankOf (g := g) w)
        (Forest.nodeOfVertex (report g w) p) =
        Forest.top (parentOf (g := g) w) (rankOf (g := g) w) (blockOf (g := g) w h) := by
      by_cases hc : p ∈ cuts g w
      · rw [nodeOfVertex_of_cut hc, ← h0.top_parent (cutNodeOf_lt hc).2, parentOf_cut hc,
          ite_eq_right hpa]
      · have hnc : w.cut p = false := by
          by_contra h'
          exact hc (mem_cuts.mpr ⟨hp, by simpa using h'⟩)
        obtain ⟨k0, -, he, hcase⟩ := node_cases hg hS hO hD hp hnc
        rcases hcase with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨h', -⟩
        · rw [he]
        · exact absurd h' hpa
        · exact absurd h' hpa
    rw [hstep]
    have hru : Above w r (w.up h) := by
      rcases above_total hrp ((Above.up hht.2.1).trans hhp) with h' | h'
      · exact h'
      · exact (above_root hra h') ▸ Above.refl w r
    by_cases hcu : w.up h ∈ cuts g w
    · rw [← h0.top_parent (by rw [size_eq]; omega), parentOf_blockOf hg hS hO hD hht,
        ite_eq_left (mem_cuts.mp hcu).2,
        ← nodeOfVertex_of_cut hcu]
      exact ih (w.up h) (by omega) hun r hru hra
    · have hua : w.arrival (w.up h) = none := by
        by_contra h'
        exact hcu (cut_up_of_top hS hO hD hht h')
      have hru' : r = w.up h := above_root hua hru
      have hnc : w.cut (w.up h) = false := by
        by_contra h'
        exact hcu (mem_cuts.mpr ⟨hun, by simpa using h'⟩)
      rw [Forest.top_of_root (by rw [parentOf_blockOf hg hS hO hD hht, hnc]; rfl), hru']
      obtain ⟨k0, -, he, hcase⟩ := node_cases hg hS hO hD hun hnc
      rw [he]
      rcases hcase with ⟨h', -⟩ | ⟨-, c, hct, hcu', rfl⟩ | ⟨-, hlone, -⟩
      · exact absurd hua h'
      · by_cases hch : c = h
        · rw [hch]
        · exfalso
          exact hcu (mem_cuts.mpr ⟨hun, (cut_iff hS hO hD hun).mpr (Or.inr ⟨hua,
            two_children_iff.mpr ⟨c, finished_lt hO hct.1, h, finished_lt hO hht.1, hch,
              ⟨entered_of_finished hS hO hct.1, hct.2.1, hcu'⟩, ⟨hhe, hht.2.1, rfl⟩⟩⟩)⟩)
      · obtain ⟨-, -, h0'⟩ := hlone
        unfold numChildren at h0'
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0'
        exact absurd (decide_eq_true ⟨hhe, hht.2.1, rfl⟩)
          (h0' h (List.mem_range.mpr (finished_lt hO hht.1)))

include hg in
/-- **The forest is rooted at each piece's smallest vertex.** -/
theorem treeSpec (hR : RootsOk (g := g) w) :
    Forest.TreeSpec (report g w) g.n (parentOf (g := g) w) (rankOf (g := g) w) := by
  have h0 := treeSpec0 hg hS hO hD
  refine ⟨h0.lt, h0.rank, h0.around, fun p hp => node_lt hg hS hO hD hp, fun p hp hfirst => ?_⟩
  have hpe := (done_finished hS hD hp).1
  obtain ⟨r, hrp, hra, hre⟩ := exists_root hS hO _ p le_rfl hpe
  have hrn := lt_n_of_entered hO hre
  by_cases hrpe : r = p
  · subst hrpe
    exact parent_node_root hg hS hO hD hrn hra
  · exfalso
    have hrle := hR p hp hpe r hrn ((anc_iff hS hO r p).mpr hrp) hra
    refine hfirst r (by omega) ?_
    rw [top_node hg hS hO hD _ r le_rfl hrn r (Above.refl w r) hra,
      top_node hg hS hO hD _ p le_rfl hp r hrp hra]

include hg in
/-- A vertex that is no cut vertex lies in its node's block. -/
theorem mem_vertices_node {p : ℕ} (hp : p < g.n) (hnc : w.cut p = false) :
    p ∈ w.vertices.getD (Forest.nodeOfVertex (report g w) p) [] := by
  obtain ⟨k0, -, he, hcase⟩ := node_cases hg hS hO hD hp hnc
  rw [he]
  rcases hcase with ⟨hpa, rfl⟩ | ⟨-, c, hct, hcu, rfl⟩ | ⟨-, -, hemp⟩
  · have hh := headOf_spec hS hO hD hp hpa
    exact (mem_vertices_iff hg hS hO hD ((headIs_iff hS hO).mp hh).2.1).mpr (Or.inr hh)
  · exact (mem_vertices_iff hg hS hO hD hct).mpr (Or.inl hcu.symm)
  · rw [hemp.2]
    exact List.mem_singleton_self p

include hg in
/-- Different roots have different nodes. -/
theorem node_root_inj {r r' : ℕ} (hr : r < g.n) (hr' : r' < g.n) (hra : w.arrival r = none)
    (hra' : w.arrival r' = none)
    (h : Forest.nodeOfVertex (report g w) r = Forest.nodeOfVertex (report g w) r') : r = r' := by
  have hvertex : ∀ q < g.n, w.arrival q = none → q ∉ cuts g w →
      Forest.nodeOfVertex (report g w) q < w.blocks.length ∧
        q ∈ w.vertices.getD (Forest.nodeOfVertex (report g w) q) [] := by
    intro q hq hqa hqc
    have hnc : w.cut q = false := by
      by_contra h'
      exact hqc (mem_cuts.mpr ⟨hq, by simpa using h'⟩)
    obtain ⟨k0, hk0, he, -⟩ := node_cases hg hS hO hD hq hnc
    exact ⟨he ▸ hk0, mem_vertices_node hg hS hO hD hq hnc⟩
  by_cases hc : r ∈ cuts g w <;> by_cases hc' : r' ∈ cuts g w
  · rw [nodeOfVertex_of_cut hc, nodeOfVertex_of_cut hc'] at h
    exact cutNodeOf_inj hc hc' h
  · rw [nodeOfVertex_of_cut hc] at h
    have := (cutNodeOf_lt hc).1
    have := (hvertex r' hr' hra' hc').1
    omega
  · rw [nodeOfVertex_of_cut hc'] at h
    have := (cutNodeOf_lt hc').1
    have := (hvertex r hr hra hc).1
    omega
  · obtain ⟨hk, hm⟩ := hvertex r hr hra hc
    obtain ⟨-, hm'⟩ := hvertex r' hr' hra' hc'
    rw [← h] at hm'
    rcases block_cases hg hS hO hD hk with ⟨-, -, hmem⟩ | ⟨-, r0, -, hpl, -⟩
    · rcases (hmem r).mp hm with h1 | h1
      · rcases (hmem r').mp hm' with h2 | h2
        · exact h1.trans h2.symm
        · exact (not_headIs_root hS hO hra' h2).elim
      · exact (not_headIs_root hS hO hra h1).elim
    · rw [hpl, List.mem_singleton] at hm hm'
      exact hm.trans hm'.symm

omit hS hO hD in
theorem dAnc_root {D : ℕ → ℕ} {a x : ℕ} (hx : D x = x) (h : Forest.DAnc D a x) : a = x := by
  unfold Forest.DAnc at h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨y, -, hD, hne⟩
  · exact h.symm
  · exact (hne (hx ▸ hD)).elim

omit hD in
/-- Above a vertex, a block top is its first block top or above the vertex that one hangs from. -/
theorem above_iff_head {c z h : ℕ} (hc : BlockTop w c) (hh : HeadIs (g := g) w z h) :
    Above w c z ↔ c = h ∨ Above w c (w.up h) := by
  obtain ⟨hhz, hht, hbet⟩ := (headIs_iff hS hO).mp hh
  constructor
  · intro hcz
    rcases above_total hcz hhz with h1 | h1
    · by_cases hch : c = h
      · exact Or.inl hch
      · exact Or.inr ((above_iff.mp h1).resolve_left hch).2
    · by_cases hch : c = h
      · exact Or.inl hch
      · exact (hbet c hcz h1 hch hc).elim
  · rintro (rfl | h1)
    · exact hhz
    · exact h1.trans ((Above.up hht.2.1).trans hhz)

include hg in
/-- **A block above a vertex's node**: the block of a block top hanging from a cut vertex lies
above a vertex's node exactly when the top lies above the vertex. -/
theorem dAnc_block_iff {c : ℕ} (hc : BlockTop w c) (hcu : w.up c ∈ cuts g w) :
    ∀ k z, w.entry z ≤ k → z < g.n →
      (Forest.DAnc (parentOf (g := g) w) (blockOf (g := g) w c)
        (Forest.nodeOfVertex (report g w) z) ↔ Above w c z) := by
  obtain ⟨hb, hgb⟩ := blockOf_spec hS hO hc
  intro k
  induction k with
  | zero =>
    intro z hk hz
    have := (done_finished hS hD hz).1
    omega
  | succ k ih =>
    intro z hk hz
    have hbk : ∀ c', BlockTop w c' → (blockOf (g := g) w c = blockOf (g := g) w c' ↔ c = c') :=
      fun c' hc' => ⟨fun h => by rw [← topOf_blockOf hg hS hO hD hc,
        ← topOf_blockOf hg hS hO hD hc', h], fun h => h ▸ rfl⟩
    have hcna : w.arrival c ≠ none := hc.2.1
    by_cases hza : w.arrival z = none
    · have hroot := parent_node_root hg hS hO hD hz hza
      constructor
      · intro hd
        have heq := dAnc_root hroot hd
        exfalso
        by_cases hzc : z ∈ cuts g w
        · rw [nodeOfVertex_of_cut hzc] at heq
          have := (cutNodeOf_lt hzc).1
          omega
        · have hnc : w.cut z = false := by
            by_contra h'
            exact hzc (mem_cuts.mpr ⟨hz, by simpa using h'⟩)
          obtain ⟨k0, -, he, hcase⟩ := node_cases hg hS hO hD hz hnc
          rw [he] at heq
          rcases hcase with ⟨h', -⟩ | ⟨-, c0, hc0, hc0u, rfl⟩ | ⟨-, -, hemp⟩
          · exact h' hza
          · rw [(hbk c0 hc0).mp heq, hc0u] at hcu
            exact hzc hcu
          · exact hgb.1 (heq ▸ hemp.1)
      · intro hcz
        exact (hcna (above_root hza hcz ▸ hza)).elim
    · have hh := headOf_spec hS hO hD hz hza
      obtain ⟨hhz, hht, -⟩ := (headIs_iff hS hO).mp hh
      set h := headOf (g := g) w z with hhdef
      obtain ⟨hbh, hgbh⟩ := blockOf_spec hS hO hht
      obtain ⟨-, -, hun, hue, hlt, -⟩ := hangs hS hO h hht.2.1
      have hle := entry_le_of_above' hS hO hhz (entered_of_finished hS hO hht.1)
      -- from `z`'s node to `h`'s block
      have hstep : Forest.DAnc (parentOf (g := g) w) (blockOf (g := g) w c)
          (Forest.nodeOfVertex (report g w) z) ↔
          Forest.DAnc (parentOf (g := g) w) (blockOf (g := g) w c) (blockOf (g := g) w h) := by
        by_cases hzc : z ∈ cuts g w
        · rw [nodeOfVertex_of_cut hzc]
          have hpz : parentOf (g := g) w (cutNodeOf (g := g) w z) = blockOf (g := g) w h := by
            rw [parentOf_cut hzc, ite_eq_right hza]
          rw [Forest.dAnc_iff (by rw [hpz]; have := (cutNodeOf_lt hzc).1; omega), hpz]
          constructor
          · rintro (h' | h')
            · have := (cutNodeOf_lt hzc).1
              omega
            · exact h'
          · exact Or.inr
        · have hnc : w.cut z = false := by
            by_contra h'
            exact hzc (mem_cuts.mpr ⟨hz, by simpa using h'⟩)
          obtain ⟨k0, -, he, hcase⟩ := node_cases hg hS hO hD hz hnc
          rw [he]
          rcases hcase with ⟨-, rfl⟩ | ⟨h', -⟩ | ⟨h', -⟩
          · exact Iff.rfl
          · exact absurd h' hza
          · exact absurd h' hza
      rw [hstep, above_iff_head hS hO hc hh]
      by_cases hcuh : w.up h ∈ cuts g w
      · have hph : parentOf (g := g) w (blockOf (g := g) w h) = cutNodeOf (g := g) w (w.up h) := by
          rw [parentOf_blockOf hg hS hO hD hht, ite_eq_left (mem_cuts.mp hcuh).2]
        rw [Forest.dAnc_iff (by rw [hph]; have := (cutNodeOf_lt hcuh).1; omega), hph,
          ← nodeOfVertex_of_cut hcuh, ih (w.up h) (by omega) hun, hbk h hht]
      · have hua : w.arrival (w.up h) = none := by
          by_contra h'
          exact hcuh (cut_up_of_top hS hO hD hht h')
        have hnc : w.cut (w.up h) = false := by
          by_contra h'
          exact hcuh (mem_cuts.mpr ⟨hun, by simpa using h'⟩)
        have hph : parentOf (g := g) w (blockOf (g := g) w h) = blockOf (g := g) w h := by
          rw [parentOf_blockOf hg hS hO hD hht, hnc]
          rfl
        constructor
        · intro hd
          exact Or.inl ((hbk h hht).mp (dAnc_root hph hd))
        · rintro (rfl | h')
          · exact Relation.ReflTransGen.refl
          · exact (hcna (above_root hua h' ▸ hua)).elim

end Done

end Walk

end AlgoDesign.Graphs.Blocks
