/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.StepShape
public import AlgoDesign.Graphs.Blocks.Groups

/-!
# Bridges, cut vertices and blocks: one step keeps what was found

One step of the walk keeps `BlocksOk`, `BridgesOk` and `CutOk`. `blocks_step_moves` names the
walk after each move of a step. `BlocksGrow w w'` says that `w'` keeps what `w` has entered and
finished: the same entry numbers, arrival links and vertices above for entered vertices, the same
climb-back numbers for finished vertices, every taken link still taken, and no new vertex hanging
from a finished one. Every move grows the walk this way, and a growing walk keeps every block
top's group, every finished root with no children, and the children of every finished vertex.

A new block appears only when a vertex `v` finishes under `u` with `entry u ≤ low v`: the links
popped, the stack down to `v`'s arrival link, are the links on the stack whose deeper end was
entered no earlier than `v`, that is the taken links below `v` in no older block, which is `v`'s
group. A block without links appears only when a root with no children finishes. A bridge is
`v`'s arrival link, found when `entry u < low v`; a cut flag is set at `u` by the same test as a
block when `u` is not a root, or at a root with two or more children.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

/-! ## The moves of a step -/

/-- **The moves of a step**, with the whole walk after each: enter a new root, move the outer loop
on, nothing, take a row entry and skip it, take a row entry and push a link back, take a row entry
and descend, finish a vertex under another, finish a root. -/
theorem blocks_step_moves (w : Walk) :
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next = 0 ∧ step g w = newRoot w) ∨
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next ≠ 0 ∧
      step g w = { w with next := w.next + 1 }) ∨
    (w.path = [] ∧ g.n ≤ w.next ∧ step g w = w) ∨
    (∃ v arr i rest x e, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = some (x, e) ∧
      ((x = v ∨ arr = some e ∨ (w.entry x ≠ 0 ∧ w.entry v ≤ w.entry x)) ∧
          step g w = tick w v arr i rest ∨
        (x ≠ v ∧ arr ≠ some e ∧ w.entry x ≠ 0 ∧ w.entry x < w.entry v) ∧
          step g w = { tick w v arr i rest with
            edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.entry x)) } ∨
        (x ≠ v ∧ arr ≠ some e ∧ w.entry x = 0) ∧
          step g w = { descend w v arr i rest x e with edges := e :: w.edges })) ∨
    (∃ v e i u a j above, w.path = ⟨v, some e, i⟩ :: ⟨u, a, j⟩ :: above ∧
      (g.adj v)[i]? = none ∧
      step g w = finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty) ∨
    (∃ v arr i rest, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = none ∧
      (rest = [] ∨ arr = none) ∧ step g w = finishRoot (pop w v rest) v) := by
  unfold step
  rcases hp : w.path with _ | ⟨⟨v, arr, i⟩, rest⟩
  · by_cases h1 : w.next < g.n
    · by_cases h2 : w.entry w.next = 0
      · exact Or.inl ⟨rfl, h1, h2, by simp only [h1, h2, ite_true]; unfold newRoot; rw [hp]⟩
      · exact Or.inr (Or.inl ⟨rfl, h1, h2, by simp only [h1, h2, ite_true, ite_false]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by simp only [h1, ite_false]⟩))
  · right; right; right
    rcases hx : (g.adj v)[i]? with _ | ⟨x, e⟩
    · right
      simp only [hx]
      rcases rest with _ | ⟨⟨u, a, j⟩, above⟩ <;> rcases arr with _ | e
      · exact Or.inr ⟨v, none, i, [], rfl, hx, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨v, some e, i, [], rfl, hx, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨_, none, i, _, rfl, hx, Or.inr rfl, rfl⟩
      · exact Or.inl ⟨v, e, i, u, a, j, above, rfl, hx, rfl⟩
    · left
      refine ⟨v, arr, i, rest, x, e, rfl, hx, ?_⟩
      simp only [hx]
      unfold look
      dsimp only
      by_cases h1 : x = v ∨ arr = some e
      · exact Or.inl ⟨h1.elim Or.inl (Or.inr ∘ Or.inl), by rw [ite_eq_left h1]; rfl⟩
      · rw [ite_eq_right h1]
        have hxv : x ≠ v := fun h => h1 (Or.inl h)
        have hae : arr ≠ some e := fun h => h1 (Or.inr h)
        by_cases h2 : w.entry x = 0
        · rw [ite_eq_left h2]
          exact Or.inr (Or.inr ⟨⟨hxv, hae, h2⟩, rfl⟩)
        · rw [ite_eq_right h2]
          by_cases h3 : w.entry x < w.entry v
          · rw [ite_eq_left h3]
            exact Or.inr (Or.inl ⟨⟨hxv, hae, h2, h3⟩, rfl⟩)
          · rw [ite_eq_right h3]
            exact Or.inl ⟨Or.inr (Or.inr ⟨h2, by omega⟩), rfl⟩

/-! ## What the finishing rules change -/

/-- Finishing under a vertex keeps the tree, the status and the rows taken. -/
theorem blocks_fu_fields (w : Walk) (u v e : ℕ) (b : Bool) :
    (finishUnder g w u v e b).entry = w.entry ∧ (finishUnder g w u v e b).arrival = w.arrival ∧
    (finishUnder g w u v e b).up = w.up ∧ (finishUnder g w u v e b).finished = w.finished ∧
    (finishUnder g w u v e b).taken = w.taken ∧ (finishUnder g w u v e b).path = w.path ∧
    (finishUnder g w u v e b).children = w.children := by
  unfold finishUnder
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem blocks_fu_low (w : Walk) (u v e : ℕ) (b : Bool) :
    (finishUnder g w u v e b).low = Function.update w.low u (min (w.low u) (w.low v)) := by
  unfold finishUnder
  dsimp only
  split_ifs <;> rfl

/-- What finishing `v` under `u` finds: a block when `u`'s entry number is at most `low v`, a
bridge when it is below, and `u`'s cut flag when it is not a root. -/
theorem blocks_fu_found (w : Walk) {u v : ℕ} (e : ℕ) (b : Bool) (huv : u ≠ v) :
    (finishUnder g w u v e b).blocks =
      (if w.entry u ≤ w.low v then w.blocks ++ [(popBlock e w.edges).1] else w.blocks) ∧
    (finishUnder g w u v e b).vertices = (if w.entry u ≤ w.low v then
      w.vertices ++ [verticesOf g (popBlock e w.edges).1] else w.vertices) ∧
    (finishUnder g w u v e b).edges =
      (if w.entry u ≤ w.low v then (popBlock e w.edges).2 else w.edges) ∧
    (finishUnder g w u v e b).bridges =
      (if w.entry u < w.low v then w.bridges ++ [e] else w.bridges) ∧
    (finishUnder g w u v e b).cut = (if w.entry u ≤ w.low v ∧ b = false then
      Function.update w.cut u true else w.cut) := by
  have hl : Function.update w.low u (min (w.low u) (w.low v)) v = w.low v :=
    Function.update_of_ne (Ne.symm huv) _ _
  unfold finishUnder
  dsimp only
  simp only [hl]
  split_ifs <;> simp_all

/-- Finishing a root keeps everything but what it finds. -/
theorem blocks_fr_fields (w : Walk) (v : ℕ) :
    (finishRoot w v).entry = w.entry ∧ (finishRoot w v).arrival = w.arrival ∧
    (finishRoot w v).up = w.up ∧ (finishRoot w v).finished = w.finished ∧
    (finishRoot w v).taken = w.taken ∧ (finishRoot w v).low = w.low ∧
    (finishRoot w v).bridges = w.bridges := by
  unfold finishRoot
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What finishing a root finds: a block of its own with no children, a cut vertex with two or
more. -/
theorem blocks_fr_found (w : Walk) (v : ℕ) :
    (finishRoot w v).blocks = (if w.children = 0 then w.blocks ++ [[]] else w.blocks) ∧
    (finishRoot w v).vertices = (if w.children = 0 then w.vertices ++ [[v]] else w.vertices) ∧
    (finishRoot w v).cut =
      (if 2 ≤ w.children then Function.update w.cut v true else w.cut) := by
  unfold finishRoot
  dsimp only
  split_ifs <;> first | omega | simp_all

/-! ## The frames of a finishing vertex -/

section Frames

variable {w : Walk} (hS : Shape (g := g) w)
include hS

/-- A vertex finishing as a root is the path's only frame and has no arrival link. -/
theorem blocks_root_frame {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (h : rest = [] ∨ arr = none) :
    rest = [] ∧ arr = none := by
  obtain ⟨-, hch, hlast, -⟩ := hS.2.1
  rw [hp] at hch hlast
  rcases rest with _ | ⟨b, l⟩
  · exact ⟨rfl, hlast ⟨v, arr, i⟩ (by simp)⟩
  · rcases h with h | h
    · simp at h
    · subst h
      rw [List.isChain_cons_cons] at hch
      obtain ⟨⟨e, he, -⟩, -⟩ := hch.1
      simp at he

/-- A vertex finishing under another: what the path says about the two. -/
theorem blocks_under_frame {v e i u j : ℕ} {a : Option ℕ} {above : List Frame}
    (hp : w.path = ⟨v, some e, i⟩ :: ⟨u, a, j⟩ :: above) :
    u ≠ v ∧ w.up v = u ∧ w.arrival v = some e ∧ w.arrival u = a ∧ Joins g e u v ∧
      w.entry u < w.entry v ∧ w.onPath u = true ∧ w.onPath v = true ∧ v < g.n ∧ u < g.n ∧
      (above.isEmpty = true ↔ a = none) := by
  obtain ⟨hnd, hch, hlast, hall⟩ := hS.2.1
  rw [hp] at hnd hch hlast hall
  rw [List.isChain_cons_cons] at hch
  obtain ⟨⟨e', he', hj⟩, hup, hlt⟩ := hch.1
  simp only [Option.mem_def, Option.some.injEq] at he'
  subst he'
  have hv := hall _ List.mem_cons_self
  have hu := hall _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [List.map_cons, List.nodup_cons] at hnd
  refine ⟨fun h => hnd.1 (by simp [h]), hup, hv.2.2.1, hu.2.2.1, hj, hlt,
    by simp [onPath, hp], by simp [onPath, hp], hv.1, hu.1, ?_⟩
  rcases above with _ | ⟨b, l⟩
  · simp only [List.isEmpty_nil, true_iff]
    exact hlast ⟨u, a, j⟩ (by simp)
  · simp only [List.isEmpty_cons, Bool.false_eq_true, false_iff]
    have h2 := hch.2
    rw [List.isChain_cons_cons] at h2
    obtain ⟨⟨e'', he'', -⟩, -⟩ := h2.1
    intro ha
    simp [ha] at he''

end Frames

/-! ## Growing walks -/

/-- `w'` keeps what `w` has entered and finished: the tree among entered vertices, the climb-back
numbers of finished vertices and the links taken; no new vertex hangs from a finished one; and
`Anc` reads `w'`'s tree. -/
def BlocksGrow (w w' : Walk) : Prop :=
  (∀ z, w.entry z ≠ 0 → w'.entry z = w.entry z ∧ w'.arrival z = w.arrival z ∧
    w'.up z = w.up z) ∧
  (∀ z, w.finished z = true → w'.finished z = true ∧ w'.low z = w.low z) ∧
  (∀ c, w.entry c = 0 → w'.arrival c ≠ none → w.finished (w'.up c) = false) ∧
  (∀ f, Taken (g := g) w f → Taken (g := g) w' f) ∧
  ∀ a y, Anc (g := g) w' a y ↔ Above w' a y

/-- Links taken stay taken when every row's entries taken stay taken. -/
theorem blocks_taken_mono {w w' : Walk}
    (h : ∀ x, ∀ s ∈ looked (g := g) w x, s ∈ looked (g := g) w' x) {f : ℕ}
    (hf : Taken (g := g) w f) : Taken (g := g) w' f := by
  obtain ⟨hnl, x, hx, s, hs, rfl⟩ := hf
  exact ⟨hnl, x, hx, s, h x s hs, rfl⟩

theorem blocks_above_congr {w w' : Walk} (ha : w'.arrival = w.arrival) (hu : w'.up = w.up)
    (a y : ℕ) : Above w' a y ↔ Above w a y := by
  unfold Above
  rw [ha, hu]

section Grow

variable (hg : g.WellFormed) {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)

include hS hO in
/-- A walk with the same tree, whose finished vertices keep their climb-back numbers and whose
taken links stay taken, grows. -/
theorem blocks_grow_of (he : w'.entry = w.entry) (ha : w'.arrival = w.arrival)
    (hu : w'.up = w.up)
    (hf : ∀ z, w.finished z = true → w'.finished z = true ∧ w'.low z = w.low z)
    (ht : ∀ f, Taken (g := g) w f → Taken (g := g) w' f) : BlocksGrow (g := g) w w' := by
  refine ⟨fun z _ => ⟨by rw [he], by rw [ha], by rw [hu]⟩, hf, fun c hc hca => ?_, ht,
    fun a y => ?_⟩
  · rw [ha] at hca
    by_cases hcn : c < g.n
    · exact absurd ((hS.2.2.1 c hcn).2.2.2 hc).2 hca
    · exact absurd (hO c (by omega)).2.2.2.2 hca
  · rw [anc_congr ha hu, anc_iff hS hO, blocks_above_congr ha hu]

variable (hG : BlocksGrow (g := g) w w')

include hS hO hG

/-- A growing walk keeps every link up the tree. -/
theorem blocks_above_lift {a y : ℕ} (h : Above w a y) : Above w' a y := by
  induction h with
  | refl => exact Above.refl _ _
  | @tail b c _ hbc ih =>
    obtain ⟨hc, rfl⟩ := hbc
    have hce := (hangs hS hO c hc).2.1
    obtain ⟨-, hca, hcu⟩ := hG.1 c hce
    exact ih.trans (Relation.ReflTransGen.single ⟨by rw [hca]; exact hc, hcu⟩)

/-- Below a finished vertex, a growing walk adds no link up the tree. -/
theorem blocks_above_drop {a y : ℕ} (h : Above w' a y) (ha : w.finished a = true) :
    Above w a y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Above.refl _ _
  | @head b c hst _ ih =>
    obtain ⟨hc, hcb⟩ := hst
    by_cases hce : w.entry c = 0
    · have := hG.2.2.1 c hce hc
      rw [hcb, ha] at this
      exact absurd this (by simp)
    · obtain ⟨-, hca, hcu⟩ := hG.1 c hce
      rw [hca] at hc
      rw [hcu] at hcb
      subst hcb
      have hbc : Above w (w.up c) c := Above.up hc
      exact hbc.trans (ih (finished_of_above hS hO hbc ha hce))

/-- A finished vertex is a block top in a growing walk exactly when it was one. -/
theorem blocks_blockTop_iff {c : ℕ} (hc : w.finished c = true) :
    BlockTop w' c ↔ BlockTop w c := by
  have hce := entered_of_finished hS hO hc
  obtain ⟨he, ha, hu⟩ := hG.1 c hce
  obtain ⟨hf, hl⟩ := hG.2.1 c hc
  unfold BlockTop
  rw [ha, hu, hl, hf, hc]
  by_cases hca : w.arrival c = none
  · simp [hca]
  · rw [(hG.1 (w.up c) (hangs hS hO c hca).2.2.2.1).1]

omit hS hO in
/-- A finished vertex has the same children in a growing walk. -/
theorem blocks_child_iff {p c : ℕ} (hp : w.finished p = true) : Child w' p c ↔ Child w p c := by
  unfold Child
  by_cases hce : w.entry c = 0
  · rw [hce]
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_and]
    intro _ hca hcu
    have := hG.2.2.1 c hce hca
    rw [hcu, hp] at this
    exact absurd this (by simp)
  · obtain ⟨he, ha, hu⟩ := hG.1 c hce
    rw [he, ha, hu]

omit hS hO in
theorem blocks_numChildren_eq {p : ℕ} (hp : w.finished p = true) :
    numChildren (g := g) w' p = numChildren (g := g) w p := by
  unfold numChildren
  congr 1
  exact List.filter_congr fun c _ => by
    rw [decide_eq_decide]
    exact blocks_child_iff hG hp

/-- A finished vertex is a finished root with no children in a growing walk exactly when it was
one. -/
theorem blocks_loneRoot_iff {r : ℕ} (hr : w.finished r = true) :
    LoneRoot (g := g) w' r ↔ LoneRoot (g := g) w r := by
  unfold LoneRoot
  rw [blocks_numChildren_eq hG hr, (hG.1 r (entered_of_finished hS hO hr)).2.1,
    (hG.2.1 r hr).1, hr]

end Grow

/-! ## First block tops -/

/-- `HeadIs`, read through `Above`, wherever `Anc` is `Above`. -/
theorem blocks_headIs_iff {w : Walk} (hanc : ∀ a y, Anc (g := g) w a y ↔ Above w a y)
    {x c : ℕ} : HeadIs (g := g) w x c ↔ Above w c x ∧ BlockTop w c ∧
      ∀ c', Above w c' x → Above w c c' → c' ≠ c → ¬ BlockTop w c' := by
  unfold HeadIs
  rw [hanc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h c' h1 h2 h3
    exact h c' ((hanc c' x).mpr h1) ((hanc c c').mpr h2) h3
  · intro h c' h1 h2 h3
    exact h c' ((hanc c' x).mp h1) ((hanc c c').mp h2) h3

/-! ## Links at finished vertices -/

section Finished

variable (hg : g.WellFormed) {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)

include hg hS hO in
/-- Both ends of a link at a finished vertex are entered. -/
theorem blocks_ends_entered {f x a b : ℕ} (hxf : w.finished x = true)
    (hl : g.links[f]? = some (a, b)) (hx : a = x ∨ b = x) : w.entry a ≠ 0 ∧ w.entry b ≠ 0 := by
  have hxn := finished_lt hO hxf
  have hxe := entered_of_finished hS hO hxf
  obtain ⟨y, hj, hy, hne⟩ := ends_of_deep hl hx
  by_cases hab : a = b
  · subst hab
    obtain rfl : a = x := hx.elim id id
    exact ⟨hxe, hxe⟩
  · have hyx := hne hab
    have hye := (link_of_finished hg hS hO hxn hxf hj hyx).1
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hyx
    · exact ⟨hxe, hye⟩
    · exact ⟨hye, hxe⟩
    · exact absurd rfl hyx

include hg hS in
/-- A link other than a loop at a finished vertex is taken. -/
theorem blocks_taken_of_deep {f x : ℕ} (hxf : w.finished x = true)
    (hd : Deep (g := g) w f x) (hnl : NonLoop g f) : Taken (g := g) w f := by
  have hxn : x < g.n := by
    by_contra hn
    exact hn (by
      obtain ⟨⟨a, b⟩, hl, hab, -⟩ := hd
      simp only [Option.mem_def] at hl
      rcases hab with rfl | rfl
      · exact (hg _ (List.mem_of_getElem? hl)).1
      · exact (hg _ (List.mem_of_getElem? hl)).2)
  obtain ⟨⟨a, b⟩, hl, hab, -⟩ := hd
  simp only [Option.mem_def] at hl
  obtain ⟨y, hj, -, -⟩ := ends_of_deep hl hab
  refine ⟨hnl, x, hxn, (y, f), ?_, rfl⟩
  rw [looked_of_finished hS hxn hxf]
  exact adj_mem_of_joins hg hj

variable (hG : BlocksGrow (g := g) w w')

include hg hS hO hG in
/-- At a finished vertex, the deeper ends of links are the same in a growing walk. -/
theorem blocks_deep_iff {f x : ℕ} (hxf : w.finished x = true) :
    Deep (g := g) w' f x ↔ Deep (g := g) w f x := by
  rcases hl : g.links[f]? with _ | ⟨a, b⟩
  · simp [Deep, hl]
  rw [deep_iff hl, deep_iff hl]
  by_cases hx : a = x ∨ b = x
  · obtain ⟨ha, hb⟩ := blocks_ends_entered hg hS hO hxf hl hx
    have key : ∀ y, (a = y ∨ b = y) → w'.entry y = w.entry y := by
      rintro y (rfl | rfl)
      exacts [(hG.1 _ ha).1, (hG.1 _ hb).1]
    rw [key x hx, key a (Or.inl rfl), key b (Or.inr rfl)]
  · exact ⟨fun h => absurd h.1 hx, fun h => absurd h.1 hx⟩

include hg hS hO hG in
/-- **Old groups stay**: a block top's group is the same in a growing walk. -/
theorem blocks_inGroup_iff {c f : ℕ} (hc : BlockTop w c) :
    InGroup (g := g) w' c f ↔ InGroup (g := g) w c f := by
  have hanc := hG.2.2.2.2
  have hcf := hc.1
  have hce := entered_of_finished hS hO hcf
  constructor
  · rintro ⟨htk, x, hxn, hd, hh⟩
    obtain ⟨hcx', -, hmin'⟩ := (blocks_headIs_iff hanc).mp hh
    have hcx := blocks_above_drop hS hO hG hcx' hcf
    have hxf := finished_of_above hS hO hcx hcf (entered_of_above hS hO hcx hce)
    have hd' := (blocks_deep_iff hg hS hO hG hxf).mp hd
    refine ⟨blocks_taken_of_deep hg hS hxf hd' htk.1, x, hxn, hd',
      (headIs_iff hS hO).mpr ⟨hcx, hc, fun c' h1 h2 h3 h4 => ?_⟩⟩
    exact hmin' c' (blocks_above_lift hS hO hG h1) (blocks_above_lift hS hO hG h2) h3
      ((blocks_blockTop_iff hS hO hG h4.1).mpr h4)
  · rintro ⟨htk, x, hxn, hd, hh⟩
    obtain ⟨hcx, -, hmin⟩ := (headIs_iff hS hO).mp hh
    have hxf := finished_of_above hS hO hcx hcf (entered_of_above hS hO hcx hce)
    refine ⟨hG.2.2.2.1 f htk, x, hxn, (blocks_deep_iff hg hS hO hG hxf).mpr hd,
      (blocks_headIs_iff hanc).mpr ⟨blocks_above_lift hS hO hG hcx,
        (blocks_blockTop_iff hS hO hG hcf).mpr hc, fun c' h1 h2 h3 h4 => ?_⟩⟩
    have h2' := blocks_above_drop hS hO hG h2 hcf
    have hc'f := finished_of_above hS hO h2' hcf (entered_of_above hS hO h2' hce)
    exact hmin c' (blocks_above_drop hS hO hG h1 hc'f) h2' h3
      ((blocks_blockTop_iff hS hO hG hc'f).mp h4)

include hg hS hO hG in
theorem blocks_isGroupOf_iff {b : List ℕ} {c : ℕ} (hc : BlockTop w c) :
    IsGroupOf (g := g) w' b c ↔ IsGroupOf (g := g) w b c := by
  unfold IsGroupOf
  rw [blocks_blockTop_iff hS hO hG hc.1]
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun f => ?_
  rw [blocks_inGroup_iff hg hS hO hG hc]

end Finished

/-! ## The first block top -/

section Head

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

/-- Below a block top, every vertex has a first block top. -/
theorem blocks_exists_head {c x : ℕ} (hcx : Above w c x) (hc : BlockTop w c) :
    ∃ c', HeadIs (g := g) w x c' := by
  have self : ∀ x, BlockTop w x → ∃ c', HeadIs (g := g) w x c' := fun x hx =>
    ⟨x, (headIs_iff hS hO).mpr ⟨Above.refl w x, hx, fun c' h1 h2 h3 _ =>
      h3 (above_antisymm hS hO h1 h2)⟩⟩
  suffices ∀ k x, w.entry x ≤ k → Above w c x → ∃ c', HeadIs (g := g) w x c' from
    this _ x le_rfl hcx
  intro k
  induction k with
  | zero =>
    intro x hk hcx
    by_cases hxt : BlockTop w x
    · exact self x hxt
    · rcases above_iff.mp hcx with h | ⟨ha, -⟩
      · exact absurd (h ▸ hc) hxt
      · exact absurd (by omega) (hangs hS hO x ha).2.1
  | succ k ih =>
    intro x hk hcx
    by_cases hxt : BlockTop w x
    · exact self x hxt
    · rcases above_iff.mp hcx with h | ⟨ha, hcu⟩
      · exact absurd (h ▸ hc) hxt
      · have hlt := (hangs hS hO x ha).2.2.2.2.1
        obtain ⟨c', hh⟩ := ih (w.up x) (by omega) hcu
        obtain ⟨h1, h2, h3⟩ := (headIs_iff hS hO).mp hh
        refine ⟨c', (headIs_iff hS hO).mpr ⟨h1.trans (Above.up ha), h2,
          fun c'' g1 g2 g3 g4 => ?_⟩⟩
        rcases above_iff.mp g1 with h | ⟨-, g1'⟩
        · exact hxt (h ▸ g4)
        · exact h3 c'' g1' g2 g3 g4

end Head

/-! ## Every move grows the walk -/

/-- Links taken stay taken when no row's count of entries taken drops. -/
theorem blocks_taken_le {w w' : Walk} (h : ∀ x, w.taken x ≤ w'.taken x) {f : ℕ}
    (hf : Taken (g := g) w f) : Taken (g := g) w' f :=
  blocks_taken_mono (fun x _ hs => (List.take_prefix_take_left (h x)).subset hs) hf

section Moves

variable {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

/-- A walk that enters one new vertex and otherwise keeps the tree, the status and the climb-back
numbers grows. -/
theorem blocks_grow_new {x0 : ℕ} (h0 : w.entry x0 = 0)
    (he : ∀ z, z ≠ x0 → w'.entry z = w.entry z) (ha : ∀ z, z ≠ x0 → w'.arrival z = w.arrival z)
    (hu : ∀ z, z ≠ x0 → w'.up z = w.up z) (hf : w'.finished = w.finished)
    (hl : ∀ z, z ≠ x0 → w'.low z = w.low z)
    (hx0 : w'.arrival x0 ≠ none → w.finished (w'.up x0) = false)
    (ht : ∀ f, Taken (g := g) w f → Taken (g := g) w' f)
    (hanc : ∀ a y, Anc (g := g) w' a y ↔ Above w' a y) : BlocksGrow (g := g) w w' := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun c hc hca => ?_, ht, hanc⟩
  · have hzx : z ≠ x0 := fun h => hz (h ▸ h0)
    exact ⟨he z hzx, ha z hzx, hu z hzx⟩
  · have hzx : z ≠ x0 := fun h => (entered_of_finished hS hO hz) (h ▸ h0)
    exact ⟨by rw [hf]; exact hz, hl z hzx⟩
  · by_cases hcx : c = x0
    · subst hcx
      exact hx0 hca
    · rw [ha c hcx] at hca
      by_cases hcn : c < g.n
      · exact absurd ((hS.2.2.1 c hcn).2.2.2 hc).2 hca
      · exact absurd (hO c (by omega)).2.2.2.2 hca

/-- **Every move grows the walk.** -/
theorem blocks_grow_step : BlocksGrow (g := g) w (step g w) := by
  rcases blocks_step_moves (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h⟩ | ⟨⟨-, -, h0⟩, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, -, h⟩ <;> rw [h]
  · refine blocks_grow_new (x0 := w.next) hS hO h0 (fun z hz => ?_) (fun z hz => ?_)
      (fun z hz => ?_) rfl (fun z hz => ?_) (fun h => by simp [newRoot, enter] at h)
      (fun _ => blocks_taken_le fun _ => le_rfl) (anc_iff_newRoot hS hO h0)
    all_goals simp [newRoot, enter, Function.update_of_ne hz]
  · exact blocks_grow_of hS hO rfl rfl rfl (fun z hz => ⟨hz, rfl⟩)
      (fun _ => blocks_taken_le fun _ => le_rfl)
  · exact blocks_grow_of hS hO rfl rfl rfl (fun z hz => ⟨hz, rfl⟩) (fun _ h => h)
  all_goals
    obtain ⟨hvn, -, -, htv, -, hvon⟩ := top_facts hS hp
    have hvf : w.finished v = false := by
      by_contra hc
      exact (hS.2.2.1 v hvn).2.1 ⟨hvon, by simpa using hc⟩
  · have htk : ∀ y, w.taken y ≤ (tick w v arr i rest).taken y := by
      intro y
      simp only [tick, Function.update_apply]
      split_ifs with hy
      · subst hy
        omega
      · exact le_rfl
    exact blocks_grow_of hS hO rfl rfl rfl (fun z hz => ⟨hz, rfl⟩)
      (fun _ => blocks_taken_le htk)
  · have htk : ∀ y, w.taken y ≤ (tick w v arr i rest).taken y := by
      intro y
      simp only [tick, Function.update_apply]
      split_ifs with hy
      · subst hy
        omega
      · exact le_rfl
    refine blocks_grow_of hS hO rfl rfl rfl (fun z hz => ⟨hz, ?_⟩)
      (fun _ => blocks_taken_le htk)
    have hzv : z ≠ v := fun h' => by rw [h'] at hz; simp [hz] at hvf
    exact Function.update_of_ne hzv _ _
  · have htk : ∀ y, w.taken y ≤ (tick w v arr i rest).taken y := by
      intro y
      simp only [tick, Function.update_apply]
      split_ifs with hy
      · subst hy
        omega
      · exact le_rfl
    refine blocks_grow_new (x0 := x) hS hO h0 (fun z hz => ?_) (fun z hz => ?_)
      (fun z hz => ?_) rfl (fun z hz => ?_) (fun _ => by simpa [descend, enter] using hvf)
      (fun _ => blocks_taken_le htk) (fun a y => ?_)
    · simp [descend, enter, tick, Function.update_of_ne hz]
    · simp [descend, enter, tick, Function.update_of_ne hz]
    · simp [descend, enter, tick, Function.update_of_ne hz]
    · simp [descend, enter, tick, Function.update_of_ne hz]
    · have h1 := anc_congr (g := g) (w := descend w v arr i rest x e)
        (w' := { descend w v arr i rest x e with edges := e :: w.edges }) rfl rfl
      have h2 := blocks_above_congr (w := descend w v arr i rest x e)
        (w' := { descend w v arr i rest x e with edges := e :: w.edges }) rfl rfl a y
      rw [h1, h2]
      exact anc_iff_descend hS hO hp h0 a y
  · obtain ⟨-, -, -, -, -, -, hon_u, -, -, hun, -⟩ := blocks_under_frame hS hp
    obtain ⟨he, ha, hu, hf, ht, -, -⟩ :=
      blocks_fu_fields (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty
    refine blocks_grow_of hS hO he ha hu (fun z hz => ⟨?_, ?_⟩)
      (fun _ => blocks_taken_le fun y => by rw [ht]; exact le_rfl)
    · rw [hf]
      simp [pop, Function.update_apply, hz]
    · have hzu : z ≠ u := fun h' => (hS.2.2.1 u hun).2.1 ⟨hon_u, h' ▸ hz⟩
      rw [blocks_fu_low, Function.update_of_ne hzu]
      rfl
  · obtain ⟨he, ha, hu, hf, ht, hl, -⟩ := blocks_fr_fields (pop w v rest) v
    refine blocks_grow_of hS hO he ha hu (fun z hz => ⟨?_, by rw [hl]; rfl⟩)
      (fun _ => blocks_taken_le fun y => by rw [ht]; exact le_rfl)
    rw [hf]
    simp [pop, Function.update_apply, hz]

end Moves

/-! ## Lists -/

theorem blocks_getD_app (l m : List (List ℕ)) (k : ℕ) :
    (l ++ m).getD k [] = if k < l.length then l.getD k [] else m.getD (k - l.length) [] := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega)]

theorem blocks_getD_mem {l : List (List ℕ)} {k : ℕ} (hk : k < l.length) : l.getD k [] ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

theorem blocks_getD_idxOf {l : List ℕ} {f : ℕ} (h : f ∈ l) : l.getD (l.idxOf f) 0 = f := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h), Option.getD_some]
  exact List.getElem_idxOf _

/-- The first `k + 1` entries of a list hold exactly the members first found at `k` or before. -/
theorem blocks_mem_take_iff (l : List ℕ) (f k : ℕ) :
    f ∈ l.take (k + 1) ↔ f ∈ l ∧ l.idxOf f ≤ k := by
  induction l generalizing k with
  | nil => simp
  | cons x l ih =>
    by_cases hx : x = f
    · subst hx
      simp [List.idxOf_cons_self]
    · rw [List.idxOf_cons_ne _ hx]
      cases k with
      | zero => simp [Ne.symm hx]
      | succ k =>
        rw [List.take_succ_cons, List.mem_cons, ih k, List.mem_cons]
        simp only [Ne.symm hx, false_or]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

/-- `popBlock e` cuts the stack just after `e`. -/
theorem blocks_popBlock_eq (e : ℕ) : ∀ l : List ℕ,
    popBlock e l = (l.take (l.idxOf e + 1), l.drop (l.idxOf e + 1))
  | [] => rfl
  | x :: rest => by
    unfold popBlock
    by_cases h : x = e
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      rw [blocks_popBlock_eq e rest, List.idxOf_cons_ne _ h]
      simp

theorem blocks_deep_congr {w w' : Walk} (he : w'.entry = w.entry) (f x : ℕ) :
    Deep (g := g) w' f x ↔ Deep (g := g) w f x := by
  unfold Deep deepEntry
  rw [he]

theorem blocks_taken_congr {w w' : Walk} (ht : w'.taken = w.taken) (f : ℕ) :
    Taken (g := g) w' f ↔ Taken (g := g) w f := by
  unfold Taken looked
  rw [ht]

/-! ## Assembling the blocks -/

section Assemble

variable (hg : g.WellFormed) {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hG : BlocksGrow (g := g) w w')
include hg hS hO hG

/-- `BlocksOk` after a growing step that appends blocks `B` with vertices `P`: the new blocks with
links are groups and list their vertices, the new blocks without links are new finished roots with
no children, one each, and every new block top and new such root has a new block. -/
theorem blocks_blocksOk_of {B P : List (List ℕ)}
    (hb : w'.blocks = w.blocks ++ B) (hpl : w'.vertices = w.vertices ++ P)
    (hlen : P.length = B.length)
    (h2 : ∀ k < B.length, B.getD k [] ≠ [] → P.getD k [] = verticesOf g (B.getD k []))
    (h3 : ∀ k < B.length, B.getD k [] ≠ [] → ∃ c < g.n, IsGroupOf (g := g) w' (B.getD k []) c)
    (h4 : ∀ k < B.length, B.getD k [] = [] → ∃ r < g.n, P.getD k [] = [r] ∧
      LoneRoot (g := g) w' r ∧ w.finished r = false)
    (h5 : ∀ c < g.n, BlockTop w' c → w.finished c = false →
      ∃ k < B.length, IsGroupOf (g := g) w' (B.getD k []) c)
    (h6 : ∀ r < g.n, LoneRoot (g := g) w' r → w.finished r = false →
      ∃ k < B.length, B.getD k [] = [] ∧ P.getD k [] = [r])
    (h7 : ∀ j < B.length, ∀ k < B.length, ∀ r, B.getD j [] = [] → P.getD j [] = [r] →
      B.getD k [] = [] → P.getD k [] = [r] → j = k)
    (h8 : B.flatten.Nodup) (h8' : ∀ f ∈ B.flatten, f ∉ w.blocks.flatten)
    (h9 : ∀ b ∈ B, ∀ f ∈ b, f < g.links.length) : BlocksOk (g := g) w' := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold BlocksOk EmptyAt
  rw [hb, hpl]
  simp only [List.length_append]
  refine ⟨by omega, fun k hk hne => ?_, fun k hk hne => ?_, fun k hk hemp => ?_,
    fun c hc hbt => ?_, fun r hr hlr => ?_, fun j hj k hk r hr ⟨ej1, ej2⟩ ⟨ek1, ek2⟩ => ?_, ?_,
    fun b hb f hf => ?_⟩
  · simp only [blocks_getD_app, o1] at hne ⊢
    by_cases hkl : k < w.blocks.length
    · simp only [hkl, ↓reduceIte] at hne ⊢
      exact o2 k hkl hne
    · simp only [hkl, ↓reduceIte] at hne ⊢
      exact h2 _ (by omega) hne
  · rw [blocks_getD_app] at hne ⊢
    by_cases hkl : k < w.blocks.length
    · simp only [hkl, ↓reduceIte] at hne ⊢
      obtain ⟨c, hc, hgr⟩ := o3 k hkl hne
      exact ⟨c, hc, (blocks_isGroupOf_iff hg hS hO hG hgr.2.1).mpr hgr⟩
    · simp only [hkl, ↓reduceIte] at hne ⊢
      exact h3 _ (by omega) hne
  · rw [blocks_getD_app] at hemp
    simp only [blocks_getD_app, o1]
    by_cases hkl : k < w.blocks.length
    · simp only [hkl, ↓reduceIte] at hemp ⊢
      obtain ⟨r, hr, ⟨e1, e2⟩, hlr⟩ := o4 k hkl hemp
      exact ⟨r, hr, ⟨e1, e2⟩, (blocks_loneRoot_iff hS hO hG hlr.1).mpr hlr⟩
    · simp only [hkl, ↓reduceIte] at hemp ⊢
      obtain ⟨r, hr, e2, hlr, -⟩ := h4 _ (by omega) hemp
      exact ⟨r, hr, ⟨hemp, e2⟩, hlr⟩
  · by_cases hcf : w.finished c = true
    · obtain ⟨k, hk, hgr⟩ := o5 c hc ((blocks_blockTop_iff hS hO hG hcf).mp hbt)
      refine ⟨k, by omega, ?_⟩
      rw [blocks_getD_app]
      simp only [hk, ↓reduceIte]
      exact (blocks_isGroupOf_iff hg hS hO hG hgr.2.1).mpr hgr
    · obtain ⟨k, hk, hgr⟩ := h5 c hc hbt (by simpa using hcf)
      refine ⟨w.blocks.length + k, by omega, ?_⟩
      rw [blocks_getD_app]
      simpa using hgr
  · by_cases hrf : w.finished r = true
    · obtain ⟨k, hk, e1, e2⟩ := o6 r hr ((blocks_loneRoot_iff hS hO hG hrf).mp hlr)
      refine ⟨k, by omega, ?_, ?_⟩
      · rw [blocks_getD_app]
        simp only [hk, ↓reduceIte]
        exact e1
      · rw [blocks_getD_app, o1]
        simp only [hk, ↓reduceIte]
        exact e2
    · obtain ⟨k, hk, e1, e2⟩ := h6 r hr hlr (by simpa using hrf)
      refine ⟨w.blocks.length + k, by omega, ?_, ?_⟩
      · rw [blocks_getD_app]
        simpa using e1
      · rw [blocks_getD_app, o1]
        simpa using e2
  · rw [blocks_getD_app] at ej1 ek1
    rw [blocks_getD_app, o1] at ej2 ek2
    have old : ∀ i < w.blocks.length, ∀ i' < B.length, w.blocks.getD i [] = [] →
        w.vertices.getD i [] = [r] → B.getD i' [] = [] → P.getD i' [] = [r] → False := by
      intro i hi i' hi' a1 a2 a3 a4
      obtain ⟨r', -, ⟨-, e2⟩, hlr⟩ := o4 i hi a1
      rw [a2, List.cons.injEq] at e2
      obtain ⟨r'', -, hrr, -, hf⟩ := h4 i' hi' a3
      rw [a4, List.cons.injEq] at hrr
      rw [← hrr.1, e2.1] at hf
      rw [hlr.1] at hf
      exact absurd hf (by simp)
    by_cases hjl : j < w.blocks.length <;> by_cases hkl : k < w.blocks.length <;>
      simp only [hjl, hkl, ↓reduceIte] at ej1 ej2 ek1 ek2
    · exact o7 j hjl k hkl r hr ⟨ej1, ej2⟩ ⟨ek1, ek2⟩
    · exact (old j hjl _ (by omega) ej1 ej2 ek1 ek2).elim
    · exact (old k hkl _ (by omega) ek1 ek2 ej1 ej2).elim
    · have := h7 _ (by omega) _ (by omega) r ej1 ej2 ek1 ek2
      omega
  · rw [List.flatten_append, List.nodup_append]
    exact ⟨o8, h8, fun a ha b hb hab => h8' b hb (hab ▸ ha)⟩
  · rcases List.mem_append.mp hb with hb | hb
    · exact o9 b hb f hf
    · exact h9 b hb f hf

end Assemble

/-! ## The new block -/

section Popped

variable {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hG : BlocksGrow (g := g) w w')
include hS hO hG

/-- **The links popped are `v`'s group**: when `v`, open and arrived by `e` from `u`, finishes with
`entry u ≤ low v`, the stack down to `e` is the group of the new block top `v`; those links are
distinct, in no older block, and links of the graph. -/
theorem blocks_popped_group {v e i u : ℕ} {rest : List Frame}
    (hp : w.path = ⟨v, some e, i⟩ :: rest) (hup : w.up v = u) (hj : Joins g e u v)
    (hlt : w.entry u < w.entry v) (he : w'.entry = w.entry) (ha : w'.arrival = w.arrival)
    (hu : w'.up = w.up) (ht : w'.taken = w.taken)
    (hf : ∀ c, w'.finished c = true ↔ w.finished c = true ∨ c = v)
    (hlv : w'.low v = w.low v) (hle : w.entry u ≤ w.low v) :
    IsGroupOf (g := g) w' (popBlock e w.edges).1 v ∧ (popBlock e w.edges).1.Nodup ∧
      ∀ f ∈ (popBlock e w.edges).1, f ∉ w.blocks.flatten ∧ f < g.links.length := by
  obtain ⟨hvn, hve, hva, -, -, hvon⟩ := top_facts hS hp
  have hvf : w.finished v = false := by
    by_contra hc
    exact (hS.2.2.1 v hvn).2.1 ⟨hvon, by simpa using hc⟩
  have hOB := hS.2.2.2.2.1
  have hNd := hS.2.2.2.2.2.2.2.2.2.1
  have hCont := hS.2.2.2.2.2.2.2.2.2.2.1
  have hStk := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr := hStk.2 ⟨v, some e, i⟩ (by rw [hp]; exact List.mem_cons_self) e rfl
  dsimp only at hfr
  have hem : e ∈ w.edges := hfr.1
  have hde : deepEntry (g := g) w e = w.entry v := by
    unfold deepEntry
    rcases hj with h | h <;> rw [h] <;> simp only <;> omega
  have key : ∀ f ∈ w.edges,
      (w.edges.idxOf f ≤ w.edges.idxOf e ↔ w.entry v ≤ deepEntry (g := g) w f) := by
    intro f hf
    have hfl := List.idxOf_lt_length_iff.mpr hf
    have hgf := blocks_getD_idxOf hf
    rcases lt_trichotomy (w.edges.idxOf f) (w.edges.idxOf e) with h | h | h
    · have := (hfr.2 _ hfl).1 h
      rw [hgf] at this
      exact ⟨fun _ => this, fun _ => h.le⟩
    · have hfe : f = e := by rw [← hgf, h, blocks_getD_idxOf hem]
      subst hfe
      exact ⟨fun _ => hde.ge, fun _ => le_rfl⟩
    · have := (hfr.2 _ hfl).2 h
      rw [hgf] at this
      exact ⟨fun h' => absurd h' (by omega), fun h' => by omega⟩
  have hmem : ∀ f, f ∈ (popBlock e w.edges).1 ↔
      f ∈ w.edges ∧ w.entry v ≤ deepEntry (g := g) w f := by
    intro f
    rw [blocks_popBlock_eq, blocks_mem_take_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key f h1).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (key f h1).mpr h2⟩
  have habv : ∀ a y, Above w' a y ↔ Above w a y := blocks_above_congr ha hu
  have hanc := hG.2.2.2.2
  have hbt : ∀ c, c ≠ v → (BlockTop w' c ↔ BlockTop w c) := by
    intro c hcv
    by_cases hcf : w.finished c = true
    · exact blocks_blockTop_iff hS hO hG hcf
    · have : w'.finished c = false := by
        by_contra h
        rcases (hf c).mp (by simpa using h) with h | h
        · exact hcf h
        · exact hcv h
      exact ⟨fun h => absurd h.1 (by simp [this]), fun h => absurd h.1 hcf⟩
  have hbtv : BlockTop w' v :=
    ⟨(hf v).mpr (Or.inr rfl), by rw [ha, hva]; simp, by rw [hu, hup, he, hlv]; exact hle⟩
  refine ⟨⟨List.ne_nil_of_mem ((hmem e).mpr ⟨hem, hde.ge⟩), hbtv, fun f hfl => ?_⟩, ?_,
    fun f hf => ?_⟩
  · rw [hmem]
    constructor
    · rintro ⟨hfe, hle'⟩
      obtain ⟨htk, hnot⟩ := (hCont f hfl).mp hfe
      obtain ⟨⟨a, b⟩, hl, -⟩ := htk.1
      simp only [Option.mem_def] at hl
      obtain ⟨x, hx, hxe⟩ : ∃ x, (a = x ∨ b = x) ∧ w.entry x = max (w.entry a) (w.entry b) := by
        rcases le_total (w.entry a) (w.entry b) with h | h
        · exact ⟨b, Or.inr rfl, (max_eq_right h).symm⟩
        · exact ⟨a, Or.inl rfl, (max_eq_left h).symm⟩
      have hd : Deep (g := g) w f x := (deep_iff hl).mpr ⟨hx, hxe⟩
      have hdx : deepEntry (g := g) w f = w.entry x := by simp [deepEntry, hl, hxe]
      have hxe0 : w.entry x ≠ 0 := by omega
      have hxn := lt_n_of_entered hO hxe0
      have hvx : Above w v x := (anc_iff hS hO v x).mp (hOB v hvn hvon x hxn hxe0 (by omega))
      refine ⟨(blocks_taken_congr ht f).mpr htk, x, hxn, (blocks_deep_congr he f x).mpr hd,
        (blocks_headIs_iff hanc).mpr ⟨(habv v x).mpr hvx, hbtv, fun c' h1 _ h3 h4 => ?_⟩⟩
      have hbc := (hbt c' h3).mp h4
      obtain ⟨c'', hh⟩ := blocks_exists_head hS hO ((habv c' x).mp h1) hbc
      have hbc'' := ((headIs_iff hS hO).mp hh).2.1
      obtain ⟨k, hk, hgr⟩ := hBO.2.2.2.2.1 c'' (finished_lt hO hbc''.1) hbc''
      have : f ∈ w.blocks.getD k [] := (hgr.2.2 f hfl).mpr ⟨htk, x, hxn, hd, hh⟩
      exact hnot (List.mem_flatten.mpr ⟨_, blocks_getD_mem hk, this⟩)
    · rintro ⟨htk', x, -, hd', hh'⟩
      have htk := (blocks_taken_congr ht f).mp htk'
      have hd := (blocks_deep_congr he f x).mp hd'
      obtain ⟨hvx', -, hmin⟩ := (blocks_headIs_iff hanc).mp hh'
      have hvx := (habv v x).mp hvx'
      have hxe0 := entered_of_above hS hO hvx hve
      obtain ⟨-, -, -, hdx⟩ := hd
      refine ⟨(hCont f hfl).mpr ⟨htk, fun hfl' => ?_⟩, by
        rw [← hdx]; exact entry_le_of_above' hS hO hvx hve⟩
      obtain ⟨blk, hblk, hfb⟩ := List.mem_flatten.mp hfl'
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hblk
      have hbk : w.blocks.getD k [] = w.blocks[k] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      obtain ⟨c, -, hgr⟩ := hBO.2.2.1 k hk (by rw [hbk]; exact List.ne_nil_of_mem hfb)
      obtain ⟨-, x', -, hd2, hh2⟩ := (hgr.2.2 f hfl).mp (by rw [hbk]; exact hfb)
      obtain ⟨-, -, -, hdx2⟩ := hd2
      have hxx : x = x' := entry_inj hS hO hxe0 (hdx.trans hdx2.symm)
      subst hxx
      obtain ⟨hcx, hct, -⟩ := (headIs_iff hS hO).mp hh2
      rcases above_total hvx hcx with hvc | hcv
      · have hcv' : c ≠ v := fun h => by
          subst h
          have := hct.1
          rw [hvf] at this
          exact absurd this (by simp)
        exact hmin c ((habv c x).mpr hcx) ((habv v c).mpr hvc) hcv' ((hbt c hcv').mpr hct)
      · have := finished_of_above hS hO hcv hct.1 hve
        rw [hvf] at this
        exact absurd this (by simp)
  · rw [blocks_popBlock_eq]
    exact hNd.sublist (List.take_sublist _ _)
  · have h1 := ((hmem f).mp hf).1
    have hfl := hStk.1 f h1
    exact ⟨((hCont f hfl).mp h1).2, hfl⟩

end Popped

/-! ## One step keeps the blocks -/

section Step

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)

include hg hS hO in
/-- `BlocksOk` after a growing step that finds no block, where no new finished vertex is a block
top or a finished root with no children. -/
theorem blocks_blocksOk_same {w' : Walk} (hG : BlocksGrow (g := g) w w')
    (hb : w'.blocks = w.blocks) (hpl : w'.vertices = w.vertices)
    (hnew : ∀ c, w'.finished c = true → w.finished c = false →
      ¬ BlockTop w' c ∧ ¬ LoneRoot (g := g) w' c) : BlocksOk (g := g) w' :=
  blocks_blocksOk_of (B := []) (P := []) hg hS hO hG (by simp [hb]) (by simp [hpl]) rfl
    (by simp) (by simp) (by simp) (fun c _ hbt hcf => absurd hbt (hnew c hbt.1 hcf).1)
    (fun r _ hlr hrf => absurd hlr (hnew r hlr.1 hrf).2) (by simp) (by simp) (by simp)
    (by simp)

include hS in
omit hg in
theorem blocks_top_open {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}
    (hp : w.path = ⟨v, arr, i⟩ :: rest) : w.finished v = false := by
  obtain ⟨hvn, -, -, -, -, hvon⟩ := top_facts hS hp
  by_contra hc
  exact (hS.2.2.1 v hvn).2.1 ⟨hvon, by simpa using hc⟩

include hg hS hO in
/-- **One step keeps the blocks**: every block emitted with links is the group of a block top
and lists its vertices, every block top has its group emitted, every block without links holds a
finished root with no children, one for each, and no link is in two blocks. -/
theorem blocksOk_step (_hT : OpenTaken (g := g) w) : BlocksOk (g := g) (step g w) := by
  have hG := blocks_grow_step hS hO
  have same : ∀ w', BlocksGrow (g := g) w w' → w'.blocks = w.blocks →
      w'.vertices = w.vertices → w'.finished = w.finished → BlocksOk (g := g) w' :=
    fun w' hG' hb hpl hf => blocks_blocksOk_same hg hS hO hG' hb hpl fun c hc hcf => by
      rw [hf, hcf] at hc
      exact absurd hc (by simp)
  rcases blocks_step_moves (g := g) w with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, hor, h⟩ <;> rw [h] at hG ⊢
  · exact same _ hG rfl rfl rfl
  · exact same _ hG rfl rfl rfl
  · exact same _ hG rfl rfl rfl
  · exact same _ hG rfl rfl rfl
  · exact same _ hG rfl rfl rfl
  · exact same _ hG rfl rfl rfl
  · obtain ⟨hne, hup, hva, -, hj, hlt, -, -, hvn, -, -⟩ := blocks_under_frame hS hp
    have hvf := blocks_top_open hS hp
    obtain ⟨fe, fa, fu, ff, ft, -, -⟩ :=
      blocks_fu_fields (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty
    obtain ⟨fb, fp, -, -, -⟩ :=
      blocks_fu_found (g := g) (pop w v (⟨u, a, j⟩ :: above)) e above.isEmpty hne
    have hlv : (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).low v =
        w.low v := by
      rw [blocks_fu_low, Function.update_of_ne (Ne.symm hne)]
      rfl
    have hf : ∀ c, (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).finished c
        = true ↔ w.finished c = true ∨ c = v := by
      intro c
      rw [ff]
      by_cases hcv : c = v <;> simp [pop, hcv]
    have hnewv : ∀ c, (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).finished c = true → w.finished c = false → c = v := by
      intro c hc hcf
      rcases (hf c).mp hc with h | h
      · rw [hcf] at h
        exact absurd h (by simp)
      · exact h
    have hlone : ∀ r, ¬ LoneRoot (g := g) (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty) r ∨ r ≠ v := by
      intro r
      by_cases hrv : r = v
      · subst hrv
        refine Or.inl fun hl => ?_
        have := hl.2.1
        rw [fa] at this
        simp [pop, hva] at this
      · exact Or.inr hrv
    by_cases hle : w.entry u ≤ w.low v
    · obtain ⟨hgrp, hnd, hdis⟩ := blocks_popped_group hS hO hG hp hup hj hlt fe fa fu ft hf hlv
        hle
      refine blocks_blocksOk_of (B := [(popBlock e w.edges).1])
        (P := [verticesOf g (popBlock e w.edges).1]) hg hS hO hG (fb.trans (ite_eq_left hle))
        (fp.trans (ite_eq_left hle)) rfl ?_ ?_ ?_ ?_ ?_ ?_ (by simpa using hnd) ?_ ?_
      · intro k hk _
        obtain rfl : k = 0 := by simpa using hk
        rfl
      · intro k hk _
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨v, hvn, hgrp⟩
      · intro k hk hemp
        obtain rfl : k = 0 := by simpa using hk
        exact absurd hemp hgrp.1
      · intro c _ hbt hcf
        obtain rfl := hnewv c hbt.1 hcf
        exact ⟨0, by simp, hgrp⟩
      · intro r _ hlr hrf
        obtain rfl := hnewv r hlr.1 hrf
        exact absurd hlr ((hlone r).resolve_right (by simp))
      · intro j' hj' _ _ _ hemp
        obtain rfl : j' = 0 := by simpa using hj'
        exact absurd hemp hgrp.1
      · simpa using fun f hf => (hdis f hf).1
      · simpa using fun f hf => (hdis f hf).2
    · refine blocks_blocksOk_same hg hS hO hG (fb.trans (ite_eq_right hle))
        (fp.trans (ite_eq_right hle)) fun c hc hcf => ?_
      obtain rfl := hnewv c hc hcf
      refine ⟨fun hbt => hle ?_, (hlone c).resolve_right (by simp)⟩
      have := hbt.2.2
      rw [hlv, fu, fe] at this
      simpa [pop, hup] using this
  · obtain ⟨rfl, rfl⟩ := blocks_root_frame hS hp hor
    obtain ⟨hvn, -, hva, -, -, -⟩ := top_facts hS hp
    have hvf := blocks_top_open hS hp
    obtain ⟨fe, fa, fu, ff, -, -, -⟩ := blocks_fr_fields (pop w v []) v
    obtain ⟨fb, fp, -⟩ := blocks_fr_found (pop w v []) v
    have hch : w.children = numChildren (g := g) w v :=
      hS.2.2.2.2.2.2.2.1 ⟨v, none, i⟩ (by rw [hp]; rfl)
    have hnum : numChildren (g := g) (finishRoot (pop w v []) v) v = numChildren (g := g) w v := by
      simp only [numChildren, Child, fe, fa, fu]
      rfl
    have hnewv : ∀ c, (finishRoot (pop w v []) v).finished c = true → w.finished c = false →
        c = v := by
      intro c hc hcf
      rw [ff] at hc
      by_contra hcv
      simp [pop, hcv, hcf] at hc
    have hbtv : ¬ BlockTop (finishRoot (pop w v []) v) v := fun hbt => by
      have := hbt.2.1
      rw [fa] at this
      exact this hva
    have hlr : LoneRoot (g := g) (finishRoot (pop w v []) v) v ↔ w.children = 0 := by
      unfold LoneRoot
      rw [hnum, ← hch, ff, fa]
      simp [pop, hva]
    by_cases hc0 : w.children = 0
    · refine blocks_blocksOk_of (B := [[]]) (P := [[v]]) hg hS hO hG
        (fb.trans (ite_eq_left hc0)) (fp.trans (ite_eq_left hc0)) rfl ?_ ?_ ?_ ?_ ?_ ?_
        (by simp) (by simp) (by simp)
      · intro k hk hne
        obtain rfl : k = 0 := by simpa using hk
        exact absurd rfl hne
      · intro k hk hne
        obtain rfl : k = 0 := by simpa using hk
        exact absurd rfl hne
      · intro k hk _
        obtain rfl : k = 0 := by simpa using hk
        exact ⟨v, hvn, rfl, hlr.mpr hc0, hvf⟩
      · intro c _ hbt hcf
        obtain rfl := hnewv c hbt.1 hcf
        exact absurd hbt hbtv
      · intro r _ hlr' hrf
        obtain rfl := hnewv r hlr'.1 hrf
        exact ⟨0, by simp, rfl, rfl⟩
      · intro j' hj' k hk _ _ _ _ _
        obtain rfl : j' = 0 := by simpa using hj'
        obtain rfl : k = 0 := by simpa using hk
        rfl
    · refine blocks_blocksOk_same hg hS hO hG (fb.trans (ite_eq_right hc0))
        (fp.trans (ite_eq_right hc0)) fun c hc hcf => ?_
      obtain rfl := hnewv c hc hcf
      exact ⟨hbtv, fun h => hc0 (hlr.mp h)⟩

end Step

/-! ## One step keeps the bridges -/

section Bridges

variable {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

/-- Two vertices arrived by one link are one vertex. -/
theorem blocks_arrival_inj {c v e : ℕ} (hc : w.arrival c = some e) (hv : w.arrival v = some e) :
    c = v := by
  obtain ⟨-, -, -, -, hltc, hjc⟩ := hangs hS hO c (by simp [hc])
  obtain ⟨-, -, -, -, hltv, hjv⟩ := hangs hS hO v (by simp [hv])
  rcases (hjc e (by simp [hc])).ends (hjv e (by simp [hv])) with ⟨-, h⟩ | ⟨h1, h2⟩
  · exact h.symm
  · rw [h1] at hltv
    rw [← h2] at hltc
    omega

/-- `BridgesOk` after a growing step that appends bridges `E`, exactly the arrival links of the
newly finished vertices that cannot climb back to the vertex they hang from. -/
theorem blocks_bridgesOk_of (hG : BlocksGrow (g := g) w w') {E : List ℕ}
    (hb : w'.bridges = w.bridges ++ E) (hE : E.Nodup) (hdisj : ∀ f ∈ E, f ∉ w.bridges)
    (hlt : ∀ f ∈ E, f < g.links.length)
    (hnew : ∀ f < g.links.length, (∃ c < g.n, w'.finished c = true ∧ w.finished c = false ∧
      w'.arrival c = some f ∧ w'.entry (w'.up c) < w'.low c) ↔ f ∈ E) :
    BridgesOk (g := g) w' := by
  obtain ⟨o1, o2, o3⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ c f, w.finished c = true → ((w'.arrival c = some f ∧
      w'.entry (w'.up c) < w'.low c) ↔ (w.arrival c = some f ∧ w.entry (w.up c) < w.low c)) := by
    intro c f hcf
    obtain ⟨-, ha, hu⟩ := hG.1 c (entered_of_finished hS hO hcf)
    rw [ha, hu, (hG.2.1 c hcf).2]
    constructor
    · rintro ⟨h1, h2⟩
      rw [(hG.1 _ (hangs hS hO c (by simp [h1])).2.2.2.1).1] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [(hG.1 _ (hangs hS hO c (by simp [h1])).2.2.2.1).1]
      exact ⟨h1, h2⟩
  unfold BridgesOk
  rw [hb, List.nodup_append]
  refine ⟨⟨o1, hE, fun a ha b hb hab => hdisj b hb (hab ▸ ha)⟩, fun f hf => ?_,
    fun f hf => ?_⟩
  · rcases List.mem_append.mp hf with h | h
    · exact o2 f h
    · exact hlt f h
  · rw [List.mem_append, o3 f hf, ← hnew f hf]
    constructor
    · rintro (⟨c, hc, hcf, h⟩ | ⟨c, hc, h1, h2, h3⟩)
      · exact ⟨c, hc, (hG.2.1 c hcf).1, (key c f hcf).mpr h⟩
      · exact ⟨c, hc, h1, h3⟩
    · rintro ⟨c, hc, h1, h3⟩
      by_cases hcf : w.finished c = true
      · exact Or.inl ⟨c, hc, hcf, (key c f hcf).mp h3⟩
      · exact Or.inr ⟨c, hc, h1, by simpa using hcf, h3⟩

end Bridges

section StepBridges

variable {w : Walk}

/-- **One step keeps the bridges**: the bridges found are, once each, the arrival links of the
finished vertices whose subtree cannot climb back to the vertex they hang from. -/
theorem bridgesOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (_hT : OpenTaken (g := g) w) : BridgesOk (g := g) (step g w) := by
  have hG := blocks_grow_step hS hO
  have same : ∀ w', BlocksGrow (g := g) w w' → w'.bridges = w.bridges →
      w'.finished = w.finished → BridgesOk (g := g) w' := by
    intro w' hG' hb hf
    refine blocks_bridgesOk_of (E := []) hS hO hG' (by simp [hb]) List.nodup_nil (by simp)
      (by simp) fun f _ => ?_
    simp only [List.not_mem_nil, iff_false, not_exists, not_and]
    intro c _ hc hcf
    rw [hf, hcf] at hc
    exact absurd hc (by simp)
  rcases blocks_step_moves (g := g) w with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, hor, h⟩ <;> rw [h] at hG ⊢
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · obtain ⟨hne, hup, hva, -, hj, -, -, -, hvn, -, -⟩ := blocks_under_frame hS hp
    have hvf := blocks_top_open hS hp
    obtain ⟨fe, fa, fu, ff, -, -, -⟩ :=
      blocks_fu_fields (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty
    obtain ⟨-, -, -, fb, -⟩ :=
      blocks_fu_found (g := g) (pop w v (⟨u, a, j⟩ :: above)) e above.isEmpty hne
    have hlv : (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).low v =
        w.low v := by
      rw [blocks_fu_low, Function.update_of_ne (Ne.symm hne)]
      rfl
    have hnewv : ∀ c, (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).finished c = true → w.finished c = false → c = v := by
      intro c hc hcf
      rw [ff] at hc
      by_contra hcv
      simp [pop, hcv, hcf] at hc
    have hvv : (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).finished v =
        true := by
      rw [ff]
      simp [pop]
    have hel := joins_lt hj
    have hcond : ∀ f, ((finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).arrival v = some f ∧ (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).entry ((finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).up v) < (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e
        above.isEmpty).low v) ↔ f = e ∧ w.entry u < w.low v := by
      intro f
      rw [hlv, fa, fu, fe]
      change w.arrival v = some f ∧ w.entry (w.up v) < w.low v ↔ _
      rw [hva, hup, Option.some.injEq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
    by_cases hlt : w.entry u < w.low v
    · refine blocks_bridgesOk_of (E := [e]) hS hO hG (fb.trans (ite_eq_left hlt)) (by simp)
        (fun f hf => ?_) (by simpa using hel) fun f _ => ?_
      · rw [List.mem_singleton] at hf
        subst hf
        intro hm
        obtain ⟨c, -, hcf, hca, -⟩ := (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2 f hel).mp hm
        rw [blocks_arrival_inj hS hO hca hva, hvf] at hcf
        exact absurd hcf (by simp)
      · rw [List.mem_singleton]
        constructor
        · rintro ⟨c, -, hc, hcf, h⟩
          obtain rfl := hnewv c hc hcf
          exact ((hcond f).mp h).1
        · rintro rfl
          exact ⟨v, hvn, hvv, hvf, (hcond f).mpr ⟨rfl, hlt⟩⟩
    · refine blocks_bridgesOk_of (E := []) hS hO hG
        (fb.trans ((ite_eq_right hlt).trans (List.append_nil _).symm)) List.nodup_nil (by simp)
        (by simp) fun f _ => ?_
      simp only [List.not_mem_nil, iff_false, not_exists, not_and]
      intro c _ hc hcf h1 h2
      obtain rfl := hnewv c hc hcf
      exact hlt ((hcond f).mp ⟨h1, h2⟩).2
  · obtain ⟨rfl, rfl⟩ := blocks_root_frame hS hp hor
    obtain ⟨-, -, hva, -, -, -⟩ := top_facts hS hp
    obtain ⟨-, fa, -, ff, -, -, fb⟩ := blocks_fr_fields (pop w v []) v
    refine blocks_bridgesOk_of (E := []) hS hO hG (by rw [fb, List.append_nil]; rfl)
      List.nodup_nil (by simp) (by simp) fun f _ => ?_
    simp only [List.not_mem_nil, iff_false, not_exists, not_and]
    intro c _ hc hcf h1
    rw [ff] at hc
    by_cases hcv : c = v
    · subst hcv
      rw [fa] at h1
      change w.arrival c = some f at h1
      rw [hva] at h1
      exact absurd h1 (by simp)
    · simp [pop, hcv, hcf] at hc

end StepBridges

/-! ## One step keeps the cut flags -/

/-- The rule `CutOk` reads at `x`: a vertex other than a root with a finished child that cannot
climb above it, or a finished root with two or more children. -/
def BlocksCutRule (w : Walk) (x : ℕ) : Prop :=
  (w.arrival x ≠ none ∧ ∃ c < g.n, Child w x c ∧ w.finished c ∧ w.entry x ≤ w.low c) ∨
    (w.arrival x = none ∧ w.finished x ∧ 2 ≤ numChildren (g := g) w x)

section Cut

variable {w w' : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hG : BlocksGrow (g := g) w w')
include hS hO hG

/-- With no vertex newly finished, the rule reads the same in a growing walk. -/
theorem blocks_rule_same (hfin : w'.finished = w.finished) {x : ℕ} (hx : x < g.n) :
    BlocksCutRule (g := g) w' x ↔ BlocksCutRule (g := g) w x := by
  have hchild : ∀ p c, w.entry c ≠ 0 → (Child w' p c ↔ Child w p c) := fun p c hce => by
    unfold Child
    obtain ⟨he, ha, hu⟩ := hG.1 c hce
    rw [he, ha, hu]
  unfold BlocksCutRule
  rw [hfin]
  by_cases hxe : w.entry x = 0
  · have hxa := ((hS.2.2.1 x hx).2.2.2 hxe).2
    have hxf : w.finished x = false := by
      by_contra h
      exact ((hS.2.2.1 x hx).1.mpr (Or.inr (by simpa using h))) hxe
    constructor
    · rintro (⟨-, c, -, hch, hcf, -⟩ | ⟨-, hf, -⟩)
      · obtain ⟨-, hca, hcu⟩ := (hchild x c (entered_of_finished hS hO hcf)).mp hch
        have := (hangs hS hO c hca).2.2.2.1
        rw [hcu] at this
        exact absurd hxe this
      · rw [hxf] at hf
        exact absurd hf (by simp)
    · rintro (⟨h, -⟩ | ⟨-, hf, -⟩)
      · exact absurd hxa h
      · rw [hxf] at hf
        exact absurd hf (by simp)
  · obtain ⟨he, ha, -⟩ := hG.1 x hxe
    rw [ha, he]
    refine or_congr (and_congr_right fun _ => ?_)
      (and_congr_right fun _ => and_congr_right fun hxf => ?_)
    · constructor
      · rintro ⟨c, hc, hch, hcf, hle⟩
        exact ⟨c, hc, (hchild x c (entered_of_finished hS hO hcf)).mp hch, hcf,
          by rwa [(hG.2.1 c hcf).2] at hle⟩
      · rintro ⟨c, hc, hch, hcf, hle⟩
        exact ⟨c, hc, (hchild x c (entered_of_finished hS hO hcf)).mpr hch, hcf,
          by rwa [(hG.2.1 c hcf).2]⟩
    · rw [blocks_numChildren_eq hG hxf]

omit hS hO in
/-- With the tree kept and `v` newly finished, the rule gains `v` as a finished child and `v` as
a finished root. -/
theorem blocks_rule_finish {v : ℕ} (hvn : v < g.n) (he : w'.entry = w.entry)
    (ha : w'.arrival = w.arrival) (hu : w'.up = w.up)
    (hf : ∀ c, w'.finished c = true ↔ w.finished c = true ∨ c = v) (x : ℕ) :
    BlocksCutRule (g := g) w' x ↔ BlocksCutRule (g := g) w x ∨
      (w.arrival x ≠ none ∧ Child w x v ∧ w.entry x ≤ w'.low v) ∨
      (w.arrival x = none ∧ x = v ∧ 2 ≤ numChildren (g := g) w x) := by
  have hch : ∀ p c, Child w' p c ↔ Child w p c := by
    intro p c
    unfold Child
    rw [he, ha, hu]
  have hnum : ∀ p, numChildren (g := g) w' p = numChildren (g := g) w p := by
    intro p
    simp only [numChildren, Child, he, ha, hu]
  unfold BlocksCutRule
  rw [ha, hnum]
  constructor
  · rintro (⟨hxa, c, hc, hchc, hcf, hle⟩ | ⟨hxa, hxf, h2⟩)
    · rw [hch] at hchc
      rcases (hf c).mp hcf with hcf | rfl
      · rw [he, (hG.2.1 c hcf).2] at hle
        exact Or.inl (Or.inl ⟨hxa, c, hc, hchc, hcf, hle⟩)
      · rw [he] at hle
        exact Or.inr (Or.inl ⟨hxa, hchc, hle⟩)
    · rcases (hf x).mp hxf with hxf | rfl
      · exact Or.inl (Or.inr ⟨hxa, hxf, h2⟩)
      · exact Or.inr (Or.inr ⟨hxa, rfl, h2⟩)
  · rintro ((⟨hxa, c, hc, hchc, hcf, hle⟩ | ⟨hxa, hxf, h2⟩) | ⟨hxa, hchv, hle⟩ | ⟨hxa, rfl, h2⟩)
    · refine Or.inl ⟨hxa, c, hc, (hch x c).mpr hchc, (hf c).mpr (Or.inl hcf), ?_⟩
      rwa [he, (hG.2.1 c hcf).2]
    · exact Or.inr ⟨hxa, (hf x).mpr (Or.inl hxf), h2⟩
    · refine Or.inl ⟨hxa, v, hvn, (hch x v).mpr hchv, (hf v).mpr (Or.inr rfl), ?_⟩
      rwa [he]
    · exact Or.inr ⟨hxa, (hf _).mpr (Or.inr rfl), h2⟩

end Cut

section StepCut

variable {w : Walk}

/-- **One step keeps the cut flags**: a vertex is flagged exactly when it is not a root and has a
finished child that cannot climb above it, or it is a finished root with two or more children. -/
theorem cutOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (_hT : OpenTaken (g := g) w) : CutOk (g := g) (step g w) := by
  have hG := blocks_grow_step hS hO
  have hCut : ∀ x < g.n, (w.cut x = true ↔ BlocksCutRule (g := g) w x) :=
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have same : ∀ w', BlocksGrow (g := g) w w' → w'.cut = w.cut →
      w'.finished = w.finished → CutOk (g := g) w' := by
    intro w' hG' hc hf x hx
    rw [hc]
    exact (hCut x hx).trans (blocks_rule_same hS hO hG' hf hx).symm
  rcases blocks_step_moves (g := g) w with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, hor, h⟩ <;> rw [h] at hG ⊢
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · exact same _ hG rfl rfl
  · obtain ⟨hne, hup, hva, hua, -, -, -, -, hvn, -, hiso⟩ := blocks_under_frame hS hp
    have hve := (top_facts hS hp).2.1
    obtain ⟨fe, fa, fu, ff, -, -, -⟩ :=
      blocks_fu_fields (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty
    obtain ⟨-, -, -, -, fc⟩ :=
      blocks_fu_found (g := g) (pop w v (⟨u, a, j⟩ :: above)) e above.isEmpty hne
    have hlv : (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).low v =
        w.low v := by
      rw [blocks_fu_low, Function.update_of_ne (Ne.symm hne)]
      rfl
    have hf : ∀ c, (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).finished c
        = true ↔ w.finished c = true ∨ c = v := by
      intro c
      rw [ff]
      by_cases hcv : c = v <;> simp [pop, hcv]
    have key := blocks_rule_finish hG hvn fe fa fu hf
    have hchv : ∀ y, Child w y v ↔ y = u := by
      intro y
      unfold Child
      rw [hva, hup]
      exact ⟨fun h => h.2.2.symm, fun h => ⟨hve, by simp, h.symm⟩⟩
    intro y hy
    change _ ↔ BlocksCutRule (g := g) _ y
    rw [key y, hchv, hlv]
    by_cases hyu : y = u
    · subst hyu
      have hyv : y ≠ v := hne
      rw [fc]
      by_cases hc : w.entry y ≤ w.low v ∧ a ≠ none
      · have hc' : (pop w v (⟨y, a, j⟩ :: above)).entry y ≤
            (pop w v (⟨y, a, j⟩ :: above)).low v ∧ above.isEmpty = false := by
          refine ⟨hc.1, ?_⟩
          by_contra hb
          exact hc.2 (hiso.mp (by simpa using hb))
        rw [ite_eq_left hc']
        simp only [Function.update_self, true_iff]
        exact Or.inr (Or.inl ⟨by rw [hua]; exact hc.2, trivial, hc.1⟩)
      · have hc' : ¬ ((pop w v (⟨y, a, j⟩ :: above)).entry y ≤
            (pop w v (⟨y, a, j⟩ :: above)).low v ∧ above.isEmpty = false) := by
          rintro ⟨h1, h2⟩
          refine hc ⟨h1, fun ha' => ?_⟩
          rw [hiso.mpr ha'] at h2
          exact absurd h2 (by simp)
        rw [ite_eq_right hc']
        refine (hCut y hy).trans ⟨Or.inl, ?_⟩
        rintro (h | ⟨hya, -, hle⟩ | ⟨-, h, -⟩)
        · exact h
        · exact absurd ⟨hle, by rw [← hua]; exact hya⟩ hc
        · exact absurd h hyv
    · rw [cut_finishUnder _ _ _ _ _ _ hyu]
      refine (hCut y hy).trans ⟨Or.inl, ?_⟩
      rintro (h | ⟨-, h, -⟩ | ⟨hya, rfl, -⟩)
      · exact h
      · exact absurd h hyu
      · rw [hva] at hya
        exact absurd hya (by simp)
  · obtain ⟨rfl, rfl⟩ := blocks_root_frame hS hp hor
    obtain ⟨hvn, hve, hva, -, -, -⟩ := top_facts hS hp
    have hvf := blocks_top_open hS hp
    obtain ⟨fe, fa, fu, ff, -, -, -⟩ := blocks_fr_fields (pop w v []) v
    obtain ⟨-, -, fc⟩ := blocks_fr_found (pop w v []) v
    have hchn : w.children = numChildren (g := g) w v :=
      hS.2.2.2.2.2.2.2.1 ⟨v, none, i⟩ (by rw [hp]; rfl)
    have hf : ∀ c, (finishRoot (pop w v []) v).finished c = true ↔
        w.finished c = true ∨ c = v := by
      intro c
      rw [ff]
      by_cases hcv : c = v <;> simp [pop, hcv]
    have key := blocks_rule_finish hG hvn fe fa fu hf
    have hchv : ∀ y, ¬ Child w y v := fun y h => h.2.1 hva
    intro y hy
    change _ ↔ BlocksCutRule (g := g) _ y
    rw [key y]
    by_cases hyv : y = v
    · subst hyv
      have hcv : w.cut y = false := by
        by_contra hc
        rcases (hCut y hy).mp (by simpa using hc) with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact h hva
        · rw [hvf] at h
          exact absurd h (by simp)
      rw [fc]
      change (if 2 ≤ w.children then Function.update w.cut y true else w.cut) y = true ↔ _
      rw [hchn]
      by_cases h2 : 2 ≤ numChildren (g := g) w y
      · rw [ite_eq_left h2]
        simp only [Function.update_self, true_iff]
        exact Or.inr (Or.inr ⟨hva, trivial, h2⟩)
      · rw [ite_eq_right h2, hcv]
        simp only [Bool.false_eq_true, false_iff]
        rintro (h | ⟨-, h, -⟩ | ⟨-, -, h⟩)
        · exact absurd ((hCut y hy).mpr h) (by simp [hcv])
        · exact hchv y h
        · exact h2 h
    · rw [cut_finishRoot _ _ _ hyv]
      refine (hCut y hy).trans ⟨Or.inl, ?_⟩
      rintro (h | ⟨-, h, -⟩ | ⟨-, h, -⟩)
      · exact h
      · exact absurd h (hchv y)
      · exact absurd h hyv

end StepCut

end Walk

end AlgoDesign.Graphs.Blocks
