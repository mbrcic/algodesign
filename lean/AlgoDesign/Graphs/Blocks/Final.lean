/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Groups
public import AlgoDesign.Graphs.Blocks.Pieces

/-!
# Bridges, cut vertices and blocks: what the finished walk reports

Once the walk has finished, every vertex has finished, and the deletions read off its tree. A link
leaving the subtree of a finished vertex `c` is `c`'s own arrival link, or reaches a vertex above
`c` no earlier than `c`'s climb-back number (`leave_sub`). So `c`'s arrival link is a bridge
exactly when the subtree cannot climb back to the vertex it hangs from; a vertex separates two
others exactly when a child's subtree cannot climb above it, or it is a root with two children;
and the blocks reported are the block tops' groups.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

section Shape

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

/-- No two vertices arrive by one link. -/
theorem arrival_inj {t t' f : ℕ} (h : w.arrival t = some f) (h' : w.arrival t' = some f) :
    t = t' := by
  obtain ⟨-, -, -, -, hlt, hj⟩ := hangs hS hO t (by simp [h])
  obtain ⟨-, -, -, -, hlt', hj'⟩ := hangs hS hO t' (by simp [h'])
  rcases Joins.ends (hj f (by simp [h])) (hj' f (by simp [h'])) with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2.symm
  · have := congrArg w.entry h1
    have := congrArg w.entry h2
    omega

include hg in
/-- **What leaves a finished subtree**: a link from below a finished vertex `c` (not a root) to a
vertex not below it is `c`'s arrival link, or reaches a vertex above the one `c` hangs from, entered
no earlier than `c`'s climb-back number. -/
theorem leave_sub {c i a b : ℕ} (hcf : w.finished c = true) (hca : w.arrival c ≠ none)
    (hl : Joins g i a b) (ha : Above w c a) (hb : ¬ Above w c b) :
    (a = c ∧ b = w.up c ∧ w.arrival c = some i) ∨ (Above w b (w.up c) ∧ w.low c ≤ w.entry b) := by
  have hce := entered_of_finished hS hO hcf
  have hae := entered_of_above hS hO ha hce
  have han := lt_n_of_entered hO hae
  have haf := finished_of_above hS hO ha hcf hae
  have hba : b ≠ a := fun h => hb (h ▸ ha)
  obtain ⟨hbe, hab | hab⟩ := link_of_finished hg hS hO han haf hl hba
  · by_cases hfa : w.arrival a = some i
    · obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO a (by simp [hfa])
      rcases Joins.ends (hj i (by simp [hfa])) hl with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd h2 hba
      · have hac : a = c := by
          by_contra hne
          rcases above_iff.mp ha with h' | ⟨-, h'⟩
          · exact hne h'.symm
          · exact hb (h2 ▸ h')
        subst hac
        exact Or.inl ⟨rfl, h2, hfa⟩
    · have hle := low_le hg hS hO hcf ha hl hfa
      rcases above_total hab ha with h' | h'
      · have hbc : b ≠ c := fun h => hb (h ▸ Above.refl w c)
        rcases above_iff.mp h' with h'' | ⟨-, h''⟩
        · exact absurd h'' hbc
        · exact Or.inr ⟨h'', hle⟩
      · exact absurd h' hb
  · exact absurd (ha.trans hab) hb

/-- A graph holding every tree link from `a` down to `x` connects them. -/
theorem connected_of_above {h : Graph} {a x : ℕ} (hax : Above w a x)
    (hstep : ∀ t, Above w a t → Above w t x → t ≠ a → h.Link (w.up t) t) :
    h.Connected a x := by
  induction hax with
  | refl => exact ReflTransGen.refl
  | @tail b c hab hbc ih =>
    obtain ⟨hc, rfl⟩ := hbc
    have hca : c ≠ a := by
      intro h
      subst h
      have h1 := above_antisymm hS hO hab (Above.up hc)
      have h2 := (hangs hS hO c hc).2.2.2.2.1
      rw [← h1] at h2
      omega
    refine (ih fun t h1 h2 h3 => hstep t h1 (h2.trans (Above.up hc)) h3).tail ?_
    exact hstep c (hab.trans (Above.up hc)) (Above.refl w c) hca

/-- A tree link, as a link of the graph. -/
theorem link_up {t : ℕ} (ht : w.arrival t ≠ none) : g.Link (w.up t) t := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp ht
  obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO t ht
  rcases hj e (by simp [he]) with h | h
  · exact Or.inl (List.mem_of_getElem? h)
  · exact Or.inr (List.mem_of_getElem? h)

/-- Every entered vertex hangs, by tree links, under a root. -/
theorem exists_root : ∀ k x, w.entry x ≤ k → w.entry x ≠ 0 →
    ∃ r, Above w r x ∧ w.arrival r = none ∧ w.entry r ≠ 0
  | 0, x, hk, hx => absurd (by omega) hx
  | k + 1, x, hk, hx => by
    by_cases hxa : w.arrival x = none
    · exact ⟨x, Above.refl w x, hxa, hx⟩
    · obtain ⟨-, -, -, hue, hlt, -⟩ := hangs hS hO x hxa
      obtain ⟨r, hr, hra, hre⟩ := exists_root k (w.up x) (by omega) hue
      exact ⟨r, hr.trans (Above.up hxa), hra, hre⟩

end Shape

/-! ## The finished walk -/

section Done

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
  (hD : Done (g := g) w)
include hS hO hD

omit hO in
theorem done_finished {x : ℕ} (hx : x < g.n) : w.entry x ≠ 0 ∧ w.finished x = true := by
  obtain ⟨-, hp, -⟩ := hS.2.2.2.2.2.2.1
  have h1 := (hp hD.1 x hx).1 (by rw [hD.2]; exact hx)
  exact ⟨h1, (hp hD.1 x hx).2 h1⟩

include hg in
/-- Two vertices of one piece hang under one root. -/
theorem above_of_connected {r x y : ℕ} (hr : w.arrival r = none) (hrx : Above w r x)
    (hxy : g.Connected x y) : Above w r y := by
  refine mem_of_connected_closed (S := Above w r) (fun z z' hl hz => ?_) hxy hrx
  by_cases hzz : z' = z
  · exact hzz ▸ hz
  have hl' : ∃ i, Joins g i z z' := by
    rcases hl with h | h
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
      exact ⟨i, Or.inl hi⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
      exact ⟨i, Or.inr hi⟩
  obtain ⟨i, hi⟩ := hl'
  have hzn : z < g.n := by
    rcases hi with h | h
    · exact (hg _ (List.mem_of_getElem? h)).1
    · exact (hg _ (List.mem_of_getElem? h)).2
  obtain ⟨-, h1 | h1⟩ := link_of_finished hg hS hO hzn (done_finished hS hD hzn).2 hi hzz
  · rcases above_total h1 hz with h2 | h2
    · exact (above_root hr h2) ▸ Above.refl w r
    · exact h2
  · exact hz.trans h1

include hg in
/-- **A bridge, read off the tree**: link `f` is a bridge exactly when it is the arrival link of a
vertex whose subtree cannot climb back to the vertex it hangs from. -/
theorem isBridge_iff_tree {f : ℕ} (hf : f < g.links.length) :
    IsBridge g f ↔ ∃ c < g.n, w.finished c ∧ w.arrival c = some f ∧
      w.entry (w.up c) < w.low c := by
  obtain ⟨⟨a, b⟩, hab⟩ : ∃ l, g.links[f]? = some l :=
    ⟨_, List.getElem?_eq_getElem hf⟩
  rw [isBridge_iff hg hab]
  have han : a < g.n := (hg _ (List.mem_of_getElem? hab)).1
  have hbn : b < g.n := (hg _ (List.mem_of_getElem? hab)).2
  constructor
  · intro hcon
    have hne : a ≠ b := fun h => hcon (h ▸ ReflTransGen.refl)
    -- the deeper end and the other
    obtain ⟨x, y, hxy, hxe, hye, hyx, hlt⟩ : ∃ x y, Joins g f x y ∧ w.entry x ≠ 0 ∧
        w.entry y ≠ 0 ∧ y ≠ x ∧ w.entry y < w.entry x := by
      have ha := (done_finished hS hD han).1
      have hb := (done_finished hS hD hbn).1
      rcases lt_or_gt_of_ne (fun h => hne (entry_inj hS hO ha h)) with h | h
      · exact ⟨b, a, Or.inr hab, hb, ha, hne, h⟩
      · exact ⟨a, b, Or.inl hab, ha, hb, Ne.symm hne, h⟩
    have hxn := lt_n_of_entered hO hxe
    have hxf := (done_finished hS hD hxn).2
    obtain ⟨-, hyx' | hxy'⟩ := link_of_finished hg hS hO hxn hxf hxy hyx
    swap
    · have := entry_le_of_above' hS hO hxy' hxe
      omega
    have hconn : ∀ h : Graph, (∀ u v, h.Connected u v → (deleteLink g f).Connected u v) →
        h.Connected y x → False := by
      intro h hh hc
      apply hcon
      have := hh _ _ hc
      rcases hxy with h' | h'
      · rw [hab] at h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact connected_symm this
      · rw [hab] at h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact this
    by_cases hfx : w.arrival x = some f
    swap
    · exfalso
      refine hconn (deleteLink g f) (fun _ _ h => h) (connected_of_above hS hO hyx' ?_)
      intro t h1 h2 h3
      have hta : w.arrival t ≠ none := (above_iff.mp h1).resolve_left (Ne.symm h3) |>.1
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hta
      have hef : e ≠ f := fun h => not_arrival_between hS hO hxy hfx t h1 h2 h3 (h ▸ he)
      obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO t hta
      exact link_deleteLink.mpr ⟨e, hef, hj e (by simp [he])⟩
    refine ⟨x, hxn, hxf, hfx, ?_⟩
    by_contra hle
    push Not at hle
    have hxa : w.arrival x ≠ none := by simp [hfx]
    obtain ⟨-, -, hun, hue, hult, hjx⟩ := hangs hS hO x hxa
    have hlow : climb (g := g) w x < w.entry (w.up x) + 1 := by
      rw [← shape_low_eq hS hxn hxe]
      omega
    rw [climb_lt_iff] at hlow
    rcases hlow with h | ⟨z, hzn, hex, ⟨y', h'⟩, hs, hzh, hy'⟩
    · omega
    simp only at hzh hy'
    have hxz := above_of_explored hS hO hex
    have hze := entered_of_above hS hO hxz hxe
    have hzf := (done_finished hS hD hzn).2
    have hj : Joins g h' z y' := joins_of_adj_mem (List.mem_of_mem_take hs)
    have hxzle := entry_le_of_above' hS hO hxz hxe
    have hyz : y' ≠ z := fun h => by rw [h] at hy'; omega
    obtain ⟨hy'e, hyz' | hzy⟩ := link_of_finished hg hS hO hzn hzf hj hyz
    swap
    · have := entry_le_of_above' hS hO hzy hze
      omega
    have hy'u : Above w y' (w.up x) := by
      rcases above_total hyz' hxz with h | h
      · have hy'x : y' ≠ x := fun h => by rw [h] at hy'; omega
        exact ((above_iff.mp h).resolve_left hy'x).2
      · have := entry_le_of_above' hS hO h hxe
        omega
    -- the tree between, avoiding `f`
    have hfree : ∀ t, w.arrival t = some f → t = x := fun t ht => arrival_inj hS hO ht hfx
    have hlink : ∀ t, w.arrival t ≠ none → t ≠ x → (deleteLink g f).Link (w.up t) t := by
      intro t hta htx
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hta
      obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO t hta
      exact link_deleteLink.mpr ⟨e, fun hef => htx (hfree t (hef ▸ he)), hj e (by simp [he])⟩
    have c1 : (deleteLink g f).Connected x z := connected_of_above hS hO hxz fun t h1 _ h3 =>
      hlink t ((above_iff.mp h1).resolve_left (Ne.symm h3)).1 h3
    have hhf : h' ≠ f := by
      intro hh
      rw [hh] at hj hzh
      rcases Joins.ends (hjx f (by simp [hfx])) hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := entry_le_of_above' hS hO hxz hxe
        rw [h1] at this
        omega
      · exact hzh (h1 ▸ hfx)
    have c2 : (deleteLink g f).Connected z y' :=
      ReflTransGen.single (link_deleteLink.mpr ⟨h', hhf, hj⟩)
    have c3 : (deleteLink g f).Connected y' (w.up x) := connected_of_above hS hO hy'u
      fun t h1 h2 h3 => hlink t ((above_iff.mp h1).resolve_left (Ne.symm h3)).1
        (fun htx => by
          rw [htx] at h2
          have := entry_le_of_above' hS hO h2 hxe
          omega)
    have hyu : y = w.up x := by
      rcases Joins.ends (hjx f (by simp [hfx])) hxy with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact absurd h2 hyx
      · exact h2
    refine hconn (deleteLink g f) (fun _ _ h => h) (connected_symm ?_)
    rw [hyu]
    exact connected_trans (connected_trans c1 c2) c3
  · rintro ⟨c, -, hcf, hca, hlt⟩ hcon
    have hca' : w.arrival c ≠ none := by simp [hca]
    obtain ⟨-, hce, -, -, hult, hj⟩ := hangs hS hO c hca'
    have hclosed : ∀ z z', (deleteLink g f).Link z z' → Above w c z → Above w c z' := by
      intro z z' hl hz
      by_contra hz'
      obtain ⟨i, hif, hi⟩ := link_deleteLink.mp hl
      rcases leave_sub hg hS hO hcf hca' hi hz hz' with ⟨-, -, h⟩ | ⟨h1, h2⟩
      · rw [hca] at h
        exact hif (Option.some.inj h).symm
      · have := (entry_le_of_above hS hO h1 (hangs hS hO c hca').2.2.2.1).2.1
        omega
    have hnot : ¬ Above w c (w.up c) := fun h => by
      have := entry_le_of_above' hS hO h hce
      omega
    rcases Joins.ends (hj f (by simp [hca])) (Or.inl hab) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnot (mem_of_connected_closed hclosed (connected_symm hcon) (Above.refl w _))
    · exact hnot (mem_of_connected_closed hclosed hcon (Above.refl w _))

omit hS hO hD in
theorem two_children_iff {v : ℕ} : 2 ≤ numChildren (g := g) w v ↔
    ∃ c < g.n, ∃ c' < g.n, c ≠ c' ∧ Child w v c ∧ Child w v c' := by
  unfold numChildren
  have hnd : ((List.range g.n).filter fun x => decide (Child w v x)).Nodup :=
    List.nodup_range.filter _
  constructor
  · intro h
    rcases hl : (List.range g.n).filter (fun x => decide (Child w v x)) with _ | ⟨c, _ | ⟨c', l⟩⟩
    · simp [hl] at h
    · simp [hl] at h
    · rw [hl] at hnd
      have hc : c ∈ (List.range g.n).filter fun x => decide (Child w v x) := by simp [hl]
      have hc' : c' ∈ (List.range g.n).filter fun x => decide (Child w v x) := by simp [hl]
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hc hc'
      exact ⟨c, hc.1, c', hc'.1, fun h => by simp_all, hc.2, hc'.2⟩
  · rintro ⟨c, hc, c', hc', hne, h1, h2⟩
    have hsub : [c, c'] ⊆ (List.range g.n).filter fun x => decide (Child w v x) := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> simp_all
    have := ((List.nodup_cons.mpr ⟨by simpa using hne, List.nodup_singleton _⟩).subperm
      hsub).length_le
    simpa using this

omit hD in
/-- Tree links from `a` down to `x` avoid `v` when no vertex strictly below `a` on the way is `v`
or hangs from `v`. -/
theorem connected_down_isolate {v a x : ℕ} (hax : Above w a x)
    (hv : ∀ t, Above w a t → Above w t x → t ≠ a → t ≠ v ∧ w.up t ≠ v) :
    (isolate g v).Connected a x := by
  refine connected_of_above hS hO hax fun t h1 h2 h3 => ?_
  have hta : w.arrival t ≠ none := ((above_iff.mp h1).resolve_left (Ne.symm h3)).1
  exact link_isolate.mpr ⟨link_up hS hO hta, (hv t h1 h2 h3).2, (hv t h1 h2 h3).1⟩

omit hD in
/-- Below a vertex entered after `v`, tree links avoid `v`. -/
theorem connected_below_isolate {v c z : ℕ} (hcz : Above w c z) (hce : w.entry c ≠ 0)
    (hvc : w.entry v < w.entry c) : (isolate g v).Connected c z := by
  refine connected_down_isolate hS hO hcz fun t h1 _ h3 => ⟨fun h => ?_, fun h => ?_⟩
  · have := entry_le_of_above' hS hO h1 hce
    rw [h] at this
    omega
  · have hcu : Above w c (w.up t) := ((above_iff.mp h1).resolve_left (Ne.symm h3)).2
    have := entry_le_of_above' hS hO hcu hce
    rw [h] at this
    omega

include hg in
/-- **A cut vertex, read off the tree**: a vertex other than a root with a child whose subtree
cannot climb above it, or a root with two or more children. -/
theorem isCutVertex_iff_tree {v : ℕ} (hv : v < g.n) :
    IsCutVertex g v ↔ ((w.arrival v ≠ none ∧ ∃ c < g.n, Child w v c ∧ w.finished c ∧
      w.entry v ≤ w.low c) ∨ (w.arrival v = none ∧ w.finished v ∧
        2 ≤ numChildren (g := g) w v)) := by
  rw [isCutVertex_iff hg hv]
  have hve := (done_finished hS hD hv).1
  have hvf := (done_finished hS hD hv).2
  constructor
  swap
  · rintro (⟨hva, c, hcn, ⟨hce, hca, hcu⟩, hcf, hlow⟩ | ⟨hva, -, h2⟩)
    · obtain ⟨-, -, hun, hue, hlt, -⟩ := hangs hS hO v hva
      obtain ⟨-, -, -, -, hltc, -⟩ := hangs hS hO c hca
      rw [hcu] at hltc
      refine ⟨c, hcn, w.up v, hun, fun h => ?_, fun h => ?_, ?_, fun hcon => ?_⟩
      · rw [h] at hltc
        omega
      · have := congrArg w.entry h
        omega
      · have l1 := link_up hS hO hca
        have l2 := link_up hS hO hva
        rw [hcu] at l1
        exact connected_symm (connected_trans (connected_of_link l2) (connected_of_link l1))
      · have hclosed : ∀ z z', (isolate g v).Link z z' → Above w c z → Above w c z' := by
          intro z z' hl hz
          by_contra hz'
          obtain ⟨hl', hzv, hz'v⟩ := link_isolate.mp hl
          obtain ⟨i, hi⟩ : ∃ i, Joins g i z z' := by
            rcases hl' with h | h
            · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
              exact ⟨i, Or.inl hi⟩
            · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
              exact ⟨i, Or.inr hi⟩
          rcases leave_sub hg hS hO hcf hca hi hz hz' with ⟨-, h, -⟩ | ⟨h1, h2⟩
          · exact hz'v (h.trans hcu)
          · rw [hcu] at h1
            have := entry_le_of_above' hS hO h1 (entry_le_of_above hS hO h1 hve).1
            exact hz'v (entry_inj hS hO (entry_le_of_above hS hO h1 hve).1 (by omega))
        have := mem_of_connected_closed hclosed hcon (Above.refl w c)
        have := entry_le_of_above' hS hO this hce
        omega
    · obtain ⟨c, hcn, c', hc'n, hne, ⟨hce, hca, hcu⟩, ⟨hc'e, hc'a, hc'u⟩⟩ :=
        two_children_iff.mp h2
      obtain ⟨-, -, -, -, hltc, -⟩ := hangs hS hO c hca
      obtain ⟨-, -, -, -, hltc', -⟩ := hangs hS hO c' hc'a
      rw [hcu] at hltc
      rw [hc'u] at hltc'
      refine ⟨c, hcn, c', hc'n, fun h => ?_, fun h => ?_, ?_, fun hcon => ?_⟩
      · rw [h] at hltc
        omega
      · rw [h] at hltc'
        omega
      · have l1 := link_up hS hO hca
        have l2 := link_up hS hO hc'a
        rw [hcu] at l1
        rw [hc'u] at l2
        exact connected_trans (connected_symm (connected_of_link l1)) (connected_of_link l2)
      · have hcf := finished_of_above hS hO (hcu ▸ Above.up hca) hvf hce
        have hclosed : ∀ z z', (isolate g v).Link z z' → Above w c z → Above w c z' := by
          intro z z' hl hz
          by_contra hz'
          obtain ⟨hl', hzv, hz'v⟩ := link_isolate.mp hl
          obtain ⟨i, hi⟩ : ∃ i, Joins g i z z' := by
            rcases hl' with h | h
            · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
              exact ⟨i, Or.inl hi⟩
            · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
              exact ⟨i, Or.inr hi⟩
          rcases leave_sub hg hS hO hcf hca hi hz hz' with ⟨-, h, -⟩ | ⟨h1, -⟩
          · exact hz'v (h.trans hcu)
          · rw [hcu] at h1
            exact hz'v (above_root hva h1)
        have hcc' := mem_of_connected_closed hclosed hcon (Above.refl w c)
        rcases above_iff.mp hcc' with h | ⟨-, h⟩
        · exact hne h
        · rw [hc'u] at h
          have := entry_le_of_above' hS hO h hce
          omega
  · rintro ⟨x, hxn, y, hyn, hvx, hvy, hcxy, hncon⟩
    by_contra hnot
    apply hncon
    have hxe := (done_finished hS hD hxn).1
    obtain ⟨r, hrx, hra, hre⟩ := exists_root hS hO _ x le_rfl hxe
    have hry : Above w r y := above_of_connected hg hS hO hD hra hrx hcxy
    have hlinkJ : ∀ z z', g.Link z z' → ∃ i, Joins g i z z' := by
      intro z z' hl
      rcases hl with h | h
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
        exact ⟨i, Or.inl hi⟩
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
        exact ⟨i, Or.inr hi⟩
    by_cases hrv : Above w r v
    swap
    · have hclosed : ∀ z z', g.Link z z' →
          (Above w r z ∧ (isolate g v).Connected x z) →
          (Above w r z' ∧ (isolate g v).Connected x z') := by
        intro z z' hl ⟨hz, hxz⟩
        have hz' : Above w r z' := above_of_connected hg hS hO hD hra hz (connected_of_link hl)
        refine ⟨hz', hxz.tail (link_isolate.mpr ⟨hl, fun h => hrv (h ▸ hz),
          fun h => hrv (h ▸ hz')⟩)⟩
      exact (mem_of_connected_closed hclosed hcxy ⟨hrx, ReflTransGen.refl⟩).2
    -- the subtree of a child of `v` reaches a vertex above `v`, or `v` is a root
    have hchild : ∀ z, Above w v z → z ≠ v → ∃ c, Child w v c ∧ Above w c z ∧
        (isolate g v).Connected c z := by
      intro z hvz hzv
      obtain ⟨c, hcz, hca, hcu⟩ := exists_child_of_above hvz (Ne.symm hzv)
      obtain ⟨-, hce, -, -, hlt, -⟩ := hangs hS hO c hca
      rw [hcu] at hlt
      exact ⟨c, ⟨hce, hca, hcu⟩, hcz, connected_below_isolate hS hO hcz hce hlt⟩
    by_cases hva : w.arrival v = none
    · -- a root with at most one child
      have hrv' : r = v := above_root hva hrv
      subst hrv'
      have hxv : Above w r x := hrx
      obtain ⟨c, hc, -, hcx⟩ := hchild x hxv (Ne.symm hvx)
      obtain ⟨c', hc', -, hcy⟩ := hchild y hry (Ne.symm hvy)
      have hcc : c = c' := by
        by_contra hne
        exact hnot (Or.inr ⟨hva, hvf, two_children_iff.mpr ⟨c, lt_n_of_entered hO hc.1, c',
          lt_n_of_entered hO hc'.1, hne, hc, hc'⟩⟩)
      subst hcc
      exact connected_trans (connected_symm hcx) hcy
    · -- not a root: every vertex of the tree but `v` reaches the root avoiding `v`
      have hrne : r ≠ v := fun h => hva (h ▸ hra)
      have hup : ∀ z, Above w r z → ¬ Above w v z → (isolate g v).Connected r z := by
        intro z hrz hvz
        refine connected_down_isolate hS hO hrz fun t h1 h2 h3 => ⟨fun h => hvz (h ▸ h2),
          fun h => hvz ?_⟩
        have hta : w.arrival t ≠ none := ((above_iff.mp h1).resolve_left (Ne.symm h3)).1
        exact h ▸ (Above.up hta).trans h2
      have hall : ∀ z < g.n, z ≠ v → Above w r z → (isolate g v).Connected z r := by
        intro z hzn hzv hrz
        by_cases hvz : Above w v z
        · obtain ⟨c, ⟨hce, hca, hcu⟩, hcz, hconn⟩ := hchild z hvz hzv
          have hcn := lt_n_of_entered hO hce
          have hcf := (done_finished hS hD hcn).2
          have hlow : w.low c < w.entry v := by
            by_contra h
            exact hnot (Or.inl ⟨hva, c, hcn, ⟨hce, hca, hcu⟩, hcf, by omega⟩)
          have hvlt : w.entry v < w.entry c := by
            have := (hangs hS hO c hca).2.2.2.2.1
            rwa [hcu] at this
          rw [shape_low_eq hS hcn hce, climb_lt_iff] at hlow
          rcases hlow with h | ⟨z0, hz0n, hex, ⟨y0, h0⟩, hs, hz0h, hy0⟩
          · omega
          simp only at hz0h hy0
          have hcz0 := above_of_explored hS hO hex
          have hz0e := entered_of_above hS hO hcz0 hce
          have hz0f := (done_finished hS hD hz0n).2
          have hj : Joins g h0 z0 y0 := joins_of_adj_mem (List.mem_of_mem_take hs)
          have hcz0le := entry_le_of_above' hS hO hcz0 hce
          have hyz : y0 ≠ z0 := fun h => by rw [h] at hy0; omega
          obtain ⟨hy0e, hyz' | hzy⟩ := link_of_finished hg hS hO hz0n hz0f hj hyz
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
          have c1 := connected_below_isolate hS hO hcz0 hce hvlt
          have c2 : (isolate g v).Connected z0 y0 :=
            connected_of_link (link_isolate.mpr ⟨by
              rcases hj with h | h
              · exact Or.inl (List.mem_of_getElem? h)
              · exact Or.inr (List.mem_of_getElem? h), hz0v, hy0v⟩)
          have c3 := connected_symm (hup y0 hry0 hnvy)
          exact connected_trans (connected_symm hconn) (connected_trans c1 (connected_trans c2 c3))
        · exact connected_symm (hup z hrz hvz)
      exact connected_trans (hall x hxn (Ne.symm hvx) hrx)
        (connected_symm (hall y hyn (Ne.symm hvy) hry))

end Done

end Walk

end AlgoDesign.Graphs.Blocks
