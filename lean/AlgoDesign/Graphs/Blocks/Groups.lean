/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Tree

/-!
# Bridges, cut vertices and blocks: a block top's group is a block

From the walk's shape: a finished vertex has looked at its whole row, and every link there leads
above or below it. Below a block top `c`, hanging from `u`, every link leaving `c`'s subtree lands
on `u` (`gate`), since the subtree cannot climb above `u`. So no cycle holds a link of `c`'s
group and a link outside it (`inGroup_of_sameBlock`), and inside the group a link back and the
tree links above its deeper end lie on one cycle, which chains every link of the group to `c`'s
arrival link (`sameBlock_of_inGroup`). Together with the rest of the shape this is `Valid`
(`valid_of_shape`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

/-- **A row lists each end of each link at the vertex**: the other end and the link's id. -/
theorem adj_mem_iff {v y i : ℕ} :
    (y, i) ∈ g.adj v ↔ y < g.n ∧ (g.links[i]? = some (v, y) ∨ g.links[i]? = some (y, v)) := by
  simp only [Graph.adj, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨y', hy', i', ⟨j, hj, hi'⟩, rfl, rfl⟩
    unfold Graph.entries at hi'
    refine ⟨hy', ?_⟩
    rcases hl : g.links[j]? with _ | ⟨a, b⟩
    · simp [hl] at hi'
    · simp only [hl] at hi'
      rw [List.mem_append] at hi'
      rcases hi' with hi' | hi'
      · split_ifs at hi' with h1
        · obtain ⟨rfl, rfl⟩ := h1
          rw [List.mem_singleton] at hi'
          subst hi'
          exact Or.inl hl
        · simp at hi'
      · split_ifs at hi' with h1
        · obtain ⟨rfl, rfl⟩ := h1
          rw [List.mem_singleton] at hi'
          subst hi'
          exact Or.inr hl
        · simp at hi'
  · rintro ⟨hy, h⟩
    have hi : i < g.links.length := by
      rcases h with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
    refine ⟨y, hy, i, ⟨i, hi, ?_⟩, rfl, rfl⟩
    unfold Graph.entries
    rcases h with h | h <;> simp [h]

theorem adj_mem_of_joins (hg : g.WellFormed) {i x y : ℕ} (h : Joins g i x y) :
    (y, i) ∈ g.adj x := by
  refine adj_mem_iff.mpr ⟨?_, h⟩
  rcases h with h | h
  · exact (hg _ (List.mem_of_getElem? h)).2
  · exact (hg _ (List.mem_of_getElem? h)).1

theorem joins_of_adj_mem {i x y : ℕ} (h : (y, i) ∈ g.adj x) : Joins g i x y :=
  (adj_mem_iff.mp h).2

section Shape

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

omit hO in
theorem entry_le_n (x : ℕ) (hx : x < g.n) : w.entry x ≤ g.n := by
  have := hS.1.1 x hx
  have : w.time ≤ g.n := by
    rw [hS.1.2.2]
    exact (List.length_filter_le _ _).trans (by simp)
  omega

omit hS in
theorem lt_n_of_entered {x : ℕ} (hx : w.entry x ≠ 0) : x < g.n := by
  by_contra h
  exact hx (hO x (by omega)).1

theorem entry_inj {x y : ℕ} (hx : w.entry x ≠ 0) (h : w.entry x = w.entry y) : x = y :=
  hS.1.2.1 x (lt_n_of_entered hO hx) y
    (lt_n_of_entered hO (h ▸ hx)) h hx

omit hO in
/-- A finished vertex has looked at its whole row. -/
theorem looked_of_finished {x : ℕ} (hx : x < g.n) (hf : w.finished x = true) :
    looked (g := g) w x = g.adj x := by
  unfold looked
  rw [(hS.2.2.1 x hx).2.2.1 hf]
  exact List.take_length

include hg in
/-- Every link at a finished vertex leads to an entered vertex above or below it. -/
theorem link_of_finished {f x y : ℕ} (hx : x < g.n) (hf : w.finished x = true)
    (hj : Joins g f x y) (hxy : y ≠ x) :
    w.entry y ≠ 0 ∧ (Above w y x ∨ Above w x y) := by
  have hm : (y, f) ∈ looked (g := g) w x := by
    rw [looked_of_finished hS hx hf]
    exact adj_mem_of_joins hg hj
  obtain ⟨h1, h2⟩ := hS.2.2.2.2.2.1 x hx (y, f) hm
  refine ⟨h1, ?_⟩
  rcases h2 hxy with h | h
  · exact Or.inl ((anc_iff hS hO y x).mp h)
  · exact Or.inr ((anc_iff hS hO x y).mp h)

/-- Below a finished vertex, the explored subtree is everything below. -/
theorem explored_of_above {v x : ℕ} (hv : w.finished v = true) (h : Above w v x) :
    Explored (g := g) w v x := by
  by_cases hxv : x = v
  · exact Or.inl hxv
  · obtain ⟨y, hyx, hy, rfl⟩ := exists_child_of_above h (Ne.symm hxv)
    have hye := (hangs hS hO y hy).2.1
    refine Or.inr ⟨y, (anc_iff hS hO y x).mpr hyx, ?_, hy, rfl⟩
    exact finished_of_above hS hO (Above.up hy) hv hye

include hg in
/-- A finished vertex's climb-back number is at most the entry number of every vertex a link
reaches from its subtree, other than a vertex's own arrival link. -/
theorem low_le {c x y f : ℕ} (hc : w.finished c = true) (h : Above w c x)
    (hj : Joins g f x y) (hfa : w.arrival x ≠ some f) : w.low c ≤ w.entry y := by
  have hcn : c < g.n := by
    by_contra hn
    have := (hO c (by omega)).2.2.1
    simp_all
  have hce : w.entry c ≠ 0 := (hS.2.2.1 c hcn).1.mpr (Or.inr hc)
  rw [shape_low_eq hS hcn hce]
  have hxe : w.entry x ≠ 0 := by
    rcases above_iff.mp h with h' | ⟨h', -⟩
    · exact h' ▸ hce
    · exact (hangs hS hO x h').2.1
  have hxn := lt_n_of_entered hO hxe
  have hxf := finished_of_above hS hO h hc hxe
  refine ((le_climb_iff w c _).mp le_rfl).2 x hxn (explored_of_above hS hO hc h) (y, f) ?_ hfa
  rw [looked_of_finished hS hxn hxf]
  exact adj_mem_of_joins hg hj

theorem entered_of_above {a x : ℕ} (h : Above w a x) (ha : w.entry a ≠ 0) :
    w.entry x ≠ 0 := by
  rcases above_iff.mp h with h' | ⟨h', -⟩
  · exact h' ▸ ha
  · exact (hangs hS hO x h').2.1

omit hS in
theorem finished_lt {c : ℕ} (hc : w.finished c = true) : c < g.n := by
  by_contra hn
  have := (hO c (by omega)).2.2.1
  simp_all

theorem entered_of_finished {c : ℕ} (hc : w.finished c = true) : w.entry c ≠ 0 :=
  (hS.2.2.1 c (finished_lt hO hc)).1.mpr (Or.inr hc)

include hg in
/-- **The gate below a block top**: every link with exactly one end below a block top `c` has its
other end at the vertex `c` hangs from. -/
theorem gate {c : ℕ} (hc : BlockTop w c) {i a b : ℕ} (hl : Joins g i a b)
    (ha : Above w c a) (hb : ¬ Above w c b) : b = w.up c := by
  obtain ⟨hcf, hca, hlow⟩ := hc
  have hce := entered_of_finished hS hO hcf
  have hae := entered_of_above hS hO ha hce
  have han := lt_n_of_entered hO hae
  have haf := finished_of_above hS hO ha hcf hae
  have hba : b ≠ a := fun h => hb (h ▸ ha)
  obtain ⟨hbe, hab | hab⟩ := link_of_finished hg hS hO han haf hl hba
  · by_cases hfa : w.arrival a = some i
    · obtain ⟨-, -, -, -, -, hj⟩ := hangs hS hO a (by simp [hfa])
      rcases Joins.ends (hj i (by simp [hfa])) hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd h2 hba
      · have hac : a = c := by
          by_contra hne
          rcases above_iff.mp ha with h' | ⟨-, h'⟩
          · exact hne h'.symm
          · exact hb (h2 ▸ h')
        subst hac
        exact h2
    · have hle := low_le hg hS hO hcf ha hl hfa
      rcases above_total hab ha with h' | h'
      · have hbc : b ≠ c := fun h => hb (h ▸ Above.refl w c)
        rcases above_iff.mp h' with h'' | ⟨-, h''⟩
        · exact absurd h'' hbc
        · rcases eq_or_ne b (w.up c) with h3 | h3
          · exact h3
          · have := (entry_le_of_above hS hO h'' (hangs hS hO c hca).2.2.2.1).2.2 h3
            omega
      · exact absurd h' hb
  · exact absurd (ha.trans hab) hb

/-- **A link back and the tree links it closes lie on one cycle**: a link from `z` to a vertex `y`
above it, not the arrival link of any vertex between them, closes a cycle with the tree links from
`z` up to `y`. -/
theorem onCycleWith_back {z y f t a : ℕ} (hze : w.entry z ≠ 0) (hyz : Above w y z) (hne : y ≠ z)
    (hj : Joins g f z y)
    (hf : ∀ t, Above w y t → Above w t z → t ≠ y → w.arrival t ≠ some f)
    (ht₁ : Above w y t) (ht₂ : Above w t z) (ht₃ : t ≠ y) (ha : w.arrival t = some a) :
    OnCycleWith g f a := by
  obtain ⟨hp, hsteps, hall⟩ := upSteps_spec hS hO g.n z y
    (entry_le_n hS z (lt_n_of_entered hO hze)) hyz hze
  have hc : IsCycle g z (upSteps w g.n z y ++ [(f, z)]) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact trail_append.mpr ⟨hp.trail, by rw [hp.endOf_eq]; exact ⟨hj.symm, trivial⟩⟩
    · rw [endOf_append, endOf_singleton]
    · have hnd := hp.nodup
      rw [List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨(List.nodup_cons.mp hnd).2, by simp, ?_⟩
      intro p hp' q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact fun h => (List.nodup_cons.mp hnd).1 (h ▸ hp')
    · rw [List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hp.links_nodup, by simp, ?_⟩
      intro p hp' q hq
      simp only [List.mem_singleton] at hq
      subst hq
      obtain ⟨⟨p1, p2⟩, hpm, rfl⟩ := List.mem_map.mp hp'
      obtain ⟨t', h1, h2, h3, h4, -⟩ := hsteps _ hpm
      intro h
      exact hf t' h1 h2 h3 (h ▸ h4)
  have hfa : f ≠ a := fun h => hf t ht₁ ht₂ ht₃ (h ▸ ha)
  obtain ⟨e', he', hm⟩ := hall t ht₁ ht₂ ht₃
  rw [ha] at he'
  cases he'
  refine onCycleWith_iff.mpr ⟨hfa, z, _, hc, by simp, ?_⟩
  simp only [List.map_append, List.mem_append, List.mem_map]
  exact Or.inl ⟨_, hm, rfl⟩

theorem headIs_iff {x c : ℕ} : HeadIs (g := g) w x c ↔ Above w c x ∧ BlockTop w c ∧
    ∀ c', Above w c' x → Above w c c' → c' ≠ c → ¬ BlockTop w c' := by
  unfold HeadIs
  rw [anc_iff hS hO]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h c' h1 h2 h3
    exact h c' ((anc_iff hS hO c' x).mpr h1) ((anc_iff hS hO c c').mpr h2) h3
  · intro h c' h1 h2 h3
    exact h c' ((anc_iff hS hO c' x).mp h1) ((anc_iff hS hO c c').mp h2) h3

include hg in
/-- The gate below a block top, in the form cycles read. -/
theorem gate' {c : ℕ} (hc : BlockTop w c) : ∀ i a b : ℕ, g.links[i]? = some (a, b) →
    (Above w c a → ¬ Above w c b → b = w.up c) ∧ (Above w c b → ¬ Above w c a → a = w.up c) :=
  fun _ _ _ hl => ⟨gate hg hS hO hc (Or.inl hl), gate hg hS hO hc (Or.inr hl)⟩

end Shape

theorem deep_iff {w : Walk} {f x a b : ℕ} (hl : g.links[f]? = some (a, b)) :
    Deep (g := g) w f x ↔ (a = x ∨ b = x) ∧ w.entry x = max (w.entry a) (w.entry b) := by
  simp [Deep, deepEntry, hl]

theorem isEnd_of_link {f a b : ℕ} (hl : g.links[f]? = some (a, b)) :
    IsEnd g f a ∧ IsEnd g f b :=
  ⟨⟨b, Or.inl hl⟩, ⟨a, Or.inr hl⟩⟩

/-- The two ends of a link that is not a loop: the deeper one, and the other. -/
theorem ends_of_deep {f x a b : ℕ} (hab : g.links[f]? = some (a, b))
    (hx : a = x ∨ b = x) : ∃ y, Joins g f x y ∧ (y = a ∨ y = b) ∧ (a ≠ b → y ≠ x) := by
  rcases hx with rfl | rfl
  · exact ⟨b, Or.inl hab, Or.inr rfl, fun h => Ne.symm h⟩
  · exact ⟨a, Or.inr hab, Or.inl rfl, fun h => h⟩

section Group

variable (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hg hS hO

omit hg in
theorem entry_le_of_above' {a x : ℕ} (h : Above w a x) (ha : w.entry a ≠ 0) :
    w.entry a ≤ w.entry x :=
  (entry_le_of_above hS hO h (entered_of_above hS hO h ha)).2.1

/-- **No cycle leaves a group**: a link on a cycle with a link of block top `c`'s group is in that
group. -/
theorem inGroup_of_sameBlock {c f f' : ℕ} (hgr : InGroup (g := g) w c f)
    (hsb : SameBlock g f f') : InGroup (g := g) w c f' := by
  obtain ⟨-, ⟨⟨p, q⟩, hpq, hpqne⟩, hor⟩ := hsb
  simp only [Option.mem_def] at hpq
  simp only at hpqne
  rcases hor with rfl | hcyc
  · exact hgr
  obtain ⟨htk, x, hxn, hdeep, hhead⟩ := hgr
  obtain ⟨⟨a, b⟩, hab, hne⟩ := htk.1
  simp only [Option.mem_def] at hab
  simp only at hne
  obtain ⟨hcx, hct, hbetween⟩ := (headIs_iff hS hO).mp hhead
  have hce := entered_of_finished hS hO hct.1
  obtain ⟨-, -, -, hue, hlt, -⟩ := hangs hS hO c hct.2.1
  obtain ⟨hxab, hxmax⟩ := (deep_iff hab).mp hdeep
  obtain ⟨y, hxy, hyab, hyx⟩ := ends_of_deep hab hxab
  have hyx := hyx hne
  have hxend : IsEnd g f x := ⟨y, hxy⟩
  have hyend : IsEnd g f y := ⟨x, hxy.symm⟩
  have hymax : w.entry y ≤ w.entry x := by rcases hyab with rfl | rfl <;> omega
  have hpend : IsEnd g f' p := (isEnd_of_link hpq).1
  have hqend : IsEnd g f' q := (isEnd_of_link hpq).2
  have hnu : ¬ Above w c (w.up c) := fun h => by
    have := entry_le_of_above' hS hO h hce
    omega
  have hside : ∀ z, IsEnd g f' z → Above w c z ∨ z = w.up c := by
    intro z hz
    by_cases hzc : Above w c z
    · exact Or.inl hzc
    · exact Or.inr (onCycleWith_gate hnu (gate' hg hS hO hct) hcyc (Or.inl hxend) (Or.inr hz)
        hcx hzc)
  -- the deeper end of `f'` is below `c`
  obtain ⟨x', hx'pq, hx'max, hx'c⟩ : ∃ x', (p = x' ∨ q = x') ∧
      w.entry x' = max (w.entry p) (w.entry q) ∧ Above w c x' := by
    by_cases hle : w.entry q ≤ w.entry p
    · refine ⟨p, Or.inl rfl, by omega, ?_⟩
      rcases hside p hpend with h | h
      · exact h
      · rcases hside q hqend with h' | h'
        · have := entry_le_of_above' hS hO h' hce
          rw [h] at hle
          omega
        · exact absurd (h.trans h'.symm) hpqne
    · refine ⟨q, Or.inr rfl, by omega, ?_⟩
      rcases hside q hqend with h | h
      · exact h
      · rcases hside p hpend with h' | h'
        · have := entry_le_of_above' hS hO h' hce
          rw [h] at hle
          omega
        · exact absurd (h'.trans h.symm) hpqne
  have hx'end : IsEnd g f' x' := by rcases hx'pq with rfl | rfl; exacts [hpend, hqend]
  have hx'e := entered_of_above hS hO hx'c hce
  have hx'n := lt_n_of_entered hO hx'e
  have hx'f := finished_of_above hS hO hx'c hct.1 hx'e
  obtain ⟨o, ho⟩ := hx'end
  refine ⟨⟨⟨(p, q), hpq, hpqne⟩, x', hx'n, (o, f'), ?_, rfl⟩, x', hx'n,
    (deep_iff hpq).mpr ⟨hx'pq, hx'max⟩, (headIs_iff hS hO).mpr ⟨hx'c, hct, ?_⟩⟩
  · rw [looked_of_finished hS hx'n hx'f]
    exact adj_mem_of_joins hg ho
  intro c' h1 h2 h3 hbt
  have hxS : ¬ Above w c' x := fun h => hbetween c' h h2 h3 hbt
  have hc'e := entered_of_finished hS hO hbt.1
  obtain ⟨-, -, -, -, hlt', -⟩ := hangs hS hO c' hbt.2.1
  have hnu' : ¬ Above w c' (w.up c') := fun h => by
    have := entry_le_of_above' hS hO h hc'e
    omega
  by_cases hxu : x = w.up c'
  · have hyS : ¬ Above w c' y := fun h => by
      have := entry_le_of_above' hS hO h hc'e
      rw [hxu] at hymax
      omega
    exact hyx (onCycleWith_gate hnu' (gate' hg hS hO hbt) hcyc (Or.inr ⟨o, ho⟩)
      (Or.inl hyend) h1 hyS |>.trans hxu.symm)
  · exact hxu (onCycleWith_gate hnu' (gate' hg hS hO hbt) hcyc (Or.inr ⟨o, ho⟩)
      (Or.inl hxend) h1 hxS)

omit hg hS hO in
theorem nonLoop_of_joins {f a b : ℕ} (h : Joins g f a b) (hab : a ≠ b) : NonLoop g f := by
  rcases h with h | h
  · exact ⟨(a, b), h, hab⟩
  · exact ⟨(b, a), h, Ne.symm hab⟩

omit hg in
theorem nonLoop_arrival {x a : ℕ} (h : w.arrival x = some a) : NonLoop g a := by
  obtain ⟨-, -, -, -, hlt, hj⟩ := hangs hS hO x (by simp [h])
  refine nonLoop_of_joins (hj a (by simp [h])) (fun h' => ?_)
  rw [h'] at hlt
  omega

omit hg in
theorem above_of_explored {x z : ℕ} (h : Explored (g := g) w x z) : Above w x z := by
  rcases h with rfl | ⟨y, hy, -, hya, rfl⟩
  · exact Above.refl w _
  · exact (Above.up hya).trans ((anc_iff hS hO y z).mp hy)

omit hg in
/-- A link from `z` to `y` is not the arrival link of a vertex strictly between them, unless it is
`z`'s own. -/
theorem not_arrival_between {z y f : ℕ} (hj : Joins g f z y) (hfz : w.arrival z ≠ some f) :
    ∀ t, Above w y t → Above w t z → t ≠ y → w.arrival t ≠ some f := by
  intro t _ _ hty hta
  obtain ⟨-, -, -, -, -, hj'⟩ := hangs hS hO t (by simp [hta])
  rcases Joins.ends (hj' f (by simp [hta])) hj with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hty h2.symm
  · exact hfz (h1 ▸ hta)

/-- **Up the group, tree links share a block**: below a block top `c`, every vertex whose first
block top is `c` has its arrival link in one block with `c`'s. -/
theorem sameBlock_arrival {c ec : ℕ} (hec : w.arrival c = some ec) :
    ∀ k x, w.entry x ≤ k → HeadIs (g := g) w x c → ∀ a, w.arrival x = some a →
      SameBlock g a ec := by
  intro k
  induction k with
  | zero =>
    intro x hk _ a ha
    exact absurd (by omega) (hangs hS hO x (by simp [ha])).2.1
  | succ k ih =>
    intro x hk hhead a ha
    obtain ⟨hcx, hct, hbetween⟩ := (headIs_iff hS hO).mp hhead
    by_cases hxc : x = c
    · subst hxc
      rw [ha] at hec
      cases hec
      exact ⟨nonLoop_arrival hS hO ha, nonLoop_arrival hS hO ha, Or.inl rfl⟩
    have hce := entered_of_finished hS hO hct.1
    have hxe := entered_of_above hS hO hcx hce
    have hxn := lt_n_of_entered hO hxe
    have hxf := finished_of_above hS hO hcx hct.1 hxe
    have hxa : w.arrival x ≠ none := by simp [ha]
    obtain ⟨-, -, hun, hue, hlt, -⟩ := hangs hS hO x hxa
    have hnbt : ¬ BlockTop w x := hbetween x (Above.refl w x) hcx hxc
    have hlow : w.low x < w.entry (w.up x) := by
      by_contra h
      exact hnbt ⟨hxf, hxa, by omega⟩
    rw [shape_low_eq hS hxn hxe, climb_lt_iff] at hlow
    rcases hlow with h | ⟨z, hzn, hex, ⟨y, f⟩, hs, hfz, hy⟩
    · omega
    simp only at hfz hy
    have hxz := above_of_explored hS hO hex
    have hze := entered_of_above hS hO hxz hxe
    have hzf := finished_of_above hS hO hxz hxf hze
    have hj : Joins g f z y := joins_of_adj_mem (List.mem_of_mem_take hs)
    have hxzle := entry_le_of_above' hS hO hxz hxe
    have hyz : y ≠ z := fun h => by rw [h] at hy; omega
    obtain ⟨hye, hyz' | hzy⟩ := link_of_finished hg hS hO hzn hzf hj hyz
    swap
    · have := entry_le_of_above' hS hO hzy hze
      omega
    have huz : Above w (w.up x) z := (Above.up hxa).trans hxz
    rcases above_total hyz' huz with hyu | huy
    swap
    · have := entry_le_of_above' hS hO huy hue
      omega
    have hyu' : y ≠ w.up x := fun h => by rw [h] at hy; omega
    have hnb := not_arrival_between hS hO hj hfz
    obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists'.mp
      (above_iff.mp hyu |>.resolve_left hyu').1
    have hfl : NonLoop g f := nonLoop_of_joins hj (Ne.symm hyz)
    have h1 : SameBlock g f a := ⟨hfl, nonLoop_arrival hS hO ha, Or.inr
      (onCycleWith_back hS hO hze hyz' (Ne.symm hyz).symm hj hnb (hyu.trans (Above.up hxa)) hxz
        (fun h => by have := congrArg w.entry h; omega) ha)⟩
    have h2 : SameBlock g f a' := ⟨hfl, nonLoop_arrival hS hO ha', Or.inr
      (onCycleWith_back hS hO hze hyz' (Ne.symm hyz).symm hj hnb hyu huz (Ne.symm hyu') ha')⟩
    have h12 : SameBlock g a a' := sameBlock_trans (sameBlock_symm h1) h2
    by_cases huc : w.up x = c
    · rw [huc, hec] at ha'
      cases ha'
      exact h12
    have hcu : Above w c (w.up x) := (above_iff.mp hcx).resolve_left (Ne.symm hxc) |>.2
    refine sameBlock_trans h12 (ih (w.up x) (by omega) ((headIs_iff hS hO).mpr
      ⟨hcu, hct, fun c' h1 h2 h3 => hbetween c' (h1.trans (Above.up hxa)) h2 h3⟩) a' ha')

/-- **A group lies in one block**: two links of a block top's group are on a common cycle, or the
same link. -/
theorem sameBlock_of_inGroup {c f f' : ℕ} (hf : InGroup (g := g) w c f)
    (hf' : InGroup (g := g) w c f') : SameBlock g f f' := by
  have key : ∀ f, InGroup (g := g) w c f → ∃ ec, w.arrival c = some ec ∧ SameBlock g f ec := by
    intro f ⟨htk, x, hxn, hdeep, hhead⟩
    obtain ⟨hcx, hct, -⟩ := (headIs_iff hS hO).mp hhead
    obtain ⟨ec, hec⟩ := Option.ne_none_iff_exists'.mp hct.2.1
    refine ⟨ec, hec, ?_⟩
    have hce := entered_of_finished hS hO hct.1
    have hxe := entered_of_above hS hO hcx hce
    have hxf := finished_of_above hS hO hcx hct.1 hxe
    have hxa : w.arrival x ≠ none := by
      rcases above_iff.mp hcx with h | ⟨h, -⟩
      · exact h ▸ hct.2.1
      · exact h
    obtain ⟨ax, hax⟩ := Option.ne_none_iff_exists'.mp hxa
    have hchain := sameBlock_arrival hg hS hO hec _ x le_rfl hhead ax hax
    obtain ⟨⟨a, b⟩, hab, hne⟩ := htk.1
    simp only [Option.mem_def] at hab
    simp only at hne
    obtain ⟨hxab, hxmax⟩ := (deep_iff hab).mp hdeep
    obtain ⟨y, hxy, hyab, hyx⟩ := ends_of_deep hab hxab
    have hyx := hyx hne
    by_cases hfa : f = ax
    · subst hfa
      exact hchain
    have hymax : w.entry y ≤ w.entry x := by rcases hyab with rfl | rfl <;> omega
    obtain ⟨hye, hyx' | hxy'⟩ := link_of_finished hg hS hO hxn hxf hxy hyx
    · have hfz : w.arrival x ≠ some f := fun h => hfa (by rw [hax] at h; cases h; rfl)
      exact sameBlock_trans ⟨htk.1, nonLoop_arrival hS hO hax, Or.inr
        (onCycleWith_back hS hO hxe hyx' hyx hxy (not_arrival_between hS hO hxy hfz) hyx'
          (Above.refl w x) (Ne.symm hyx) hax)⟩ hchain
    · have := (entry_le_of_above hS hO hxy' hye).2.2 (Ne.symm hyx)
      omega
  obtain ⟨ec, hec, h1⟩ := key f hf
  obtain ⟨ec', hec', h2⟩ := key f' hf'
  rw [hec] at hec'
  cases hec'
  exact sameBlock_trans h1 (sameBlock_symm h2)

/-- A finished root with no children has only loops: an isolated vertex. -/
theorem isolated_of_loneRoot {r : ℕ} (h : LoneRoot (g := g) w r) : IsolatedVertex g r := by
  obtain ⟨hrf, hra, hch⟩ := h
  have hrn := finished_lt hO hrf
  refine ⟨hrn, fun l hl hend => ?_⟩
  by_contra hne
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨y, hj, hyr⟩ : ∃ y, Joins g i r y ∧ y ≠ r := by
    rcases hend with h | h
    · refine ⟨l.2, Or.inl (by rw [hi, ← h]), fun h' => hne (h.trans h'.symm)⟩
    · refine ⟨l.1, Or.inr (by rw [hi, ← h]), fun h' => hne (h'.trans h.symm)⟩
  obtain ⟨-, hyr' | hry⟩ := link_of_finished hg hS hO hrn hrf hj hyr
  · exact hyr (above_root hra hyr')
  · obtain ⟨t, -, hta, htu⟩ := exists_child_of_above hry (Ne.symm hyr)
    obtain ⟨htn, hte, -⟩ := hangs hS hO t hta
    unfold numChildren at hch
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at hch
    exact hch t (List.mem_range.mpr htn) (by simp [Child, hte, hta, htu])

/-- **The shape gives `Valid`**: the climb-back numbers are the shape's own, the stack's contents
too, every block with links is a block top's group, which is a whole block of the network, and
every block without links is an isolated vertex. -/
theorem valid_of_shape : Valid w := by
  refine ⟨hS.2.2.2.2.2.2.2.2.1.2, ?_⟩
  unfold StackHoldsOpenLinks
  rw [hS.2.2.2.2.2.2.2.2.1.1]
  refine ⟨hS.2.2.2.2.2.2.2.2.2.1, hS.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro b hb e he f hf
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have hbk : w.blocks.getD k [] = w.blocks[k] := by simp [hk]
    have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨c, -, hne, hct, hiff⟩ := hBO.2.2.1 k hk (by rw [hbk]; exact List.ne_nil_of_mem he)
    rw [hbk] at hiff
    have hem : e < g.links.length := hBO.2.2.2.2.2.2.2.2 _ hb e he
    have hge := (hiff e hem).mp he
    rw [hiff f hf]
    exact ⟨fun h => sameBlock_of_inGroup hg hS hO hge h,
      fun h => inGroup_of_sameBlock hg hS hO hge h⟩
  · intro k hk hemp
    obtain ⟨r, -, ⟨-, hpl⟩, hlone⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.1 k hk hemp
    rw [hpl]
    exact ⟨rfl, fun v hv => by
      rw [List.mem_singleton] at hv
      exact hv ▸ isolated_of_loneRoot hg hS hO hlone⟩

end Group

end Walk

end AlgoDesign.Graphs.Blocks
