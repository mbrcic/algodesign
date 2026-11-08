/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Kruskal.Decide

/-! # Cheapest spanning forest: joining, forests and the exchange

The facts the walk's proofs share. One link added to a set joins two vertices exactly when the set
already joins them or joins each to one end of the link (`joins_cons_iff`); so a link whose ends
are already joined adds nothing (`joins_cons_of_joins`). Whether a set closes no cycle does not
depend on its order, and it holds of a link added to a set that does not join its ends
(`closesNoCycle_cons_iff`). The exchange (`exchange`), the cut property's proof: when a set `K` of
links of a spanning forest `T` does not join the ends of a link `e` outside `T`, some link `f` of
`T` whose ends `K` does not join either can be swapped for `e`, and the result is again a spanning
forest that contains `K`. -/

@[expose] public section

namespace AlgoDesign.Paths.LinkNetwork

open AlgoDesign.Graphs UnionFind

variable {N : LinkNetwork}

/-! ## One link more -/

/-- **One link more**: `i :: F` joins `u` and `v` exactly when `F` joins them, or joins `u` to one
end of `i` and the other end to `v`. -/
theorem joins_cons_iff {F : List ℕ} {i u v : ℕ} :
    N.Joins (i :: F) u v ↔ N.Joins F u v ∨
      (N.Joins F u (N.ends i).1 ∧ N.Joins F (N.ends i).2 v) ∨
      (N.Joins F u (N.ends i).2 ∧ N.Joins F (N.ends i).1 v) := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
      rcases List.mem_cons.1 hab with hab | hab
      · rw [← hab]; exact Or.inr (Or.inl ⟨Joins.refl _ _, Joins.refl _ _⟩)
      · exact Or.inl (Relation.EqvGen.rel _ _ hab)
    | refl => exact Or.inl (Joins.refl _ _)
    | symm a b _ ih =>
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
      · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with A | ⟨A1, A2⟩ | ⟨A1, A2⟩ <;> rcases ih2 with B | ⟨B1, B2⟩ | ⟨B1, B2⟩
      · exact Or.inl (A.trans B)
      · exact Or.inr (Or.inl ⟨A.trans B1, B2⟩)
      · exact Or.inr (Or.inr ⟨A.trans B1, B2⟩)
      · exact Or.inr (Or.inl ⟨A1, A2.trans B⟩)
      · exact Or.inr (Or.inl ⟨A1, B2⟩)
      · exact Or.inl (A1.trans B2)
      · exact Or.inr (Or.inr ⟨A1, A2.trans B⟩)
      · exact Or.inl (A1.trans B2)
      · exact Or.inr (Or.inr ⟨A1, B2⟩)
  · have hsub : ∀ k ∈ F, k ∈ i :: F := fun k hk => List.mem_cons_of_mem _ hk
    have hi : N.Joins (i :: F) (N.ends i).1 (N.ends i).2 := joins_of_mem List.mem_cons_self
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact joins_mono hsub h
    · exact ((joins_mono hsub h1).trans hi).trans (joins_mono hsub h2)
    · exact ((joins_mono hsub h1).trans hi.symm).trans (joins_mono hsub h2)

/-- **A link whose ends are already joined adds nothing**: the merge that answers no leaves the
groups as they were. -/
theorem joins_cons_of_joins {F : List ℕ} {i : ℕ} (h : N.Joins F (N.ends i).1 (N.ends i).2)
    {u v : ℕ} : N.Joins (i :: F) u v ↔ N.Joins F u v := by
  rw [joins_cons_iff]
  constructor
  · rintro (h' | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h'
    · exact (h1.trans h).trans h2
    · exact (h1.trans h.symm).trans h2
  · exact Or.inl

theorem joins_append_singleton {F : List ℕ} {i u v : ℕ} :
    N.Joins (F ++ [i]) u v ↔ N.Joins (i :: F) u v :=
  joins_congr fun k => by simp [or_comm]

/-! ## Closing no cycle -/

/-- Closing no cycle, link by link: each link joins two vertices the links after it do not. -/
def Grows (N : LinkNetwork) : List ℕ → Prop
  | [] => True
  | i :: F => ¬ N.Joins F (N.ends i).1 (N.ends i).2 ∧ Grows N F

theorem grows_perm {F G : List ℕ} (h : F.Perm G) : N.Grows F ↔ N.Grows G := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [Grows, ih, joins_congr fun k => h.mem_iff]
  | swap x y l =>
    simp only [Grows]
    rw [joins_cons_iff, joins_cons_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun h => h1 ?_, fun h => h1 (Or.inl h), h3⟩
      rcases h with h | ⟨a, b⟩ | ⟨a, b⟩ <;>
        first
        | exact absurd h h2
        | exact Or.inr (Or.inl ⟨a.symm, b.symm⟩)
        | exact Or.inr (Or.inr ⟨b, a⟩)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun h => h1 ?_, fun h => h1 (Or.inl h), h3⟩
      rcases h with h | ⟨a, b⟩ | ⟨a, b⟩ <;>
        first
        | exact absurd h h2
        | exact Or.inr (Or.inl ⟨a.symm, b.symm⟩)
        | exact Or.inr (Or.inr ⟨b, a⟩)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem closesNoCycle_iff_grows {F : List ℕ} : N.ClosesNoCycle F ↔ N.Grows F := by
  constructor
  · intro h
    induction F with
    | nil => trivial
    | cons i F ih =>
      have hi : ¬ N.Joins F (N.ends i).1 (N.ends i).2 := by
        have := h i List.mem_cons_self
        rwa [List.erase_cons_head] at this
      refine ⟨hi, ih fun j hj hJ => ?_⟩
      have hji : j ≠ i := by rintro rfl; exact hi (joins_of_mem hj)
      refine h j (List.mem_cons_of_mem _ hj) (joins_mono (fun k hk => ?_) hJ)
      rw [List.erase_cons_tail (by simpa using hji.symm)]
      exact List.mem_cons_of_mem _ hk
  · intro h i hi
    have := (grows_perm (List.perm_cons_erase hi)).1 h
    exact this.1

/-- **A link added to links that close no cycle closes none** exactly when they do not join its
ends. -/
theorem closesNoCycle_cons_iff {F : List ℕ} {i : ℕ} :
    N.ClosesNoCycle (i :: F) ↔ ¬ N.Joins F (N.ends i).1 (N.ends i).2 ∧ N.ClosesNoCycle F := by
  simp only [closesNoCycle_iff_grows, Grows]

theorem ClosesNoCycle.erase {F : List ℕ} (h : N.ClosesNoCycle F) (f : ℕ) :
    N.ClosesNoCycle (F.erase f) := by
  by_cases hf : f ∈ F
  · exact (closesNoCycle_cons_iff.1 ((closesNoCycle_perm (List.perm_cons_erase hf)).1 h)).2
  · rwa [List.erase_of_not_mem hf]

/-! ## The exchange -/

/-- Adding the links `L` to `K` one at a time, some first link makes `a` and `b` joined when `K`
alone does not and `K` with all of `L` does. -/
theorem exists_first_join {K L : List ℕ} {a b : ℕ} (h0 : ¬ N.Joins K a b)
    (h : N.Joins (K ++ L) a b) :
    ∃ L₁ f L₂, L = L₁ ++ f :: L₂ ∧ ¬ N.Joins (K ++ L₁) a b ∧ N.Joins (f :: (K ++ L₁)) a b := by
  induction L generalizing K with
  | nil => exact absurd (by simpa using h) h0
  | cons f L ih =>
    by_cases hf : N.Joins (f :: K) a b
    · exact ⟨[], f, L, rfl, by simpa using h0, by simpa using hf⟩
    · obtain ⟨L₁, f', L₂, rfl, h1, h2⟩ :=
        ih (K := K ++ [f]) (fun h' => hf (joins_append_singleton.1 h')) (by simpa using h)
      exact ⟨f :: L₁, f', L₂, rfl, by simpa using h1, by simpa using h2⟩

/-- **The exchange.** Let `T` be a spanning forest, `K` some of its links, and `e` a link of the
graph outside `T` whose ends `K` does not join. Then some link `f` of `T` outside `K`, whose ends
`K` does not join either, can be swapped for `e`: `e` with the rest of `T` is a spanning forest
that still contains `K`. -/
theorem exchange {T K : List ℕ} {e : ℕ} (hT : N.IsSpanningForest T) (hK : ∀ i ∈ K, i ∈ T)
    (he : e < N.g.links.length) (heT : e ∉ T) (hKe : ¬ N.Joins K (N.ends e).1 (N.ends e).2) :
    ∃ f ∈ T, f ∉ K ∧ ¬ N.Joins K (N.ends f).1 (N.ends f).2 ∧
      N.IsSpanningForest (e :: T.erase f) ∧ ∀ i ∈ K, i ∈ T.erase f := by
  obtain ⟨hTl, hTj, hTc⟩ := hT
  set a := (N.ends e).1
  set b := (N.ends e).2
  have hTnd := hTc.nodup
  set L := T.filter fun t => t ∉ K
  have hab : N.Joins (K ++ L) a b :=
    joins_mono (fun t ht => by
      by_cases htK : t ∈ K
      · exact List.mem_append_left _ htK
      · exact List.mem_append_right _ (List.mem_filter.2 ⟨ht, by simpa using htK⟩))
      (joinsWhatGraphJoins_iff.1 hTj e he)
  obtain ⟨L₁, f, L₂, hL, h1, h2⟩ := exists_first_join hKe hab
  have hfL : f ∈ L := hL ▸ List.mem_append_right _ List.mem_cons_self
  have hfT : f ∈ T := (List.mem_filter.1 hfL).1
  have hfK : f ∉ K := by simpa using (List.mem_filter.1 hfL).2
  set x := (N.ends f).1
  set y := (N.ends f).2
  -- with `f`, the links before it join `a` to one end of `f` and the other end to `b`
  have hxy : (N.Joins (K ++ L₁) a x ∧ N.Joins (K ++ L₁) y b) ∨
      (N.Joins (K ++ L₁) a y ∧ N.Joins (K ++ L₁) x b) := by
    rcases joins_cons_iff.1 h2 with h | h | h
    · exact absurd h h1
    · exact Or.inl h
    · exact Or.inr h
  -- the links before `f` are links of `T` other than `f`
  have hsub : ∀ k ∈ K ++ L₁, k ∈ T.erase f := by
    intro k hk
    have hkf : k ≠ f := by
      rintro rfl
      rcases List.mem_append.1 hk with hk | hk
      · exact hfK hk
      · have hLnd : L.Nodup := hTnd.filter _
        rw [hL] at hLnd
        exact List.disjoint_of_nodup_append hLnd hk List.mem_cons_self
    refine (List.mem_erase_of_ne hkf).2 ?_
    rcases List.mem_append.1 hk with hk | hk
    · exact hK k hk
    · exact (List.mem_filter.1 (hL ▸ List.mem_append_left _ hk : k ∈ L)).1
  -- `T` without `f` does not join `a` and `b`
  have hTf : ¬ N.Joins (T.erase f) a b := by
    intro h
    refine hTc f hfT ?_
    rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact (((joins_mono hsub h3).symm.trans h).trans (joins_mono hsub h4).symm)
    · exact ((joins_mono hsub h4).trans h.symm).trans (joins_mono hsub h3)
  set T' := e :: T.erase f
  have hsub' : ∀ k ∈ T.erase f, k ∈ T' := fun k hk => List.mem_cons_of_mem _ hk
  have he' : N.Joins T' a b := joins_of_mem List.mem_cons_self
  -- `e` with the rest of `T` joins the two ends of `f`
  have hfx : N.Joins T' x y := by
    rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact (((joins_mono (fun k hk => hsub' k (hsub k hk)) h3).symm.trans he').trans
        (joins_mono (fun k hk => hsub' k (hsub k hk)) h4).symm)
    · exact ((joins_mono (fun k hk => hsub' k (hsub k hk)) h4).trans he'.symm).trans
        (joins_mono (fun k hk => hsub' k (hsub k hk)) h3)
  refine ⟨f, hfT, hfK, fun h => ?_, ⟨?_, ?_, ?_⟩, fun k hk => hsub k (List.mem_append_left _ hk)⟩
  · -- were the ends of `f` joined by `K`, the links before `f` would join `a` and `b`
    have h' := joins_mono (fun k hk => List.mem_append_left L₁ hk) h
    rcases hxy with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact h1 ((h3.trans h').trans h4)
    · exact h1 ((h3.trans h'.symm).trans h4)
  · intro k hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact he
    · exact hTl k (List.mem_of_mem_erase hk)
  · -- everything `T` joins, `e` with the rest of `T` joins
    intro u v huv
    have hT := (joins_congr fun k => (List.perm_cons_erase hfT).mem_iff).1 (hTj u v huv)
    rcases joins_cons_iff.1 hT with h | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact joins_mono hsub' h
    · exact ((joins_mono hsub' h3).trans hfx).trans (joins_mono hsub' h4)
    · exact ((joins_mono hsub' h3).trans hfx.symm).trans (joins_mono hsub' h4)
  · exact closesNoCycle_cons_iff.2 ⟨hTf, hTc.erase f⟩

/-- The total after the exchange: `f`'s cost out, `e`'s in. -/
theorem total_cons_erase {T : List ℕ} {f : ℕ} (hf : f ∈ T) (e : ℕ) :
    N.total (e :: T.erase f) + N.linkCost f = N.total T + N.linkCost e := by
  rw [total_perm (List.perm_cons_erase hf)]
  simp only [total, List.map_cons, List.sum_cons]
  omega

/-! ## A cheapest spanning forest -/

theorem exists_min {α : Type*} (f : α → ℤ) {l : List α} (h : l ≠ []) :
    ∃ x ∈ l, ∀ y ∈ l, f x ≤ f y := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
    by_cases hl : l = []
    · subst hl; exact ⟨a, List.mem_cons_self, by simp⟩
    · obtain ⟨x, hx, hmin⟩ := ih hl
      by_cases hax : f a ≤ f x
      · exact ⟨a, List.mem_cons_self, fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact le_rfl
          · exact hax.trans (hmin y hy)⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact (not_le.1 hax).le
          · exact hmin y hy⟩

/-- **Where there is a spanning forest, there is a cheapest one**: the cheapest among the
finitely many sets of link ids. -/
theorem exists_cheapestForest {F : List ℕ} (hF : N.IsSpanningForest F) :
    ∃ T, N.CheapestForest T := by
  set C := (List.range N.g.links.length).sublists.filter fun G => N.IsSpanningForest G
  obtain ⟨G, hG, hGp⟩ := hF.exists_sublist
  have hC : C ≠ [] := List.ne_nil_of_mem (List.mem_filter.2 ⟨hG,
    by simpa using (isSpanningForest_perm hGp).2 hF⟩)
  obtain ⟨T, hT, hmin⟩ := exists_min N.total hC
  have hTs : N.IsSpanningForest T := by simpa using (List.mem_filter.1 hT).2
  refine ⟨T, hTs, fun F' hF' => ?_⟩
  obtain ⟨G', hG', hp⟩ := hF'.exists_sublist
  rw [← total_perm hp]
  exact hmin G' (List.mem_filter.2 ⟨hG', by simpa using (isSpanningForest_perm hp).2 hF'⟩)

/-- **Part of a cheapest spanning forest, and a spanning forest itself, is a cheapest one**: it
has the same links. -/
theorem cheapestForest_of_part {T K : List ℕ} (hT : N.CheapestForest T) (hK : ∀ i ∈ K, i ∈ T)
    (hKj : N.JoinsWhatGraphJoins K) (hKc : N.ClosesNoCycle K) : N.CheapestForest K := by
  obtain ⟨⟨hTl, hTj, hTc⟩, hmin⟩ := hT
  have hTK : ∀ t ∈ T, t ∈ K := by
    intro t ht
    by_contra htK
    refine hTc t ht (joins_mono (fun k hk => ?_) (joinsWhatGraphJoins_iff.1 hKj t (hTl t ht)))
    exact (List.mem_erase_of_ne (by rintro rfl; exact htK hk)).2 (hK k hk)
  have hp : K.Perm T := (List.perm_ext_iff_of_nodup hKc.nodup hTc.nodup).2
    fun i => ⟨hK i, hTK i⟩
  refine ⟨(isSpanningForest_perm hp).2 ⟨hTl, hTj, hTc⟩, fun F' hF' => ?_⟩
  rw [total_perm hp]
  exact hmin F' hF'

end AlgoDesign.Paths.LinkNetwork

namespace AlgoDesign.Graphs.UnionFind

/-- **One group left**: on a legal, well-formed union-find whose count is 1, every two items are
together. -/
theorem same_of_count_eq_one {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) (h1 : u.count = 1)
    {i j : ℕ} (hi : i < u.n) (hj : j < u.n) : u.Same i j := by
  obtain ⟨hup, -, -⟩ := hu
  have hc := hw
  by_contra hne
  have hri : u.root i < u.n := iterate_lt (fun k hk => (hup k hk).1) hi u.n
  have hrj : u.root j < u.n := iterate_lt (fun k hk => (hup k hk).1) hj u.n
  have hsub : [u.root i, u.root j].Subperm ((List.range u.n).filter fun r => u.parent r = r) :=
    List.subperm_of_subset (by simpa [Same] using hne) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_filter.2 ⟨List.mem_range.2 hri, by simpa [IsRoot] using (hup i hi).2⟩
      · exact List.mem_filter.2 ⟨List.mem_range.2 hrj, by simpa [IsRoot] using (hup j hj).2⟩)
  have := hsub.length_le
  rw [← List.countP_eq_length_filter, ← hc, h1] at this
  simp at this

end AlgoDesign.Graphs.UnionFind
