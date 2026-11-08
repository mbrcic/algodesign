/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Union

/-!
# Union-find: the promise over a run of merges

On any valid structure the question answers who is together, `Same` (`joined_iff_same`), the
lookup answers agree exactly when two items are together (`find_eq_find_iff_same`), and asking
changes no one's group (`same_joined_iff`). These need only `Valid` and `WellFormed`, not a
history.

From every item alone, after a run of merges `us` with every pair among the items, the structure
is legal and well formed (`valid_unions`) and two items are together exactly when the run joined
them, `Joined us` (`same_unions_iff`), so the question answers exactly that
(`joined_unions_iff`). The proof adds one merge at a time, from the end of the run, through
`UnionSpec.groups`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

/-! ## A valid structure suffices -/

/-- **Two lookups give the same answer exactly when the items are together.** -/
theorem find_eq_find_iff_same {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) (x y : ℕ) :
    (u.find x).2 = (u.find y).2 ↔ u.Same x y := by
  rw [(find_spec hu hw x).answer, (find_spec hu hw y).answer]
  rfl

/-- **The question answers who is together**, on any valid structure. Only `y` needs to be an
item: the lookup of `x` runs first and must keep `y`'s root. -/
theorem joined_iff_same {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ}
    (hy : y < u.n) :
    (u.joined x y).2 = true ↔ u.Same x y := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, hrx, hry⟩ := find_find hu hw hy h1 h2
  simp only [joined, h1, h2, beq_iff_eq, Same, hrx, hry]

/-- **Asking changes no one's group**: after the question, two items are together exactly when
they were before. -/
theorem same_joined_iff {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ}
    (hy : y < u.n) {i j : ℕ} (hi : i < u.n) (hj : j < u.n) :
    (u.joined x y).1.Same i j ↔ u.Same i j := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  obtain ⟨-, -, -, -, hroot, -, -⟩ := find_find hu hw hy h1 h2
  simp only [joined, h1, h2, Same, hroot i hi, hroot j hj]

/-- **The question keeps its promise**: it answers who is together, changes no one's group, and
keeps the items and the count. -/
theorem joined_spec {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hy : y < u.n) :
    JoinedSpec u x y (u.joined x y) := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  obtain ⟨-, hn, -, hc, -, -, -⟩ := find_find hu hw hy h1 h2
  exact { n_eq := by simp only [joined, h1, h2, hn]
          answer := joined_iff_same hu hw hy
          same := fun _ hi _ hj => same_joined_iff hu hw hy hi hj
          count_eq := by simp only [joined, h1, h2, hc] }

/-! ## A run of merges -/

/-- Merging a run in two parts merges the first part, then the second. -/
theorem unions_append (u : UnionFind) (us vs : List (ℕ × ℕ)) :
    u.unions (us ++ vs) = (u.unions us).unions vs := by
  induction us generalizing u with
  | nil => rfl
  | cons p us ih => exact ih _

/-- **A run of merges keeps the structure legal and well formed and the items the same**, when
every pair is among the items. -/
theorem valid_unions {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {us : List (ℕ × ℕ)}
    (hus : ∀ p ∈ us, p.1 < u.n ∧ p.2 < u.n) :
    ((u.unions us).Valid ∧ (u.unions us).WellFormed) ∧ (u.unions us).n = u.n := by
  induction us generalizing u with
  | nil => exact ⟨⟨hu, hw⟩, rfl⟩
  | cons p us ih =>
    obtain ⟨hx, hy⟩ := hus p List.mem_cons_self
    have hn := (union_spec hu hw hx hy).n_eq
    have hvu := valid_union hu hw hx hy
    obtain ⟨hv, hvn⟩ := ih hvu.1 hvu.2 fun q hq => hn ▸ hus q (List.mem_cons_of_mem _ hq)
    exact ⟨hv, hvn.trans hn⟩

/-- With no merges, each item is joined only to itself. -/
theorem joined_nil_iff {i j : ℕ} : Joined [] i j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ Relation.EqvGen.refl i⟩
  induction h with
  | rel _ _ h => simp at h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- From every item alone, after a run of merges, two items are together exactly when the run
joined them; the structure is legal and well formed and keeps its items. -/
theorem unions_init (n : ℕ) (us : List (ℕ × ℕ)) (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n) :
    (((init n).unions us).Valid ∧ ((init n).unions us).WellFormed) ∧ ((init n).unions us).n = n ∧
      ∀ i < n, ∀ j < n, (((init n).unions us).Same i j ↔ Joined us i j) := by
  induction us using List.reverseRecOn with
  | nil =>
    have hroot : ∀ k, (init n).root k = k := fun k => root_of_isRoot rfl
    refine ⟨⟨valid_init n, wellFormed_init n⟩, rfl, fun i _ j _ => ?_⟩
    rw [joined_nil_iff]
    exact Eq.congr (hroot i) (hroot j)
  | append_singleton us p ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨⟨hv, hw⟩, hn, hsame⟩ := ih fun q hq => hus q (List.mem_append_left _ hq)
    obtain ⟨ha, hb⟩ := hus (a, b) (List.mem_append_right _ (List.mem_singleton_self _))
    set v := (init n).unions us
    have hrun : (init n).unions (us ++ [(a, b)]) = (v.union a b).1 := by
      rw [unions_append]; rfl
    have hspec := union_spec hv hw (hn ▸ ha) (hn ▸ hb)
    have hmono : ∀ i j, Joined us i j → Joined (us ++ [(a, b)]) i j :=
      fun i j => Relation.EqvGen.mono (fun c d h => List.mem_append_left _ h) i j
    have hab : Joined (us ++ [(a, b)]) a b :=
      Relation.EqvGen.rel _ _ (List.mem_append_right _ (List.mem_singleton_self _))
    -- each merged pair, old or new, ends together; `Same` is an equivalence on every item
    have hback : ∀ i j, Joined (us ++ [(a, b)]) i j → (v.union a b).1.Same i j := by
      intro i j h
      induction h with
      | rel c d h =>
        rcases List.mem_append.1 h with h | h
        · obtain ⟨hc, hd⟩ := hus (c, d) (List.mem_append_left _ h)
          exact (hspec.groups c (hn ▸ hc) d (hn ▸ hd)).2
            (Or.inl ((hsame c hc d hd).2 (Relation.EqvGen.rel _ _ h)))
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.1 h)
          exact (hspec.groups c (hn ▸ ha) d (hn ▸ hb)).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    rw [hrun]
    refine ⟨valid_union hv hw (hn ▸ ha) (hn ▸ hb), hspec.n_eq.trans hn,
      fun i hi j hj => ⟨fun h => ?_, hback i j⟩⟩
    rcases (hspec.groups i (hn ▸ hi) j (hn ▸ hj)).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hmono _ _ ((hsame i hi j hj).1 h)
    · exact ((hmono _ _ ((hsame i hi a ha).1 h1)).trans _ _ _ hab).trans _ _ _
        (hmono _ _ ((hsame j hj b hb).1 h2)).symm
    · exact ((hmono _ _ ((hsame i hi b hb).1 h1)).trans _ _ _ hab.symm).trans _ _ _
        (hmono _ _ ((hsame j hj a ha).1 h2)).symm

/-- **The promise over a run of merges**: from every item alone, after merging each pair of `us` in
turn, two items are together exactly when the run joined them. -/
theorem same_unions_iff {n : ℕ} {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n) {x y : ℕ}
    (hx : x < n) (hy : y < n) : ((init n).unions us).Same x y ↔ Joined us x y :=
  (unions_init n us hus).2.2 x hx y hy

/-- **The question answers the promise**: after the run, `joined` says yes exactly when the run
joined the two. -/
theorem joined_unions_iff {n : ℕ} {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n)
    {x y : ℕ} (hx : x < n) (hy : y < n) :
    (((init n).unions us).joined x y).2 = true ↔ Joined us x y := by
  obtain ⟨⟨hv, hw⟩, hn, -⟩ := unions_init n us hus
  rw [joined_iff_same hv hw (by rw [hn]; exact hy), same_unions_iff hus hx hy]

/-- Merging `0` with `1`, then `2` with `1`, joins `0` and `2` and leaves `3` alone. -/
example : (((init 4).unions [(0, 1), (2, 1)]).joined 0 2).2 = true ∧
    (((init 4).unions [(0, 1), (2, 1)]).joined 0 3).2 = false := by
  decide

end AlgoDesign.Graphs.UnionFind
