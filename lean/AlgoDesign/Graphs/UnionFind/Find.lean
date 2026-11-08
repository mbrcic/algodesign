/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Basic

/-!
# Union-find: the lookup

`find` is CLRS's `FIND-SET` (§19.3, p. 530) with full path compression: walk up to the root, and on
the way back point every item walked straight at it. The walk is given `n` steps, as many as there
are items; on a valid structure no path upward is that long.

The walk sends every item it passes at least one step up its old path (`findAux_jumps`), and any
such repointing keeps `Valid`, `WellFormed` and every item's root (`valid_of_jumps`). So
`find_spec`: `find` discharges `FindSpec`; `valid_find`: a lookup keeps the structure legal and well
formed.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

/-- The walk behind `find`, with `fuel` steps: the parents after compression, and the root reached.
If `x` is not a root, look up its parent's root, then point `x` at it. -/
def findAux : ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) × ℕ
  | 0, p, x => (p, x)
  | f + 1, p, x =>
    if p x = x then (p, x)
    else
      let pr := findAux f p (p x)
      (Function.update pr.1 x pr.2, pr.2)

/-- **Lookup**: the root of `x`'s group, and the structure with every item on the walk pointing
straight at it. -/
def find (u : UnionFind) (x : ℕ) : UnionFind × ℕ :=
  let pr := findAux u.n u.parent x
  ({ u with parent := pr.1 }, pr.2)

/-! ## What the walk does -/

/-- The walk answers where `fuel` steps up from `x` lead; it stops early only at a root, which
stays put. -/
theorem findAux_snd (fuel : ℕ) (p : ℕ → ℕ) (x : ℕ) : (findAux fuel p x).2 = p^[fuel] x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ f ih =>
    unfold findAux
    split_ifs with hx
    · exact (Function.iterate_fixed hx _).symm
    · exact ih (p x)

/-- After the walk, each item keeps its link, or it was walked and now points at the answer. -/
theorem findAux_fst (fuel : ℕ) (p : ℕ → ℕ) (x j : ℕ) :
    (findAux fuel p x).1 j = p j ∨
      ∃ k < fuel, p^[k] x = j ∧ (findAux fuel p x).1 j = p^[fuel] x := by
  induction fuel generalizing x with
  | zero => exact Or.inl rfl
  | succ f ih =>
    unfold findAux
    split_ifs with hx
    · exact Or.inl rfl
    · simp only
      rcases eq_or_ne j x with rfl | hj
      · refine Or.inr ⟨0, by omega, rfl, ?_⟩
        rw [Function.update_self, findAux_snd, Function.iterate_succ_apply]
      · rw [Function.update_of_ne hj]
        rcases ih (p x) with h | ⟨k, hk, hkj, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨k + 1, by omega, by rwa [Function.iterate_succ_apply], h⟩

/-- After the walk, each item points somewhere at least one step up its old path. -/
theorem findAux_jumps (fuel : ℕ) (p : ℕ → ℕ) (x j : ℕ) :
    ∃ m, 0 < m ∧ p^[m] j = (findAux fuel p x).1 j := by
  rcases findAux_fst fuel p x j with h | ⟨k, hk, rfl, h⟩
  · exact ⟨1, one_pos, h.symm⟩
  · refine ⟨fuel - k, by omega, ?_⟩
    rw [h, ← Function.iterate_add_apply, Nat.sub_add_cancel hk.le]

/-! ## Repointing items up their own paths -/

/-- **Pointing items higher up their own paths keeps a structure legal and every item's root.**
The new links `q` send each item at least one step up its old path. -/
theorem valid_of_jumps {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {q : ℕ → ℕ}
    (hq : ∀ j < u.n, ∃ m, 0 < m ∧ u.parent^[m] j = q j) :
    (({ u with parent := q } : UnionFind).Valid ∧ ({ u with parent := q } : UnionFind).WellFormed) ∧
      ∀ i < u.n, ({ u with parent := q } : UnionFind).root i = u.root i := by
  obtain ⟨hup, hrise, hsize⟩ := hu
  have hcount : u.CountIsRoots := hw
  have hlt : ∀ i < u.n, u.parent i < u.n := fun i hi => (hup i hi).1
  set v : UnionFind := { u with parent := q } with hv
  have hroots : ∀ r < u.n, (q r = r ↔ u.IsRoot r) := by
    intro r hr
    obtain ⟨m, hm, he⟩ := hq r hr
    constructor
    · intro hqr
      by_contra hp
      have := rank_lt_iterate hlt hrise hr (j := 0) hm (by rwa [he, hqr])
      rw [he, hqr] at this
      exact lt_irrefl _ this
    · intro hp
      rw [← he, iterate_root hp]
  have hvlt : ∀ i < v.n, v.parent i < v.n := by
    intro i hi
    obtain ⟨m, -, he⟩ := hq i hi
    change q i < u.n
    rw [← he]
    exact iterate_lt hlt hi m
  have hvrise : v.RanksRiseUpward := by
    intro i hi hne
    obtain ⟨m, hm, he⟩ := hq i hi
    have hp : u.parent i ≠ i := fun hp => hne (by
      change q i = i
      rw [← he, iterate_root hp])
    have h1 := hrise i hi hp
    have h2 := rank_le_iterate hlt hrise (hlt i hi) (m - 1)
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hm, he] at h2
    exact h1.trans_le h2
  have hvup := upwardEndsAtRoot_of_ranksRise hvlt hvrise
  have hpath : ∀ i < u.n, ∀ t, ∃ s, t ≤ s ∧ q^[t] i = u.parent^[s] i := by
    intro i hi t
    induction t with
    | zero => exact ⟨0, le_rfl, rfl⟩
    | succ t ih =>
      obtain ⟨s, hs, he⟩ := ih
      obtain ⟨m, hm, hm'⟩ := hq _ (iterate_lt hlt hi s)
      refine ⟨m + s, by omega, ?_⟩
      rw [Function.iterate_succ_apply', he, ← hm', Function.iterate_add_apply]
  have hvroot : ∀ i < u.n, v.root i = u.root i := by
    intro i hi
    obtain ⟨s, hs, he⟩ := hpath i hi u.n
    exact he.trans (iterate_eq_root_of_le hup hi hs)
  refine ⟨⟨⟨hvup, hvrise, ?_⟩, ?_⟩, hvroot⟩
  · intro r hr hvr
    have hur : u.IsRoot r := (hroots r hr).1 hvr
    refine (hsize r hr hur).trans_eq (List.countP_congr fun i hi => ?_)
    rw [hvroot i (List.mem_range.1 hi)]
  · refine hcount.trans (List.countP_congr fun r hr => ?_)
    simpa [v, IsRoot] using (hroots r (List.mem_range.1 hr)).symm

/-! ## The lookup keeps its promise -/

/-- After the walk, every item it passed points at the answer. -/
theorem findAux_compresses (fuel : ℕ) (p : ℕ → ℕ) (x : ℕ) :
    ∀ k < fuel, (findAux fuel p x).1 (p^[k] x) = p^[fuel] x := by
  induction fuel generalizing x with
  | zero => intro k hk; omega
  | succ f ih =>
    intro k hk
    unfold findAux
    split_ifs with hx
    · simp only [Function.iterate_fixed hx]
      exact hx
    · simp only
      rcases k with _ | k
      · rw [Function.iterate_zero_apply, Function.update_self, findAux_snd,
          Function.iterate_succ_apply]
      · rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        rcases eq_or_ne (p^[k] (p x)) x with he | he
        · rw [he, Function.update_self, findAux_snd]
        · rw [Function.update_of_ne he, ih (p x) k (by omega)]

/-- **A lookup keeps its promise**: it answers `x`'s root, keeps every item's root, points every
item on its walk straight at the root and moves no other. No bound on `x` is needed: from any start
the walk keeps every root. -/
theorem find_spec {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) (x : ℕ) :
    FindSpec u x (u.find x) where
  answer := findAux_snd _ _ _
  same_root := (valid_of_jumps hu hw fun j _ => findAux_jumps u.n u.parent x j).2
  points_higher i _ := findAux_jumps u.n u.parent x i
  compresses := findAux_compresses u.n u.parent x
  others_kept i hi := by
    rcases findAux_fst u.n u.parent x i with h | ⟨k, hk, hki, -⟩
    · exact h
    · exact absurd hki (hi k hk)
  n_eq := rfl
  rank_eq := rfl
  count_eq := rfl

/-- **A lookup keeps the structure legal and well formed.** -/
theorem valid_find {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) (x : ℕ) :
    (u.find x).1.Valid ∧ (u.find x).1.WellFormed :=
  (valid_of_jumps hu hw fun j _ => findAux_jumps u.n u.parent x j).1

/-! ## Examples, checked by the kernel -/

/-- One group of four with root 3: `0 → 1 → 3` and `2 → 3`, ranks 0, 1, 0, 2. -/
def twoDeep : UnionFind :=
  ⟨4, fun i => if i = 0 then 1 else 3, fun i => if i = 1 then 1 else if i = 3 then 2 else 0, 1⟩

example : twoDeep.Valid ∧ twoDeep.WellFormed := by decide

/-- Looking up 0 answers 3 and points 0 straight at it. -/
example : (twoDeep.find 0).2 = 3 ∧ (twoDeep.find 0).1.parent 0 = 3 := by decide

example : (twoDeep.find 0).1.Valid ∧ (twoDeep.find 0).1.WellFormed := by decide

/-- Rank does not shrink when a path does: 1 keeps rank 1 with no item below it. -/
example : (twoDeep.find 0).1.rank 1 = 1 := by decide

end AlgoDesign.Graphs.UnionFind
