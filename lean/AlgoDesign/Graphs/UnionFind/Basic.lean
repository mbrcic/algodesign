/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Decide
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup

/-!
# Union-find: paths upward

Facts about following the links upward. While every link stays among the items and ranks rise
toward the root, a path upward visits no item twice, so it reaches a root in fewer than `n` steps
and stays there (`upwardEndsAtRoot_of_ranksRise`). Then `root i` is the one root a path from `i`
reaches (`root_eq_of_iterate`), and the proofs reason about paths, not about exact `n`-fold
iterates. `valid_init` and `wellFormed_init`: every item alone is a legal, well-formed start.
`pieces_iff_valid_wellFormed`: the box's pieces and the count together are `Valid` and
`WellFormed`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

/-- **Every item alone**: each its own root, of rank 0, so `n` groups. -/
def init (n : ℕ) : UnionFind := ⟨n, id, fun _ => 0, n⟩

/-! ## What the operations owe -/

/-- **What a lookup of `x` owes**, `res` being the structure after it and the answer: the answer
is `x`'s root; every item keeps its root, so a lookup never changes who is together; each item now
points at an item at least one step up its old path (a step, not one of the box's invariants);
every item on the walk from `x` now points straight at the root, and no other item moves (the
idea's "a lookup points everything it walked through straight at the root"); ranks, the count and
the items are untouched. The walk is the items within `n` links up from `x`: on a valid structure,
`x`'s whole path to its root. -/
structure FindSpec (u : UnionFind) (x : ℕ) (res : UnionFind × ℕ) : Prop where
  /-- The answer is `x`'s root. -/
  answer : res.2 = u.root x
  /-- A lookup never changes who is together: every item keeps its root. -/
  same_root : ∀ i < u.n, res.1.root i = u.root i
  /-- Box invariant 3: shortening only points an item at another item higher up in its own
  tree. -/
  points_higher : ∀ i < u.n, ∃ k, 0 < k ∧ u.parent^[k] i = res.1.parent i
  /-- Every item on the walk from `x` now points straight at the root. -/
  compresses : ∀ k < u.n, res.1.parent (u.parent^[k] x) = u.root x
  /-- No item off the walk moves. -/
  others_kept : ∀ i, (∀ k < u.n, u.parent^[k] x ≠ i) → res.1.parent i = u.parent i
  /-- The items stay the same. -/
  n_eq : res.1.n = u.n
  /-- Ranks are untouched. -/
  rank_eq : res.1.rank = u.rank
  /-- The count is untouched. -/
  count_eq : res.1.count = u.count

/-- **What a merge of `x` and `y` owes**, `res` being the structure after it and the answer. If they
are already together: nothing merges, the answer is no, and ranks and the count stay. Otherwise:
exactly their two groups join and no other changes, the answer is yes, and the count drops by one.
On equal ranks the first root stays a root. -/
structure UnionSpec (u : UnionFind) (x y : ℕ) (res : UnionFind × Bool) : Prop where
  /-- The items stay the same. -/
  n_eq : res.1.n = u.n
  /-- The answer is yes exactly when the two were apart. -/
  answer : res.2 = true ↔ ¬ u.Same x y
  /-- Exactly the two named groups join, and no other changes. -/
  groups : ∀ i < u.n, ∀ j < u.n,
    res.1.Same i j ↔ u.Same i j ∨ (u.Same i x ∧ u.Same j y) ∨ (u.Same i y ∧ u.Same j x)
  /-- Merging two items already together keeps ranks and the count. -/
  together : u.Same x y → res.1.rank = u.rank ∧ res.1.count = u.count
  /-- A real merge drops the count by one. -/
  count_merge : ¬ u.Same x y → res.1.count + 1 = u.count
  /-- On equal ranks the first root stays a root. -/
  tie : ¬ u.Same x y → u.rank (u.root x) = u.rank (u.root y) → res.1.root x = u.root x

/-- **What the question "are `x` and `y` joined yet?" owes**, `res` being the structure after it
and the answer: yes exactly when they are together, and asking changes no one's group. -/
structure JoinedSpec (u : UnionFind) (x y : ℕ) (res : UnionFind × Bool) : Prop where
  /-- The items stay the same. -/
  n_eq : res.1.n = u.n
  /-- The answer is yes exactly when the two are together. -/
  answer : res.2 = true ↔ u.Same x y
  /-- Asking never changes who is together. -/
  same : ∀ i < u.n, ∀ j < u.n, res.1.Same i j ↔ u.Same i j
  /-- The count is untouched. -/
  count_eq : res.1.count = u.count

/-! ## The groups after a run of merges -/

/-- **Joined by a run of merges**: `x` and `y` are linked by a chain of merged pairs, each pair
read either way, and every item is joined to itself. The groups after the run are the classes of
this relation. -/
def Joined (us : List (ℕ × ℕ)) : ℕ → ℕ → Prop :=
  Relation.EqvGen (fun a b => (a, b) ∈ us)

variable {u : UnionFind}

/-- A path upward from an item stays among the items. -/
theorem iterate_lt (h : ∀ i < u.n, u.parent i < u.n) {i : ℕ} (hi : i < u.n) (k : ℕ) :
    u.parent^[k] i < u.n := by
  induction k with
  | zero => exact hi
  | succ k ih => rw [Function.iterate_succ_apply']; exact h _ ih

/-- From a root, the path upward stays put. -/
theorem iterate_root {r : ℕ} (hr : u.IsRoot r) (k : ℕ) : u.parent^[k] r = r :=
  Function.iterate_fixed hr k

/-- Once a path upward reaches a root, it stays there. -/
theorem iterate_add_of_root {i k : ℕ} (hk : u.IsRoot (u.parent^[k] i)) (m : ℕ) :
    u.parent^[m + k] i = u.parent^[k] i := by
  rw [Function.iterate_add_apply, iterate_root hk]

/-- Ranks do not fall along a path upward. -/
theorem rank_le_iterate (h : ∀ i < u.n, u.parent i < u.n) (hr : u.RanksRiseUpward) {i : ℕ}
    (hi : i < u.n) (k : ℕ) : u.rank i ≤ u.rank (u.parent^[k] i) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hp : u.parent (u.parent^[k] i) = u.parent^[k] i
    · rwa [hp]
    · exact ih.trans (hr _ (iterate_lt h hi k) hp).le

/-- Ranks rise strictly along a path upward that has not yet met a root. -/
theorem rank_lt_iterate (h : ∀ i < u.n, u.parent i < u.n) (hr : u.RanksRiseUpward) {i : ℕ}
    (hi : i < u.n) {k j : ℕ} (hjk : j < k) (hk : ¬ u.IsRoot (u.parent^[k] i)) :
    u.rank (u.parent^[j] i) < u.rank (u.parent^[k] i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjk
  have hj : ¬ u.IsRoot (u.parent^[j] i) := fun hj => hk (by
    rw [show j + m + 1 = (m + 1) + j by omega, iterate_add_of_root hj]; exact hj)
  have hstep := hr _ (iterate_lt h hi j) hj
  calc u.rank (u.parent^[j] i) < u.rank (u.parent^[j + 1] i) := by
        rwa [Function.iterate_succ_apply']
    _ ≤ u.rank (u.parent^[m] (u.parent^[j + 1] i)) :=
        rank_le_iterate h hr (iterate_lt h hi (j + 1)) m
    _ = u.rank (u.parent^[j + m + 1] i) := by
        rw [← Function.iterate_add_apply, show m + (j + 1) = j + m + 1 by omega]

/-- **Invariant 1 from invariant 2a**: while every link stays among the items and ranks rise
toward the root, `n` steps up from any item reach a root. Otherwise the first `n + 1` items on
the path would be distinct, by their rising ranks, yet only `n` items exist. -/
theorem upwardEndsAtRoot_of_ranksRise (h : ∀ i < u.n, u.parent i < u.n)
    (hr : u.RanksRiseUpward) : u.UpwardEndsAtRoot := by
  intro i hi
  refine ⟨h i hi, ?_⟩
  by_contra hn
  have hinj : Function.Injective (fun k : Fin (u.n + 1) =>
      (⟨u.parent^[k] i, iterate_lt h hi k⟩ : Fin u.n)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    have hne : ∀ c : Fin (u.n + 1), ¬ u.IsRoot (u.parent^[c] i) := fun c hc => hn (by
      unfold root
      rw [show u.n = (u.n - c) + c by omega, iterate_add_of_root hc]; exact hc)
    rcases lt_trichotomy a b with hab' | hab' | hab'
    · exact absurd (congrArg u.rank hab) (rank_lt_iterate h hr hi hab' (hne b)).ne
    · exact hab'
    · exact absurd (congrArg u.rank hab) (rank_lt_iterate h hr hi hab' (hne a)).ne'
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, Fintype.card_fin] at this
  omega

/-- On a valid structure, `root i` is the root that any path upward from `i` reaches. -/
theorem root_eq_of_iterate (hv : u.UpwardEndsAtRoot) {i : ℕ} (hi : i < u.n) {k r : ℕ}
    (hk : u.parent^[k] i = r) (hr : u.IsRoot r) : u.root i = r := by
  have hroot := (hv i hi).2
  unfold root at hroot ⊢
  rcases le_total k u.n with hkn | hkn
  · rw [show u.n = (u.n - k) + k by omega, Function.iterate_add_apply, hk, iterate_root hr]
  · rw [← hk, show k = (k - u.n) + u.n by omega, Function.iterate_add_apply,
      iterate_root hroot]

/-- On a valid structure, every path upward from `i` that reaches a root reaches `root i`. -/
theorem iterate_eq_root (hv : u.UpwardEndsAtRoot) {i : ℕ} (hi : i < u.n) {k : ℕ}
    (hk : u.IsRoot (u.parent^[k] i)) : u.parent^[k] i = u.root i :=
  (root_eq_of_iterate hv hi rfl hk).symm

/-- A root is its own root. -/
theorem root_of_isRoot {r : ℕ} (hr : u.IsRoot r) : u.root r = r := iterate_root hr _

/-- Following the links upward from `i` for at least `n` steps lands on `root i`. -/
theorem iterate_eq_root_of_le (hv : u.UpwardEndsAtRoot) {i : ℕ} (hi : i < u.n) {k : ℕ}
    (hk : u.n ≤ k) : u.parent^[k] i = u.root i := by
  unfold root
  rw [show k = (k - u.n) + u.n by omega, iterate_add_of_root (hv i hi).2]

/-- **The pieces split into the box's and the rest**: the box's pieces and the count are exactly
`Valid` and `WellFormed`. -/
theorem pieces_iff_valid_wellFormed (u : UnionFind) :
    (UpwardEndsAtRoot u ∧ RanksRiseUpward u ∧ RootRankBoundsSize u ∧ CountIsRoots u) ↔
      Valid u ∧ WellFormed u := by
  simp only [Valid, WellFormed, and_assoc]

/-- **Every item alone is legal.** -/
theorem valid_init (n : ℕ) : (init n).Valid := by
  have hroot : ∀ i, (init n).root i = i := fun i => root_of_isRoot rfl
  refine ⟨fun i hi => ⟨hi, (hroot i).symm ▸ rfl⟩, fun i _ h => absurd rfl h,
    fun r hr _ => ?_⟩
  simp only [hroot]
  exact List.countP_pos_iff.2 ⟨r, List.mem_range.2 hr, by simp⟩

/-- **Every item alone is well formed.** -/
theorem wellFormed_init (n : ℕ) : (init n).WellFormed := by
  simp [WellFormed, CountIsRoots, init]

end AlgoDesign.Graphs.UnionFind
