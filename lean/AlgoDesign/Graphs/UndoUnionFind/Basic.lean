/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UndoUnionFind.Decide
public import AlgoDesign.Graphs.UnionFind.Union

/-!
# Union-find with undo: the operations

`merge` is the union-find's merge without compression: both roots are read off the links, `x`'s
first, then `y`'s; the same root merges nothing; the root of lower rank goes under the other; on
equal ranks the second root goes under the first, whose rank rises by one. It hands back the
entry it logs. `union` logs that entry; `undo` takes back the newest entry with `unmerge`.

`unmerge_merge`: taking back the entry a merge logged gives the structure before it, so
`undo_union`: undo right after union gives back the state before it. `merge_spec`: the merge keeps
the union-find's promise `UnionSpec`. `valid_init`, `valid_union` and `valid_undo` keep `Valid`.
`pieces_iff_valid`: `Valid` is the union-find's pieces, the count's included, on the structure and
on every structure the log rolls back to.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UndoUnionFind

/-- **Merge without compression** the groups of `x` and `y`: the structure after it, and the
entry it logs, `none` when they were already together. -/
def merge (u : UnionFind) (x y : ℕ) : UnionFind × Option (ℕ × Bool) :=
  let rx := u.root x
  let ry := u.root y
  if rx = ry then (u, none)
  else if u.rank rx < u.rank ry then
    ({ u with parent := Function.update u.parent rx ry, count := u.count - 1 }, some (rx, false))
  else if u.rank ry < u.rank rx then
    ({ u with parent := Function.update u.parent ry rx, count := u.count - 1 }, some (ry, false))
  else
    ({ u with parent := Function.update u.parent ry rx,
              rank := Function.update u.rank rx (u.rank rx + 1),
              count := u.count - 1 }, some (ry, true))

/-- **Every item alone**, the log empty. -/
def init (n : ℕ) : UndoUnionFind := ⟨UnionFind.init n, []⟩

/-- **Lookup**: `x`'s root, walking up; nothing changes. -/
def find (s : UndoUnionFind) (x : ℕ) : ℕ := s.uf.root x

/-- **Merge** the groups of `x` and `y`, logging one entry; the answer says whether two groups
became one. -/
def union (s : UndoUnionFind) (x y : ℕ) : UndoUnionFind × Bool :=
  let r := merge s.uf x y
  (⟨r.1, r.2 :: s.log⟩, r.2.isSome)

/-- **Are `x` and `y` joined?** Both are looked up, `x` first. -/
def joined (s : UndoUnionFind) (x y : ℕ) : Bool := s.find x == s.find y

/-- **The number of groups.** -/
def count (s : UndoUnionFind) : ℕ := s.uf.count

/-- **Take back the newest `union` call**; on an empty log nothing changes and the answer is no. -/
def undo (s : UndoUnionFind) : UndoUnionFind × Bool :=
  match s.log with
  | [] => (s, false)
  | e :: log => (⟨unmerge s.uf e, log⟩, true)

/-! ## Facts about a legal union-find -/

variable {u : UnionFind}

/-- On a legal union-find, an item's root is a root among the items. -/
theorem root_isRoot_lt (hu : u.Valid) {x : ℕ} (hx : x < u.n) :
    u.IsRoot (u.root x) ∧ u.root x < u.n :=
  ⟨(hu.1 x hx).2, UnionFind.iterate_lt (fun i hi => (hu.1 i hi).1) hx _⟩

/-- A well-formed union-find over at least one item has at least one group. -/
theorem count_pos (hw : u.WellFormed) {r : ℕ} (hr : r < u.n) (hrr : u.IsRoot r) :
    0 < u.count := by
  rw [hw]
  exact List.countP_pos_iff.2 ⟨r, List.mem_range.2 hr, by simpa [UnionFind.IsRoot] using hrr⟩

/-! ## Taking back a merge -/

/-- Taking back a link of root `a` under `b` gives the structure before it. -/
theorem unmerge_link {a : ℕ} (b : ℕ) (ha : u.IsRoot a) (hc : 0 < u.count) :
    unmerge { u with parent := Function.update u.parent a b, count := u.count - 1 }
      (some (a, false)) = u := by
  obtain ⟨n, p, r, c⟩ := u
  simp only [UnionFind.IsRoot] at ha
  simp only [unmerge, Function.update_idem, Bool.false_eq_true, ↓reduceIte, UnionFind.mk.injEq,
    true_and]
  exact ⟨Function.update_eq_self_iff.2 ha.symm, by simp only at hc; omega⟩

/-- Taking back a link of root `a` under `b` whose rank rose gives the structure before it. -/
theorem unmerge_link_rose {a b : ℕ} (ha : u.IsRoot a) (hc : 0 < u.count) :
    unmerge { u with parent := Function.update u.parent a b,
                     rank := Function.update u.rank b (u.rank b + 1),
                     count := u.count - 1 } (some (a, true)) = u := by
  obtain ⟨n, p, r, c⟩ := u
  simp only [UnionFind.IsRoot] at ha
  simp only [unmerge, Function.update_idem, Function.update_self, ↓reduceIte,
    UnionFind.mk.injEq, true_and, Nat.add_sub_cancel]
  exact ⟨Function.update_eq_self_iff.2 ha.symm, Function.update_eq_self _ _,
    by simp only at hc; omega⟩

/-- **Taking back the entry a merge logged gives the structure before it.** -/
theorem unmerge_merge (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hx : x < u.n)
    (hy : y < u.n) : unmerge (merge u x y).1 (merge u x y).2 = u := by
  obtain ⟨hrx, hrxn⟩ := root_isRoot_lt hu hx
  obtain ⟨hry, -⟩ := root_isRoot_lt hu hy
  have hc := count_pos hw hrxn hrx
  simp only [merge]
  split_ifs
  · rfl
  · exact unmerge_link _ hrx hc
  · exact unmerge_link _ hry hc
  · exact unmerge_link_rose hry hc

/-! ## The merge keeps the structure legal and the union-find's promise -/

/-- **A merge keeps the union-find legal and well formed.** -/
theorem valid_merge (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hx : x < u.n) (hy : y < u.n) :
    (merge u x y).1.Valid ∧ (merge u x y).1.WellFormed := by
  obtain ⟨hrxr, hrxn⟩ := root_isRoot_lt hu hx
  obtain ⟨hryr, hryn⟩ := root_isRoot_lt hu hy
  have hsx := hu.2.2 _ hrxn hrxr
  have hsy := hu.2.2 _ hryn hryr
  simp only [merge]
  split_ifs with heq hlt hgt
  · exact ⟨hu, hw⟩
  · exact (UnionFind.valid_link hu hw hrxn hryn hrxr hryr heq (fun _ _ => rfl) le_rfl hlt
      (hsy.trans (Nat.le_add_left _ _))).1
  · exact (UnionFind.valid_link hu hw hryn hrxn hryr hrxr (Ne.symm heq) (fun _ _ => rfl) le_rfl
      hgt (hsx.trans (Nat.le_add_left _ _))).1
  · have htie : u.rank (u.root y) = u.rank (u.root x) := by omega
    refine (UnionFind.valid_link hu hw hryn hrxn hryr hrxr (Ne.symm heq)
      (fun i hi => Function.update_of_ne hi ..) (by simp) (by simp [htie]) ?_).1
    rw [Function.update_self, Nat.pow_succ]
    rw [htie] at hsy
    omega

/-- **A merge keeps the union-find's promise**: on two groups it joins exactly those two and
changes no other, drops the count by one and answers yes, keeping the first root on a tie; on one
group it merges nothing and answers no. -/
theorem merge_spec (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hx : x < u.n) (hy : y < u.n) :
    UnionFind.UnionSpec u x y ((merge u x y).1, (merge u x y).2.isSome) := by
  obtain ⟨hrxr, hrxn⟩ := root_isRoot_lt hu hx
  obtain ⟨hryr, hryn⟩ := root_isRoot_lt hu hy
  have hsx := hu.2.2 _ hrxn hrxr
  have hsy := hu.2.2 _ hryn hryr
  have hpos := count_pos hw hrxn hrxr
  -- after a link of `a` under `b`, two items are together exactly as the promise says
  have hgroups : ∀ a b, u.root x ≠ u.root y →
      (a = u.root x ∧ b = u.root y ∨ a = u.root y ∧ b = u.root x) → ∀ i j,
      ((if u.root i = a then b else u.root i) = (if u.root j = a then b else u.root j) ↔
        u.Same i j ∨ (u.Same i x ∧ u.Same j y) ∨ (u.Same i y ∧ u.Same j x)) := by
    intro a b hne hab i j
    simp only [UnionFind.Same]
    split_ifs <;> constructor <;> intro <;> omega
  simp only [merge]
  split_ifs with heq hlt hgt
  · refine ⟨rfl, by simp [UnionFind.Same, heq], fun i _ j _ => ?_, fun _ => ⟨rfl, rfl⟩,
      fun h => absurd heq h, fun h => absurd heq h⟩
    simp only [UnionFind.Same]
    constructor <;> intro <;> omega
  · obtain ⟨-, hvroot⟩ := UnionFind.valid_link hu hw hrxn hryn hrxr hryr heq (fun _ _ => rfl)
      le_rfl hlt (hsy.trans (Nat.le_add_left _ _))
    refine ⟨rfl, by simp [UnionFind.Same, heq], fun i hi j hj => ?_, fun h => absurd h heq,
      fun _ => by dsimp only; omega, fun _ hr => by omega⟩
    simp only [UnionFind.Same]
    rw [hvroot i hi, hvroot j hj]
    exact hgroups _ _ heq (Or.inl ⟨rfl, rfl⟩) i j
  · obtain ⟨-, hvroot⟩ := UnionFind.valid_link hu hw hryn hrxn hryr hrxr (Ne.symm heq)
      (fun _ _ => rfl) le_rfl hgt (hsx.trans (Nat.le_add_left _ _))
    refine ⟨rfl, by simp [UnionFind.Same, heq], fun i hi j hj => ?_, fun h => absurd h heq,
      fun _ => by dsimp only; omega, fun _ hr => by omega⟩
    simp only [UnionFind.Same]
    rw [hvroot i hi, hvroot j hj]
    exact hgroups _ _ heq (Or.inr ⟨rfl, rfl⟩) i j
  · have htie : u.rank (u.root y) = u.rank (u.root x) := by omega
    obtain ⟨-, hvroot⟩ := UnionFind.valid_link hu hw hryn hrxn hryr hrxr (Ne.symm heq)
      (rk := Function.update u.rank (u.root x) (u.rank (u.root x) + 1))
      (fun i hi => Function.update_of_ne hi ..) (by simp) (by simp [htie]) (by
        rw [Function.update_self, Nat.pow_succ]
        rw [htie] at hsy
        omega)
    refine ⟨rfl, by simp [UnionFind.Same, heq], fun i hi j hj => ?_, fun h => absurd h heq,
      fun _ => by dsimp only; omega, fun _ _ => ?_⟩
    · simp only [UnionFind.Same]
      rw [hvroot i hi, hvroot j hj]
      exact hgroups _ _ heq (Or.inr ⟨rfl, rfl⟩) i j
    · dsimp only
      rw [hvroot x hx]
      simp [heq]

/-- **What an entry holds**: the root that stopped being a root, one of the two named roots, and
whether the rank of the root it went under rose. -/
theorem merge_entry (hu : u.Valid) {x y c : ℕ} {rose : Bool} (hx : x < u.n) (hy : y < u.n)
    (h : (merge u x y).2 = some (c, rose)) :
    (c = u.root x ∨ c = u.root y) ∧ u.IsRoot c ∧ ¬ (merge u x y).1.IsRoot c ∧
      (merge u x y).1.rank ((merge u x y).1.parent c) =
        u.rank ((merge u x y).1.parent c) + rose.toNat := by
  obtain ⟨hrxr, -⟩ := root_isRoot_lt hu hx
  obtain ⟨hryr, -⟩ := root_isRoot_lt hu hy
  simp only [UnionFind.IsRoot] at hrxr hryr
  revert h
  simp only [merge]
  split_ifs with heq hlt hgt <;> intro h <;> simp only [Option.some.injEq,
    Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
  · simp [UnionFind.IsRoot, hrxr, heq, Ne.symm heq]
  · simp [UnionFind.IsRoot, hryr, heq, Ne.symm heq]
  · simp [UnionFind.IsRoot, hryr, heq, Ne.symm heq]

/-! ## `Valid`, piece by piece -/

/-- **Every structure the log rolls back to has the union-find's pieces**: taking back the newest
`k` entries, for every `k` from one to the length of the log, gives a structure with each piece of
`Valid` and `WellFormed`. -/
theorem rollbacksLegal_iff (u : UnionFind) (log : List (Option (ℕ × Bool))) :
    RollbacksLegal u log ↔ ∀ k, 0 < k → k ≤ log.length →
      (fun v : UnionFind => v.UpwardEndsAtRoot ∧ v.RanksRiseUpward ∧ v.RootRankBoundsSize ∧
        v.CountIsRoots) ((log.take k).foldl unmerge u) := by
  induction log generalizing u with
  | nil =>
    simp only [RollbacksLegal, List.length_nil, true_iff]
    intro k h1 h2
    omega
  | cons e log ih =>
    simp only [RollbacksLegal, ih, UnionFind.pieces_iff_valid_wellFormed]
    constructor
    · rintro ⟨h0, h⟩ k hk hkl
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simpa using h0
      · simpa [List.take_succ_cons] using h j hj (by simpa using hkl)
    · intro h
      refine ⟨by simpa using h 1 Nat.one_pos (by simp), fun j hj hjl => ?_⟩
      simpa [List.take_succ_cons] using h (j + 1) (by omega) (by simpa using hjl)

/-- **`Valid` is the union-find's pieces throughout**: the structure has each piece of the
union-find's `Valid` and `WellFormed`, and so does every structure its log rolls back to. -/
theorem pieces_iff_valid (s : UndoUnionFind) :
    ((s.uf.UpwardEndsAtRoot ∧ s.uf.RanksRiseUpward ∧ s.uf.RootRankBoundsSize ∧
        s.uf.CountIsRoots) ∧
      ∀ k, 0 < k → k ≤ s.log.length →
        (fun v : UnionFind => v.UpwardEndsAtRoot ∧ v.RanksRiseUpward ∧ v.RootRankBoundsSize ∧
          v.CountIsRoots) ((s.log.take k).foldl unmerge s.uf)) ↔ s.Valid := by
  rw [Valid, UnionFind.pieces_iff_valid_wellFormed, rollbacksLegal_iff]

/-! ## The state keeps `Valid` -/

/-- **Every item alone, the log empty, is legal.** -/
theorem valid_init (n : ℕ) : (init n).Valid :=
  ⟨⟨UnionFind.valid_init n, UnionFind.wellFormed_init n⟩, trivial⟩

/-- **A merge keeps the state legal.** -/
theorem valid_union {s : UndoUnionFind} (hs : s.Valid) {x y : ℕ} (hx : x < s.uf.n)
    (hy : y < s.uf.n) : (s.union x y).1.Valid := by
  refine ⟨valid_merge hs.1.1 hs.1.2 hx hy, ?_⟩
  change ((unmerge (merge s.uf x y).1 (merge s.uf x y).2).Valid ∧
    (unmerge (merge s.uf x y).1 (merge s.uf x y).2).WellFormed) ∧
    RollbacksLegal (unmerge (merge s.uf x y).1 (merge s.uf x y).2) s.log
  rw [unmerge_merge hs.1.1 hs.1.2 hx hy]
  exact hs

/-- **An undo keeps the state legal.** -/
theorem valid_undo {s : UndoUnionFind} (hs : s.Valid) : (s.undo).1.Valid := by
  obtain ⟨uf, log⟩ := s
  cases log with
  | nil => exact hs
  | cons e log => exact hs.2

/-! ## Undo takes back a merge -/

/-- **Undo right after a merge gives back the state before it**, links, ranks, count and log, and
answers yes; a merge that merged nothing is one entry too, taken back by one undo. -/
theorem undo_union {s : UndoUnionFind} (hs : s.uf.Valid) (hw : s.uf.WellFormed) {x y : ℕ}
    (hx : x < s.uf.n) (hy : y < s.uf.n) : (s.union x y).1.undo = (s, true) := by
  obtain ⟨uf, log⟩ := s
  simp only [union, undo, unmerge_merge hs hw hx hy]

/-- **On an empty log, undo changes nothing** and answers no. -/
theorem undo_nil {s : UndoUnionFind} (h : s.log = []) : s.undo = (s, false) := by
  simp [undo, h]

/-- A merge logs one entry, and taking it back gives the structure before it. -/
theorem union_records {s : UndoUnionFind} (hs : s.uf.Valid) (hw : s.uf.WellFormed) {x y : ℕ}
    (hx : x < s.uf.n) (hy : y < s.uf.n) :
    ∃ e, (s.union x y).1.log = e :: s.log ∧ unmerge (s.union x y).1.uf e = s.uf :=
  ⟨_, rfl, unmerge_merge hs hw hx hy⟩

/-- The merge's answer is whether two groups became one. -/
theorem union_spec {s : UndoUnionFind} (hs : s.uf.Valid) (hw : s.uf.WellFormed) {x y : ℕ}
    (hx : x < s.uf.n) (hy : y < s.uf.n) :
    UnionFind.UnionSpec s.uf x y ((s.union x y).1.uf, (s.union x y).2) :=
  merge_spec hs hw hx hy

end AlgoDesign.Graphs.UndoUnionFind
