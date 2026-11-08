/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Find

/-!
# Union-find: the merge and the question

`union` looks up both roots, `x`'s first, then `y`'s. If they are the same it merges nothing and
answers no. Otherwise the root of lower rank goes under the other; on equal ranks the second root
goes under the first, whose rank rises by one (Weiss, §8.5, Fig. 8.14); the count drops by one and
the answer is yes. `joined` looks up both and compares.

`valid_link`: hanging one root under another keeps `Valid` and `WellFormed` when ranks and sizes
allow it, and
changes the root of exactly the items in the tree hung below. So `valid_union` and
`valid_joined` keep the structure legal, and `union_spec`: `union` discharges `UnionSpec`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

/-- **Merge** the groups of `x` and `y`; the answer says whether two groups became one. -/
def union (u : UnionFind) (x y : ℕ) : UnionFind × Bool :=
  let (u1, rx) := u.find x
  let (u2, ry) := u1.find y
  if rx = ry then (u2, false)
  else if u2.rank rx < u2.rank ry then
    ({ u2 with parent := Function.update u2.parent rx ry, count := u2.count - 1 }, true)
  else if u2.rank ry < u2.rank rx then
    ({ u2 with parent := Function.update u2.parent ry rx, count := u2.count - 1 }, true)
  else
    ({ u2 with parent := Function.update u2.parent ry rx,
               rank := Function.update u2.rank rx (u2.rank rx + 1),
               count := u2.count - 1 }, true)

/-- **Are `x` and `y` joined yet?** Both are looked up, `x` first. -/
def joined (u : UnionFind) (x y : ℕ) : UnionFind × Bool :=
  let (u1, rx) := u.find x
  let (u2, ry) := u1.find y
  (u2, rx == ry)

/-- The structure after merging each pair in turn, from the first. -/
def unions (u : UnionFind) : List (ℕ × ℕ) → UnionFind
  | [] => u
  | (x, y) :: ps => (u.union x y).1.unions ps

/-! ## Counting -/

/-- Items whose root is one of two different roots split into the two groups. -/
theorem countP_eq_or {f : ℕ → ℕ} {a b : ℕ} (hab : a ≠ b) (l : List ℕ) :
    l.countP (fun i => f i = a ∨ f i = b) =
      l.countP (fun i => f i = a) + l.countP (fun i => f i = b) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.countP_cons, ih]
    by_cases ha : f x = a <;> by_cases hb : f x = b <;>
      simp [ha, hb, hab, Ne.symm hab] <;> omega

/-- Leaving out one item that counts drops the count by one. -/
theorem countP_eq_add_one {P : ℕ → Prop} [DecidablePred P] {a : ℕ} {l : List ℕ} (hl : l.Nodup)
    (ha : a ∈ l) (hP : P a) :
    l.countP (fun x => P x) = l.countP (fun x => P x ∧ x ≠ a) + 1 := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    obtain ⟨hxt, ht⟩ := List.nodup_cons.1 hl
    rw [List.countP_cons, List.countP_cons]
    rcases eq_or_ne x a with rfl | hxa
    · have : t.countP (fun y => P y ∧ y ≠ x) = t.countP (fun y => P y) :=
        List.countP_congr fun y hy => by
          simp only [decide_eq_true_eq]
          exact ⟨fun h => h.1, fun h => ⟨h, fun hyx => hxt (hyx ▸ hy)⟩⟩
      rw [this]
      simp [hP]
    · have hat : a ∈ t := (List.mem_cons.1 ha).resolve_left hxa.symm
      rw [ih ht hat]
      simp only [ne_eq, hxa, not_false_eq_true, and_true]
      omega

/-! ## Linking one root under another -/

/-- **Linking keeps a structure legal and well formed.** Root `a` goes under root `b`, ranks
change only at `b` and only upward, `b` ends above `a`, the merged tree is large enough for `b`'s
new rank, and the count drops by one. Every item that had root `a` now has root `b`; every other
keeps its root. -/
theorem valid_link {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {a b : ℕ} (ha : a < u.n)
    (hb : b < u.n) (hra : u.IsRoot a) (hrb : u.IsRoot b) (hab : a ≠ b) {rk : ℕ → ℕ}
    (hrk : ∀ i, i ≠ b → rk i = u.rank i) (hrkb : u.rank b ≤ rk b) (hlt : u.rank a < rk b)
    (hsz : 2 ^ rk b ≤ (List.range u.n).countP (fun i => u.root i = a) +
      (List.range u.n).countP (fun i => u.root i = b)) :
    ((⟨u.n, Function.update u.parent a b, rk, u.count - 1⟩ : UnionFind).Valid ∧
      (⟨u.n, Function.update u.parent a b, rk, u.count - 1⟩ : UnionFind).WellFormed) ∧
      ∀ i < u.n, (⟨u.n, Function.update u.parent a b, rk, u.count - 1⟩ : UnionFind).root i =
        if u.root i = a then b else u.root i := by
  obtain ⟨hup, hrise, hsize⟩ := hu
  have hcount : u.CountIsRoots := hw
  have hplt : ∀ i < u.n, u.parent i < u.n := fun i hi => (hup i hi).1
  set q := Function.update u.parent a b with hqdef
  set v : UnionFind := ⟨u.n, q, rk, u.count - 1⟩ with hv
  have hqa : q a = b := Function.update_self ..
  have hq : ∀ i, i ≠ a → q i = u.parent i := fun i hi => Function.update_of_ne hi ..
  have hqb : q b = b := (hq b hab.symm).trans hrb
  have hle : ∀ j, u.rank j ≤ rk j := fun j => by
    rcases eq_or_ne j b with rfl | hj
    · exact hrkb
    · exact (hrk j hj).ge
  have hvlt : ∀ i < v.n, v.parent i < v.n := by
    intro i hi
    change q i < u.n
    rcases eq_or_ne i a with rfl | hia
    · rwa [hqa]
    · rw [hq i hia]; exact hplt i hi
  have hvrise : v.RanksRiseUpward := by
    intro i hi hne
    change q i ≠ i at hne
    change rk i < rk (q i)
    rcases eq_or_ne i a with rfl | hia
    · rw [hqa, hrk i hab]; exact hlt
    · rw [hq i hia] at hne ⊢
      have hib : i ≠ b := fun h => hne (h ▸ hrb)
      rw [hrk i hib]
      exact (hrise i hi hne).trans_le (hle _)
  have hvup := upwardEndsAtRoot_of_ranksRise hvlt hvrise
  have hagree : ∀ i k, (∀ j < k, u.parent^[j] i ≠ a) → q^[k] i = u.parent^[k] i := by
    intro i k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih fun j hj => h j (by omega), hq _ (h k (by omega))]
  have hvroot : ∀ i < u.n, v.root i = if u.root i = a then b else u.root i := by
    intro i hi
    split_ifs with hia
    · have hex : ∃ k, u.parent^[k] i = a := ⟨u.n, hia⟩
      classical
      have hk := Nat.find_spec hex
      have hmin : ∀ j < Nat.find hex, u.parent^[j] i ≠ a := fun j hj => Nat.find_min hex hj
      refine root_eq_of_iterate hvup hi (k := Nat.find hex + 1) ?_ hqb
      change q^[Nat.find hex + 1] i = b
      rw [Function.iterate_succ_apply', hagree i _ hmin, hk, hqa]
    · have hne : ∀ j, u.parent^[j] i ≠ a := fun j hj => hia (root_eq_of_iterate hup hi hj hra)
      change q^[u.n] i = u.root i
      exact hagree i u.n fun j _ => hne j
  have hvroots : ∀ r, (q r = r ↔ u.IsRoot r ∧ r ≠ a) := by
    intro r
    rcases eq_or_ne r a with rfl | hra'
    · simp only [hqa, ne_eq, not_true_eq_false, and_false, iff_false]
      exact hab.symm
    · rw [hq r hra']
      exact ⟨fun h => ⟨h, hra'⟩, fun h => h.1⟩
  refine ⟨⟨⟨hvup, hvrise, ?_⟩, ?_⟩, hvroot⟩
  · intro r hr hvr
    obtain ⟨hur, hra'⟩ := (hvroots r).1 hvr
    change 2 ^ rk r ≤ (List.range u.n).countP (fun i => v.root i = r)
    rcases eq_or_ne r b with rfl | hrb'
    · rw [← countP_eq_or hab] at hsz
      refine hsz.trans_eq (List.countP_congr fun i hi => ?_)
      rw [hvroot i (List.mem_range.1 hi)]
      by_cases h : u.root i = a <;> simp [h]
    · rw [hrk r hrb']
      refine (hsize r hr hur).trans_eq (List.countP_congr fun i hi => ?_)
      rw [hvroot i (List.mem_range.1 hi)]
      by_cases h : u.root i = a
      · simp [h, Ne.symm hrb', Ne.symm hra']
      · simp [h]
  · change u.count - 1 = (List.range u.n).countP (fun r => q r = r)
    have h1 := countP_eq_add_one (P := fun r => u.parent r = r) (List.nodup_range)
      (List.mem_range.2 ha) hra
    have h2 : (List.range u.n).countP (fun r => q r = r) =
        (List.range u.n).countP (fun r => u.parent r = r ∧ r ≠ a) :=
      List.countP_congr fun r _ => by simpa [IsRoot] using hvroots r
    rw [hcount, h1, h2]
    omega

/-! ## The merge keeps the structure legal -/

/-- After looking up `x` and then `y`: the structure is legal and well formed, has the same
items, ranks, count and roots, and the two answers are the roots of `x` and `y`. -/
theorem find_find {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hy : y < u.n)
    {u1 u2 : UnionFind} {rx ry : ℕ} (h1 : u.find x = (u1, rx)) (h2 : u1.find y = (u2, ry)) :
    (u2.Valid ∧ u2.WellFormed) ∧ u2.n = u.n ∧ u2.rank = u.rank ∧ u2.count = u.count ∧
      (∀ i < u.n, u2.root i = u.root i) ∧ rx = u.root x ∧ ry = u.root y := by
  have s1 := find_spec hu hw x
  have v1 := valid_find hu hw x
  rw [h1] at s1 v1
  have s2 := find_spec v1.1 v1.2 y
  have v2 := valid_find v1.1 v1.2 y
  rw [h2] at s2 v2
  refine ⟨v2, s2.n_eq.trans s1.n_eq, s2.rank_eq.trans s1.rank_eq,
    s2.count_eq.trans s1.count_eq, fun i hi => ?_, s1.answer, ?_⟩
  · rw [s2.same_root i (s1.n_eq ▸ hi), s1.same_root i hi]
  · exact s2.answer.trans (s1.same_root y hy)

/-- **A merge keeps the structure legal and well formed.** -/
theorem valid_union {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hx : x < u.n)
    (hy : y < u.n) : (u.union x y).1.Valid ∧ (u.union x y).1.WellFormed := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  obtain ⟨⟨hv, hw2⟩, hn, -, -, hroot, hrx, hry⟩ := find_find hu hw hy h1 h2
  have hplt : ∀ i < u2.n, u2.parent i < u2.n := fun i hi => (hv.1 i hi).1
  have hx2 : x < u2.n := hn ▸ hx
  have hy2 : y < u2.n := hn ▸ hy
  have hrx2 : rx = u2.root x := by rw [hrx, hroot x hx]
  have hry2 : ry = u2.root y := by rw [hry, hroot y hy]
  have hrxr : u2.IsRoot rx := hrx2 ▸ (hv.1 x hx2).2
  have hryr : u2.IsRoot ry := hry2 ▸ (hv.1 y hy2).2
  have hrxn : rx < u2.n := hrx2 ▸ iterate_lt hplt hx2 _
  have hryn : ry < u2.n := hry2 ▸ iterate_lt hplt hy2 _
  have hsx := hv.2.2 rx hrxn hrxr
  have hsy := hv.2.2 ry hryn hryr
  simp only [union, h1, h2]
  split_ifs with heq hlt hgt
  · exact ⟨hv, hw2⟩
  · exact (valid_link hv hw2 hrxn hryn hrxr hryr heq (fun _ _ => rfl) le_rfl hlt
      (hsy.trans (Nat.le_add_left _ _))).1
  · exact (valid_link hv hw2 hryn hrxn hryr hrxr (Ne.symm heq) (fun _ _ => rfl) le_rfl hgt
      (hsx.trans (Nat.le_add_left _ _))).1
  · have htie : u2.rank ry = u2.rank rx := by omega
    refine (valid_link hv hw2 hryn hrxn hryr hrxr (Ne.symm heq)
      (fun i hi => Function.update_of_ne hi ..) (by simp) (by simp [htie]) ?_).1
    rw [Function.update_self, Nat.pow_succ]
    rw [htie] at hsy
    omega

/-- **Asking keeps the structure legal and well formed.** -/
theorem valid_joined {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) (x y : ℕ) :
    (u.joined x y).1.Valid ∧ (u.joined x y).1.WellFormed := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  have v1 := valid_find hu hw x
  rw [h1] at v1
  have v2 := valid_find v1.1 v1.2 y
  rw [h2] at v2
  simpa only [joined, h1, h2] using v2

/-! ## The merge keeps its promise -/

/-- **A merge keeps its promise**: on two groups it joins exactly those two and changes no other,
drops the count by one and answers yes, keeping the first root on a tie; on one group it merges
nothing, keeps ranks and the count, and answers no. -/
theorem union_spec {u : UnionFind} (hu : u.Valid) (hw : u.WellFormed) {x y : ℕ} (hx : x < u.n)
    (hy : y < u.n) : UnionSpec u x y (u.union x y) := by
  obtain ⟨⟨u1, rx⟩, h1⟩ : ∃ r, u.find x = r := ⟨_, rfl⟩
  obtain ⟨⟨u2, ry⟩, h2⟩ : ∃ r, u1.find y = r := ⟨_, rfl⟩
  obtain ⟨⟨hv, hw2⟩, hn, hrk, hc, hroot, hrx, hry⟩ := find_find hu hw hy h1 h2
  have hplt : ∀ i < u2.n, u2.parent i < u2.n := fun i hi => (hv.1 i hi).1
  have hx2 : x < u2.n := hn ▸ hx
  have hy2 : y < u2.n := hn ▸ hy
  have hrx2 : rx = u2.root x := by rw [hrx, hroot x hx]
  have hry2 : ry = u2.root y := by rw [hry, hroot y hy]
  have hrxr : u2.IsRoot rx := hrx2 ▸ (hv.1 x hx2).2
  have hryr : u2.IsRoot ry := hry2 ▸ (hv.1 y hy2).2
  have hrxn : rx < u2.n := hrx2 ▸ iterate_lt hplt hx2 _
  have hryn : ry < u2.n := hry2 ▸ iterate_lt hplt hy2 _
  have hsx := hv.2.2 rx hrxn hrxr
  have hsy := hv.2.2 ry hryn hryr
  have hsame : u.Same x y ↔ rx = ry := by rw [Same, hrx, hry]
  have hpos : 0 < u2.count := by
    rw [hw2]
    exact List.countP_pos_iff.2 ⟨rx, List.mem_range.2 hrxn, by simpa [IsRoot] using hrxr⟩
  -- after a link of `a` under `b`, two items are together exactly as the promise says
  have hgroups : ∀ a b, rx ≠ ry → (a = rx ∧ b = ry ∨ a = ry ∧ b = rx) → ∀ i j,
      ((if u.root i = a then b else u.root i) = (if u.root j = a then b else u.root j) ↔
        u.Same i j ∨ (u.Same i x ∧ u.Same j y) ∨ (u.Same i y ∧ u.Same j x)) := by
    intro a b hne hab i j
    simp only [Same, ← hrx, ← hry]
    split_ifs <;> constructor <;> intro <;> omega
  simp only [union, h1, h2]
  split_ifs with heq hlt hgt
  · refine ⟨hn, by simp [hsame, heq], fun i hi j hj => ?_, fun _ => ⟨hrk, hc⟩,
      fun h => absurd (hsame.2 heq) h, fun h => absurd (hsame.2 heq) h⟩
    simp only [Same, hroot i hi, hroot j hj, ← hrx, ← hry, heq]
    constructor <;> intro <;> omega
  · obtain ⟨-, hvroot⟩ := valid_link hv hw2 hrxn hryn hrxr hryr heq (fun _ _ => rfl) le_rfl hlt
      (hsy.trans (Nat.le_add_left _ _))
    refine ⟨hn, by simp [hsame, heq], fun i hi j hj => ?_, fun h => absurd (hsame.1 h) heq,
      fun _ => by dsimp only; omega, fun _ hr => ?_⟩
    · simp only [Same]
      rw [hvroot i (hn ▸ hi), hvroot j (hn ▸ hj), hroot i hi, hroot j hj]
      exact hgroups rx ry heq (Or.inl ⟨rfl, rfl⟩) i j
    · rw [← hrx, ← hry, ← hrk] at hr
      omega
  · obtain ⟨-, hvroot⟩ := valid_link hv hw2 hryn hrxn hryr hrxr (Ne.symm heq) (fun _ _ => rfl)
      le_rfl
      hgt (hsx.trans (Nat.le_add_left _ _))
    refine ⟨hn, by simp [hsame, heq], fun i hi j hj => ?_, fun h => absurd (hsame.1 h) heq,
      fun _ => by dsimp only; omega, fun _ hr => ?_⟩
    · simp only [Same]
      rw [hvroot i (hn ▸ hi), hvroot j (hn ▸ hj), hroot i hi, hroot j hj]
      exact hgroups ry rx heq (Or.inr ⟨rfl, rfl⟩) i j
    · rw [← hrx, ← hry, ← hrk] at hr
      omega
  · have htie : u2.rank ry = u2.rank rx := by omega
    obtain ⟨-, hvroot⟩ := valid_link hv hw2 hryn hrxn hryr hrxr (Ne.symm heq)
      (rk := Function.update u2.rank rx (u2.rank rx + 1))
      (fun i hi => Function.update_of_ne hi ..) (by simp) (by simp [htie]) (by
        rw [Function.update_self, Nat.pow_succ]
        rw [htie] at hsy
        omega)
    refine ⟨hn, by simp [hsame, heq], fun i hi j hj => ?_, fun h => absurd (hsame.1 h) heq,
      fun _ => by dsimp only; omega, fun _ _ => ?_⟩
    · simp only [Same]
      rw [hvroot i (hn ▸ hi), hvroot j (hn ▸ hj), hroot i hi, hroot j hj]
      exact hgroups ry rx heq (Or.inr ⟨rfl, rfl⟩) i j
    · dsimp only
      rw [hvroot x hx2, hroot x hx, ← hrx]
      simp [heq]

/-! ## Examples, checked by the kernel -/

/-- On equal ranks the second root goes under the first: `union 0 1` keeps 0 the root. -/
example : ((init 2).union 0 1).1.parent 1 = 0 ∧ ((init 2).union 0 1).1.rank 0 = 1 := by decide

/-- Merging two items already together merges nothing: ranks and the count stay. -/
example :
    let u := (init 2).unions [(0, 1)]
    (u.union 1 0).2 = false ∧ (u.union 1 0).1.rank 0 = 1 ∧ (u.union 1 0).1.rank 1 = 0 ∧
      (u.union 1 0).1.count = 1 := by
  decide

/-- Two pairs, then their groups: one tie raises the root's rank to 2. -/
example :
    let u := (init 4).unions [(0, 1), (2, 3), (1, 3)]
    u.Valid ∧ u.WellFormed ∧ u.rank 0 = 2 ∧ u.count = 1 ∧ (u.joined 1 2).2 = true := by
  decide

example :
    let u := (init 5).unions [(0, 1), (2, 3), (1, 3), (4, 4), (3, 4), (0, 4)]
    u.Valid ∧ u.WellFormed := by
  decide

/-! ### Each piece of `Valid` and `WellFormed` can fail -/

/-- Without the check for one root, `LINK(r, r)` raises a rank with no new item: a root of rank 1
over one item breaks `RootRankBoundsSize`. -/
example : ¬ ({ init 1 with rank := fun _ => 1 } : UnionFind).RootRankBoundsSize := by decide

/-- CLRS's tie on `union 0 1` puts 0 under 1 and leaves both at rank 0: `RanksRiseUpward` fails
until the rank is raised. -/
example :
    ¬ ({ init 2 with parent := Function.update id 0 1, count := 1 } :
      UnionFind).RanksRiseUpward := by
  decide

/-- A link out of the items breaks `UpwardEndsAtRoot`. -/
example : ¬ ({ init 2 with parent := fun _ => 5 } : UnionFind).UpwardEndsAtRoot := by decide

/-- A count that skips a merge breaks `CountIsRoots`. -/
example : ¬ ({ (init 2).unions [(0, 1)] with count := 2 } : UnionFind).CountIsRoots := by decide

end AlgoDesign.Graphs.UnionFind
