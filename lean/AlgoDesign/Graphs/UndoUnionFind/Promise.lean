/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UndoUnionFind.Basic
public import AlgoDesign.Graphs.UnionFind.Promise

/-!
# Union-find with undo: runs of merges and rollbacks

`unions` merges each pair in turn; `rollback s k` undoes `k` times. `rollback_unions`: undoing
after a run of merges walks back through every earlier state, last first. From every item alone,
`rollback_unions_init`: after a run and `k` undos the state is the one built by the run without
its last `k` merges. `unions_init`: two items are together exactly when the run joined them,
`Joined` (`UnionFind/Spec.lean`); so `joined_rollback_iff`: after a run and `k` undos, the question
answers exactly who the merges still in the log joined.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UndoUnionFind

open UnionFind (Joined)

/-- The state after merging each pair in turn, from the first. -/
def unions (s : UndoUnionFind) : List (ℕ × ℕ) → UndoUnionFind
  | [] => s
  | (x, y) :: ps => (s.union x y).1.unions ps

/-- The state after `k` undos. -/
def rollback (s : UndoUnionFind) (k : ℕ) : UndoUnionFind := (fun t => t.undo.1)^[k] s

/-- Merging a run in two parts merges the first part, then the second. -/
theorem unions_append (s : UndoUnionFind) (us vs : List (ℕ × ℕ)) :
    s.unions (us ++ vs) = (s.unions us).unions vs := by
  induction us generalizing s with
  | nil => rfl
  | cons p us ih => exact ih _

/-- A merge keeps the items. -/
theorem n_union (s : UndoUnionFind) (x y : ℕ) : (s.union x y).1.uf.n = s.uf.n := by
  simp only [union, merge]
  split_ifs <;> rfl

/-- **A run of merges keeps the state legal and the items the same**, when every pair is among
the items. -/
theorem valid_unions {s : UndoUnionFind} (hs : s.Valid) {us : List (ℕ × ℕ)}
    (hus : ∀ p ∈ us, p.1 < s.uf.n ∧ p.2 < s.uf.n) :
    (s.unions us).Valid ∧ (s.unions us).uf.n = s.uf.n := by
  induction us generalizing s with
  | nil => exact ⟨hs, rfl⟩
  | cons p us ih =>
    obtain ⟨hx, hy⟩ := hus p List.mem_cons_self
    obtain ⟨hv, hvn⟩ := ih (valid_union hs hx hy)
      fun q hq => n_union s _ _ ▸ hus q (List.mem_cons_of_mem _ hq)
    exact ⟨hv, hvn.trans (n_union s _ _)⟩

/-- **Undo walks back through a run of merges**: after merging `us` and then `vs`, undoing as many
times as `vs` has pairs gives the state after `us`, every earlier state on the way. -/
theorem rollback_unions {s : UndoUnionFind} (hs : s.Valid) {us vs : List (ℕ × ℕ)}
    (hus : ∀ p ∈ us ++ vs, p.1 < s.uf.n ∧ p.2 < s.uf.n) :
    (s.unions (us ++ vs)).rollback vs.length = s.unions us := by
  induction vs generalizing us with
  | nil => simp [rollback]
  | cons q vs ih =>
    have h := ih (us := us ++ [q]) (by simpa using hus)
    rw [List.append_assoc, List.singleton_append] at h
    obtain ⟨hv, hn⟩ := valid_unions hs (us := us) fun p hp => hus p (List.mem_append_left _ hp)
    obtain ⟨hx, hy⟩ := hus q (by simp)
    rw [rollback, List.length_cons, Function.iterate_succ_apply', ← rollback, h, unions_append]
    exact congrArg Prod.fst (undo_union hv.1.1 hv.1.2 (hn ▸ hx) (hn ▸ hy))

/-- **Undo on every item alone changes nothing.** -/
theorem rollback_init (n k : ℕ) : (init n).rollback k = init n :=
  Function.iterate_fixed (congrArg Prod.fst (undo_nil rfl)) k

/-- **The state a rollback reaches**: from every item alone, after merging `us` and undoing `k`
times, the state is the one built by `us` without its last `k` merges (every item alone, once `k`
reaches the number of merges). -/
theorem rollback_unions_init (n : ℕ) {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n)
    (k : ℕ) : ((init n).unions us).rollback k = (init n).unions (us.take (us.length - k)) := by
  have hle : ∀ j ≤ us.length,
      ((init n).unions us).rollback j = (init n).unions (us.take (us.length - j)) := by
    intro j hj
    have h := rollback_unions (valid_init n) (us := us.take (us.length - j))
      (vs := us.drop (us.length - j)) (by rw [List.take_append_drop]; exact hus)
    rwa [List.take_append_drop, List.length_drop, show us.length - (us.length - j) = j by omega]
      at h
  rcases le_total k us.length with hk | hk
  · exact hle k hk
  · rw [show us.length - k = 0 by omega, List.take_zero]
    have h := hle _ le_rfl
    rw [Nat.sub_self, List.take_zero] at h
    calc ((init n).unions us).rollback k
        = (((init n).unions us).rollback us.length).rollback (k - us.length) := by
          rw [rollback, rollback, rollback, ← Function.iterate_add_apply]
          congr 1
          omega
      _ = init n := by rw [h]; exact rollback_init n _

/-- From every item alone, after a run of merges, two items are together exactly when the run
joined them; the state is legal and keeps its items. -/
theorem unions_init (n : ℕ) (us : List (ℕ × ℕ)) (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n) :
    ((init n).unions us).Valid ∧ ((init n).unions us).uf.n = n ∧
      ∀ i < n, ∀ j < n, (((init n).unions us).uf.Same i j ↔ Joined us i j) := by
  induction us using List.reverseRecOn with
  | nil =>
    have hroot : ∀ k, (UnionFind.init n).root k = k := fun k => UnionFind.root_of_isRoot rfl
    refine ⟨valid_init n, rfl, fun i _ j _ => ?_⟩
    rw [UnionFind.joined_nil_iff]
    exact Eq.congr (hroot i) (hroot j)
  | append_singleton us p ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hv, hn, hsame⟩ := ih fun q hq => hus q (List.mem_append_left _ hq)
    obtain ⟨ha, hb⟩ := hus (a, b) (List.mem_append_right _ (List.mem_singleton_self _))
    set v := (init n).unions us
    have hrun : (init n).unions (us ++ [(a, b)]) = (v.union a b).1 := by
      rw [unions_append]; rfl
    have hspec := union_spec hv.1.1 hv.1.2 (hn ▸ ha) (hn ▸ hb)
    have hmono : ∀ i j, Joined us i j → Joined (us ++ [(a, b)]) i j :=
      fun i j => Relation.EqvGen.mono (fun c d h => List.mem_append_left _ h) i j
    have hab : Joined (us ++ [(a, b)]) a b :=
      Relation.EqvGen.rel _ _ (List.mem_append_right _ (List.mem_singleton_self _))
    -- each merged pair, old or new, ends together; `Same` is an equivalence on every item
    have hback : ∀ i j, Joined (us ++ [(a, b)]) i j → (v.union a b).1.uf.Same i j := by
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
    refine ⟨valid_union hv (hn ▸ ha) (hn ▸ hb), hspec.n_eq.trans hn,
      fun i hi j hj => ⟨fun h => ?_, hback i j⟩⟩
    rcases (hspec.groups i (hn ▸ hi) j (hn ▸ hj)).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hmono _ _ ((hsame i hi j hj).1 h)
    · exact ((hmono _ _ ((hsame i hi a ha).1 h1)).trans _ _ _ hab).trans _ _ _
        (hmono _ _ ((hsame j hj b hb).1 h2)).symm
    · exact ((hmono _ _ ((hsame i hi b hb).1 h1)).trans _ _ _ hab.symm).trans _ _ _
        (hmono _ _ ((hsame j hj a ha).1 h2)).symm

/-- **The question answers who is together.** -/
theorem joined_iff_same (s : UndoUnionFind) (x y : ℕ) : s.joined x y = true ↔ s.uf.Same x y := by
  simp [joined, find, UnionFind.Same]

/-- **The promise over a rolled-back run**: from every item alone, after merging `us` and undoing
`k` times, two items have the same root exactly when the merges still in the log joined them. -/
theorem same_rollback_iff {n : ℕ} {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n)
    (k : ℕ) {x y : ℕ} (hx : x < n) (hy : y < n) :
    (((init n).unions us).rollback k).uf.Same x y ↔ Joined (us.take (us.length - k)) x y := by
  rw [rollback_unions_init n hus k]
  exact (unions_init n _ fun p hp => hus p (List.mem_of_mem_take hp)).2.2 x hx y hy

/-- **The question over a rolled-back run** answers exactly who the merges still in the log
joined. -/
theorem joined_rollback_iff {n : ℕ} {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n)
    (k : ℕ) {x y : ℕ} (hx : x < n) (hy : y < n) :
    (((init n).unions us).rollback k).joined x y = true ↔
      Joined (us.take (us.length - k)) x y := by
  rw [joined_iff_same]
  exact same_rollback_iff hus k hx hy

end AlgoDesign.Graphs.UndoUnionFind
