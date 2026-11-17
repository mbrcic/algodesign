/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UndoUnionFind.Spec
public import AlgoDesign.Graphs.UndoUnionFind.Decide
public import AlgoDesign.Graphs.UndoUnionFind.Basic
public import AlgoDesign.Graphs.UndoUnionFind.Promise
public import AlgoDesign.Graphs.UndoUnionFind.Cost

/-! The union-find with undo. Its specification is in `UndoUnionFind/Spec.lean`; this file imports
the whole structure. -/

@[expose] public section

namespace AlgoDesign.Graphs.UndoUnionFind

/-! ## What the library's union-find with undo keeps

No design box exists for undo, so there is no contract: each clause of the appendix's rule is a
theorem about the library's operations. -/

/-- **It starts with every item alone and an empty log**: the items are `0, …, n - 1`, each its
own root. -/
theorem starts_alone (n : ℕ) :
    (init n).uf.n = n ∧ (∀ i < n, (init n).uf.IsRoot i) ∧ (init n).log = [] :=
  ⟨rfl, fun _ _ => rfl, rfl⟩

/-- **Union by rank, logged**: a merge keeps the union-find's promise, guard and tie rule
included, logs one entry per call, an empty one when nothing merged, and taking that entry back
gives the structure before it. -/
theorem merge_logs {s : UndoUnionFind} (hs : s.Valid) {x y : ℕ} (hx : x < s.uf.n)
    (hy : y < s.uf.n) :
    UnionFind.UnionSpec s.uf x y ((s.union x y).1.uf, (s.union x y).2) ∧
    ∃ e, (s.union x y).1.log = e :: s.log ∧ unmerge (s.union x y).1.uf e = s.uf :=
  ⟨union_spec hs.1.1 hs.1.2 hx hy, union_records hs.1.1 hs.1.2 hx hy⟩

/-- **Without path compression, lookups tell**: the lookup answers the root, and the question
answers yes exactly when the two are together; neither changes the state. -/
theorem lookup_tells (s : UndoUnionFind) (x y : ℕ) :
    s.find x = s.uf.root x ∧ (s.joined x y = true ↔ s.uf.Same x y) :=
  ⟨rfl, joined_iff_same s x y⟩

/-- **Rollback pops entries**: undo right after a merge gives back the state before it and
answers yes, a merge that merged nothing included; on an empty log it changes nothing and answers
no. -/
theorem undo_takes_back :
    (∀ s : UndoUnionFind, s.Valid → ∀ x < s.uf.n, ∀ y < s.uf.n, (s.union x y).1.undo = (s, true)) ∧
    ∀ s : UndoUnionFind, s.log = [] → s.undo = (s, false) :=
  ⟨fun _ hs _ hx _ hy => undo_union hs.1.1 hs.1.2 hx hy, fun _ h => undo_nil h⟩

/-- **Over a whole run**: after a run of merges and `k` undos, the lookups and the question say
exactly who the merges still in the log joined. -/
theorem rolls_back {n : ℕ} {us : List (ℕ × ℕ)} (hus : ∀ p ∈ us, p.1 < n ∧ p.2 < n) (k : ℕ)
    {x y : ℕ} (hx : x < n) (hy : y < n) :
    ((((init n).unions us).rollback k).find x = (((init n).unions us).rollback k).find y ↔
      UnionFind.Joined (us.take (us.length - k)) x y) ∧
    ((((init n).unions us).rollback k).joined x y = true ↔
      UnionFind.Joined (us.take (us.length - k)) x y) :=
  ⟨same_rollback_iff hus k hx hy, joined_rollback_iff hus k hx hy⟩

/-- **A rollback restores the group count**: the count is the number of groups, one per root. -/
theorem counts_groups {s : UndoUnionFind} (hs : s.Valid) :
    s.count = (List.range s.uf.n).countP fun r => s.uf.parent r = r :=
  hs.1.2

/-- The start is legal, and a merge and an undo keep the state legal. -/
theorem keeps_invariants :
    (∀ n, (init n).Valid) ∧
    (∀ s : UndoUnionFind, s.Valid → ∀ x < s.uf.n, ∀ y < s.uf.n, (s.union x y).1.Valid) ∧
    ∀ s : UndoUnionFind, s.Valid → (s.undo).1.Valid :=
  ⟨valid_init, fun _ hs _ hx _ hy => valid_union hs hx hy, fun _ hs => valid_undo hs⟩

/-! ## Examples, checked by the kernel -/

/-- A merge of two items already together is one entry, taken back by one undo. -/
example : let s := ((init 2).union 0 1).1
    (s.union 1 0).1.log = [none, some (1, true)] ∧ ((s.union 1 0).1.undo).1.log = s.log := by
  decide

/-- On equal ranks the second root goes under the first, whose rank rises; undo lowers it. -/
example : ((init 2).union 0 1).1.uf.parent 1 = 0 ∧ ((init 2).union 0 1).1.uf.rank 0 = 1 ∧
    (((init 2).union 0 1).1.undo).1.uf.rank 0 = 0 := by
  decide

end AlgoDesign.Graphs.UndoUnionFind
