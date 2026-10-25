/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Spec

/-! # Union-find: deciding the invariants

Each piece of `Valid` and `WellFormed`, and each of the two itself, decides on a stored structure,
so `decide` checks a small one and a separate Lean–Rust check evaluates them. -/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

instance decidableIsRoot (u : UnionFind) (r : ℕ) : Decidable (u.IsRoot r) :=
  inferInstanceAs (Decidable (u.parent r = r))

instance decidableUpwardEndsAtRoot (u : UnionFind) : Decidable u.UpwardEndsAtRoot := by
  unfold UpwardEndsAtRoot; infer_instance

instance decidableRanksRiseUpward (u : UnionFind) : Decidable u.RanksRiseUpward := by
  unfold RanksRiseUpward; infer_instance

instance decidableRootRankBoundsSize (u : UnionFind) : Decidable u.RootRankBoundsSize := by
  unfold RootRankBoundsSize; infer_instance

instance decidableCountIsRoots (u : UnionFind) : Decidable u.CountIsRoots := by
  unfold CountIsRoots; infer_instance

instance decidableValid (u : UnionFind) : Decidable (Valid u) := by
  unfold Valid; infer_instance

instance decidableWellFormed (u : UnionFind) : Decidable (WellFormed u) := by
  unfold WellFormed; infer_instance

end AlgoDesign.Graphs.UnionFind
