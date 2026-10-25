/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UndoUnionFind.Spec
public import AlgoDesign.Graphs.UnionFind.Decide

/-! # Union-find with undo: deciding the invariant

`RollbacksLegal`, and `Valid` itself, decide on a stored state, so `decide` checks a small one and
a separate Lean–Rust check evaluates them. -/

@[expose] public section

namespace AlgoDesign.Graphs

namespace UndoUnionFind

instance decidableRollbacksLegal :
    ∀ (u : UnionFind) (log : List (Option (ℕ × Bool))), Decidable (RollbacksLegal u log)
  | _, [] => isTrue trivial
  | u, e :: log =>
    have := decidableRollbacksLegal (unmerge u e) log
    inferInstanceAs (Decidable (_ ∧ _))

instance decidableValid (s : UndoUnionFind) : Decidable (Valid s) := by
  unfold Valid; infer_instance

end UndoUnionFind

end AlgoDesign.Graphs
