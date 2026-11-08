/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Spec

/-! # Binary search tree: deciding the invariant

`Sorted`, and so `Valid`, decides on a concrete tree, so `decide` checks a small tree and a
separate Lean–Rust check evaluates it. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace BST

variable {α : Type}

/-- `All` decides on a concrete tree. -/
instance decidableAll (p : α → Prop) [DecidablePred p] : ∀ t : BST α, Decidable (All p t)
  | leaf => inferInstanceAs (Decidable True)
  | node l k r =>
      haveI := decidableAll p l
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p k ∧ All p r))

variable [LinearOrder α]

instance decidableSorted : ∀ t : BST α, Decidable (Sorted t)
  | leaf => inferInstanceAs (Decidable True)
  | node l k r =>
      haveI := decidableSorted l
      haveI := decidableSorted r
      inferInstanceAs (Decidable (All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r))

instance (t : BST α) : Decidable (Valid t) := inferInstanceAs (Decidable (Sorted t))

end BST

end AlgoDesign.Searching
