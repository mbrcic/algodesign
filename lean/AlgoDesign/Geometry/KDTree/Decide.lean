/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Search

/-! # The k-d tree: deciding the invariants

Each piece of `KDTree.Valid` and of the search's `BestFirst.Valid`, and both invariants, decide on
a concrete tree and run, so `decide` checks a small one and a separate Lean–Rust check evaluates
them. -/

@[expose] public section

namespace AlgoDesign.Geometry.KDTree

variable {d : ℕ} {α : Type} [LinearOrder α]

instance decCutsSeparate : (t : KDTree d α) → Decidable (CutsSeparate t)
  | leaf _ => isTrue trivial
  | node _ _ l r =>
    have := decCutsSeparate l
    have := decCutsSeparate r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance decCutsHalve : (t : KDTree d α) → Decidable (CutsHalve t)
  | leaf _ => isTrue trivial
  | node _ _ l r =>
    have := decCutsHalve l
    have := decCutsHalve r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance decValid (t : KDTree d α) : Decidable (Valid t) :=
  inferInstanceAs (Decidable (CutsSeparate t ∧ CutsHalve t))

namespace BestFirst

variable [CommRing α] [IsStrictOrderedRing α]

instance (r : Run d α) : Decidable (NothingCloserSkipped r) := by
  unfold NothingCloserSkipped; infer_instance

instance (r : Run d α) : Decidable (QueuedCutsSeparate r) := by
  unfold QueuedCutsSeparate; infer_instance

instance (r : Run d α) : Decidable (OffsetsBound r) := by
  unfold OffsetsBound; infer_instance

instance (r : Run d α) : Decidable (EachPointOnce r) := by
  unfold EachPointOnce; infer_instance

instance (r : Run d α) : Decidable (Valid r) := by
  unfold Valid; infer_instance

end BestFirst

end AlgoDesign.Geometry.KDTree
