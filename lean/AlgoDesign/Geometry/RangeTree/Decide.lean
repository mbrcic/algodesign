/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Spec

/-! # The range tree: deciding the invariants

Each piece of `RangeTree1D.Valid`, and `Valid` itself, decides on a concrete tree, so `decide`
checks a small one and a separate Lean–Rust check evaluates them. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace RangeTree1D

variable {α : Type} [LinearOrder α]

instance decKeysSeparate : (t : RangeTree1D α) → Decidable (KeysSeparate t)
  | leaf _ => isTrue trivial
  | node _ l r =>
    have := decKeysSeparate l
    have := decKeysSeparate r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

omit [LinearOrder α] in
instance decSplitsHalve : (t : RangeTree1D α) → Decidable (SplitsHalve t)
  | leaf _ => isTrue trivial
  | node _ l r =>
    have := decSplitsHalve l
    have := decSplitsHalve r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance decValid (t : RangeTree1D α) : Decidable (Valid t) :=
  inferInstanceAs (Decidable (KeysSeparate t ∧ SplitsHalve t))

end RangeTree1D

end AlgoDesign.Geometry
