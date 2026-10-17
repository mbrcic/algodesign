/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.LSH.Spec

/-! # LSH: deciding the invariants

Each piece of `LSH.Valid`, `Valid` itself, a query answer's `MeasuredExactly` and the two cost
statements decide on a concrete index, so `decide` checks a small one and the Lean–Rust
comparison evaluates them. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

instance (x : Index d α κ) : Decidable (InItsBucket x) := by
  unfold InItsBucket; infer_instance

instance (x : Index d α κ) : Decidable (OneBucketPerKey x) := by
  unfold OneBucketPerKey; infer_instance

instance (x : Index d α κ) : Decidable (EachPointOncePerTable x) := by
  unfold EachPointOncePerTable; infer_instance

instance (x : Index d α κ) : Decidable (Valid x) := by
  unfold Valid; infer_instance

instance (a : Answer d α κ) : Decidable (MeasuredExactly a) := by
  unfold MeasuredExactly; infer_instance

instance (x : Index d α κ) (q : Point d α) (m : Cslib.Algorithms.Lean.TimeM ℕ (Option ℕ)) :
    Decidable (QueryTicksKeysPlusCandidates x q m) :=
  inferInstanceAs (Decidable (_ = _))

instance (x : Index d α κ) : Decidable (EntriesOnePerPointPerTable x) := by
  unfold EntriesOnePerPointPerTable; infer_instance

end LSH

end AlgoDesign.Geometry
