/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Workbench.Spec

/-! # The design project's contract: deciding its pieces

Each piece of the contract decides on a concrete answer, so `decide` checks a small one. -/

@[expose] public section

namespace AlgoDesign.Geometry.Workbench

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

instance (k : ℕ) (ans : Answer α) : Decidable (UpToK k ans) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (ps : List (Point d α)) (ans : Answer α) : Decidable (Stored ps ans) := by
  unfold Stored; infer_instance

instance (ans : Answer α) : Decidable (EachOnce ans) := by
  unfold EachOnce; infer_instance

instance (ans : Answer α) : Decidable (NearestFirst ans) := by
  unfold NearestFirst; infer_instance

instance (ps : List (Point d α)) (q : Point d α) (ans : Answer α) :
    Decidable (ExactDistance ps q ans) := by
  unfold ExactDistance; infer_instance

end AlgoDesign.Geometry.Workbench
