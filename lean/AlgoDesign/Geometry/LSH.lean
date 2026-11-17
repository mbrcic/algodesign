/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.LSH.Spec
public import AlgoDesign.Geometry.LSH.Families
public import AlgoDesign.Geometry.LSH.Rerank
public import AlgoDesign.Geometry.LSH.Build
public import AlgoDesign.Geometry.LSH.Query
public import AlgoDesign.Geometry.LSH.Cost
public import AlgoDesign.Geometry.LSH.Decide

/-! Locality-sensitive hashing. Its contract is in `LSH/Spec.lean`; this file imports the whole
structure and proves the library's operations meet `Contract`. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- The library's operations, as the box names them; `nearestM` is the query's counting. -/
def ops : Ops d α κ where
  build := build
  nearest := nearest
  kNearest := kNearest
  Valid := Valid
  nearestM := nearestM
  counted := ret_nearestM
  buildStores := build_stores
  buildValid := valid_build
  buildWellFormed := wellFormed_build

omit [IsStrictOrderedRing α] in
/-- **The library's LSH meets its contract** (`Contract` in `LSH/Spec.lean`). -/
theorem contract : Contract (ops : Ops d α κ) where
  promise :=
    ⟨fun _ q hv _ => measuredExactly_nearest hv q,
      fun _ q k hv _ => measuredExactly_kNearest hv q k⟩
  invariants _ := Iff.rfl
  cost := ⟨time_nearestM, fun _ hv hw _ ht => entries_length hv hw ht⟩

end LSH

end AlgoDesign.Geometry
