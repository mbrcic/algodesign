/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Spec
public import AlgoDesign.Geometry.RangeTree.Build
public import AlgoDesign.Geometry.RangeTree.Query
public import AlgoDesign.Geometry.RangeTree.Cost
public import AlgoDesign.Geometry.RangeTree.Query2D
public import AlgoDesign.Geometry.RangeTree.Cost2D
public import AlgoDesign.Geometry.RangeTree.Decide

/-! The 1D range tree, and the 2D tree built on it (`RangeTree/Query2D.lean`; its counted query
and cost in `RangeTree/Cost2D.lean`). Its contract is in
`RangeTree/Spec.lean`; this file imports the whole structure. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace RangeTree1D

variable {α : Type} [LinearOrder α]

/-! ## The library's range tree meets its contract

`Contract` in `RangeTree/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The library's operations, as the box names them; `queryM` is the query's counting. -/
def ops : Ops α where
  build := ofList
  query := query
  Valid := Valid
  queryM := queryM
  counted lo hi _ h := ret_queryM h.1 lo hi

/-- **The library's range tree meets its contract** (`Contract` in `RangeTree/Spec.lean`). -/
theorem contract : Contract (ops : Ops α) where
  promise := ⟨fun _ h lo hi => query_eq_filter h.1 lo hi,
    fun _ => ofList_eq_none, fun _ _ h => leaves_ofList h, fun _ _ h => valid_ofList h⟩
  invariants _ := Iff.rfl
  cost _ h lo hi := time_queryM_le h lo hi

end RangeTree1D
end AlgoDesign.Geometry
