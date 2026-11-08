/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.TopoOrder.Spec
public import AlgoDesign.Graphs.TopoOrder.Decide
public import AlgoDesign.Graphs.TopoOrder.Basic
public import AlgoDesign.Graphs.TopoOrder.Kahn
public import AlgoDesign.Graphs.TopoOrder.Dfs

/-! Topological order: Kahn's method and the DFS order. The contract is in `TopoOrder/Spec.lean`;
this file imports both methods. -/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

/-! ## The library's methods meet their contract

`Contract` in `TopoOrder/Spec.lean` is the part of the contract that Lean checks; this proves the
library's procedures meet it, from the theorems the files above prove. -/

/-- The library's procedures: Kahn's start, step and walk. -/
def ops : Ops where
  kahnStart := start
  kahnStep := step
  kahn := kahn
  Valid := Valid
  walks _ := rfl
  carries _ := rfl
  keepsGraph := step_g
  emptyValid _ _ := valid_start
  stepKeeps _ _ h hq := valid_step h hq

/-- **The library's topological orders meet their contract** (`Contract` in
`TopoOrder/Spec.lean`). -/
theorem contract : Contract ops where
  promise _ hg := kahn_spec hg
  invariants _ := Iff.rfl
  cost := kahn_cost

end AlgoDesign.Graphs.TopoOrder
