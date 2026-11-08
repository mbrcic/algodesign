/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Kruskal.Spec
public import AlgoDesign.Paths.Kruskal.Decide
public import AlgoDesign.Paths.Kruskal.Basic
public import AlgoDesign.Paths.Kruskal.Walk

/-! Cheapest spanning forest: the walk that takes the links cheapest first and keeps each one that
joins two groups. The contract is in `Kruskal/Spec.lean`; this file imports the walk and its
proofs. -/

@[expose] public section

namespace AlgoDesign.Paths.Kruskal

/-! ## The library's walk meets its contract

`Contract` in `Kruskal/Spec.lean` is the part of the contract that Lean checks; this proves the
library's procedures meet it, from the theorems the files above prove. -/

/-- The library's procedures: the order, the walk's start and step, and its answer. -/
def ops : Ops where
  order := order
  start := start
  step := step
  kruskal := kruskal
  Valid := Valid
  walks _ := rfl
  orderCheapestFirst := cheapestFirst_order
  carries _ _ := rfl
  keepsNetwork := step_net
  emptyValid _ hN _ hord := valid_start hN hord
  emptyWellFormed _ _ _ hord := wellFormed_start hord
  stepKeeps _ hN _ hn h hw hr := valid_step hN hn h hw hr
  stepKeepsWellFormed _ hN _ hn h hw hr := wellFormed_step hN hn h hw hr

/-- **The library's cheapest spanning forest meets its contract** (`Contract` in
`Kruskal/Spec.lean`). -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hN => (kruskal_cheapestForest hN).1.2.1,
      fun _ hN => ⟨(kruskal_cheapestForest hN).1.1, (kruskal_cheapestForest hN).1.2.2⟩,
      fun _ hN _ hF => (kruskal_cheapestForest hN).2 _ hF⟩
  invariants _ := Iff.rfl
  cost := kruskal_cost

end AlgoDesign.Paths.Kruskal
