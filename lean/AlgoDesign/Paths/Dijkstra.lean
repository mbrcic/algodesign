/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Spec
public import AlgoDesign.Paths.Dijkstra.Decide
public import AlgoDesign.Paths.Dijkstra.Basic
public import AlgoDesign.Paths.Dijkstra.Walk
public import AlgoDesign.Paths.Dijkstra.Goal

/-! Cheapest paths: the walk that settles the cheapest known vertex first. The contract is in
`Dijkstra/Spec.lean`; this file imports the walk and its proofs, and the walk stopped at one goal
(`dijkstraTo`). -/

@[expose] public section

namespace AlgoDesign.Paths.Dijkstra

/-! ## The library's walk meets its contract

`Contract` in `Dijkstra/Spec.lean` is the part of the contract that Lean checks; this proves the
library's procedures meet it, from the theorems the files above prove. -/

/-- The library's procedures: the walk's start, step and answer. -/
def ops : Ops where
  start := start
  step := step
  dijkstra := dijkstra
  Valid := Valid
  walks _ _ := rfl
  carries _ _ := ⟨rfl, rfl⟩
  keepsNetwork := step_net_source
  emptyValid _ _ _ _ hs := (valid_start hs).1
  emptyWellFormed _ _ _ _ hs := (valid_start hs).2
  stepKeeps _ hN hnn _ hn hs h hw hq := (valid_step hN hnn hs hn rfl ⟨h, hw⟩ hq).1
  stepKeepsWellFormed _ hN hnn _ hn hs h hw hq := (valid_step hN hnn hs hn rfl ⟨h, hw⟩ hq).2

/-- **The library's cheapest paths meet their contract** (`Contract` in `Dijkstra/Spec.lean`). -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hN hnn _ hs _ _ hr => dijkstra_reached hN hnn hs hr,
      fun _ _ _ hs _ hv => dijkstra_previous hs hv,
      fun _ _ _ hs _ hv hr => dijkstra_unreached hs hv hr⟩
  invariants _ := Iff.rfl
  cost := dijkstra_cost

/-! ## Examples, checked by the kernel -/

/-- **With one negative arrow, a settled cost can be wrong**, on the chapter's corner of the
town: the Bakery 0, the Square 1 and the Hilltop 2; the Bakery to the Square costs 2, the Bakery to
the Hilltop 4, and the Hilltop down to the Square −3. The walk settles the Square at 2, and its
cheapest path, over the Hilltop, costs 1. -/
theorem settled_cost_can_be_wrong :
    let N : Network := ⟨⟨3, [(0, 1), (0, 2), (2, 1)]⟩, [2, 4, -3]⟩
    N.WellFormed ∧ ¬ N.NoArrowBelowZero ∧ 1 ∈ (ops.final N 0).settled ∧
      (dijkstra N 0).cost 1 = some 2 ∧ N.Cheapest 0 1 (some 1) := by
  decide

end AlgoDesign.Paths.Dijkstra
