/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.BellmanFord.Spec
public import AlgoDesign.Paths.BellmanFord.Decide
public import AlgoDesign.Paths.BellmanFord.Basic
public import AlgoDesign.Paths.BellmanFord.Walk

/-! Cheapest paths with negative arrows: rounds over the number of arrows, and the cycle a last
round that still lowers a cost shows. The contract is in `BellmanFord/Spec.lean`; this file imports
the rounds and their proofs. -/

@[expose] public section

namespace AlgoDesign.Paths.BellmanFord

/-! ## The library's rounds meet their contract

`Contract` in `BellmanFord/Spec.lean` is the part of the contract that Lean checks; this proves
the library's procedures meet it, from the theorems the files above prove. -/

/-- The library's procedures: the start, one round and the run. -/
def ops : Ops where
  start := start
  round := round
  bellmanFord := bellmanFord
  Valid := Valid
  walks _ _ := rfl
  carries _ _ := ⟨rfl, rfl⟩
  keepsNetwork _ st := ⟨round_net st, round_source st⟩
  emptyValid _ _ _ hs := (valid_start hs).1
  emptyWellFormed _ _ _ hs := (valid_start hs).2
  stepKeeps _ hN _ hn hs h hw := (valid_round hN hs hn rfl ⟨h, hw⟩).1
  stepKeepsWellFormed _ hN _ hn hs h hw := (valid_round hN hs hn rfl ⟨h, hw⟩).2

/-- **The library's cheapest paths with negative arrows meet their contract** (`Contract` in
`BellmanFord/Spec.lean`). -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hN _ hs hno => bellmanFord_cheapest hN hs hno,
      fun _ hN _ hs _ h => bellmanFord_error hN hs h,
      fun _ hN _ hs h => bellmanFord_cycle_exists hN hs h⟩
  invariants _ := Iff.rfl
  cost _ hN s := bellmanFord_cost hN s

end AlgoDesign.Paths.BellmanFord
