/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.AStar.Spec
public import AlgoDesign.Paths.AStar.Decide
public import AlgoDesign.Paths.AStar.Walk

/-! Heading for the goal: the cheapest-paths walk to one goal, its keys moved by an estimate of the
cost still to go. The contract is in `AStar/Spec.lean`; this file imports the search and its
proofs. -/

@[expose] public section

namespace AlgoDesign.Paths.AStar

open Dijkstra

/-! ## The library's search meets its contract

`Contract` in `AStar/Spec.lean` is the part of the contract that Lean checks; this proves the
library's procedures meet it, from the theorems the files above prove. -/

/-- The library's procedures: the search's start, step and answer. -/
def ops : Ops where
  start := start
  step := step
  astar := astar
  Valid := Valid
  walks _ _ _ _ := rfl
  carries _ _ _ _ := ⟨rfl, rfl, rfl, rfl⟩
  keepsNetwork := step_fields
  emptyValid _ _ _ _ _ h hs := (valid_start h hs).1
  emptyWellFormed _ _ _ _ _ h hs := (valid_start h hs).2
  stepKeeps _ hN _ hn hs h hw hq := (valid_step hN hn hs ⟨h, hw⟩ hq).1
  stepKeepsWellFormed _ hN _ hn hs h hw hq := (valid_step hN hn hs ⟨h, hw⟩ hq).2

/-- **The library's search meets its contract** (`Contract` in `AStar/Spec.lean`). -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hN _ _ _ h hs _ hr => astar_goal hN h hs hr,
      fun _ _ _ _ _ _ hs ht => astar_previous hs ht,
      fun _ _ _ _ _ _ hs ht hr => astar_unreached hs ht hr⟩
  invariants _ := Iff.rfl
  cost N est s t := by
    have hc := final_counted N est s t
    exact ⟨hc.1, nodup_tried hc.1, by rw [Nat.add_comm]; exact hc.2⟩

end AlgoDesign.Paths.AStar
