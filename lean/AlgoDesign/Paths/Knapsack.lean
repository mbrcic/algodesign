/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Knapsack.Spec
public import AlgoDesign.Paths.Knapsack.Basic
public import AlgoDesign.Paths.Knapsack.Decide
public import AlgoDesign.Paths.Knapsack.Walk

/-! Knapsack as a longest path through the vertices (items decided, weight used), filled layer by
layer. The specification is in `Knapsack/Spec.lean`; this file imports the walk and its proofs. -/

@[expose] public section

namespace AlgoDesign.Paths.Knapsack

/-! ## The chapter's picture

Every path from `(0, 0)` to the last layer is one packing that fits, and every packing that fits
is one path, with the path's gain as the packing's value; so the longest path is the best packing.
Every move decides one more item, so the graph has no cycle. `Knapsack/Basic.lean` proves both,
as `paths_are_packings` (`PathsArePackings` in `Knapsack/Spec.lean`) and `no_cycle` (`NoCycle`). -/

/-! ## Examples, checked by the kernel -/

/-- **The cargo box**: a box of 10 kg and three orders, of 6 kg for a tip of 30 and two of 5 kg for
a tip of 20 each. Greedy by tip per kilo takes the 6 kg order first (5 a kilo against 4), and then
nothing else fits: 30. The two 5 kg orders together fill the box for 40, the best. -/
example : knapsack [⟨6, 30⟩, ⟨5, 20⟩, ⟨5, 20⟩] 10 = ⟨40, [1, 2]⟩ := by decide

example : IsBest [⟨6, 30⟩, ⟨5, 20⟩, ⟨5, 20⟩] 10 40 := by decide

/-- Greedy's packing fits but is not the best. -/
example : Fits [⟨6, 30⟩, ⟨5, 20⟩, ⟨5, 20⟩] 10 [0] ∧ ¬ IsBest [⟨6, 30⟩, ⟨5, 20⟩, ⟨5, 20⟩] 10 30 := by
  decide

end AlgoDesign.Paths.Knapsack
