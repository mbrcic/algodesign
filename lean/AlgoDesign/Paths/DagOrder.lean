/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.DagOrder.Spec
public import AlgoDesign.Paths.DagOrder.Decide
public import AlgoDesign.Paths.DagOrder.Walk

/-! Cheapest paths in a graph with no cycle: the walk that tries each vertex's row in a
topological order. The specification is in `DagOrder/Spec.lean`; this file imports the walk and
its proofs. -/

@[expose] public section

namespace AlgoDesign.Paths.DagOrder

/-! ## Examples, checked by the kernel -/

/-- A negative arrow: the way round through 2 costs less than the direct arrow to 1. -/
example : ((dagPaths ⟨⟨4, [(0, 1), (0, 2), (2, 1), (1, 3)]⟩, [5, 2, -4, 1]⟩ 0).map fun a =>
    ((List.range 4).map a.cost, (List.range 4).map a.prev)) =
      .ok ([some 0, some (-2), some 2, some (-1)], [none, some 2, some 0, some 1]) := by
  decide

/-- A cycle: Kahn's stuck set. -/
example : ((dagPaths ⟨⟨3, [(0, 1), (1, 0), (1, 2)]⟩, [1, 1, 1]⟩ 0).map fun a =>
    (List.range 3).map a.cost) = .error [0, 1, 2] := by
  decide

end AlgoDesign.Paths.DagOrder
