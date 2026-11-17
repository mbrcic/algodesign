/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.AStar.Spec
public import AlgoDesign.Paths.Dijkstra.Decide

/-! # Heading for the goal: deciding the definitions

The box's invariant, the piece not in the box, `Valid` and `WellFormed` decide on a concrete
network, so `decide` checks small cases. -/

@[expose] public section

namespace AlgoDesign.Paths.AStar

instance decidableConsistent (N : Network) (t : ℕ) (est : List ℤ) :
    Decidable (Consistent N t est) := by
  unfold Consistent; infer_instance

instance decidableEstimateIsConsistent (st : State) : Decidable (EstimateIsConsistent st) := by
  unfold EstimateIsConsistent; infer_instance

instance decidableWalkIsCheapestPathsOnChangedCosts (st : State) :
    Decidable (WalkIsCheapestPathsOnChangedCosts st) := by
  unfold WalkIsCheapestPathsOnChangedCosts; infer_instance

instance decidableSettledAtMostOnce (st : State) : Decidable (SettledAtMostOnce st) := by
  unfold SettledAtMostOnce; infer_instance

instance decidableWorkAsCheapestPaths (N : Network) (st : State) :
    Decidable (WorkAsCheapestPaths N st) := by
  unfold WorkAsCheapestPaths; infer_instance

instance decidableWellFormed (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

instance decidableValid (st : State) : Decidable (Valid st) := by
  unfold Valid; infer_instance

end AlgoDesign.Paths.AStar
