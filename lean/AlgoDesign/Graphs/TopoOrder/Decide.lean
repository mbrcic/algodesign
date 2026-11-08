/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.TopoOrder.Spec

/-! # Topological order: deciding the definitions

Each property of an answer that needs no search, each piece of `Valid`, and `Valid` itself decide
on a concrete graph, so `decide` checks small cases and a separate Lean–Rust check
evaluates them. The rest, `RestPlaceable` and `IsStuck`, decide through their checker
(`TopoOrder/Basic.lean`). -/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

instance decidableBefore (l : List ℕ) (u v : ℕ) : Decidable (Before l u v) :=
  inferInstanceAs (Decidable ([u, v].Sublist l))

instance decidableIsTopoOrder (g : Digraph) (l : List ℕ) : Decidable (IsTopoOrder g l) := by
  unfold IsTopoOrder; infer_instance

instance decidableAfterWaits (g : Digraph) (l : List ℕ) : Decidable (AfterWaits g l) := by
  unfold AfterWaits; infer_instance

instance decidableWaitsInside (g : Digraph) (s : List ℕ) : Decidable (WaitsInside g s) := by
  unfold WaitsInside; infer_instance

instance decidablePlacedAfterWaits (st : KahnState) :
    Decidable (PlacedAfterWaits st) := by
  unfold PlacedAfterWaits; infer_instance

instance decidableCountsUnplacedWaits (st : KahnState) :
    Decidable (CountsUnplacedWaits st) := by
  unfold CountsUnplacedWaits; infer_instance

instance decidableReadyIsZero (st : KahnState) : Decidable (ReadyIsZero st) := by
  unfold ReadyIsZero; infer_instance

instance decidableValid (st : KahnState) : Decidable (Valid st) := by
  unfold Valid; infer_instance

end AlgoDesign.Graphs.TopoOrder
