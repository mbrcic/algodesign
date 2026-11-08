/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Spec

/-! # Strong components: deciding the definitions

Each property of a grouping, each piece of Algorithm T's `Valid`, and `Valid` itself decide on a
concrete graph, so `decide` checks small cases and a separate Lean–Rust check evaluates them. -/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

instance (g : Digraph) (c : List ℕ) : Decidable (IsPartition g c) := by
  unfold IsPartition; infer_instance

instance (g : Digraph) (c : List ℕ) : Decidable (IdsTopological g c) := by
  unfold IdsTopological; infer_instance

instance (g : Digraph) (c : List ℕ) : Decidable (IsSccPartition g c) := by
  unfold IsSccPartition; infer_instance

instance (g : Digraph) (c : List ℕ) : Decidable (QuotientAcyclic g c) := by
  unfold QuotientAcyclic; infer_instance

namespace AlgorithmT

variable {g : Digraph}

instance (w : Walk) (v : ℕ) : Decidable (LeaderOut (g := g) w v) := by
  unfold LeaderOut; infer_instance

end AlgorithmT

instance (w : Walk) : Decidable (FollowersInFinishOrder w) := by
  unfold FollowersInFinishOrder; infer_instance

instance (w : Walk) : Decidable (ClimbBackIsEarliest w) := by
  unfold ClimbBackIsEarliest; infer_instance

instance (w : Walk) : Decidable (DoneIffGroupOut w) := by
  unfold DoneIffGroupOut; infer_instance

instance (w : Walk) : Decidable (Valid w) := by
  unfold Valid; infer_instance

end AlgoDesign.Graphs.Scc
