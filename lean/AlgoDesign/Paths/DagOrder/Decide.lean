/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.DagOrder.Spec
public import AlgoDesign.Paths.Dijkstra.Decide
public import AlgoDesign.Graphs.TopoOrder.Decide

/-! # Cheapest paths in a graph with no cycle: deciding the definitions

Each piece of `Valid`, and `Valid` itself, decides on a concrete network, so `decide` checks small
cases. A question about every path decides through `Network.candidates`, every list of distinct
arrow ids. -/

@[expose] public section

namespace AlgoDesign.Paths.DagOrder

open Network
open Dijkstra (Through LeadsBack)

instance decidableInOrder (N : Network) (st : State) : Decidable (InOrder N st) := by
  unfold InOrder; infer_instance

instance decidableKnownIsCheapestThroughDone (N : Network) (s : ℕ) (st : State) :
    Decidable (KnownIsCheapestThroughDone N s st) := by
  unfold KnownIsCheapestThroughDone; infer_instance

/-- The paths back exist exactly when one is among the candidates. -/
theorem previousLeadsBack_iff {N : Network} {s : ℕ} {st : State} :
    PreviousLeadsBack N s st ↔ st.prev s = none ∧ ∀ v < N.g.n, ∀ d ∈ st.known v,
      ∃ p ∈ N.candidates, N.IsPath s p v ∧ N.pathCost p = d ∧ Through N st.done s p ∧
        LeadsBack st.prev s (N.visits s p) := by
  unfold PreviousLeadsBack
  refine and_congr_right fun _ => forall₂_congr fun v _ => forall₂_congr fun d _ => ?_
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp.mem_candidates, hp, h⟩, fun ⟨p, _, h⟩ => ⟨p, h⟩⟩

instance decidablePreviousLeadsBack (N : Network) (s : ℕ) (st : State) :
    Decidable (PreviousLeadsBack N s st) :=
  decidable_of_iff' _ previousLeadsBack_iff

instance decidableValid (N : Network) (s : ℕ) (st : State) : Decidable (Valid N s st) := by
  unfold Valid; infer_instance

end AlgoDesign.Paths.DagOrder
