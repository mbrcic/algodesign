/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Spec

/-! # Cheapest paths: deciding the definitions

Each piece of `Valid` and `WellFormed`, and the two themselves, decide on a concrete network, so
`decide` checks small cases and a separate Lean–Rust check evaluates them. A question about every
path decides through `Network.candidates`, every list of distinct arrow ids. -/

@[expose] public section

namespace AlgoDesign.Paths.Dijkstra

open Network

instance : DecidableRel EntryLe := fun a b =>
  inferInstanceAs (Decidable (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2))

instance decidableThrough (N : Network) (S : List ℕ) (s : ℕ) (p : List ℕ) :
    Decidable (Through N S s p) := by
  unfold Through; infer_instance

instance decidableLeadsBack (prev : ℕ → Option ℕ) (s : ℕ) (l : List ℕ) :
    Decidable (LeadsBack prev s l) := by
  unfold LeadsBack; infer_instance

instance decidableSettledAreCheapest (st : State) : Decidable (SettledAreCheapest st) := by
  unfold SettledAreCheapest; infer_instance

instance decidableKnownIsCheapestThroughSettled (st : State) :
    Decidable (KnownIsCheapestThroughSettled st) := by
  unfold KnownIsCheapestThroughSettled; infer_instance

instance decidableStartSettledFirst (st : State) : Decidable (StartSettledFirst st) := by
  unfold StartSettledFirst; infer_instance

instance decidableSettledRowsTried (st : State) : Decidable (SettledRowsTried st) := by
  unfold SettledRowsTried; infer_instance

instance decidableQueueHoldsKnown (st : State) : Decidable (QueueHoldsKnown st) := by
  unfold QueueHoldsKnown; infer_instance

/-- The paths back exist exactly when one is among the candidates. -/
theorem previousLeadsBack_iff {st : State} :
    PreviousLeadsBack st ↔ st.prev st.source = none ∧ ∀ v < st.net.g.n, ∀ d ∈ st.known v,
      ∃ p ∈ st.net.candidates, st.net.IsPath st.source p v ∧ st.net.pathCost p = d ∧
        Through st.net st.settled st.source p ∧
          LeadsBack st.prev st.source (st.net.visits st.source p) := by
  unfold PreviousLeadsBack
  refine and_congr_right fun _ => forall₂_congr fun v _ => forall₂_congr fun d _ => ?_
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp.mem_candidates, hp, h⟩, fun ⟨p, _, h⟩ => ⟨p, h⟩⟩

instance decidablePreviousLeadsBack (st : State) : Decidable (PreviousLeadsBack st) :=
  decidable_of_iff' _ previousLeadsBack_iff

instance decidableWellFormed (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

instance decidableValid (st : State) : Decidable (Valid st) := by
  unfold Valid; infer_instance

end AlgoDesign.Paths.Dijkstra
