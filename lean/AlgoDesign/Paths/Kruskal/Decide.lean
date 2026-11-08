/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Kruskal.Spec

/-! # Cheapest spanning forest: deciding the definitions

Each piece of `Valid` and `WellFormed`, and the two themselves, decide on a concrete network and
state, so `decide` checks small cases and a separate Lean–Rust check evaluates them. Whether the
kept links are part of some cheapest spanning forest decides through the sublists of the link
ids. -/

@[expose] public section

namespace AlgoDesign.Paths.Kruskal

open AlgoDesign.Graphs LinkNetwork

instance decidableCheapestFirst (N : LinkNetwork) (ord : List ℕ) :
    Decidable (CheapestFirst N ord) := by
  unfold CheapestFirst; infer_instance

/-- Some cheapest spanning forest holds the kept links exactly when one among the sublists of the
link ids does. -/
theorem partOfCheapest_iff {st : State} :
    PartOfCheapest st ↔ ∃ T ∈ (List.range st.net.g.links.length).sublists,
      st.net.CheapestForest T ∧ ∀ i ∈ st.kept, i ∈ T := by
  refine ⟨fun ⟨T, hT, hk⟩ => ?_, fun ⟨T, _, h⟩ => ⟨T, h⟩⟩
  obtain ⟨G, hG, hp⟩ := hT.1.exists_sublist
  refine ⟨G, hG, ⟨(isSpanningForest_perm hp).2 hT.1, fun F' hF' => ?_⟩,
    fun i hi => hp.mem_iff.2 (hk i hi)⟩
  rw [total_perm hp]
  exact hT.2 F' hF'

instance decidablePartOfCheapest (st : State) :
    Decidable (PartOfCheapest st) :=
  decidable_of_iff' _ partOfCheapest_iff

instance decidableGroupsAreKeptJoins (st : State) :
    Decidable (GroupsAreKeptJoins st) := by
  unfold GroupsAreKeptJoins UnionFind.Same; infer_instance

instance decidableUnionFindReady (st : State) :
    Decidable (UnionFindReady st) := by
  unfold UnionFindReady; infer_instance

instance decidableKeptClosesNoCycle (st : State) :
    Decidable (KeptClosesNoCycle st) := by
  unfold KeptClosesNoCycle; infer_instance

instance decidableRestCheapestFirst (st : State) :
    Decidable (RestCheapestFirst st) := by
  unfold RestCheapestFirst; infer_instance

instance decidablePassedAreJoined (st : State) :
    Decidable (PassedAreJoined st) := by
  unfold PassedAreJoined; infer_instance

instance decidableWellFormed (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

instance decidableValid (st : State) : Decidable (Valid st) := by
  unfold Valid; infer_instance

end AlgoDesign.Paths.Kruskal
