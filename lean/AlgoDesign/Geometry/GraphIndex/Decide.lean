/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Spec

/-! # The graph index: deciding the invariants

Each piece of `HNSW.Valid`, `Valid` itself, the picking rule's `PicksDiverse`, the report order
`ByDistance` and the memory bound decide on a concrete graph, so `decide` checks a small one, the
search sorts by `ByDistance`, and the Lean–Rust comparison evaluates them. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type}

instance (g : HNSW d α) (v l : ℕ) : Decidable (g.OnLayer v l) := by
  unfold OnLayer; infer_instance

instance (g : HNSW d α) : Decidable (DegreeBounded g) := by
  unfold DegreeBounded; infer_instance

instance (g : HNSW d α) : Decidable g.NestedLayers := by
  unfold NestedLayers; infer_instance

instance (g : HNSW d α) : Decidable g.NoSelfLinks := by
  unfold NoSelfLinks; infer_instance

instance (g : HNSW d α) : Decidable g.NoRepeatedLinks := by
  unfold NoRepeatedLinks; infer_instance

instance (g : HNSW d α) : Decidable g.EntryOnTop := by
  unfold EntryOnTop; split <;> infer_instance

instance (g : HNSW d α) : Decidable g.OneNodePerPoint := by
  unfold OneNodePerPoint; infer_instance

instance (g : HNSW d α) : Decidable (Valid g) := by
  unfold Valid; infer_instance

instance (g : HNSW d α) : Decidable (LinksPerPlaceAtMost g) := by
  unfold LinksPerPlaceAtMost; infer_instance

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

instance decPicksFrom (m : ℕ) (base : Point d α) :
    (sofar cs picked : List (Point d α)) → Decidable (PicksFrom m base sofar cs picked)
  | _, [], picked => inferInstanceAs (Decidable (picked = []))
  | sofar, c :: cs, picked => by
    unfold PicksFrom
    split
    · split
      · exact isFalse id
      · have := decPicksFrom m base (sofar ++ [c]) cs ‹_›
        infer_instance
    · exact decPicksFrom m base sofar cs picked

instance (p : Picking d α) : Decidable (PicksDiverse p) := by
  unfold PicksDiverse; infer_instance

instance (a b : Neighbor α) : Decidable (ByDistance a b) := by
  unfold ByDistance; infer_instance

end HNSW

end AlgoDesign.Geometry
