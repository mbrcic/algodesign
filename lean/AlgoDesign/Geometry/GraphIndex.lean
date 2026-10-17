/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Spec
public import AlgoDesign.Geometry.GraphIndex.Decide
public import AlgoDesign.Geometry.GraphIndex.Select
public import AlgoDesign.Geometry.GraphIndex.Greedy
public import AlgoDesign.Geometry.GraphIndex.Finish
public import AlgoDesign.Geometry.GraphIndex.Search
public import AlgoDesign.Geometry.GraphIndex.Insert
public import AlgoDesign.Geometry.GraphIndex.Cost

/-! The graph index (HNSW, and the flat graph as the same structure on one layer). Its contract is
in `GraphIndex/Spec.lean`; this file imports the whole structure. -/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ## The library's graph index meets its contract

`Contract` in `GraphIndex/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The library's operations, as the box names them. -/
def ops : Ops d α where
  select m base cs := selectNeighbors m base [] cs
  finish := finish
  insert := insert
  Valid := Valid

/-- **The library's graph index meets its contract** (`Contract` in `GraphIndex/Spec.lean`). -/
theorem contract : Contract (ops : Ops d α) where
  promise := ⟨fun pts q k beam hnd hb => promise_finish pts q k beam hnd hb,
    points_insert, caps_insert,
    valid_empty, fun _ _ _ _ hm hg hc => valid_insert hm hg hc, fun _ h hm => valid_build h hm,
    fun m base cs hs => picksDiverse_selectNeighbors m base cs hs⟩
  invariants _ := Iff.rfl
  cost _ hg := linksPerPlaceAtMost_of_valid hg

omit [IsStrictOrderedRing α] in
/-- **The library's search meets `SearchSpec`**: on a valid graph, the search is the library's
last step on a beam of stored nodes, each once, not empty when `k` is positive and the graph has
nodes, at most `max ef k` long (`search_eq_finish`, `Search.lean`). -/
theorem searchSpec : SearchSpec (ops : Ops d α) search :=
  fun g q k ef hg => search_eq_finish g q k ef hg

end HNSW

end AlgoDesign.Geometry
