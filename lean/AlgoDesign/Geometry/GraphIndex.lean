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
  search := search
  finish := finish
  insert := insert
  Valid := Valid
  insertStores := points_insert
  keepsCaps := caps_insert
  emptyValid := valid_empty
  emptyWellFormed := wellFormed_empty
  insertKeeps _ _ _ _ hm hg hw hc := (valid_insert hm hg hw hc).1
  insertKeepsWellFormed _ _ _ _ hm hg hw hc := (valid_insert hm hg hw hc).2
  buildValid _ h hm := valid_build h hm
  buildWellFormed _ h hm := wellFormed_build h hm

omit [IsStrictOrderedRing α] in
/-- **The library's search meets `Ops.WalksToBeam`**: on a valid, well-formed graph, the search is
the library's last step on a beam of stored nodes, each once, not empty when `k` is positive and
the graph has nodes, at most `max ef k` long (`search_eq_finish`, `Search.lean`). -/
theorem searchSpec : (ops : Ops d α).WalksToBeam :=
  fun g q k ef hg hw => search_eq_finish g q k ef hg hw

/-- **The library's graph index meets its contract** (`Contract` in `GraphIndex/Spec.lean`). -/
theorem contract : Contract (ops : Ops d α) where
  promise := ⟨searchSpec, fun pts q k beam hnd hb => promise_finish pts q k beam hnd hb⟩
  invariants _ := Iff.rfl
  cost _ hg _ := linksPerPointAtMost_of_valid hg


end HNSW

end AlgoDesign.Geometry
