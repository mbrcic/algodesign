/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Spec
public import AlgoDesign.Graphs.UnionFind.Decide
public import AlgoDesign.Graphs.UnionFind.Basic
public import AlgoDesign.Graphs.UnionFind.Find
public import AlgoDesign.Graphs.UnionFind.Union
public import AlgoDesign.Graphs.UnionFind.Promise
public import AlgoDesign.Graphs.UnionFind.Cost

/-! The union-find. Its contract is in `UnionFind/Spec.lean`; this file imports the whole
structure. -/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

/-! ## The library's union-find meets its contract

`Contract` in `UnionFind/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The library's operations, as the box names them; `findM` is the lookup's counting. -/
def ops : Ops where
  init := init
  find := find
  union := union
  joined := joined
  count := count
  Valid := Valid
  findM := findM
  counted := ret_findM
  emptyValid := valid_init
  emptyWellFormed := wellFormed_init
  keeps _ hu hw _ hx _ hy :=
    ⟨(valid_union hu hw hx hy).1, (valid_find hu hw _).1, (valid_joined hu hw _ _).1⟩
  keepsWellFormed _ hu hw _ hx _ hy :=
    ⟨(valid_union hu hw hx hy).2, (valid_find hu hw _).2, (valid_joined hu hw _ _).2⟩
  keepsItems _ hu hw _ hx _ hy :=
    ⟨(union_spec hu hw hx hy).n_eq, (find_spec hu hw _).n_eq, (joined_spec hu hw hy).n_eq⟩

/-- **The library's union-find meets its contract** (`Contract` in `UnionFind/Spec.lean`). The
near-constant cost of a long run of operations is argued, not proved. -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩,
      fun _ hu hw _ hx _ hy =>
        ⟨(union_spec hu hw hx hy).groups, (union_spec hu hw hx hy).answer⟩,
      fun u hu hw x _ y hy => ⟨find_eq_find_iff_same hu hw x y, fun i hi j hj => by
          change (u.find x).1.root i = (u.find x).1.root j ↔ u.Same i j
          rw [(find_spec hu hw x).same_root i hi, (find_spec hu hw x).same_root j hj]; rfl,
        joined_iff_same hu hw hy, fun _ hi _ hj => same_joined_iff hu hw hy hi hj⟩,
      fun _ _ hw => hw⟩
  invariants _ := Iff.rfl
  cost _ hu _ _ hx := time_findM_le_log hu hx

end AlgoDesign.Graphs.UnionFind
