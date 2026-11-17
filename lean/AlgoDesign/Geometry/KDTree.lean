/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Build
public import AlgoDesign.Geometry.KDTree.Prune
public import AlgoDesign.Geometry.KDTree.Range
public import AlgoDesign.Geometry.KDTree.Search
public import AlgoDesign.Geometry.KDTree.Decide

/-!
# The k-d tree

The whole structure: the specification and its contract (`KDTree/Spec.lean`), the build, the
pruning bounds, the range query and best-first search with the queries on it. `Contract` in
`KDTree/Spec.lean` is the contract; this file proves the library's operations meet it.
-/

@[expose] public section

namespace AlgoDesign.Geometry.KDTree

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

variable [NeZero d]

/-- The library's operations, as the box names them: the build, and the queries on a built tree
(nothing on no tree). -/
def ops : Ops d α where
  build := ofList
  nearest q o := o.bind (nearest q)
  kNearest k q o := o.elim [] (kNearest k q)
  rectangle lo hi o := o.elim [] (rangeQuery lo hi)
  Valid := Valid
  buildValid ps t h := by
    obtain ⟨hne, rfl⟩ := ofList_eq_some h
    exact valid_build ps hne

omit [NeZero d] in
/-- **The scan's answers on a tree whose cuts separate its points**, over any list `ps` the tree
holds in some order. -/
theorem answers_of_cutsSeparate {t : KDTree d α} {ps : List (Point d α)} (h : CutsSeparate t)
    (hp : t.points.Perm ps) :
    Nearest.Answers ps (nearest · t) (kNearest · · t) (rangeQuery · · t) where
  nearest_scan q := by
    simp only [nearest]
    rw [← List.head?_map, (kNearest_spec h hp 1 q).1, List.head?_take]
    simp
  nearest_stored q p hq := (kNearest_spec h hp 1 q).2.subset (List.mem_of_head? hq)
  kNearest_scan k q := (kNearest_spec h hp k q).1
  kNearest_stored k q := (kNearest_spec h hp k q).2
  rectangle_filter lo hi := (rangeQuery_perm_filter h lo hi).trans (hp.filter _)

/-- **The scan's answers on every valid tree**, built or not, over the points it holds. -/
theorem answers_of_valid {t : KDTree d α} (h : t.Valid) :
    Nearest.Answers t.points ((ops (d := d) (α := α)).nearest · (some t))
      (ops.kNearest · · (some t)) (ops.rectangle · · (some t)) :=
  answers_of_cutsSeparate h.1 (List.Perm.refl _)

/-- **Promise:** the scan's. -/
theorem promise : Nearest.Promise (ops (d := d) (α := α)).build ops.nearest ops.kNearest
    ops.rectangle := by
  intro ps
  cases ho : ofList ps with
  | none =>
    obtain rfl := ofList_eq_none.1 ho
    refine ⟨fun q => ?_, fun q p hp => ?_, fun k q => ?_, fun k q => ?_, fun lo hi => ?_⟩ <;>
      simp_all [ops, dists]
  | some t =>
    obtain ⟨hne, rfl⟩ := ofList_eq_some ho
    simpa [ops, ho] using answers_of_cutsSeparate (valid_build ps hne).1 (points_build ps hne)

/-- **The library's k-d tree meets its contract** (`Contract` in `KDTree/Spec.lean`). -/
theorem contract : Contract (ops : Ops d α) where
  promise := promise
  invariants _ := Iff.rfl

end AlgoDesign.Geometry.KDTree
