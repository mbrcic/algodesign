/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Point
public import Mathlib.Data.List.Sort

/-!
# The scan's promise

The Geometry chapter's nearest-neighbor structures share one promise, the same answers as the scan:

> **Promise:** the same answers as the scan, the nearest stored point or the $k$ nearest. Also
> every stored point inside a rectangle.

This file is that promise, as the reader checks it. `Answers` holds one law per claim, for a
structure holding a given list of points: ask it for the nearest point, the $k$ nearest, or the
points inside a rectangle. `Promise` asks it of every structure a build makes, over the list the
build was given. Each structure states its contract as `Contract` in its `Spec.lean` and proves it
in its umbrella file. A design that answers differently (a new tree, an AI's candidate) is held to
these same laws.

`Promise` speaks of every list, the empty one included: so a structure built over no points
answers nothing (`Promise.build_nil`), and no structure picks its own idea of what it holds. The
answers are the operations' own; nothing here is counted.

The scan answers with an id and breaks ties by the lowest one (`Scan.lean`). The laws compare
squared distances and points, not ids, so the tie rule is not part of them.

**One shape, four places.** "The best `k` of a list of candidates, each with its exact squared
distance" is stated four times, over different candidates: here, over every stored point (the scan
and the k-d tree, so their answers are the true `k` nearest); in LSH's `MeasuredExactly` (with
`LSH.NearestFirst` for the order), over the points sharing a bucket with the query; in the graph
index's `Promise`, over the beam the walk ended with (RaBitQ's search re-checks such a beam); and in
the Workbench's `UpToK`, `EachOnce`, `NearestFirst` and `ExactDistance`, which ask only the form of
a reader's answer. The distances are exact everywhere; which points were measured is what differs.
-/

@[expose] public section

namespace AlgoDesign.Geometry

section Rectangle

variable {d : ℕ} {α : Type} [LinearOrder α]

/-- `x` is inside the rectangle with corners `lo` and `hi`, edges included: between them on every
axis. -/
@[simp] abbrev InRectangle (lo hi x : Point d α) : Prop := ∀ i, lo i ≤ x i ∧ x i ≤ hi i

end Rectangle

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The squared distances of `pts` from `q`, least first: the scan's ranking. Its first `k` are the
`k` least distances. -/
def dists (q : Point d α) (pts : List (Point d α)) : List α :=
  (pts.map (sqDist · q)).insertionSort (· ≤ ·)

namespace Nearest

/-- The scan's answers over the stored points `ps`: what a structure holding exactly `ps` owes,
for every query point, every `k` and every rectangle. -/
structure Answers (ps : List (Point d α)) (nearest : Point d α → Option (Point d α))
    (kNearest : ℕ → Point d α → List (Point d α))
    (rectangle : Point d α → Point d α → List (Point d α)) : Prop where
  /-- "The nearest stored point": its squared distance to the query is the least of the stored
  points', the first of the scan's ranking `dists`; and none when no point is stored. -/
  nearest_scan : ∀ q, (nearest q).map (sqDist · q) = (dists q ps).head?
  /-- The nearest point answered is a stored point. -/
  nearest_stored : ∀ q p, nearest q = some p → p ∈ ps
  /-- "Or the $k$ nearest": their squared distances, in order, are the $k$ least of the stored
  points'. -/
  kNearest_scan : ∀ k q, (kNearest k q).map (sqDist · q) = (dists q ps).take k
  /-- The $k$ nearest answered are stored points, each at most as often as it is stored. -/
  kNearest_stored : ∀ k q, (kNearest k q).Subperm ps
  /-- "Every stored point inside a rectangle": exactly those, each as often as it is stored, in
  any order. -/
  rectangle_filter : ∀ lo hi, (rectangle lo hi).Perm (ps.filter (InRectangle lo hi ·))

/-- **Promise:** the scan's. Its domain: every list of points `ps` a structure is built from, the
empty one included; built over `ps`, the structure gives the scan's `Answers` over `ps`. -/
def Promise {S : Type} (build : List (Point d α) → S)
    (nearest : Point d α → S → Option (Point d α))
    (kNearest : ℕ → Point d α → S → List (Point d α))
    (rectangle : Point d α → Point d α → S → List (Point d α)) : Prop :=
  ∀ ps, Answers ps (nearest · (build ps)) (kNearest · · (build ps)) (rectangle · · (build ps))

variable {S : Type} {build : List (Point d α) → S} {nearest : Point d α → S → Option (Point d α)}
  {kNearest : ℕ → Point d α → S → List (Point d α)}
  {rectangle : Point d α → Point d α → S → List (Point d α)}

omit [IsStrictOrderedRing α] in
/-- **Built over no points, a structure answers nothing**: no nearest point, no $k$ nearest,
nothing inside any rectangle. -/
theorem Promise.build_nil (p : Promise build nearest kNearest rectangle) (q lo hi : Point d α)
    (k : ℕ) :
    nearest q (build []) = none ∧ kNearest k q (build []) = [] ∧
      rectangle lo hi (build []) = [] := by
  refine ⟨?_, ?_, ?_⟩
  · cases h : nearest q (build []) with
    | none => rfl
    | some x => exact absurd ((p []).nearest_stored q x h) (List.not_mem_nil)
  · exact List.eq_nil_of_subset_nil ((p []).kNearest_stored k q).subset
  · simpa using (p []).rectangle_filter lo hi

end Nearest

end AlgoDesign.Geometry
