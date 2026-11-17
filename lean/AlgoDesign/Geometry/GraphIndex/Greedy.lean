/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Spec

/-!
# The graph index: the greedy step

The walk steps to the neighbor nearest the query while one is strictly nearer. Proved here: a
step never moves away (`greedyStep_le`). It does not follow that the walk reaches the nearest
point, and no search guarantee is claimed: none exists for this variant. Rust:
`hnsw::greedy_step`.

`greedyNode` is the same step over a graph's nodes on one layer (`points_greedyNode`: its point is
`greedyStep`'s). The Rust descends the upper layers by SEARCH-LAYER with `ef = 1`, a beam of one
that moves as repeated greedy steps do, ties included: both move to the nearest neighbor, a tie
going to the one first in list order, and a node already visited is never strictly nearer
(proved: `searchLayer_one`, `Search.lean`).
-/

@[expose] public section

namespace AlgoDesign.Geometry.HNSW

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- One greedy step: move to the neighbor nearest `q` if it is strictly nearer, else stay. -/
def greedyStep (q cur : Point d α) (neighbors : List (Point d α)) : Point d α :=
  neighbors.foldl (fun best x => if sqDist x q < sqDist best q then x else best) cur

omit [IsStrictOrderedRing α] in
/-- **The greedy step never moves away.** It does *not* follow that the walk reaches the nearest
neighbor: a walk can stop at a point none of whose neighbors is nearer. -/
theorem greedyStep_le (q cur : Point d α) (neighbors : List (Point d α)) :
    sqDist (greedyStep q cur neighbors) q ≤ sqDist cur q := by
  induction neighbors generalizing cur with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [greedyStep, List.foldl_cons] at ih ⊢
    split_ifs with hx
    · exact (ih x).trans hx.le
    · exact ih cur

/-- The nearer of `best` and node `x` of the graph to `q`: `x` if it is strictly nearer, else
`best`. -/
def nearer (g : HNSW d α) (q : Point d α) (best x : ℕ) : ℕ :=
  if sqDist g.points[x]! q < sqDist g.points[best]! q then x else best

/-- One greedy step on layer `l`, over nodes: from `v`, move to the node of its list on that layer
nearest `q` if one is strictly nearer, a tie going to the first in list order, else stay. -/
def greedyNode (g : HNSW d α) (q : Point d α) (l v : ℕ) : ℕ :=
  (g.neighbors v l).foldl (nearer g q) v

omit [IsStrictOrderedRing α] in
/-- The step over nodes moves as `greedyStep` does over their points. -/
theorem points_greedyNode (g : HNSW d α) (q : Point d α) (l v : ℕ) :
    g.points[greedyNode g q l v]! =
      greedyStep q g.points[v]! ((g.neighbors v l).map (g.points[·]!)) := by
  unfold greedyNode greedyStep
  generalize g.neighbors v l = es
  induction es generalizing v with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, nearer]
    by_cases h : sqDist g.points[x]! q < sqDist g.points[v]! q
    · simp only [h, ite_true]; exact ih x
    · simp only [h, ite_false]; exact ih v

end AlgoDesign.Geometry.HNSW
