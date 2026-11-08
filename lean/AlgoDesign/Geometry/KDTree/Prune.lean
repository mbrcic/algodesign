/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Spec
public import Mathlib.Tactic.Linarith

/-!
# Why pruning is safe

**Pruning soundness.** If the query sits on the left of a split, every point on the right is at
squared distance at least `(q_axis − split)²`. So when that is already no better than the best
found, the whole right side can be skipped. This is the circle-crosses-the-cut test of the
chapter's k-d section, and it is exactly the test that stops firing in high dimensions.

**The region lower bound.** `boxSqDist q lo hi` is the squared distance from `q` to an
axis-aligned box. It is ≤ the squared distance to every point inside the box.

Both are facts about squared distance, and need no invariant of the tree. The search itself
orders regions by `Region.bound`, the sum of the squared offsets to the cuts crossed
(`Search.lean`).
-/

@[expose] public section

namespace AlgoDesign.Geometry

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- **Pruning soundness.** With the query on the left of the split, a point on the right is at
least the split's distance away. -/
theorem far_side_bound (q x : Point d α) (a : Fin d) (s : α) (hq : q a ≤ s) (hx : s ≤ x a) :
    (s - q a) ^ 2 ≤ sqDist x q := by
  have h1 : (s - q a) ^ 2 ≤ (x a - q a) ^ 2 := by nlinarith
  exact h1.trans (sq_axis_le_sqDist x q a)

/-- **Pruning soundness, the mirror case.** With the query on the right of the split, a point on
the left is at least the split's distance away. -/
theorem far_side_bound_left (q x : Point d α) (a : Fin d) (s : α) (hq : s ≤ q a) (hx : x a ≤ s) :
    (q a - s) ^ 2 ≤ sqDist x q := by
  have h1 : (q a - s) ^ 2 ≤ (x a - q a) ^ 2 := by nlinarith
  exact h1.trans (sq_axis_le_sqDist x q a)

/-- Squared distance from `q` to the box `[lo, hi]` (per axis, clamped). -/
def boxSqDist (q lo hi : Point d α) : α :=
  ∑ i, (if q i < lo i then (lo i - q i) ^ 2 else if hi i < q i then (q i - hi i) ^ 2 else 0)

/-- **The region lower bound.** No point in the box is closer than the box itself. -/
theorem boxSqDist_le (q lo hi x : Point d α) (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) :
    boxSqDist q lo hi ≤ sqDist x q := by
  unfold boxSqDist sqDist
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨h1, h2⟩ := hx i
  split_ifs with hlo hhi
  · nlinarith
  · nlinarith
  · positivity

end AlgoDesign.Geometry
