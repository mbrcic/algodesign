/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Spec

/-!
# The k-d range query

dBCKO §5.2 (`SEARCHKDTREE`, p. 103): at a leaf, report the point if it lies in the rectangle; at
an inner node, enter a side only if the rectangle reaches it across the cut. This is the
**specification-level** traversal. dBCKO, the Rust and the Python also report a whole subtree at
once when its region lies inside the rectangle, which changes the cost, not the answer. The Rust
(`rust/crates/algodesign/src/geometry/kdtree.rs`) may visit the sides in any order, so the
guarantee is stated up to permutation (`rangeQuery_perm_filter`); this traversal happens to keep
the left-to-right order, which `rangeQuery_eq_filter` records. `InRectangle` is in `Nearest.lean`.
-/

@[expose] public section

namespace AlgoDesign.Geometry

variable {d : ℕ} {α : Type} [LinearOrder α]

namespace KDTree

/-- Report the stored points inside the rectangle `[lo, hi]`, skipping a side the rectangle cannot
reach. -/
def rangeQuery (lo hi : Point d α) : KDTree d α → List (Point d α)
  | leaf p => if InRectangle lo hi p then [p] else []
  | node a s l r =>
      (if lo a ≤ s then rangeQuery lo hi l else []) ++
        (if s ≤ hi a then rangeQuery lo hi r else [])

theorem rangeQuery_eq_filter {t : KDTree d α} (h : CutsSeparate t) (lo hi : Point d α) :
    rangeQuery lo hi t = (points t).filter (InRectangle lo hi ·) := by
  induction t with
  | leaf p => by_cases hp : InRectangle lo hi p <;> simp [rangeQuery, points, hp]
  | node a s l r ihl ihr =>
    obtain ⟨hl, hr, hpl, hpr⟩ := h
    simp only [rangeQuery, points, List.filter_append]
    congr 1
    · split_ifs with hs
      · exact ihl hpl
      · symm
        rw [List.filter_eq_nil_iff]
        intro x hx hin
        simp only [InRectangle, decide_eq_true_eq] at hin
        exact hs (le_trans (hin a).1 (hl x hx))
    · split_ifs with hs
      · exact ihr hpr
      · symm
        rw [List.filter_eq_nil_iff]
        intro x hx hin
        simp only [InRectangle, decide_eq_true_eq] at hin
        exact hs ((hr x hx).trans (hin a).2)

/-- **The k-d range query's guarantee.** On a tree whose cuts separate its points it reports
exactly the stored points in the rectangle, each once. -/
theorem rangeQuery_perm_filter {t : KDTree d α} (h : CutsSeparate t) (lo hi : Point d α) :
    (rangeQuery lo hi t).Perm ((points t).filter (InRectangle lo hi ·)) := by
  rw [rangeQuery_eq_filter h]

end KDTree
end AlgoDesign.Geometry
