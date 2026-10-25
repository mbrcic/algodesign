/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Points and squared distance

The chapter's points have real coordinates. The Lean states every theorem for coordinates in any
**ordered commutative ring** `α`: the reals, the rationals and the integers alike, so what is
proved is what the chapter says about real points. Distances are compared **squared**, which orders
points exactly as distances do and never needs a square root. Tests evaluate at `α = ℤ`, where
every value can be computed exactly.

The Rust (`rust/crates/algodesign/src/geometry/point.rs`) and the Python
(`python/algodesign/geometry/point.py`) use `f64`, which is not a ring: rounding is a
representation gap, and the orientation test is where it matters
(`Orientation.lean`).
-/

@[expose] public section

namespace AlgoDesign.Geometry

/-- A point in `d` dimensions with coordinates in `α`. -/
abbrev Point (d : ℕ) (α : Type) := Fin d → α

/-- One neighbor in an answer: its squared distance from the query, and its id, the point's number
in the input, counting from 0. Ids, not points, so that "each once" means each stored point once,
even when two stored points are equal. Rust: `Neighbor`. -/
structure Neighbor (α : Type) where
  /-- The squared distance from the query. -/
  sqDist : α
  /-- The point's number in the input, counting from 0 (in the graph index, its node). -/
  id : ℕ
deriving DecidableEq

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The origin, the default point (what `pts[i]!` reads past the end of a list). -/
instance : Inhabited (Point d α) := ⟨0⟩

/-- Squared Euclidean distance. -/
def sqDist (p q : Point d α) : α := ∑ i, (p i - q i) ^ 2

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem sqDist_comm (p q : Point d α) : sqDist p q = sqDist q p := by
  unfold sqDist; congr 1; ext i; ring

theorem sqDist_nonneg (p q : Point d α) : 0 ≤ sqDist p q := by
  unfold sqDist; positivity

/-- **The one-axis lower bound.** A squared distance is at least its contribution along any
single axis. Every pruning rule in the chapter is an instance of this. -/
theorem sq_axis_le_sqDist (p q : Point d α) (i : Fin d) :
    (p i - q i) ^ 2 ≤ sqDist p q := by
  unfold sqDist
  exact Finset.single_le_sum (f := fun j => (p j - q j) ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

end AlgoDesign.Geometry
