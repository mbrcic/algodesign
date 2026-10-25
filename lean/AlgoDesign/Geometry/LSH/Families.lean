/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Point
public import AlgoDesign.Geometry.Orientation
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# LSH: the chapter's two hash families

- **SimHash** (Charikar 2002): each bit is *which side* of a random hyperplane through the origin
  a point lies on, the sign of a dot product; `K` bits make a key (`simKey`). In the plane a bit
  is the orientation test of `orient`, the same "which side" question (`simBit_eq_orient`).
- **p-stable LSH** (Datar et al. 2004), "the grid on a line": project onto a random direction,
  shift by a random offset, and cut the line into cells of width `w` (`pStableKey`). Two points
  in the same cell have shadows less than `w` apart (`pStableKey_eq`).

The directions and offsets are inputs here; in the Rust they are drawn from a seeded Gaussian.
The probability that near points collide (`1 − θ/π` for SimHash; Datar et al. for p-stable) is
not stated: it needs measure theory this library does not have.
-/

@[expose] public section

namespace AlgoDesign.Geometry

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The dot product: the length of `p`'s shadow on `r`, scaled by `r`'s length. -/
def dot (r p : Point d α) : α := ∑ i, r i * p i

/-- One SimHash bit: is `p` on the non-negative side of the hyperplane with normal `r`? -/
def simBit (r p : Point d α) : Bool := decide (0 ≤ dot r p)

/-- A key: one bit per direction. -/
def simKey (rs : List (Point d α)) (p : Point d α) : List Bool := rs.map (simBit · p)

omit [IsStrictOrderedRing α] in
/-- **Which side, twice.** In the plane, the SimHash bit for normal `r` is the orientation of
`p` against the line through the origin along `r` turned a quarter turn clockwise, so that `r`
points to the line's left: `p` is on the positive side of the hyperplane exactly when it is on
the line's left or on it. -/
theorem simBit_eq_orient (r p : Point 2 α) :
    simBit r p = decide (0 ≤ orient (0, 0) (r 1, -(r 0)) (p 0, p 1)) := by
  unfold simBit dot orient
  congr 2
  simp only [Fin.sum_univ_two]
  ring

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- A projection is linear: shadows of sums are sums of shadows. -/
theorem dot_add (r p q : Point d α) : dot r (p + q) = dot r p + dot r q := by
  unfold dot; simp [mul_add, Finset.sum_add_distrib]

section PStable

variable {β : Type} [Field β] [LinearOrder β] [IsStrictOrderedRing β] [FloorRing β]

/-- **p-stable LSH, one cell number:** project `p` onto `a`, shift by `b`, and count cells of
width `w` along the line. -/
def pStableKey (a : Point d β) (b w : β) (p : Point d β) : ℤ := ⌊(dot a p + b) / w⌋

/-- **Same cell, close shadows.** Two points with the same cell number have projections less than
one cell width apart. (The converse fails: near points can straddle a cell boundary, which is why
the random offset and several tables are needed.) -/
theorem pStableKey_eq {a : Point d β} {b w : β} (hw : 0 < w) {p q : Point d β}
    (h : pStableKey a b w p = pStableKey a b w q) : |dot a p - dot a q| < w := by
  unfold pStableKey at h
  have h1 := Int.floor_le ((dot a p + b) / w)
  have h2 := Int.lt_floor_add_one ((dot a p + b) / w)
  have h3 := Int.floor_le ((dot a q + b) / w)
  have h4 := Int.lt_floor_add_one ((dot a q + b) / w)
  rw [h] at h1 h2
  have hu : (dot a p - dot a q) / w = (dot a p + b) / w - (dot a q + b) / w := by ring
  have hlt : |(dot a p - dot a q) / w| < 1 := by
    rw [hu, abs_sub_lt_iff]; constructor <;> linarith
  rw [abs_div, abs_of_pos hw, div_lt_one hw] at hlt
  exact hlt

end PStable

end AlgoDesign.Geometry
