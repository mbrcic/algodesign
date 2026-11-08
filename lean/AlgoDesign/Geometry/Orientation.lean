/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Which side of a line? The orientation test

The sign of a 2×2 determinant: positive if `a → b → c` turns left, negative if right, zero if the
three points are collinear (dBCKO §1.1; O'Rourke §1.3 `Area2`; Shewchuk 1997).

**What must correspond across languages is this exact sign.** The Rust
(`rust/crates/algodesign/src/geometry/orientation.rs`) computes it with Shewchuk's adaptive
floating-point expansions, a fast filter with an exact fallback. The Python
(`python/algodesign/geometry/orientation.py`) computes it with exact rational arithmetic.
Different arithmetic, the same contract: a representation difference, not a different variant.
Here the coordinates are in any ordered commutative ring, where the determinant is exact; what
floating point loses, and Shewchuk's method recovers, is exactly this exactness.
-/

@[expose] public section

namespace AlgoDesign.Geometry

variable {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Twice the signed area of the triangle `a b c`. -/
def orient (a b c : α × α) : α :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Swapping the first two points flips the turn. -/
theorem orient_swap (a b c : α × α) : orient b a c = - orient a b c := by
  unfold orient; ring

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Rotating the three points keeps the turn. -/
theorem orient_cycle (a b c : α × α) : orient b c a = orient a b c := by
  unfold orient; ring

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- A degenerate triple has no turn. -/
theorem orient_self_left (a c : α × α) : orient a a c = 0 := by
  unfold orient; ring

/-- **Zero means collinear.** For `a ≠ b`, `orient a b c = 0` exactly when `c - a` is a rational
multiple of `b - a`, stated without division: some nonzero `k` scales `c - a` to a multiple `m` of
`b - a`. -/
theorem orient_eq_zero_iff {a b c : α × α} (hab : a ≠ b) :
    orient a b c = 0 ↔
      ∃ k m : α, k ≠ 0 ∧ k * (c.1 - a.1) = m * (b.1 - a.1) ∧
        k * (c.2 - a.2) = m * (b.2 - a.2) := by
  constructor
  · intro h
    unfold orient at h
    by_cases h1 : b.1 = a.1
    · have h2 : b.2 ≠ a.2 := fun h2 => hab (Prod.ext h1.symm h2.symm)
      exact ⟨b.2 - a.2, c.2 - a.2, sub_ne_zero.mpr h2, by linear_combination -h, by ring⟩
    · exact ⟨b.1 - a.1, c.1 - a.1, sub_ne_zero.mpr h1, by ring, by linear_combination h⟩
  · rintro ⟨k, m, hk, h1, h2⟩
    have : k * orient a b c = 0 := by
      unfold orient; linear_combination (b.1 - a.1) * h2 - (b.2 - a.2) * h1
    exact (mul_eq_zero.mp this).resolve_left hk

end AlgoDesign.Geometry
