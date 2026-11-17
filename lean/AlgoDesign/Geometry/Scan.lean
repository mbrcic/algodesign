/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Point

/-!
# Checking every point: the nearest-neighbor specification

The chapter's first answer and every later structure's oracle. `scanNearest pts q` is the id (the
number in `pts`, counting from 0) of a stored point at the least squared distance from `q`, and
among several such points **the lowest id**, the one stored first. The Rust
(`rust/crates/algodesign/src/geometry/scan.rs`) keeps a bounded heap for *k* neighbors; for
`k = 1` it computes this.
-/

@[expose] public section

namespace AlgoDesign.Geometry

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- One step of the scan: keep the incumbent unless the candidate is *strictly* closer. -/
def scanStep (pts : List (Point d α)) (q : Point d α) (best : Option ℕ) (i : ℕ) : Option ℕ :=
  match best, pts[i]? with
  | _, none => best
  | none, some _ => some i
  | some b, some p =>
      match pts[b]? with
      | none => some i
      | some pb => if sqDist p q < sqDist pb q then some i else some b

/-- The id of a nearest stored point, or `none` when no point is stored. -/
def scanNearest (pts : List (Point d α)) (q : Point d α) : Option ℕ :=
  (List.range pts.length).foldl (scanStep pts q) none

/-- The scan after its first `n` steps. -/
def scanUpTo (pts : List (Point d α)) (q : Point d α) (n : ℕ) : Option ℕ :=
  (List.range n).foldl (scanStep pts q) none

/-- What the scan knows after `n` steps: nothing yet if `n = 0`; otherwise an id among the first
`n` whose point is as close as any of them, and strictly closer than every lower id. -/
def ScanInv (pts : List (Point d α)) (q : Point d α) (n : ℕ) : Option ℕ → Prop
  | none => n = 0
  | some i => i < n ∧ (∀ j < n, sqDist pts[i]! q ≤ sqDist pts[j]! q) ∧
      ∀ j < i, sqDist pts[i]! q < sqDist pts[j]! q

omit [IsStrictOrderedRing α] in
theorem scanUpTo_succ (pts : List (Point d α)) (q : Point d α) (n : ℕ) :
    scanUpTo pts q (n + 1) = scanStep pts q (scanUpTo pts q n) n := by
  simp [scanUpTo, List.range_succ, List.foldl_append]

omit [IsStrictOrderedRing α] in
theorem scanUpTo_inv (pts : List (Point d α)) (q : Point d α) :
    ∀ n ≤ pts.length, ScanInv pts q n (scanUpTo pts q n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < pts.length := by omega
    have ih' := ih (by omega)
    have hpn : pts[n]? = some pts[n] := List.getElem?_eq_getElem hlt
    have hbn : pts[n]! = pts[n] := by simp [hlt]
    rw [scanUpTo_succ]
    cases h : scanUpTo pts q n with
    | none =>
      rw [h] at ih'
      simp only [ScanInv] at ih'
      subst ih'
      simp only [scanStep, hpn, ScanInv]
      exact ⟨by omega, fun j hj => by
        have : j = 0 := by omega
        subst this; exact le_rfl, fun j hj => absurd hj (by omega)⟩
    | some i =>
      rw [h] at ih'
      obtain ⟨hi, hmin, hlow⟩ := ih'
      have hpi : pts[i]? = some pts[i] := List.getElem?_eq_getElem (by omega)
      have hbi : pts[i]! = pts[i] := by simp [show i < pts.length by omega]
      simp only [scanStep, hpn, hpi]
      split_ifs with hc
      · rw [← hbn, ← hbi] at hc
        refine ⟨by omega, fun j hj => ?_, fun j hj => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact le_trans hc.le (hmin j hj)
          · subst hj; exact le_rfl
        · exact lt_of_lt_of_le hc (hmin j hj)
      · rw [← hbn, ← hbi] at hc
        refine ⟨by omega, fun j hj => ?_, hlow⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact hmin j hj
        · subst hj; exact not_lt.mp hc

omit [IsStrictOrderedRing α] in
theorem scanNearest_eq_scanUpTo (pts : List (Point d α)) (q : Point d α) :
    scanNearest pts q = scanUpTo pts q pts.length := rfl

omit [IsStrictOrderedRing α] in
theorem scanNearest_isSome_iff (pts : List (Point d α)) (q : Point d α) :
    (scanNearest pts q).isSome ↔ pts ≠ [] := by
  have inv := scanUpTo_inv pts q pts.length le_rfl
  rw [← scanNearest_eq_scanUpTo] at inv
  cases h : scanNearest pts q with
  | none =>
    rw [h] at inv
    simp only [ScanInv, List.length_eq_zero_iff] at inv
    simp [inv]
  | some i =>
    rw [h] at inv
    have : pts.length ≠ 0 := by have := inv.1; omega
    simpa [List.length_eq_zero_iff] using this

omit [IsStrictOrderedRing α] in
theorem scanNearest_mem {pts : List (Point d α)} {q : Point d α} {i : ℕ}
    (h : scanNearest pts q = some i) : i < pts.length := by
  have inv := scanUpTo_inv pts q pts.length le_rfl
  rw [← scanNearest_eq_scanUpTo, h] at inv
  exact inv.1

omit [IsStrictOrderedRing α] in
theorem scanNearest_le {pts : List (Point d α)} {q : Point d α} {i : ℕ}
    (h : scanNearest pts q = some i) (j : ℕ) (hj : j < pts.length) :
    sqDist pts[i]! q ≤ sqDist pts[j]! q := by
  have inv := scanUpTo_inv pts q pts.length le_rfl
  rw [← scanNearest_eq_scanUpTo, h] at inv
  exact inv.2.1 j hj

omit [IsStrictOrderedRing α] in
/-- **The tie rule.** No point with a lower id is equally close. -/
theorem scanNearest_lowest {pts : List (Point d α)} {q : Point d α} {i : ℕ}
    (h : scanNearest pts q = some i) (j : ℕ) (hj : j < i) :
    sqDist pts[i]! q < sqDist pts[j]! q := by
  have inv := scanUpTo_inv pts q pts.length le_rfl
  rw [← scanNearest_eq_scanUpTo, h] at inv
  exact inv.2.2 j hj

end AlgoDesign.Geometry
