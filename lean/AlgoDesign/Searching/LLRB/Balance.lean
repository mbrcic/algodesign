/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Insert

/-!
# LLRB: height

`height_le_two_log`: a valid tree of `n` keys has height at most `2 * Nat.log2 (n + 1)`, from
`two_pow_bheight_le_size_succ` (a tree of black height `b` holds at least `2 ^ b - 1` keys) and
`height_le_two_mul` (no path is more than twice the black height, since no two reds touch).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

omit [LinearOrder α] in
/-- `bheight` is always positive — `leaf` alone contributes `1`, and every node only ever adds to
its left spine's count on top of that. The one fact `moveRedLeft_spec`/`moveRedRight_spec`'s
case-bash needs that isn't otherwise visible to `omega`: without it, `omega` treats `t.bheight` as
an unconstrained `Nat` atom and can't see that e.g. `Balanced`'s equations pinning some sibling's
`bheight` down to `0` are already contradictory on their own. -/
theorem bheight_pos (t : LLRB α) : 1 ≤ bheight t := by
  induction t with
  | leaf => simp [bheight]
  | node c l _ _ ihl _ => simp only [bheight]; omega

omit [LinearOrder α] in
theorem two_pow_bheight_le_size_succ {t : LLRB α} (h : Balanced t) :
    2 ^ (bheight t - 1) ≤ t.size + 1 := by
  induction t with
  | leaf => simp [bheight, size]
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hbl, hbr⟩ := h
    have hL := ihl hbl
    have hR := ihr hbr
    have hpos := bheight_pos l
    cases c with
    | black =>
      change 2 ^ bheight l ≤ l.size + r.size + 1 + 1
      rw [← Nat.sub_add_cancel hpos, Nat.pow_succ, Nat.mul_comm]
      have hR' : 2 ^ (bheight l - 1) ≤ r.size + 1 := by
        rw [hbh]; exact hR
      omega
    | red =>
      change 2 ^ (bheight l - 1) ≤ l.size + r.size + 1 + 1
      omega

omit [LinearOrder α] in
theorem height_le_two_mul {t : LLRB α} (hnrr : NoRedRed t) (hbal : Balanced t) :
    (¬ t.IsRed → height t ≤ 2 * (bheight t - 1)) ∧
    (t.IsRed → height t ≤ 2 * (bheight t - 1) + 1) := by
  induction t with
  | leaf => simp [height, bheight, IsRed]
  | node c l k r ihl ihr =>
    obtain ⟨hc, hl_nrr, hr_nrr⟩ := hnrr
    obtain ⟨hbh, hl_bal, hr_bal⟩ := hbal
    have hL := ihl hl_nrr hl_bal
    have hR := ihr hr_nrr hr_bal
    cases c with
    | black =>
      constructor
      · intro _
        have hl_le : height l ≤ 2 * (bheight l - 1) + 1 := by
          by_cases hlred : l.IsRed
          · have := hL.2 hlred; omega
          · have := hL.1 hlred; omega
        have hr_le : height r ≤ 2 * (bheight r - 1) + 1 := by
          by_cases hrred : r.IsRed
          · have := hR.2 hrred; omega
          · have := hR.1 hrred; omega
        rw [← hbh] at hr_le
        have hmax : max (height l) (height r) ≤ 2 * (bheight l - 1) + 1 :=
          Nat.max_le.mpr ⟨hl_le, hr_le⟩
        have hpos := bheight_pos l
        have htwo : 2 * (bheight l - 1) + 1 + 1 = 2 * bheight l := by omega
        have hbh_node : bheight (node .black l k r) - 1 = bheight l := by simp [bheight]
        rw [height_node, hbh_node]
        exact Nat.le_trans (Nat.add_le_add_right hmax 1) (Nat.le_of_eq htwo)
      · intro h
        simp [IsRed] at h
    | red =>
      have hl_notred : ¬ l.IsRed := (hc rfl).1
      have hr_notred : ¬ r.IsRed := (hc rfl).2
      have hl_le := hL.1 hl_notred
      have hr_le := hR.1 hr_notred
      rw [← hbh] at hr_le
      constructor
      · intro h
        simp [IsRed] at h
      · intro _
        have hmax : max (height l) (height r) ≤ 2 * (bheight l - 1) :=
          Nat.max_le.mpr ⟨hl_le, hr_le⟩
        have hbh_node : bheight (node .red l k r) - 1 = bheight l - 1 := by simp [bheight]
        rw [height_node, hbh_node]
        exact Nat.succ_le_succ hmax

/-- Sedgewick's height bound: a valid LLRB tree on `n` keys has height at most `2 ⌊lg(n+1)⌋`. -/
theorem height_le_two_log {t : LLRB α} (ht : Valid t) :
    height t ≤ 2 * Nat.log2 (t.size + 1) := by
  obtain ⟨-, hrb, -, hnrr, hbh⟩ := ht
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hblack : ¬ t.IsRed := not_isRed_of_rootBlack hrb
  have hh := (height_le_two_mul hnrr hbal).1 hblack
  have hsz := two_pow_bheight_le_size_succ hbal
  have hn0 : t.size + 1 ≠ 0 := Nat.succ_ne_zero _
  have hlog : bheight t - 1 ≤ Nat.log2 (t.size + 1) := (Nat.le_log2 hn0).mpr hsz
  omega

end LLRB

end AlgoDesign.Searching
