/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Search

/-!
# Red-black tree: height

CLRS Lemma 13.1, `height_le_two_log`: a valid tree of `n` keys has height at most
`2 * Nat.log2 (n + 1)`, from `two_pow_bheight_le_size_succ` and `height_le_two_mul`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

omit [LinearOrder α] in
/-- A balanced tree of black-height `bh` has at least `2^(bh-1) - 1` keys
(`leaf` contributes black-height 1 and 0 keys). Equivalent: `size + 1 ≥ 2^(bheight - 1)`. -/
theorem two_pow_bheight_le_size_succ {t : RBTree α} (h : Balanced t) :
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
/-- **CLRS Lemma 13.1, internal form**: no two reds in a row, plus black-height agreement,
implies the ordinary height is at most twice the black-height, plus one extra level when the
root itself is red. -/
theorem height_le_two_mul {t : RBTree α} (hnrr : NoRedRed t) (hbal : Balanced t) :
    (t.IsBlack → height t ≤ 2 * (bheight t - 1)) ∧
    (¬ t.IsBlack → height t ≤ 2 * (bheight t - 1) + 1) := by
  induction t with
  | leaf => simp [height, bheight, IsBlack]
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
          by_cases hlb : l.IsBlack
          · have := hL.1 hlb; omega
          · have := hL.2 hlb; omega
        have hr_le : height r ≤ 2 * (bheight r - 1) + 1 := by
          by_cases hrb : r.IsBlack
          · have := hR.1 hrb; omega
          · have := hR.2 hrb; omega
        rw [← hbh] at hr_le
        have hmax : max (height l) (height r) ≤ 2 * (bheight l - 1) + 1 :=
          Nat.max_le.mpr ⟨hl_le, hr_le⟩
        have hpos := bheight_pos l
        have htwo : 2 * (bheight l - 1) + 1 + 1 = 2 * bheight l := by omega
        have hbh_node : bheight (node .black l k r) - 1 = bheight l := by simp [bheight]
        rw [height_node, hbh_node]
        exact Nat.le_trans (Nat.add_le_add_right hmax 1) (Nat.le_of_eq htwo)
      · intro h
        simp [IsBlack] at h
    | red =>
      have hl_black : l.IsBlack := (hc rfl).1
      have hr_black : r.IsBlack := (hc rfl).2
      have hl_le := hL.1 hl_black
      have hr_le := hR.1 hr_black
      rw [← hbh] at hr_le
      constructor
      · intro h
        simp [IsBlack] at h
      · intro _
        have hmax : max (height l) (height r) ≤ 2 * (bheight l - 1) :=
          Nat.max_le.mpr ⟨hl_le, hr_le⟩
        have hbh_node : bheight (node .red l k r) - 1 = bheight l - 1 := by simp [bheight]
        rw [height_node, hbh_node]
        exact Nat.succ_le_succ hmax

/-- **CLRS Lemma 13.1**: a valid red-black tree on `n` keys has height at most `2 ⌊lg(n+1)⌋`. -/
theorem height_le_two_log {t : RBTree α} (ht : Valid t) :
    height t ≤ 2 * Nat.log2 (t.size + 1) := by
  obtain ⟨-, hrb, hnrr, hbh⟩ := ht
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hblack : t.IsBlack := by
    cases t with
    | leaf => trivial
    | node _ _ _ _ => exact hrb
  have hh := (height_le_two_mul hnrr hbal).1 hblack
  have hsz := two_pow_bheight_le_size_succ hbal
  have hn0 : t.size + 1 ≠ 0 := Nat.succ_ne_zero _
  have hlog : bheight t - 1 ≤ Nat.log2 (t.size + 1) := (Nat.le_log2 hn0).mpr hsz
  omega

end RBTree

end AlgoDesign.Searching
