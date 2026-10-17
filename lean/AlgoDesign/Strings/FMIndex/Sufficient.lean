/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.List.Perm.Subperm
public import AlgoDesign.Strings.FMIndex.Parts
public import AlgoDesign.Strings.FMIndex.Cost

/-!
# FM-index: `FMIndex.Valid` is enough

Any stored parts that satisfy `FMIndex.Valid` answer correctly, not only the ones the build makes.
`valid_invertBwt`: a column with the sentinel once, whose `lf` walk from row `0` visits every row,
is the Burrows–Wheeler transform of the text it rebuilds, `invertBwt bwt`; `saOf` is that text's
suffix array, read off the walk. Then `positionOf_of_valid`: `positionOf` returns each row's text
position; `backwardSearch_spec_of_valid`, `stretch_width_of_valid`: backward search over the
stored column and the stored `C` (`storedC`) holds exactly the rows whose suffix starts with the
pattern.
`keptPositionsCorrect_iff` reads invariant 2's last part plainly, through `posOf`.

The library's operations on a stored index (`FMIndex.count`, `FMIndex.locate`, and the counting
`FMIndex.countM`, `FMIndex.locateM`) close the file, with what they answer and cost on any valid
index, about the text without its `$` (`FMIndex.text`): `FMIndex.count_of_valid`,
`FMIndex.locate_perm_of_valid`, `FMIndex.time_locateM_le`.

Count reads `LettersAreBytes`: `SmallerLettersCounted` builds `C` over the bytes only, so a larger
letter would read the entry `0`.
-/

@[expose] public section

namespace AlgoDesign.Strings

open FMIndex (KeptPositionsCorrect PositionsKept SentinelOnce SmallerLettersCounted
  WalkVisitsEveryRow KeptRowsListed LettersAreBytes RateAtLeastOne)

/-- With the sentinel once in the column, row `idxOf 0` is the only row ending in it. -/
private theorem eq_idxOf_of_sentinel {ix : FMIndex} (h0 : SentinelOnce ix) {r : Nat}
    (hr : r < ix.bwt.length) (hz : ix.bwt[r]! = 0) : r = ix.bwt.idxOf 0 := by
  have hm : (0 : Nat) ∈ ix.bwt := by rw [← List.count_pos_iff]; unfold SentinelOnce at h0; omega
  have hi := List.idxOf_lt_length_of_mem hm
  have hgi : ix.bwt[ix.bwt.idxOf 0] = 0 := List.getElem_idxOf hi
  rw [getElem!_pos ix.bwt _ hr] at hz
  rcases Nat.lt_trichotomy r (ix.bwt.idxOf 0) with hlt | heq | hgt
  · have := List.not_of_lt_findIdx (p := fun c => c == 0) (xs := ix.bwt) (i := r) hlt
    simp [hz] at this
  · exact heq
  · exfalso
    have h1 : 0 < (ix.bwt.take r).count 0 :=
      List.count_pos_iff.mpr (List.mem_take_iff_getElem.mpr ⟨_, by simp; omega, hgi⟩)
    have h2 : 0 < (ix.bwt.drop r).count 0 := by
      rw [List.drop_eq_getElem_cons hr, hz]; simp
    have := List.count_append (a := 0) (l₁ := ix.bwt.take r) (l₂ := ix.bwt.drop r)
    rw [List.take_append_drop] at this
    unfold SentinelOnce at h0
    omega

/-- The walk from row `0` stays in the table. -/
private theorem iterate_lf_zero_lt {ix : FMIndex} (hw : WalkVisitsEveryRow ix)
    (hn : 0 < ix.bwt.length) :
    ∀ i, (lf ix.bwt)^[i] 0 < ix.bwt.length := by
  intro i
  induction i with
  | zero => exact hn
  | succ i ih => rw [Function.iterate_succ_apply']; exact hw.2.2 _ ih

/-- Two step counts below `n` that reach the same row are equal. -/
private theorem iterate_lf_zero_inj {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {i j : Nat}
    (hi : i < ix.bwt.length) (hj : j < ix.bwt.length)
    (he : (lf ix.bwt)^[i] 0 = (lf ix.bwt)^[j] 0) : i = j :=
  List.inj_on_of_nodup_map hw.1 (List.mem_range.mpr hi) (List.mem_range.mpr hj) he

/-- The walk from row `0` reaches every row within `n` steps. -/
private theorem iterate_lf_zero_covers {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {r : Nat}
    (hr : r < ix.bwt.length) : ∃ i, i < ix.bwt.length ∧ (lf ix.bwt)^[i] 0 = r := by
  have hn : 0 < ix.bwt.length := by omega
  have hsub : ((List.range ix.bwt.length).map fun j => (lf ix.bwt)^[j] 0)
      ⊆ List.range ix.bwt.length := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr (iterate_lf_zero_lt hw hn j)
  have hperm := (List.Nodup.subperm hw.1 hsub).perm_of_length_le (by simp)
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (hperm.mem_iff.mpr (List.mem_range.mpr hr))
  exact ⟨i, List.mem_range.mp hi, he⟩

/-- `n` more steps from row `0` change nothing. -/
private theorem iterate_lf_zero_add {ix : FMIndex} (hw : WalkVisitsEveryRow ix) (a : Nat) :
    (lf ix.bwt)^[a + ix.bwt.length] 0 = (lf ix.bwt)^[a] 0 := by
  rw [Function.iterate_add_apply, hw.2.1]

/-- The walk from row `0` reaches the sentinel's row last, after `n - 1` steps. -/
private theorem iterate_lf_zero_last {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) : (lf ix.bwt)^[ix.bwt.length - 1] 0 = ix.bwt.idxOf 0 := by
  have hm : (0 : Nat) ∈ ix.bwt := by rw [← List.count_pos_iff]; unfold SentinelOnce at h0; omega
  obtain ⟨i, hi, he⟩ := iterate_lf_zero_covers hw (List.idxOf_lt_length_of_mem hm)
  have hnext : (lf ix.bwt)^[i + 1] 0 = (lf ix.bwt)^[0] 0 := by
    rw [Function.iterate_succ_apply', he, lf_idxOf_zero]; rfl
  by_cases hlt : i + 1 < ix.bwt.length
  · exact absurd (iterate_lf_zero_inj hw hlt (by omega) hnext) (by omega)
  · rw [show ix.bwt.length - 1 = i by omega, he]

/-- The row of text position `p`: the walk from row `0` (position `n - 1`) after `n - 1 - p`
steps. -/
def rowOf (bwt : List Nat) (p : Nat) : Nat := (lf bwt)^[bwt.length - 1 - p] 0

/-- `rowOf` names a row of the table. -/
private theorem rowOf_lt {ix : FMIndex} (hw : WalkVisitsEveryRow ix) (hn : 0 < ix.bwt.length)
    (p : Nat) :
    rowOf ix.bwt p < ix.bwt.length :=
  iterate_lf_zero_lt hw hn _

/-- Different positions have different rows. -/
private theorem rowOf_inj {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {p q : Nat}
    (hp : p < ix.bwt.length) (hq : q < ix.bwt.length) (he : rowOf ix.bwt p = rowOf ix.bwt q) :
    p = q := by
  have := iterate_lf_zero_inj hw (i := ix.bwt.length - 1 - p) (j := ix.bwt.length - 1 - q)
    (by omega) (by omega) he
  omega

/-- Every row is the row of some position. -/
private theorem rowOf_covers {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {r : Nat}
    (hr : r < ix.bwt.length) : ∃ p, p < ix.bwt.length ∧ rowOf ix.bwt p = r := by
  obtain ⟨i, hi, he⟩ := iterate_lf_zero_covers hw hr
  exact ⟨ix.bwt.length - 1 - i, by omega, by rw [rowOf, show ix.bwt.length - 1 -
    (ix.bwt.length - 1 - i) = i by omega, he]⟩

/-- Position `n - 1`, the sentinel's suffix, is row `0`. -/
private theorem rowOf_last (bwt : List Nat) : rowOf bwt (bwt.length - 1) = 0 := by
  simp [rowOf]

/-- Position `0`, the whole text, is the row ending in the sentinel. -/
private theorem rowOf_zero {ix : FMIndex} (h0 : SentinelOnce ix) (hw : WalkVisitsEveryRow ix) :
    rowOf ix.bwt 0 = ix.bwt.idxOf 0 := by
  rw [rowOf, Nat.sub_zero, iterate_lf_zero_last h0 hw]

/-- `lf` moves one text position left, wrapping from `0` to `n - 1`. -/
private theorem lf_rowOf {ix : FMIndex} (h0 : SentinelOnce ix) (hw : WalkVisitsEveryRow ix)
    {p : Nat} (hp : p < ix.bwt.length) :
    lf ix.bwt (rowOf ix.bwt p) = rowOf ix.bwt ((p + ix.bwt.length - 1) % ix.bwt.length) := by
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · rw [rowOf_zero h0 hw, lf_idxOf_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega),
      rowOf_last]
  · rw [show p + ix.bwt.length - 1 = (p - 1) + ix.bwt.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), rowOf, rowOf, ← Function.iterate_succ_apply' (f := lf ix.bwt)]
    congr 1
    omega

/-- `k` steps read `k` letters. -/
theorem length_lfWalk (bwt : List Nat) : ∀ k r, (lfWalk bwt k r).length = k
  | 0, _ => rfl
  | k + 1, r => by simp [lfWalk, length_lfWalk bwt k]

/-- Letter `j` of the walk is the last letter of the row `j` steps on. -/
theorem getElem!_lfWalk (bwt : List Nat) :
    ∀ k r j, j < k → (lfWalk bwt k r)[j]! = bwt[(lf bwt)^[j] r]!
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, r, 0, _ => by simp [lfWalk]
  | k + 1, r, j + 1, hj => by
    simp only [lfWalk, List.getElem!_cons_succ, Function.iterate_succ_apply]
    exact getElem!_lfWalk bwt k _ j (by omega)

/-- The rebuilt text, letter by letter: letter `p` is the last letter of the row of `p + 1`, and
the last letter is the sentinel. -/
private theorem getElem!_invertBwt {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) {p : Nat} (hp : p < ix.bwt.length) :
    (invertBwt ix.bwt)[p]! = ix.bwt[rowOf ix.bwt ((p + 1) % ix.bwt.length)]! := by
  have hm : (0 : Nat) ∈ ix.bwt := by rw [← List.count_pos_iff]; unfold SentinelOnce at h0; omega
  have hmin : ix.bwt.min? = some 0 :=
    List.min?_eq_some_iff.mpr ⟨hm, fun b _ => Nat.zero_le b⟩
  have hlen := length_lfWalk ix.bwt ix.bwt.length (ix.bwt.idxOf 0)
  rw [invertBwt, hmin, Option.getD_some,
    getElem!_pos _ p (by rw [List.length_reverse, hlen]; exact hp), List.getElem_reverse,
    ← getElem!_pos _ _ (by omega), hlen, getElem!_lfWalk _ _ _ _ (by omega),
    ← iterate_lf_zero_last h0 hw, ← Function.iterate_add_apply]
  congr 1
  rcases Nat.lt_or_ge (p + 1) ix.bwt.length with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, rowOf, show ix.bwt.length - 1 - p + (ix.bwt.length - 1)
      = (ix.bwt.length - 1 - (p + 1)) + ix.bwt.length by omega, iterate_lf_zero_add hw]
  · rw [show p + 1 = ix.bwt.length by omega, Nat.mod_self, rowOf, Nat.sub_zero,
      show ix.bwt.length - 1 - p + (ix.bwt.length - 1) = ix.bwt.length - 1 by omega]

/-- Among the rows before `a + 1`, the letter `bwt[a]` occurs once more than before `a`. -/
private theorem filter_take_succ {bwt : List Nat} {a : Nat} (ha : a < bwt.length) :
    ((bwt.take (a + 1)).filter (fun c => decide (c = bwt[a]!))).length
      = ((bwt.take a).filter (fun c => decide (c = bwt[a]!))).length + 1 := by
  rw [← List.take_concat_get' bwt a ha, List.filter_append, List.length_append,
    getElem!_pos bwt a ha]
  simp

/-- `lf` keeps the order of (last letter, row): a smaller letter, or the same letter in an earlier
row, goes to an earlier row. -/
private theorem lf_lt_lf {bwt : List Nat} {a b : Nat} (ha : a < bwt.length)
    (h : bwt[a]! < bwt[b]! ∨ (bwt[a]! = bwt[b]! ∧ a < b)) : lf bwt a < lf bwt b := by
  unfold lf
  rcases h with hlt | ⟨heq, hab⟩
  · have hF : ((bwt.take a).filter (fun c => decide (c = bwt[a]!))).length + 1
        ≤ (bwt.filter (fun c => decide (c = bwt[a]!))).length := by
      rw [← filter_take_succ ha]
      exact ((List.take_sublist _ _).filter _).length_le
    generalize bwt[a]! = x at hlt hF ⊢
    generalize bwt[b]! = y at hlt ⊢
    have hsplit : (bwt.filter (fun c => decide (c < x))).length
        + (bwt.filter (fun c => decide (c = x))).length
        ≤ (bwt.filter (fun c => decide (c < y))).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter,
        ← countP_split (A := fun c => decide (c < x + 1)) (fun c _ => by
          by_cases h1 : c < x <;> by_cases h2 : c = x <;> simp [h1, h2] <;> omega)
          (fun c _ hc => by simp at hc ⊢; omega)]
      exact List.countP_mono_left (fun c _ hc => by simp at hc ⊢; omega)
    omega
  · rw [← heq]
    have := filter_take_succ ha
    have hle : ((bwt.take (a + 1)).filter (fun c => decide (c = bwt[a]!))).length
        ≤ ((bwt.take b).filter (fun c => decide (c = bwt[a]!))).length :=
      ((List.take_sublist_take_left (by omega)).filter _).length_le
    omega

/-- The converse: rows that `lf` puts in order were in (last letter, row) order. -/
private theorem lt_of_lf_lt {bwt : List Nat} {a b : Nat} (hb : b < bwt.length)
    (h : lf bwt a < lf bwt b) : bwt[a]! < bwt[b]! ∨ (bwt[a]! = bwt[b]! ∧ a < b) := by
  rcases Nat.lt_trichotomy bwt[a]! bwt[b]! with hlt | heq | hgt
  · exact Or.inl hlt
  · rcases Nat.lt_trichotomy a b with hab | rfl | hba
    · exact Or.inr ⟨heq, hab⟩
    · exact absurd h (Nat.lt_irrefl _)
    · exact absurd (lf_lt_lf hb (Or.inr ⟨heq.symm, hba⟩)) (by omega)
  · exact absurd (lf_lt_lf hb (Or.inl hgt)) (by omega)

/-- The rebuilt text is as long as the column. -/
theorem length_invertBwt (bwt : List Nat) : (invertBwt bwt).length = bwt.length := by
  simp [invertBwt, length_lfWalk]

/-- A suffix reads as its first letter followed by the next suffix. -/
private theorem suffix_eq_cons {t : List Nat} {i : Nat} (hi : i < t.length) :
    suffix t i = t[i]! :: suffix t (i + 1) := by
  rw [getElem!_pos t i hi]
  simp only [suffix, List.drop_eq_getElem_cons hi]

/-- Only the row of position `0` ends in the sentinel. -/
private theorem getElem!_rowOf_ne_zero {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) {p : Nat} (hp : p < ix.bwt.length) (hp0 : p ≠ 0) :
    ix.bwt[rowOf ix.bwt p]! ≠ 0 := by
  intro hz
  have hn : 0 < ix.bwt.length := by omega
  have := eq_idxOf_of_sentinel h0 (rowOf_lt hw hn p) hz
  rw [← rowOf_zero h0 hw] at this
  exact hp0 (rowOf_inj hw hp hn this)

/-- Every letter of the rebuilt text but the last is above the sentinel. -/
private theorem getElem!_invertBwt_pos {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) {p : Nat} (hp : p + 1 < ix.bwt.length) :
    0 < (invertBwt ix.bwt)[p]! := by
  rw [getElem!_invertBwt h0 hw (by omega), Nat.mod_eq_of_lt hp]
  exact Nat.pos_of_ne_zero (getElem!_rowOf_ne_zero h0 hw hp (by omega))

/-- The rebuilt text ends in the sentinel. -/
private theorem getElem!_invertBwt_last {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) (hn : 0 < ix.bwt.length) :
    (invertBwt ix.bwt)[ix.bwt.length - 1]! = 0 := by
  rw [getElem!_invertBwt h0 hw (by omega), show ix.bwt.length - 1 + 1 = ix.bwt.length by omega,
    Nat.mod_self, rowOf_zero h0 hw]
  have hm : (0 : Nat) ∈ ix.bwt := by rw [← List.count_pos_iff]; unfold SentinelOnce at h0; omega
  rw [getElem!_pos ix.bwt _ (List.idxOf_lt_length_of_mem hm)]
  exact List.getElem_idxOf _

/-- Row order is suffix order: an earlier row holds a smaller suffix of the rebuilt text. By
induction on the suffix length: the first letters are the rows' last letters one `lf` step back,
and `lf` keeps (letter, row) order. -/
private theorem suffix_lt_of_rowOf_lt {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) :
    ∀ m p q, ix.bwt.length - p ≤ m → p < ix.bwt.length → q < ix.bwt.length →
      rowOf ix.bwt p < rowOf ix.bwt q →
        suffix (invertBwt ix.bwt) p < suffix (invertBwt ix.bwt) q := by
  have hlen := length_invertBwt ix.bwt
  intro m
  induction m with
  | zero => intro p q hm hp; omega
  | succ m ih =>
    intro p q hm hp hq hrow
    by_cases hpl : p + 1 = ix.bwt.length
    · have hql : q + 1 < ix.bwt.length := by
        by_contra hc
        rw [show q = p by omega] at hrow
        exact Nat.lt_irrefl _ hrow
      rw [suffix_eq_cons (i := p) (by omega), suffix_eq_cons (i := q) (by omega),
        show p = ix.bwt.length - 1 by omega, getElem!_invertBwt_last h0 hw (by omega),
        List.cons_lt_cons_iff]
      exact Or.inl (getElem!_invertBwt_pos h0 hw hql)
    · have hql : q + 1 < ix.bwt.length := by
        by_contra hc
        rw [show q = ix.bwt.length - 1 by omega, rowOf_last] at hrow
        exact Nat.not_lt_zero _ hrow
      have hstep : ∀ x, x + 1 < ix.bwt.length →
          lf ix.bwt (rowOf ix.bwt (x + 1)) = rowOf ix.bwt x := by
        intro x hx
        rw [lf_rowOf h0 hw hx, show x + 1 + ix.bwt.length - 1 = x + ix.bwt.length by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hlf : lf ix.bwt (rowOf ix.bwt (p + 1)) < lf ix.bwt (rowOf ix.bwt (q + 1)) := by
        rw [hstep p (by omega), hstep q hql]; exact hrow
      have hn : 0 < ix.bwt.length := by omega
      rw [suffix_eq_cons (i := p) (by omega), suffix_eq_cons (i := q) (by omega),
        getElem!_invertBwt h0 hw hp, getElem!_invertBwt h0 hw hq, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt hql, List.cons_lt_cons_iff]
      rcases lt_of_lf_lt (rowOf_lt hw hn _) hlf with hlt | ⟨heq, hr⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, ih (p + 1) (q + 1) (by omega) (by omega) hql hr⟩

/-- `posOf` undoes `rowOf`. -/
private theorem posOf_rowOf {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {p : Nat}
    (hp : p < ix.bwt.length) : posOf ix.bwt (rowOf ix.bwt p) = p := by
  have h := List.Nodup.idxOf_getElem hw.1 (ix.bwt.length - 1 - p) (by simp; omega)
  simp only [List.getElem_map, List.getElem_range] at h
  rw [posOf, rowOf, h]
  omega

/-- The entry at the row of position `p` is `p`. -/
private theorem getElem!_saOf_rowOf {ix : FMIndex} (hw : WalkVisitsEveryRow ix) {p : Nat}
    (hp : p < ix.bwt.length) : (saOf ix.bwt)[rowOf ix.bwt p]! = p := by
  have hn : 0 < ix.bwt.length := by omega
  rw [getElem!_pos _ _ (by rw [length_saOf]; exact rowOf_lt hw hn p)]
  simp [saOf, posOf_rowOf hw hp]

/-- `saOf` is a suffix array of the rebuilt text. -/
theorem valid_saOf {ix : FMIndex} (h0 : SentinelOnce ix) (hw : WalkVisitsEveryRow ix) :
    SuffixArray.Valid ⟨invertBwt ix.bwt, saOf ix.bwt⟩ := by
  have hn : 0 < ix.bwt.length := by
    unfold SentinelOnce at h0; have := List.count_le_length (a := 0) (l := ix.bwt); omega
  have hlen := length_invertBwt ix.bwt
  refine ⟨?_, ?_⟩
  · unfold SuffixArray.EachPositionOnce
    rw [hlen]
    have hnd : (saOf ix.bwt).Nodup := by
      refine List.Nodup.map_on ?_ List.nodup_range
      intro x hx y hy he
      obtain ⟨p, hp, rfl⟩ := rowOf_covers hw (List.mem_range.mp hx)
      obtain ⟨q, hq, rfl⟩ := rowOf_covers hw (List.mem_range.mp hy)
      rw [posOf_rowOf hw hp, posOf_rowOf hw hq] at he
      rw [he]
    have hsub : saOf ix.bwt ⊆ List.range ix.bwt.length := by
      intro x hx
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact List.mem_range.mpr (by unfold posOf; omega)
    exact (List.Nodup.subperm hnd hsub).perm_of_length_le (by simp [length_saOf])
  · unfold SuffixArray.SuffixesSorted
    refine List.pairwise_iff_getElem.mpr fun a b ha hb hab => ?_
    simp only [List.length_map, length_saOf] at ha hb
    obtain ⟨p, hp, rfl⟩ := rowOf_covers hw ha
    obtain ⟨q, hq, rfl⟩ := rowOf_covers hw hb
    simp only [List.getElem_map, saOf, List.getElem_range, posOf_rowOf hw hp,
      posOf_rowOf hw hq]
    exact List.le_of_lt (suffix_lt_of_rowOf_lt h0 hw _ p q le_rfl hp hq hab)

/-- The column is the transform, through `saOf`, of the text it rebuilds. -/
theorem bwtOfSa_saOf {ix : FMIndex} (h0 : SentinelOnce ix) (hw : WalkVisitsEveryRow ix) :
    bwtOfSa (invertBwt ix.bwt) (saOf ix.bwt) = ix.bwt := by
  have hlen := length_invertBwt ix.bwt
  refine List.ext_getElem (by simp [bwtOfSa, length_saOf]) fun r h1 h2 => ?_
  have hn : 0 < ix.bwt.length := by omega
  obtain ⟨p, hp, rfl⟩ := rowOf_covers hw h2
  have hsa : (saOf ix.bwt)[rowOf ix.bwt p]'(by rw [length_saOf]; exact h2) = p := by
    rw [← getElem!_pos (saOf ix.bwt) _ (by rw [length_saOf]; exact h2)]
    exact getElem!_saOf_rowOf hw hp
  simp only [bwtOfSa, List.getElem_map, hsa, hlen]
  have hmod : ((p + ix.bwt.length - 1) % ix.bwt.length + 1) % ix.bwt.length = p := by
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (show ix.bwt.length - 1 < ix.bwt.length by omega),
        Nat.sub_add_cancel hn, Nat.mod_self]
    · rw [show p + ix.bwt.length - 1 = (p - 1) + ix.bwt.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show p - 1 < ix.bwt.length by omega), Nat.sub_add_cancel hpos,
        Nat.mod_eq_of_lt hp]
  rw [getElem!_invertBwt h0 hw (Nat.mod_lt _ hn), hmod, getElem!_pos ix.bwt _ h2]

/-- **The column is a Burrows–Wheeler transform.** A column holding the sentinel once, whose `lf`
walk from row `0` visits every row, is the transform of the text it rebuilds, and that text ends in
the sentinel. -/
theorem valid_invertBwt {ix : FMIndex} (h0 : SentinelOnce ix) (hw : WalkVisitsEveryRow ix) :
    Terminated (invertBwt ix.bwt) 0 ∧ BWT.Valid ⟨invertBwt ix.bwt, ix.bwt⟩ := by
  have hn : 0 < ix.bwt.length := by
    unfold SentinelOnce at h0; have := List.count_le_length (a := 0) (l := ix.bwt); omega
  have hlen := length_invertBwt ix.bwt
  have hterm : Terminated (invertBwt ix.bwt) 0 := by
    refine ⟨?_, fun c hc => ?_⟩
    · rw [List.getLast?_eq_getElem?, hlen, List.getElem?_eq_getElem (by omega),
        ← getElem!_pos _ _ (by omega), getElem!_invertBwt_last h0 hw hn]
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      simp only [List.length_dropLast, hlen] at hi
      rw [List.getElem_dropLast, ← getElem!_pos _ _ (by omega)]
      exact getElem!_invertBwt_pos h0 hw (by omega)
  refine ⟨hterm, ?_⟩
  have := valid_bwtOfSa _ hterm _ (valid_saOf h0 hw)
  rwa [bwtOfSa_saOf h0 hw] at this

/-- The marks counted before row `r` are its rank among the marked rows. -/
theorem count_true_take (marks : List Bool) (r : Nat) :
    (marks.take r).count true = rank marks r := by
  simp [rank, List.count_eq_countP, List.countP_eq_length_filter]; rfl

/-- The walk from the sentinel's row: `j < n` steps reach the row of position `(n - j) mod n`. -/
private theorem iterate_lf_idxOf_zero {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) :
    ∀ j, j < ix.bwt.length →
      (lf ix.bwt)^[j] (ix.bwt.idxOf 0) = rowOf ix.bwt ((ix.bwt.length - j) % ix.bwt.length) := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.sub_zero, Nat.mod_self, rowOf_zero h0 hw]; rfl
  | succ j ih =>
    intro hj
    have hn : 0 < ix.bwt.length := by omega
    rw [Function.iterate_succ_apply', ih (by omega),
      lf_rowOf h0 hw (Nat.mod_lt _ hn)]
    congr 1
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [Nat.sub_zero, Nat.mod_self, Nat.zero_add,
        Nat.mod_eq_of_lt (show ix.bwt.length - 1 < ix.bwt.length by omega)]
    · rw [Nat.mod_eq_of_lt (show ix.bwt.length - j < ix.bwt.length by omega),
        Nat.mod_eq_of_lt (show ix.bwt.length - (j + 1) < ix.bwt.length by omega),
        show ix.bwt.length - j + ix.bwt.length - 1 = (ix.bwt.length - (j + 1)) + ix.bwt.length
          by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show ix.bwt.length - (j + 1) < ix.bwt.length by omega)]

/-- One row's part of `KeptPositionsCorrect`, the mark read as the `Bool` the build stores. -/
private theorem keptPart_iff {marks : List Bool} {r s pos : Nat} {X : Prop} :
    (∃ h : r < marks.length, (marks[r] = true ↔ s ∣ pos) ∧ (s ∣ pos → X)) ↔
      marks[r]? = some (pos % s == 0) ∧ (pos % s = 0 → X) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨h, h1, h2⟩
    refine ⟨?_, h2⟩
    rw [List.getElem?_eq_getElem h, Option.some_inj]
    cases hm : marks[r] <;> simp_all
  · rintro ⟨h1, h2⟩
    obtain ⟨h, hv⟩ := List.getElem?_eq_some_iff.mp h1
    exact ⟨h, by rw [hv]; simp, h2⟩

/-- **Invariant 2's last part, read plainly.** On a column that holds the sentinel once and whose
walk visits every row, `KeptPositionsCorrect` says: every row is marked exactly when its own text
position, `posOf`, is a multiple of `sample`, and a marked row stores that position. -/
theorem keptPositionsCorrect_iff {ix : FMIndex} (h0 : SentinelOnce ix)
    (hw : WalkVisitsEveryRow ix) :
    KeptPositionsCorrect ix ↔ ∀ r < ix.bwt.length,
      ix.marks[r]? = some (posOf ix.bwt r % ix.sample == 0) ∧
        (posOf ix.bwt r % ix.sample = 0 →
          ix.saSamples[rank ix.marks r]? = some (posOf ix.bwt r)) := by
  have hm : (0 : Nat) ∈ ix.bwt := by
    rw [← List.count_pos_iff]; unfold SentinelOnce at h0; omega
  have hn : 0 < ix.bwt.length := List.length_pos_of_mem hm
  -- `j` steps from the sentinel's row and the position `(n - j) mod n` determine each other.
  have hback : ∀ p, p < ix.bwt.length →
      (ix.bwt.length - (ix.bwt.length - p) % ix.bwt.length) % ix.bwt.length = p := by
    intro p hp
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · simp
    · rw [Nat.mod_eq_of_lt (show ix.bwt.length - p < ix.bwt.length by omega),
        show ix.bwt.length - (ix.bwt.length - p) = p by omega, Nat.mod_eq_of_lt hp]
  unfold KeptPositionsCorrect
  simp only [FMIndex.rowAfter, FMIndex.sentinelRow, FMIndex.keptValueAt, keptPart_iff]
  constructor
  · intro hk r hr
    obtain ⟨p, hp, rfl⟩ := rowOf_covers hw hr
    have hj : (ix.bwt.length - p) % ix.bwt.length < ix.bwt.length := Nat.mod_lt _ hn
    have := hk hm _ hj
    rw [iterate_lf_idxOf_zero h0 hw _ hj, hback p hp, count_true_take] at this
    rw [posOf_rowOf hw hp]
    exact this
  · intro hk _ j hj
    rw [iterate_lf_idxOf_zero h0 hw _ hj, count_true_take]
    have hp : (ix.bwt.length - j) % ix.bwt.length < ix.bwt.length := Nat.mod_lt _ hn
    have := hk (rowOf ix.bwt ((ix.bwt.length - j) % ix.bwt.length)) (rowOf_lt hw hn _)
    rw [posOf_rowOf hw hp] at this
    exact this

/-- On the transform of a text, `KeptPositionsCorrect` row by row: each row is marked exactly when
its position is a multiple of `sample`, and a marked row's value is its position. -/
theorem keptRows_of_kept (t : List Nat) (h : Terminated t 0) (sa : List Nat)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) {ix : FMIndex} (hcol : ix.bwt = bwtOfSa t sa)
    (hkept : KeptPositionsCorrect ix) (x : Nat) (hx : x < sa.length) :
    ix.marks[x]? = some (sa[x]! % ix.sample == 0) ∧
      (sa[x]! % ix.sample = 0 → ix.saSamples[(ix.marks.take x).count true]? = some sa[x]!) := by
  unfold KeptPositionsCorrect at hkept
  simp only [FMIndex.rowAfter, FMIndex.sentinelRow, FMIndex.keptValueAt, keptPart_iff] at hkept
  rw [hcol] at hkept
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = t.length := by simp [bwtOfSa, hlen]
  have hnd : sa.Nodup := hsa.1.nodup_iff.mpr List.nodup_range
  have hpx : sa[x]! < t.length := by
    rw [getElem!_pos sa x hx]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hx))
  obtain ⟨h0r, h0v⟩ := idxOf_sentinel_bwtOfSa h hsa
  have hmem0 : (0 : Nat) ∈ bwtOfSa t sa := by
    by_contra hm
    rw [List.idxOf_eq_length hm] at h0r
    simp [bwtOfSa] at h0r
  -- Row `x` is `j = (n - sa[x]) mod n` steps from the sentinel's row, where the kept parts are
  -- checked.
  set j := (t.length - sa[x]!) % t.length with hj
  have hjn : j < t.length := Nat.mod_lt _ (by omega)
  obtain ⟨hy, hyv⟩ := iterate_lf_from h hsa _ h0r j (by omega)
  rw [h0v, Nat.zero_add] at hyv
  have hback : (t.length - j) % t.length = sa[x]! := by
    rcases Nat.eq_zero_or_pos sa[x]! with hz | hz
    · rw [hj, hz, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
    · rw [hj, Nat.mod_eq_of_lt (show t.length - sa[x]! < t.length by omega),
        show t.length - (t.length - sa[x]!) = sa[x]! by omega, Nat.mod_eq_of_lt hpx]
  have hxy : (lf (bwtOfSa t sa))^[j] ((bwtOfSa t sa).idxOf 0) = x := by
    rw [hback, getElem!_pos sa _ hy, getElem!_pos sa _ hx] at hyv
    exact (hnd.getElem_inj_iff).mp hyv
  have := hkept hmem0 j (by rw [hbl]; exact hjn)
  rw [hxy, hbl, hback] at this
  exact this

/-- On the transform of a text, kept positions that `KeptPositionsCorrect` vouches for make
`positionOf` return each row's position, within the fuel `min sample n`. -/
theorem positionOf_eq_of_kept (t : List Nat) (h : Terminated t 0) (sa : List Nat)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) {ix : FMIndex} (hcol : ix.bwt = bwtOfSa t sa)
    (hk : 0 < ix.sample)
    (hkept : KeptPositionsCorrect ix) (r : Nat) (hr : r < sa.length) :
    positionOf ix.bwt ix.marks ix.saSamples (min ix.sample t.length) r 0 = some sa[r]! := by
  have hpos : ∀ x, x < sa.length → sa[x]! < t.length := by
    intro x hx
    rw [getElem!_pos sa x hx]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hx))
  have hrow := keptRows_of_kept t h sa hsa hcol hkept
  rw [hcol]
  refine positionOf_walk t 0 h sa hsa ix.sample hk ix.marks ix.saSamples (fun x hx => ?_)
    (fun x hx hm => ?_) (sa[r]! % ix.sample) r 0 (min ix.sample t.length) hr rfl
    (by have := Nat.mod_lt sa[r]! hk; have := Nat.mod_le sa[r]! ix.sample; have := hpos r hr; omega)
    |>.trans (by rw [Nat.add_zero])
  · rw [List.getElem!_eq_getElem?_getD, (hrow x hx).1]; rfl
  · have := (hrow x hx).2 hm
    rw [List.getElem!_eq_getElem?_getD, ← count_true_take, this]; rfl

/-- On the transform of a text, with the kept positions `KeptPositionsCorrect` vouches for, the
walk from row `r` takes exactly `sa[r] mod sample` LF steps. -/
theorem time_positionOfM_of_kept (t : List Nat) (h : Terminated t 0) (sa : List Nat)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) {ix : FMIndex} (hcol : ix.bwt = bwtOfSa t sa)
    (hk : 0 < ix.sample)
    (hkept : KeptPositionsCorrect ix) (r : Nat) (hr : r < sa.length) :
    (positionOfM ix.bwt ix.marks ix.saSamples (min ix.sample t.length) r 0).time =
      sa[r]! % ix.sample := by
  have hlt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have hmodk : sa[r]! % ix.sample < ix.sample := Nat.mod_lt _ hk
  have hmodle : sa[r]! % ix.sample ≤ sa[r]! := Nat.mod_le _ _
  rw [hcol]
  refine time_positionOfM_walk t 0 h sa hsa ix.sample hk ix.marks ix.saSamples
    (fun x hx => ?_) _ r 0 _
    hr rfl (by omega)
  rw [List.getElem!_eq_getElem?_getD, (keptRows_of_kept t h sa hsa hcol hkept x hx).1]; rfl

/-- **Locate needs only `FMIndex.Valid`.** For any index that satisfies it, `positionOf` returns,
within the fuel `min sample n`, the position of row `r` in the text the column rebuilds. -/
theorem positionOf_of_valid {ix : FMIndex} (hv : ix.Valid) {r : Nat} (hr : r < ix.bwt.length) :
    positionOf ix.bwt ix.marks ix.saSamples (min ix.sample ix.bwt.length) r 0
      = some (suffixArray (invertBwt ix.bwt))[r]! := by
  obtain ⟨⟨-, -, -, hkept⟩, h0, -, hw, -, -, hk⟩ := hv
  obtain ⟨hterm, -, hcol, -⟩ := valid_invertBwt h0 hw
  have hsa := valid_suffixArray (invertBwt ix.bwt)
  have hlen := length_invertBwt ix.bwt
  replace hcol : ix.bwt = bwtOfSa (invertBwt ix.bwt) (suffixArray (invertBwt ix.bwt)) :=
    (BWT.letterBeforeEachSuffix_iff _).1 hcol
  have := positionOf_eq_of_kept _ hterm _ hsa hcol hk hkept r
    (by rw [hsa.1.length_eq, List.length_range, hlen]; exact hr)
  rw [hlen] at this
  exact this

/-- Models `self.c[dense]`: the stored `C` entry at a letter's dense index. -/
def storedC (ix : FMIndex) (x : Nat) : Nat := ix.c[indexOf (byteAlphabet ix.bwt) x]!

/-- `occ` grows with the prefix. -/
private theorem occ_mono (s : List Nat) (c : Nat) {i j : Nat} (h : i ≤ j) : occ s c i ≤ occ s c j :=
  ((List.take_sublist_take_left h).filter _).length_le

/-- A letter absent from the column occurs in no prefix. -/
private theorem occ_absent {s : List Nat} {c : Nat} (hc : c ∉ s) (i : Nat) : occ s c i = 0 := by
  rw [occ, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  simp only [beq_iff_eq]
  rintro rfl
  exact hc (List.mem_of_mem_take ha)

/-- Two `C` arrays that agree on the column's letters give the same stretch, or two empty ones. -/
private theorem backwardSearch_congr (bwt : List Nat) (C C' : Nat → Nat)
    (hC : ∀ x ∈ bwt, C x = C' x) : ∀ p : List Nat,
      backwardSearch bwt C p = backwardSearch bwt C' p ∨
        ((backwardSearch bwt C p).2 ≤ (backwardSearch bwt C p).1 ∧
          (backwardSearch bwt C' p).2 ≤ (backwardSearch bwt C' p).1) := by
  intro p
  induction p with
  | nil => exact Or.inl rfl
  | cons x q ih =>
    have hstep : ∀ D : Nat → Nat, backwardSearch bwt D (x :: q)
        = backwardStep bwt D x (backwardSearch bwt D q).1 (backwardSearch bwt D q).2 :=
      fun _ => rfl
    rw [hstep C, hstep C']
    simp only [backwardStep]
    rcases ih with he | ⟨h1, h2⟩
    · rw [he]
      by_cases hx : x ∈ bwt
      · rw [hC x hx]; exact Or.inl rfl
      · simp [occ_absent hx]
    · exact Or.inr ⟨Nat.add_le_add_left (occ_mono _ _ h1) _,
        Nat.add_le_add_left (occ_mono _ _ h2) _⟩

/-- On an index satisfying `FMIndex.Valid`, the stored `C` agrees with `cLess` of the rebuilt
text on every letter of the column. -/
private theorem storedC_eq {ix : FMIndex} (hv : ix.Valid) :
    ∀ x ∈ ix.bwt, storedC ix x = cLess (invertBwt ix.bwt) x := by
  obtain ⟨-, h0, hsmall, hw, -, hbytes, -⟩ := hv
  obtain ⟨-, hperm, -, -⟩ := valid_invertBwt h0 hw
  intro x hx
  unfold SmallerLettersCounted at hsmall
  unfold BWT.SameLetters at hperm
  rw [storedC, hsmall, cDense_eq_cLess 256 ix.bwt hbytes x hx, cLess_eq_countP,
    cLess_eq_countP, hperm.countP_eq]

/-- **Count needs only `FMIndex.Valid`.** Backward search over the stored column and the stored
`C` holds exactly the rows whose suffix of the rebuilt text starts with the pattern. -/
theorem backwardSearch_spec_of_valid {ix : FMIndex} (hv : ix.Valid)
    (p : List Nat) (hp : 0 ∉ p.dropLast) (r : Nat) :
    ((backwardSearch ix.bwt (storedC ix) p).1 ≤ r ∧ r < (backwardSearch ix.bwt (storedC ix) p).2)
      ↔ (r < (suffixArray (invertBwt ix.bwt)).length ∧
        p <+: suffix (invertBwt ix.bwt) (suffixArray (invertBwt ix.bwt))[r]!) := by
  have hC := storedC_eq hv
  obtain ⟨-, h0, -, hw, -⟩ := hv
  obtain ⟨hterm, -, hcol, -⟩ := valid_invertBwt h0 hw
  have hsa := valid_suffixArray (invertBwt ix.bwt)
  replace hcol : ix.bwt = bwtOfSa (invertBwt ix.bwt) (suffixArray (invertBwt ix.bwt)) :=
    (BWT.letterBeforeEachSuffix_iff _).1 hcol
  have hspec := backwardSearch_spec _ 0 hterm _ hsa p hp r
  rw [← hcol] at hspec
  rcases backwardSearch_congr ix.bwt _ _ hC p with he | ⟨h1, h2⟩
  · rw [he]; exact hspec
  · rw [← hspec]; omega

/-- The stretch's width is the number of occurrences of the pattern in the rebuilt text. -/
theorem stretch_width_of_valid {ix : FMIndex} (hv : ix.Valid) (p : List Nat) (hp : 0 ∉ p.dropLast) :
    (backwardSearch ix.bwt (storedC ix) p).2 - (backwardSearch ix.bwt (storedC ix) p).1
      = matchCount (invertBwt ix.bwt) p := by
  have hC := storedC_eq hv
  obtain ⟨-, h0, -, hw, -⟩ := hv
  obtain ⟨hterm, -, hcol, -⟩ := valid_invertBwt h0 hw
  have hsa := valid_suffixArray (invertBwt ix.bwt)
  replace hcol : ix.bwt = bwtOfSa (invertBwt ix.bwt) (suffixArray (invertBwt ix.bwt)) :=
    (BWT.letterBeforeEachSuffix_iff _).1 hcol
  have heq := backwardSearch_eq _ 0 hterm _ hsa p hp
  rw [← hcol] at heq
  rcases backwardSearch_congr ix.bwt _ _ hC p with he | ⟨h1, h2⟩
  · rw [he, heq]; simp
  · rw [heq] at h2; simp only at h2; omega

/-- On a valid index, the rebuilt text is the text the index answers about with its `$`. -/
theorem invertBwt_eq_text {ix : FMIndex} (hv : ix.Valid) : invertBwt ix.bwt = ix.text ++ [0] := by
  obtain ⟨-, h0, -, hw, -⟩ := hv
  obtain ⟨hterm, -⟩ := valid_invertBwt h0 hw
  have hne := hterm.ne_nil
  obtain ⟨hlast, -⟩ := hterm
  have hgl : (invertBwt ix.bwt).getLast hne = 0 := by
    rw [List.getLast?_eq_some_getLast hne] at hlast; exact Option.some.inj hlast
  conv_lhs => rw [← List.dropLast_append_getLast hne, hgl]
  rfl

/-- On a valid index, the text it answers about holds no `$`. -/
theorem zero_not_mem_text {ix : FMIndex} (hv : ix.Valid) : 0 ∉ ix.text := by
  obtain ⟨-, h0, -, hw, -⟩ := hv
  obtain ⟨⟨-, hlt⟩, -⟩ := valid_invertBwt h0 hw
  exact fun hm => Nat.lt_irrefl 0 (hlt 0 hm)

/-! ## The library's operations on a stored index

What `FmIndex::count` and `FmIndex::locate` do with the parts they keep, and the versions that
count their steps. A fragment with `$` in it occurs nowhere in the text without its `$`: both answer
nothing for it at once, as the Rust's and the Python's do. -/

namespace FMIndex

open Cslib.Algorithms.Lean

/-- Backward search over the stored parts: the stretch of rows whose suffixes start with `p`. -/
def stretch (ix : FMIndex) (p : List Nat) : Nat × Nat := backwardSearch ix.bwt (storedC ix) p

/-- The rows of the stretch. -/
def stretchRows (ix : FMIndex) (p : List Nat) : List Nat :=
  List.range' (ix.stretch p).1 ((ix.stretch p).2 - (ix.stretch p).1)

/-- `FmIndex::count`: zero for a fragment with `$` in it, else the stretch's width. -/
def count (ix : FMIndex) (p : List Nat) : Nat :=
  if 0 ∈ p then 0 else (ix.stretch p).2 - (ix.stretch p).1

/-- `FmIndex::position_of` on the stored parts: walk to a kept row, within the fuel
`min sample n`. -/
def locateRow (ix : FMIndex) (r : Nat) : Option Nat :=
  positionOf ix.bwt ix.marks ix.saSamples (min ix.sample ix.bwt.length) r 0

/-- `FmIndex::locate`: nothing for a fragment with `$` in it, else the position of every row of
the stretch. -/
def locate (ix : FMIndex) (p : List Nat) : List Nat :=
  if 0 ∈ p then [] else (ix.stretchRows p).filterMap ix.locateRow

/-- `count`, counting backward steps: one per letter, two `occ` reads each; none for a fragment
with `$` in it. -/
def countM (ix : FMIndex) (p : List Nat) : TimeM ℕ Nat :=
  if 0 ∈ p then ⟨0, 0⟩ else
    let r := backwardSearchM ix.bwt (storedC ix) p
    ⟨r.ret.2 - r.ret.1, r.time⟩

/-- `locateRow`, counting LF steps. -/
def locateRowM (ix : FMIndex) (r : Nat) : TimeM ℕ (Option Nat) :=
  positionOfM ix.bwt ix.marks ix.saSamples (min ix.sample ix.bwt.length) r 0

/-- Locate a list of rows, one walk each, the steps added up. -/
def locateRowsM (ix : FMIndex) : List Nat → TimeM ℕ (List Nat)
  | [] => ⟨[], 0⟩
  | r :: rs =>
      let x := ix.locateRowM r
      let y := ix.locateRowsM rs
      ⟨x.ret.toList ++ y.ret, x.time + y.time⟩

/-- `locate`, counting LF steps. -/
def locateM (ix : FMIndex) (p : List Nat) : TimeM ℕ (List Nat) :=
  if 0 ∈ p then ⟨[], 0⟩ else ix.locateRowsM (ix.stretchRows p)

theorem ret_countM (ix : FMIndex) (p : List Nat) : (ix.countM p).ret = ix.count p := by
  unfold countM count
  split <;> simp [stretch, ret_backwardSearchM]

/-- Counting costs at most one backward step per letter, whatever the text. -/
theorem time_countM_le (ix : FMIndex) (p : List Nat) : (ix.countM p).time ≤ p.length := by
  unfold countM
  split
  · exact Nat.zero_le _
  · exact (time_backwardSearchM _ _ p).le

theorem ret_locateRowsM (ix : FMIndex) (rows : List Nat) :
    (ix.locateRowsM rows).ret = rows.filterMap ix.locateRow := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have hr : (ix.locateRowM r).ret = ix.locateRow r := ret_positionOfM _ _ _ _ _ _
    simp only [locateRowsM, ih, hr, List.filterMap_cons]
    cases ix.locateRow r <;> rfl

theorem ret_locateM (ix : FMIndex) (p : List Nat) : (ix.locateM p).ret = ix.locate p := by
  unfold locateM locate
  split
  · rfl
  · exact ret_locateRowsM ix _

/-- **Locate cost on any valid index.** One row costs at most `sample - 1` LF steps. -/
theorem time_locateRowM_le {ix : FMIndex} (hv : ix.Valid) {r : Nat} (hr : r < ix.bwt.length) :
    (ix.locateRowM r).time ≤ ix.sample - 1 := by
  obtain ⟨⟨-, -, -, hkept⟩, h0, -, hw, -, -, hk⟩ := hv
  obtain ⟨hterm, -, hcol, -⟩ := valid_invertBwt h0 hw
  have hsa := valid_suffixArray (invertBwt ix.bwt)
  have hlen := length_invertBwt ix.bwt
  replace hcol : ix.bwt = bwtOfSa (invertBwt ix.bwt) (suffixArray (invertBwt ix.bwt)) :=
    (BWT.letterBeforeEachSuffix_iff _).1 hcol
  have := time_positionOfM_of_kept _ hterm _ hsa hcol hk hkept r
    (by rw [hsa.1.length_eq, List.length_range, hlen]; exact hr)
  rw [hlen] at this
  rw [locateRowM, this]
  have := Nat.mod_lt (suffixArray (invertBwt ix.bwt))[r]! hk
  omega

/-- Locating rows of the table costs at most `sample - 1` LF steps each. -/
theorem time_locateRowsM_le {ix : FMIndex} (hv : ix.Valid) (rows : List Nat)
    (hrows : ∀ r ∈ rows, r < ix.bwt.length) :
    (ix.locateRowsM rows).time ≤ rows.length * (ix.sample - 1) := by
  induction rows with
  | nil => simp [locateRowsM]
  | cons r rs ih =>
    have h1 := time_locateRowM_le hv (hrows r (by simp))
    have h2 := ih (fun x hx => hrows x (by simp [hx]))
    simp only [locateRowsM, List.length_cons, Nat.succ_mul]
    omega

/-- On a valid index, the stretch's rows are rows of the table. -/
private theorem stretch_lt {ix : FMIndex} (hv : ix.Valid) {p : List Nat} (hp : 0 ∉ p.dropLast)
    {r : Nat} (hr : r ∈ ix.stretchRows p) : r < ix.bwt.length := by
  rw [stretchRows, List.mem_range'_1] at hr
  have := ((backwardSearch_spec_of_valid hv p hp r).mp
    ⟨hr.1, by simp only [stretch] at hr; omega⟩).1
  rw [(valid_suffixArray (invertBwt ix.bwt)).1.length_eq, List.length_range,
    length_invertBwt] at this
  exact this

/-- A fragment without `$` has none before its end either. -/
private theorem not_mem_dropLast {p : List Nat} (hp : 0 ∉ p) : 0 ∉ p.dropLast :=
  fun h => hp (List.dropLast_subset p h)

/-- **Locate's cost on any valid index**: fewer than `sample` LF steps per match. -/
theorem time_locateM_le {ix : FMIndex} (hv : ix.Valid) (p : List Nat) :
    (ix.locateM p).time ≤ ix.count p * (ix.sample - 1) := by
  unfold locateM count
  split
  · exact Nat.zero_le _
  · rename_i hp
    have := time_locateRowsM_le hv _ (fun r hr => stretch_lt hv (not_mem_dropLast hp) hr)
    rwa [stretchRows, List.length_range'] at this

/-- On a valid index, the stretch's rows name every start position of `p` in the rebuilt text,
each once. -/
private theorem rows_perm_matchStarts {ix : FMIndex} (hv : ix.Valid) (p : List Nat)
    (hp : 0 ∉ p.dropLast) :
    ((ix.stretchRows p).filterMap ix.locateRow).Perm (matchStarts (invertBwt ix.bwt) p) := by
  set sa := suffixArray (invertBwt ix.bwt) with hsadef
  have hsa := valid_suffixArray (invertBwt ix.bwt)
  have hn : sa.length = ix.bwt.length := by
    rw [hsa.1.length_eq, List.length_range, length_invertBwt]
  have htn : (invertBwt ix.bwt).length = ix.bwt.length := length_invertBwt ix.bwt
  have hnd : sa.Nodup := hsa.1.nodup_iff.mpr List.nodup_range
  have hlt : ∀ r, r < sa.length → sa[r]! < ix.bwt.length := by
    intro r hr
    rw [getElem!_pos sa r hr, ← htn]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have hrows : (ix.stretchRows p).filterMap ix.locateRow = (ix.stretchRows p).map (sa[·]!) := by
    rw [← List.filterMap_eq_map]
    refine List.filterMap_congr fun r hr => ?_
    exact positionOf_of_valid hv (stretch_lt hv hp hr)
  rw [hrows]
  refine (List.perm_ext_iff_of_nodup ((List.nodup_range').map_on fun a ha b hb he => ?_)
    (List.nodup_range.filter _)).mpr fun x => ?_
  · have ha' := stretch_lt hv hp ha
    have hb' := stretch_lt hv hp hb
    rw [← hn] at ha' hb'
    rw [getElem!_pos sa a ha', getElem!_pos sa b hb'] at he
    exact (hnd.getElem_inj_iff).mp he
  · simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' := stretch_lt hv hp hr
      simp only [List.mem_range'_1] at hr
      have := ((backwardSearch_spec_of_valid hv p hp r).mp
        ⟨hr.1, by simp only [stretch] at hr; omega⟩).2
      exact ⟨htn ▸ hlt r (hn ▸ hr'), this⟩
    · rintro ⟨hx, hpre⟩
      have hxs : x ∈ sa := hsa.1.mem_iff.mpr (List.mem_range.mpr hx)
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hxs
      have hspec := (backwardSearch_spec_of_valid hv p hp r).mpr
        ⟨hr, by rw [getElem!_pos sa r hr]; exact hpre⟩
      refine ⟨r, ?_, by rw [getElem!_pos sa r hr]⟩
      simp only [List.mem_range'_1, stretch]
      omega

/-- On a valid index, a fragment with `$` in it occurs nowhere in the text. -/
private theorem occurrenceList_eq_nil {ix : FMIndex} (hv : ix.Valid) {p : List Nat} (hp : 0 ∈ p) :
    occurrenceList ix.text p = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun i hi =>
    not_occurs_of_absent hp (zero_not_mem_text hv) i (mem_occurrenceList.1 hi)

/-- **Locate on any valid index**: every start position of `p` in the text without its `$`, each
once, in no particular order. -/
theorem locate_perm_of_valid {ix : FMIndex} (hv : ix.Valid) (p : List Nat) :
    (ix.locate p).Perm (occurrenceList ix.text p) := by
  unfold locate
  split
  · rename_i hp
    rw [occurrenceList_eq_nil hv hp]
  · rename_i hp
    have h := rows_perm_matchStarts hv p (not_mem_dropLast hp)
    have e : matchStarts (ix.text ++ [0]) p = occurrenceList ix.text p :=
      filter_range_append _ _ hp
    rwa [invertBwt_eq_text hv, e] at h

/-- **Count on any valid index**: how many times `p` occurs in the text without its `$`. -/
theorem count_of_valid {ix : FMIndex} (hv : ix.Valid) (p : List Nat) :
    ix.count p = (occurrenceList ix.text p).length := by
  unfold count
  split
  · rename_i hp
    rw [occurrenceList_eq_nil hv hp]
    rfl
  · rename_i hp
    have e : matchStarts (ix.text ++ [0]) p = occurrenceList ix.text p :=
      filter_range_append _ _ hp
    rw [stretch, stretch_width_of_valid hv p (not_mem_dropLast hp), ← e, invertBwt_eq_text hv]
    rfl

end FMIndex

end AlgoDesign.Strings
