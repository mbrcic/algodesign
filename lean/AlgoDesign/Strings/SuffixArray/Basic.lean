/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.SuffixArray.Spec

/-!
# Suffix array: what every suffix array satisfies

Facts about any `sa` with `SuffixArray.Valid ⟨t, sa⟩`, whichever construction produced it.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Suffixes of one text are pairwise distinct: their lengths name their positions. -/
theorem suffix_inj {t : List Nat} {i j : Nat} (hi : i < t.length) (hj : j < t.length)
    (h : suffix t i = suffix t j) : i = j := by
  have hlen := congrArg List.length h
  simp only [suffix, List.length_drop] at hlen
  omega

/-- How many suffixes of `t` sort strictly below suffix `i`: its row in the suffix array. -/
def saPos (t : List Nat) (i : Nat) : Nat :=
  ((List.range t.length).filter (fun j => decide (suffix t j < suffix t i))).length

/-- **The counting characterisation.** A suffix array puts each suffix at the row equal to the
number of suffixes below it, so positions can be settled by comparisons. -/
theorem saPos_eq_count (t : List Nat) (sa : List Nat) (h : SuffixArray.Valid ⟨t, sa⟩)
    (r : Nat) (hr : r < sa.length) :
    saPos t sa[r]! = r := by
  obtain ⟨hperm, hsorted⟩ := h
  unfold SuffixArray.SuffixesSorted at hsorted
  rw [List.pairwise_map] at hsorted
  have hnodup : sa.Pairwise (· ≠ ·) := hperm.nodup_iff.mpr List.nodup_range
  have hmem : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (hperm.mem_iff.mp ha)
  -- Split the array at `r`: everything before, and everything from `r` on.
  have hsplit : sa.take r ++ sa.drop r = sa := List.take_append_drop r sa
  rw [← hsplit] at hsorted hnodup
  obtain ⟨-, hsortedD, hcross⟩ := List.pairwise_append.mp hsorted
  obtain ⟨-, -, hcrossne⟩ := List.pairwise_append.mp hnodup
  have hdrop : sa.drop r = sa[r] :: sa.drop (r + 1) := List.drop_eq_getElem_cons hr
  have hrmem : sa[r] ∈ sa.drop r := by rw [hdrop]; exact List.mem_cons_self
  -- Nothing from `r` on sorts below suffix `sa[r]`.
  have hge : ∀ b ∈ sa.drop r, suffix t sa[r] ≤ suffix t b := by
    rw [hdrop] at hsortedD ⊢
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact List.not_lt.mp (List.lt_irrefl _)
    · exact (List.pairwise_cons.mp hsortedD).1 b hb'
  rw [getElem!_pos sa r hr]
  -- The count runs over the positions of `t`, which `sa` enumerates.
  have hcount : saPos t sa[r] = sa.countP (fun j => decide (suffix t j < suffix t sa[r])) := by
    rw [saPos, ← List.countP_eq_length_filter]
    exact (hperm.countP_eq _).symm
  have happ := List.countP_append (p := fun j => decide (suffix t j < suffix t sa[r]))
    (l₁ := sa.take r) (l₂ := sa.drop r)
  rw [List.take_append_drop] at happ
  -- Everything before `r` sorts below suffix `sa[r]`: it sorts at most as high, and the two
  -- suffixes are distinct because the positions are.
  have htake : (sa.take r).countP (fun j => decide (suffix t j < suffix t sa[r])) = r := by
    have hall : ∀ a ∈ sa.take r, decide (suffix t a < suffix t sa[r]) = true := by
      intro a ha
      have hamem : a ∈ sa := List.mem_of_mem_take ha
      have hle : suffix t a ≤ suffix t sa[r] := hcross a ha _ hrmem
      have hne : a ≠ sa[r] := hcrossne a ha _ hrmem
      simp only [decide_eq_true_eq]
      refine List.not_le.mp (fun hcon => hne ?_)
      exact suffix_inj (hmem a hamem) (hmem _ (List.getElem_mem hr)) (List.le_antisymm hle hcon)
    rw [List.countP_eq_length.mpr hall, List.length_take_of_le (Nat.le_of_lt hr)]
  have hzero : (sa.drop r).countP (fun j => decide (suffix t j < suffix t sa[r])) = 0 := by
    refine List.countP_eq_zero.mpr ?_
    intro b hb
    simp only [decide_eq_true_eq]
    exact fun hlt => absurd (hge b hb) (List.not_le.mpr hlt)
  rw [hcount, happ, htake, hzero]
  rfl

/-- **The step the LF mapping walks.** Two positions carrying the same character compare exactly
as their successors do. -/
theorem suffix_le_cons_iff (t : List Nat) (i j : Nat) (hi : i < t.length) (hj : j < t.length)
    (hc : t[i]! = t[j]!) :
    suffix t i ≤ suffix t j ↔ suffix t (i + 1) ≤ suffix t (j + 1) := by
  rw [getElem!_pos t i hi, getElem!_pos t j hj] at hc
  simp only [suffix, List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj,
    List.cons_le_cons_iff, hc, Nat.lt_irrefl, true_and, false_or]

/-- **Suffix arrays are unique.** Two suffix arrays of one text are the same list. -/
theorem valid_unique {t sa sa' : List Nat} (h : SuffixArray.Valid ⟨t, sa⟩)
    (h' : SuffixArray.Valid ⟨t, sa'⟩) : sa = sa' := by
  have hmem : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (h.1.mem_iff.mp ha)
  have hmem' : ∀ a ∈ sa', a < t.length := fun a ha => List.mem_range.mp (h'.1.mem_iff.mp ha)
  exact List.Perm.eq_of_pairwise (le := fun a b => suffix t a ≤ suffix t b)
    (fun a b ha hb hab hba => suffix_inj (hmem a ha) (hmem' b hb) (List.le_antisymm hab hba))
    (List.pairwise_map.mp h.2) (List.pairwise_map.mp h'.2) (h.1.trans h'.1.symm)

end AlgoDesign.Strings
