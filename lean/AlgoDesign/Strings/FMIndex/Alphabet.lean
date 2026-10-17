/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Dedup
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import AlgoDesign.Strings.FMIndex.Search

/-!
# FM-index: the effective alphabet and the dense C array

The effective alphabet (the symbols that occur, ascending), each symbol's dense index, and `C` as
one prefix sum per dense index. `cDense_eq_cLess`: that prefix sum is `cLess`; `lfDense_eq`: the LF
formula over it is `lf`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- `Alphabet::index_of`: a symbol's dense index, its position in the alphabet. -/
def indexOf (syms : List Nat) (c : Nat) : Nat := syms.idxOf c
/-- Models `FmIndex::lf`: `C[dense(L[r])]` plus the occurrences of `L[r]` before row `r`. -/
def lfDense (σ : Nat) (bwt : List Nat) (r : Nat) : Nat :=
  let syms := alphabetOf σ bwt
  (cDense bwt syms)[indexOf syms bwt[r]!]! + occ bwt bwt[r]! r

private theorem idxOf_append_cons (A B : List Nat) (c : Nat) (h : c ∉ A) :
    (A ++ c :: B).idxOf c = A.length := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have ha : a ≠ c := fun hac => h (hac ▸ List.mem_cons_self)
    have hA : c ∉ A := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.cons_append, List.idxOf_cons_ne _ ha, ih hA]
    rfl

/-- The alphabet splits at `c`: the symbols below it, then `c`, then the rest. -/
private theorem alphabetOf_split (σ : Nat) (t : List Nat) (c : Nat) (hc : c < σ) (hct : c ∈ t) :
    ∃ B, alphabetOf σ t = (List.range c).filter (· ∈ t) ++ c :: B := by
  obtain ⟨m, rfl⟩ : ∃ m, σ = c + (m + 1) := ⟨σ - c - 1, by omega⟩
  refine ⟨(((List.range m).map Nat.succ).map (fun x => c + x)).filter (· ∈ t), ?_⟩
  rw [alphabetOf, List.range_add, List.filter_append, List.range_succ_eq_map, List.map_cons,
    List.filter_cons_of_pos (by simpa using hct)]
  simp

/-- Counting the letters below `c` by position equals counting them by value. -/
theorem cLess_eq_countP (t : List Nat) (c : Nat) :
    cLess t c = t.countP (fun x => decide (x < c)) := by
  have hmap : (List.range t.length).map (fun j => t[j]!) = t := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact getElem!_pos t i h2
  rw [cLess, ← List.countP_eq_length_filter]
  conv_rhs => rw [← hmap]
  rw [List.countP_map]
  rfl

/-- The dense C array is `cLess`: the alphabet is ascending, so the symbols before `c`'s index are
exactly those below `c`. -/
theorem cDense_eq_cLess (σ : Nat) (t : List Nat) (ht : ∀ x ∈ t, x < σ) (c : Nat) (hct : c ∈ t) :
    (cDense t (alphabetOf σ t))[indexOf (alphabetOf σ t) c]! = cLess t c := by
  obtain ⟨B, hB⟩ := alphabetOf_split σ t c (ht c hct) hct
  set A := (List.range c).filter (· ∈ t) with hA
  have hcA : c ∉ A := by simp [hA]
  have hidx : indexOf (alphabetOf σ t) c = A.length := by
    rw [indexOf, hB]; exact idxOf_append_cons A B c hcA
  have hlt : A.length < (alphabetOf σ t).length := by rw [hB]; simp
  rw [hidx, getElem!_pos _ _ (by simpa [cDense] using hlt)]
  simp only [cDense, List.getElem_map, List.getElem_range]
  rw [hB, List.take_left' rfl, cLess_eq_countP,
    ← List.sum_map_count_dedup_filter_eq_countP]
  -- The symbols below `c` that occur, listed two ways: ascending, and by first occurrence.
  have hperm : A.Perm (t.dedup.filter fun x => decide (x < c)) := by
    refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
    · exact (List.nodup_range).filter _
    · exact (List.nodup_dedup t).filter _
    · intro a
      simp [hA, List.mem_filter, List.mem_dedup, and_comm]
  exact (hperm.map _).sum_eq

/-- `lfDense` is `lf` on every row of the column. -/
theorem lfDense_eq (σ : Nat) (bwt : List Nat) (hσ : ∀ x ∈ bwt, x < σ) (r : Nat)
    (hr : r < bwt.length) : lfDense σ bwt r = lf bwt r := by
  have hmem : bwt[r]! ∈ bwt := by rw [getElem!_pos bwt r hr]; exact List.getElem_mem hr
  rw [lfDense, cDense_eq_cLess σ bwt hσ _ hmem, cLess_eq_countP, lf,
    List.countP_eq_length_filter, occ]
  congr 1

end AlgoDesign.Strings
