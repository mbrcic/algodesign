/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.List.Sort
public import AlgoDesign.Strings.BWT.Spec
public import AlgoDesign.Strings.SuffixArray.Build

/-!
# Burrows–Wheeler transform: two routes to one string

The rotation matrix and its last column, `bwtOfSorted`. The transform permutes its input
(`bwtOfSorted_perm`, `length_bwtOfSorted`), and under `Terminated` the rotation-matrix route
`bwtOfSorted` and the suffix-array route `bwtOfSa` agree (`bwt_eq_rotations`). Box invariant 2 is
decided at the library's suffix array, the only one (`BWT.letterBeforeEachSuffix_iff`).
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- A terminated text is not empty: it ends with its `$`. -/
theorem Terminated.ne_nil {t : List Nat} {s : Nat} (h : Terminated t s) : t ≠ [] := by
  rintro rfl
  exact absurd h.1 (by simp)

/-- All rotations of `t`: row `i` starts at position `i` and wraps. The unsorted matrix. -/
def rotations (t : List Nat) : List (List Nat) :=
  (List.range t.length).map fun i => t.drop i ++ t.take i

/-- The Burrows–Wheeler transform: the last column of the sorted rotation matrix. Insertion sort
reduces in the kernel; the `0` default is never reached. -/
def bwtOfSorted (t : List Nat) : List Nat :=
  (List.insertionSort (· ≤ ·) (rotations t)).map fun r => r.getLastD 0

/-- The transform read off a suffix array: row `r` holds `t[(sa[r] + n - 1) % n]`, the letter just
before the suffix row `r` names. On a suffix array of `t` every position is below `n`, so every
index is a position of `t`. -/
def bwtOfSa (t : List Nat) (sa : List Nat) : List Nat :=
  sa.map fun p => t[(p + t.length - 1) % t.length]!

/-- On a suffix array of `t`, the letter before each suffix is the transform's letter in its row:
every stored position is a position of `t`, so `letterBefore` always answers. -/
theorem map_letterBefore {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    sa.map (letterBefore t) = (bwtOfSa t sa).map some := by
  simp only [bwtOfSa, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have hp : p < t.length := List.mem_range.1 (hsa.1.mem_iff.1 hp)
  have hlt : (p + t.length - 1) % t.length < t.length := Nat.mod_lt _ (by omega)
  simp [letterBefore, List.getElem?_eq_getElem hlt, List.getElem!_eq_getElem?_getD]

/-- The transform read off a suffix array has one letter per row. -/
theorem length_bwtOfSa (t sa : List Nat) : (bwtOfSa t sa).length = sa.length := by
  simp [bwtOfSa]

/-- Box invariant 2 is decided at the library's suffix array: a text has only one. -/
theorem BWT.letterBeforeEachSuffix_iff (x : Transform) :
    BWT.LetterBeforeEachSuffix x ↔ x.letters = bwtOfSa x.text (suffixArray x.text) := by
  have hinj : ∀ l l' : List Nat, l.map some = l'.map some ↔ l = l' :=
    fun _ _ => List.map_inj_right fun _ _ => Option.some.inj
  refine ⟨fun h => ?_, fun h sa hsa => ?_⟩
  · rw [← hinj, ← map_letterBefore (valid_suffixArray _)]
    exact h _ (valid_suffixArray _)
  · rw [map_letterBefore hsa, hinj, h, valid_unique hsa (valid_suffixArray _)]

/-- The unsorted last column is the text rotated by one. -/
theorem lastColumn_rotations (t : List Nat) (ht : t ≠ []) :
    (rotations t).map (fun r => r.getLastD 0) = t.getLastD 0 :: t.dropLast := by
  have hpos : 0 < t.length := List.length_pos_iff.mpr ht
  refine List.ext_getElem ?_ ?_
  · simp [rotations]
    omega
  · intro i h1 _
    simp only [rotations, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
    match i with
    | 0 => simp
    | (j + 1) =>
      have hj : j < t.length := by
        simp [rotations] at h1
        omega
      rw [List.take_succ_eq_append_getElem hj, ← List.append_assoc, List.getLastD_concat]
      simp

/-- The transform is exactly as long as its input. -/
theorem length_bwtOfSorted (t : List Nat) : (bwtOfSorted t).length = t.length := by
  simp [bwtOfSorted, rotations, List.length_insertionSort]

/-- The transform is a permutation of its input. -/
theorem bwtOfSorted_perm (t : List Nat) : (bwtOfSorted t).Perm t := by
  by_cases ht : t = []
  · subst ht; simp [bwtOfSorted, rotations]
  · have hlast : t.getLastD 0 = t.getLast ht := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast ht]; rfl
    have hsort : (bwtOfSorted t).Perm ((rotations t).map (fun r => r.getLastD 0)) :=
      (List.perm_insertionSort _ _).map _
    rw [lastColumn_rotations t ht, hlast] at hsort
    have hsplit := List.perm_append_singleton (t.getLast ht) t.dropLast
    rw [List.dropLast_append_getLast ht] at hsplit
    exact hsort.trans hsplit.symm

/-- The sentinel is the text's last character. -/
theorem getElem!_last_of_terminated {t : List Nat} {s : Nat} (h : Terminated t s) :
    t[t.length - 1]! = s := by
  have hne := h.ne_nil
  obtain ⟨hlast, -⟩ := h
  have hpos : 0 < t.length := List.length_pos_iff.mpr hne
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
  rw [getElem!_pos t _ (by omega : t.length - 1 < t.length)]
  exact Option.some.inj hlast

/-- And everything before the end is strictly above it. -/
theorem lt_getElem!_of_terminated {t : List Nat} {s : Nat} (h : Terminated t s)
    {k : Nat} (hk : k < t.length - 1) : s < t[k]! := by
  obtain ⟨-, hmin⟩ := h
  have hlen : k < t.dropLast.length := by simp only [List.length_dropLast]; omega
  have hmem := List.getElem_mem hlen
  rw [List.getElem_dropLast] at hmem
  rw [getElem!_pos t k (by omega : k < t.length)]
  exact hmin _ hmem

/-- No suffix of a terminated text begins another: the shorter ends in the sentinel, where the
longer has a larger letter. -/
private theorem not_prefix_of_ne {t : List Nat} {s : Nat} (h : Terminated t s) {i j : Nat}
    (hi : i < t.length) (hj : j < t.length) (hij : i ≠ j) :
    ¬ suffix t i <+: suffix t j := by
  intro hpre
  have hlen := hpre.length_le
  simp only [suffix, List.length_drop] at hlen
  have hp : t.length - i - 1 < (suffix t i).length := by
    simp only [suffix, List.length_drop]; omega
  have hget := hpre.getElem hp
  simp only [suffix, List.getElem_drop] at hget
  have hget' : t[j + (t.length - i - 1)]! = t[i + (t.length - i - 1)]! := by
    rw [getElem!_pos t _ (by omega : j + (t.length - i - 1) < t.length),
      getElem!_pos t _ (by omega : i + (t.length - i - 1) < t.length)]
    exact hget.symm
  rw [(by omega : i + (t.length - i - 1) = t.length - 1),
    getElem!_last_of_terminated h] at hget'
  have hlt := lt_getElem!_of_terminated h (k := j + (t.length - i - 1)) (by omega)
  omega

/-- If neither list begins the other, appending to both does not change how they compare. -/
private theorem append_lt_append_iff_of_not_prefix :
    ∀ (A C B D : List Nat), ¬ A <+: C → ¬ C <+: A → (A ++ B < C ++ D ↔ A < C) := by
  intro A
  induction A with
  | nil => intro C _ _ hAC _; exact absurd List.nil_prefix hAC
  | cons a as ih =>
    intro C B D hAC hCA
    cases C with
    | nil => exact absurd List.nil_prefix hCA
    | cons c cs =>
      by_cases hac : a = c
      · subst hac
        have h1 : ¬ as <+: cs := fun hx => hAC (List.cons_prefix_cons.mpr ⟨rfl, hx⟩)
        have h2 : ¬ cs <+: as := fun hx => hCA (List.cons_prefix_cons.mpr ⟨rfl, hx⟩)
        simp only [List.cons_append, List.cons_lt_cons_iff, ih cs B D h1 h2]
      · simp only [List.cons_append, List.cons_lt_cons_iff, hac, false_and, or_false]

/-- The same statement for `≤`, which is what the sorted matrix is stated with. -/
private theorem append_le_append_iff_of_not_prefix (A C B D : List Nat)
    (hAC : ¬ A <+: C) (hCA : ¬ C <+: A) : A ++ B ≤ C ++ D ↔ A ≤ C := by
  change ¬ (C ++ D < A ++ B) ↔ ¬ (C < A)
  exact not_congr (append_lt_append_iff_of_not_prefix C A D B hCA hAC)

/-- Under a sentinel, two rotations compare as the suffixes they start with: the sentinel settles
the comparison before the wrapped tail is read. -/
private theorem rotation_le_iff_suffix_le (t : List Nat) (s : Nat) (h : Terminated t s)
    (i j : Nat) (hi : i < t.length) (hj : j < t.length) :
    (t.drop i ++ t.take i) ≤ (t.drop j ++ t.take j) ↔ suffix t i ≤ suffix t j := by
  by_cases hij : i = j
  · subst hij; exact iff_of_true (List.le_refl _) (List.le_refl _)
  · simp only [suffix]
    exact append_le_append_iff_of_not_prefix _ _ _ _
      (not_prefix_of_ne h hi hj hij) (not_prefix_of_ne h hj hi (Ne.symm hij))

/-- Under `Terminated`, the rotation-matrix and suffix-array routes give the same transform. -/
theorem bwt_eq_rotations (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    bwtOfSa t sa = bwtOfSorted t := by
  obtain ⟨hperm, hsorted⟩ := hsa
  unfold SuffixArray.SuffixesSorted at hsorted
  have hpos : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hmem : ∀ p ∈ sa, p < t.length := fun p hp => List.mem_range.mp (hperm.mem_iff.mp hp)
  have htotal : Std.Total (· ≤ · : List Nat → List Nat → Prop) := ⟨List.le_total⟩
  have htrans : IsTrans (List Nat) (· ≤ ·) := ⟨fun _ _ _ => List.le_trans⟩
  -- A sorted permutation is unique, so the sorted matrix is the suffix array's rows.
  have hrows : List.insertionSort (· ≤ ·) (rotations t)
      = sa.map (fun p => t.drop p ++ t.take p) := by
    refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ hab hba =>
      List.le_antisymm hab hba) (List.pairwise_insertionSort _ _) ?_ ?_
    · rw [List.pairwise_map] at hsorted ⊢
      refine hsorted.imp_of_mem ?_
      intro a b ha hb hle
      exact (rotation_le_iff_suffix_le t s h a b (hmem a ha) (hmem b hb)).mpr hle
    · refine (List.perm_insertionSort _ _).trans ?_
      simp only [rotations]
      exact (hperm.map _).symm
  rw [bwtOfSorted, hrows, List.map_map, bwtOfSa]
  refine List.map_congr_left ?_
  intro p hp
  have hplt := hmem p hp
  simp only [Function.comp_apply]
  cases p with
  | zero =>
    -- Row `0` is the text itself, ending in the sentinel.
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : t.length - 1 < t.length),
      getElem!_last_of_terminated h]
    simp only [List.drop_zero, List.take_zero, List.append_nil, List.getLastD_eq_getLast?, h.1]
    rfl
  | succ k =>
    -- Every other row ends in the character just before the suffix it names.
    have hk : k < t.length := by omega
    rw [(by omega : k + 1 + t.length - 1 = k + t.length), Nat.add_mod_right,
      Nat.mod_eq_of_lt hk, List.take_succ_eq_append_getElem hk, ← List.append_assoc,
      List.getLastD_concat]
    exact getElem!_pos t k hk

end AlgoDesign.Strings
