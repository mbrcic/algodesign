/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.FMIndex.Alphabet
public import AlgoDesign.Strings.FMIndex.Sampled

/-!
# FM-index: the build establishes `FMIndex.Valid` and `FMIndex.WellFormed`

`FMIndex.build` stores the parts `FmIndex::build` stores; `FMIndex.valid_build`: they meet
`FMIndex.Valid` and `FMIndex.WellFormed`. `FMIndex.pieces_iff_valid_wellFormed`: the seven pieces
are `Valid` and `WellFormed`. The real argument is `walkVisitsEveryRow_build`: `lf` walks the text
backwards one position per step, so it visits every row once before it returns.
-/

@[expose] public section

namespace AlgoDesign.Strings

open FMIndex (KeptPositionsCorrect PositionsKept SentinelOnce SmallerLettersCounted
  WalkVisitsEveryRow KeptRowsListed LettersAreBytes RateAtLeastTwo)

/-- The index of a text from its suffix array, keeping every `k`-th position: the parts
`FmIndex::build` stores. -/
def FMIndex.ofSa (t sa : List Nat) (k : Nat) : FMIndex where
  bwt := bwtOfSa t sa
  c := cDense (bwtOfSa t sa) (alphabetOf 256 (bwtOfSa t sa))
  marks := saMarks sa k
  saSamples := saValues sa k
  isaSamples := saKeptRows sa k
  sample := k

/-- `FmIndex::build`: the index of a text, keeping every `k`-th position, over the suffix array
the library builds. -/
def FMIndex.build (t : List Nat) (k : Nat) : FMIndex := FMIndex.ofSa t (suffixArray t) k

/-- The column the build stores holds the sentinel once: it is a permutation of the text. -/
theorem sentinelOnce_build {t sa : List Nat} (h : Terminated t 0) (hsa : SuffixArray.Valid ⟨t, sa⟩)
    (k : Nat) : SentinelOnce (FMIndex.ofSa t sa k) := by
  unfold SentinelOnce FMIndex.ofSa
  dsimp only
  rw [bwt_eq_rotations t 0 h sa hsa, (bwtOfSorted_perm t).count_eq]
  exact count_sentinel h

/-- The stored column is one `lf` cycle: each step moves one text position left, so `n` steps from
row `0` visit `n` different rows and return. -/
theorem walkVisitsEveryRow_build {t sa : List Nat} (h : Terminated t 0)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) :
    WalkVisitsEveryRow (FMIndex.ofSa t sa k) := by
  unfold WalkVisitsEveryRow FMIndex.ofSa
  dsimp only
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = t.length := by simp [bwtOfSa, hlen]
  have hnd : sa.Nodup := hsa.1.nodup_iff.mpr List.nodup_range
  have h0 : sa[0]! < t.length := by
    have hm : sa[0]! ∈ sa := by
      rw [getElem!_pos sa 0 (by omega)]; exact List.getElem_mem _
    exact List.mem_range.mp (hsa.1.mem_iff.mp hm)
  -- Rows with the same suffix-array entry are the same row.
  have hrow : ∀ r r', r < sa.length → r' < sa.length → sa[r]! = sa[r']! → r = r' := by
    intro r r' hr hr' he
    rw [getElem!_pos sa r hr, getElem!_pos sa r' hr'] at he
    exact (hnd.getElem_inj_iff).mp he
  -- Positions `j` and `j'` steps back from `sa[0]` differ when `j < j' < n`.
  have hpos : ∀ j j', j < j' → j' < t.length →
      (sa[0]! + t.length - j) % t.length ≠ (sa[0]! + t.length - j') % t.length := by
    intro j j' hjj hj' he
    have hz := Nat.sub_mod_eq_zero_of_mod_eq he
    rw [show sa[0]! + t.length - j - (sa[0]! + t.length - j') = j' - j by omega,
      Nat.mod_eq_of_lt (by omega)] at hz
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hbl]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro j hj j' hj' he
    have hj := List.mem_range.mp hj
    have hj' := List.mem_range.mp hj'
    obtain ⟨hr, hv⟩ := iterate_lf_from h hsa 0 (by omega) j (by omega)
    obtain ⟨hr', hv'⟩ := iterate_lf_from h hsa 0 (by omega) j' (by omega)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hpos j j' hlt hj' (hv ▸ hv' ▸ congrArg (sa[·]!) he)
    · exact hpos j' j hlt hj (hv' ▸ hv ▸ congrArg (sa[·]!) he.symm)
  · rw [hbl]
    obtain ⟨hr, hv⟩ := iterate_lf_from h hsa 0 (by omega) t.length (Nat.le_refl _)
    refine hrow _ 0 hr (by omega) ?_
    rw [hv, Nat.add_sub_cancel, Nat.mod_eq_of_lt h0]
  · intro r hr
    rw [hbl] at hr ⊢
    rw [← hlen] at hr ⊢
    exact lf_lt_length t 0 h sa hsa r hr

/-- The build stores one mark per row and one sample value per mark. -/
private theorem keptRowsFlagged_build (t sa : List Nat) (k : Nat) :
    (saMarks sa k).length = (bwtOfSa t sa).length ∧
      (saMarks sa k).count true = (saValues sa k).length := by
  refine ⟨by simp [saMarks, bwtOfSa], ?_⟩
  simp [saMarks, saValues, List.count_eq_countP, List.countP_eq_length_filter, List.filter_map,
    Function.comp_def]

/-- The sample values the build stores are the multiples of `k` below `n`, each once. -/
private theorem positionsKeptEvenly_build {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩)
    {k : Nat} (hk : 0 < k) :
    (saValues sa k).Perm
      ((List.range (((bwtOfSa t sa).length + k - 1) / k)).map (· * k)) := by
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = t.length := by simp [bwtOfSa, hlen]
  rw [hbl]
  refine (hsa.1.filter _).trans ((List.perm_ext_iff_of_nodup
    (List.nodup_range.filter _) ((List.nodup_range).map_on ?_)).mpr ?_)
  · intro a _ b _ he
    exact Nat.eq_of_mul_eq_mul_right hk he
  · intro x
    simp only [List.mem_filter, List.mem_range, beq_iff_eq, List.mem_map]
    constructor
    · rintro ⟨hx, hm⟩
      have hxk : x / k * k = x := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
      refine ⟨x / k, Nat.lt_of_succ_le ?_, hxk⟩
      rw [Nat.le_div_iff_mul_le hk, Nat.succ_mul, hxk]
      omega
    · rintro ⟨i, hi, rfl⟩
      have := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at this
      exact ⟨by omega, by simp⟩

/-- A marked row's stored value is at the index given by the marks before it (the `Option` form of
`getElem!_filter_rank`). -/
theorem getElem?_filter_count (P : Nat → Bool) :
    ∀ (l : List Nat) (r : Nat) (hr : r < l.length), P l[r] = true →
      (l.filter P)[((l.map P).take r).count true]? = some l[r] := by
  intro l
  induction l with
  | nil => intro r hr; simp at hr
  | cons x xs ih =>
    intro r hr hP
    cases r with
    | zero =>
      have hx : P x = true := by simpa using hP
      simp [hx]
    | succ r =>
      have hr' : r < xs.length := by simpa using hr
      have hP' : P xs[r] = true := by simpa using hP
      cases hx : P x
      · simp [hx, ih r hr' hP']
      · simp [hx, ih r hr' hP']

/-- Each marked row the build stores holds its own text position. -/
theorem keptPositionsCorrect_build {t sa : List Nat} (h : Terminated t 0)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) :
    KeptPositionsCorrect (FMIndex.ofSa t sa k) := by
  unfold KeptPositionsCorrect FMIndex.ofSa
  simp only [FMIndex.rowAfter, FMIndex.sentinelRow, FMIndex.keptValueAt]
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = t.length := by simp [bwtOfSa, hlen]
  obtain ⟨h0r, h0v⟩ := idxOf_sentinel_bwtOfSa h hsa
  intro _ j hj
  rw [hbl] at hj ⊢
  obtain ⟨hr, hv⟩ := iterate_lf_from h hsa _ h0r j (by omega)
  rw [h0v, Nat.zero_add] at hv
  set r := (lf (bwtOfSa t sa))^[j] ((bwtOfSa t sa).idxOf 0)
  rw [getElem!_pos sa r hr] at hv
  refine ⟨by simpa [saMarks] using hr, ?_, fun hm => ?_⟩
  · simp only [saMarks, List.getElem_map, beq_iff_eq, Nat.dvd_iff_mod_eq_zero]
    exact iff_of_eq (congrArg (· % k = 0) hv)
  rw [saMarks, saValues, getElem?_filter_count (fun p => p % k == 0) sa r hr
    (by simp [hv, Nat.mod_eq_zero_of_dvd hm]), hv]

/-- The build keeps every `k`-th position, at its row, and marks it: box invariant 2. -/
theorem positionsKept_build {t sa : List Nat} (h : Terminated t 0)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) {k : Nat} (hk : 0 < k) :
    PositionsKept (FMIndex.ofSa t sa k) :=
  ⟨positionsKeptEvenly_build hsa hk, (keptRowsFlagged_build t sa k).1,
    (keptRowsFlagged_build t sa k).2, keptPositionsCorrect_build h hsa k⟩

/-- The build lists, for each multiple of `k` below `n`, the marked row holding it. -/
theorem keptRowsListed_build {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {k : Nat}
    (hk : 0 < k) :
    KeptRowsListed (FMIndex.ofSa t sa k) := by
  unfold KeptRowsListed FMIndex.ofSa
  simp only [FMIndex.keptValueAt]
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = sa.length := by simp [bwtOfSa]
  refine ⟨by simp [saKeptRows, hbl], fun j hj => ?_⟩
  have hj' : j < (sa.length + k - 1) / k := by simpa [saKeptRows] using hj
  have hjk : j * k < sa.length := by
    have := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt hj')
    rw [Nat.succ_mul] at this
    omega
  have hmem : j * k ∈ sa := hsa.1.mem_iff.mpr (List.mem_range.mpr (hlen ▸ hjk))
  have hi : sa.idxOf (j * k) < sa.length := List.idxOf_lt_length_of_mem hmem
  have hget : sa[sa.idxOf (j * k)] = j * k := List.getElem_idxOf hi
  have hisa : (saKeptRows sa k)[j] = sa.idxOf (j * k) := by simp [saKeptRows]
  rw [hisa, hbl]
  refine ⟨hi, by simp [saMarks, hi, hget], ?_⟩
  rw [saMarks, saValues, getElem?_filter_count (fun p => p % k == 0) sa _ hi (by simp [hget]),
    hget]

/-- The column built from a text of bytes holds only bytes: each of its letters is a letter of the
text. -/
theorem lettersAreBytes_build {t : List Nat} (sa : List Nat) (k : Nat) (ht : t ≠ [])
    (hbytes : ∀ x ∈ t, x < 256) : LettersAreBytes (FMIndex.ofSa t sa k) := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  have hn : 0 < t.length := List.length_pos_iff.mpr ht
  rw [getElem!_pos t _ (Nat.mod_lt _ hn)]
  exact hbytes _ (List.getElem_mem _)

/-- **The pieces split into the box's and the rest**: the seven pieces of the stored index are
exactly `Valid` and `WellFormed`. -/
theorem FMIndex.pieces_iff_valid_wellFormed (ix : FMIndex) :
    (PositionsKept ix ∧ SentinelOnce ix ∧ SmallerLettersCounted ix ∧ WalkVisitsEveryRow ix ∧
      KeptRowsListed ix ∧ LettersAreBytes ix ∧ RateAtLeastTwo ix) ↔
      ix.Valid ∧ ix.WellFormed :=
  Iff.rfl

/-- The index built from a text of bytes terminated by `0` and its suffix array satisfies
`FMIndex.Valid` and `FMIndex.WellFormed`. -/
theorem FMIndex.valid_build {t sa : List Nat} {k : Nat} (h : Terminated t 0)
    (hbytes : ∀ x ∈ t, x < 256) (hsa : SuffixArray.Valid ⟨t, sa⟩) (hk : 2 ≤ k) :
    (FMIndex.ofSa t sa k).Valid ∧ (FMIndex.ofSa t sa k).WellFormed :=
  ⟨positionsKept_build h hsa (by omega), sentinelOnce_build h hsa k, rfl,
    walkVisitsEveryRow_build h hsa k, keptRowsListed_build hsa (by omega),
    lettersAreBytes_build sa k h.ne_nil hbytes, hk⟩

end AlgoDesign.Strings
