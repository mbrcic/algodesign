/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.FMIndex.Decide
public import AlgoDesign.Strings.SuffixArray.Build
public import AlgoDesign.Strings.BWT.Invert
public import AlgoDesign.Strings.RankSelect.Basic

/-!
# FM-index: backward search, count, locate and extract

`backwardSearch` reads only `bwtOfSa t sa` and `cLess t`, folding over the pattern right to left
and keeping `BackwardSearch.Valid`. `fmCount_eq`: the interval's width is the number of
occurrences; `fmLocate_perm`: its rows name exactly those positions; `fmExtract_eq`: the LF walk
from a row returns the slice ending at that row's position.

The sentinel may occur in the pattern only as its last character (`hp : s ∉ p.dropLast`): the last
column is read off rotations, so an earlier `$` would match across the wrap.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Where `p`'s block begins: the suffixes of `t` that sort strictly below `p`. -/
def lexBelow (t p : List Nat) : Nat :=
  ((List.range t.length).filter (fun i => decide (suffix t i < p))).length

/-- How wide `p`'s block is: the positions of `t` whose suffix begins with `p`. -/
def matchCount (t p : List Nat) : Nat :=
  ((List.range t.length).filter (fun i => decide (p <+: suffix t i))).length

/-! ## Backward search's running state -/

namespace BackwardSearch

/-- Not in the box: the stretch starts at the block of what has been read, which pins it
when it is empty. -/
def StretchStartsRight (s : Stretch) : Prop := s.lo = lexBelow s.index.text s.read

/-- Not in the box: the stretch is as wide as the number of matches of what has been read. -/
def StretchAsWideAsMatches (s : Stretch) : Prop :=
  s.hi = s.lo + matchCount s.index.text s.read

/-- Backward search's running state after reading the end of the pattern. -/
def Valid (s : Stretch) : Prop :=
  StretchHoldsMatches s ∧ StretchStartsRight s ∧ StretchAsWideAsMatches s

instance (s : Stretch) : Decidable (StretchStartsRight s) :=
  by unfold StretchStartsRight; infer_instance

instance (s : Stretch) : Decidable (StretchAsWideAsMatches s) :=
  by unfold StretchAsWideAsMatches; infer_instance

instance (s : Stretch) : Decidable (Valid s) :=
  by unfold Valid; infer_instance

end BackwardSearch

/-- Where `p` starts in `t`: the positions whose suffix begins with `p`, ascending. There are
`matchCount t p` of them. -/
def matchStarts (t p : List Nat) : List Nat :=
  (List.range t.length).filter (fun i => decide (p <+: suffix t i))

/-- The C array: how many of the text's letters sort strictly below `c`, the offset of `c`'s block
in the first column. -/
def cLess (t : List Nat) (c : Nat) : Nat :=
  ((List.range t.length).filter (fun j => decide (t[j]! < c))).length

/-- One backward-search step: narrow the interval `[lo, hi)` of the pattern suffix `p` to that of
`c :: p`, through the C array and `occ` on the last column. -/
def backwardStep (bwt : List Nat) (cLess : Nat → Nat) (c : Nat) (lo hi : Nat) : Nat × Nat :=
  (cLess c + occ bwt c lo, cLess c + occ bwt c hi)

/-- Backward search: fold the step over the pattern, right to left, from the full interval. -/
def backwardSearch (bwt : List Nat) (cLess : Nat → Nat) (p : List Nat) : Nat × Nat :=
  p.foldr (fun c acc => backwardStep bwt cLess c acc.1 acc.2) (0, bwt.length)

/-- The count of `p` in `t`. It builds the column and the C array from `t`; `backwardSearch`,
which does the searching, cannot read `t`. -/
def fmCount (t p : List Nat) : Nat :=
  let (lo, hi) := backwardSearch (bwtOfSorted t) (cLess t) p
  hi - lo

/-- The positions of `p` in `t`: the interval's rows, read off the full suffix array. -/
def fmLocate (t sa p : List Nat) : List Nat :=
  let (lo, hi) := backwardSearch (bwtOfSa t sa) (cLess t) p
  (sa.drop lo).take (hi - lo)

/-! ### Groundwork: prefixes and lexicographic order -/

/-- If `p` begins `y` but not `x`, and `x` does not sort below `p`, then `x` sorts above `y`. -/
private theorem lt_of_prefix_of_le : ∀ {p x y : List Nat},
    p <+: y → p ≤ x → ¬ p <+: x → y < x := by
  intro p
  induction p with
  | nil => intro _ _ _ _ hnp; exact absurd List.nil_prefix hnp
  | cons a p ih =>
    intro x y hpy hle hnp
    obtain ⟨z, rfl⟩ := hpy
    cases x with
    | nil => exact absurd (List.le_nil.mp hle) (List.cons_ne_nil a p)
    | cons b x =>
      rw [List.cons_le_cons_iff] at hle
      rw [List.cons_append, List.cons_lt_cons_iff]
      rcases hle with hab | ⟨rfl, hle'⟩
      · exact Or.inl hab
      · refine Or.inr ⟨rfl, ih (List.prefix_append p z) hle' ?_⟩
        exact fun hc => hnp (List.cons_prefix_cons.mpr ⟨rfl, hc⟩)

/-- The same fact read the other way: below everything `p` begins is below `p`. -/
private theorem lt_of_lt_of_prefix {p x y : List Nat} (hxy : x < y) (hpy : p <+: y)
    (hnp : ¬ p <+: x) : x < p := by
  by_contra hcon
  exact List.lt_asymm hxy (lt_of_prefix_of_le hpy (List.not_lt.mp hcon) hnp)

/-- A suffix reads as its first character followed by the next suffix. -/
private theorem suffix_eq_cons {t : List Nat} {i : Nat} (hi : i < t.length) :
    suffix t i = t[i]! :: suffix t (i + 1) := by
  rw [getElem!_pos t i hi]
  simp only [suffix, List.drop_eq_getElem_cons hi]

/-! ### Groundwork: rows of a slice of the suffix array -/

/-- An element of a prefix of the array is a row before the cut. -/
private theorem mem_take_row (sa : List Nat) (k : Nat) {x : Nat} (hx : x ∈ sa.take k) :
    ∃ y, y < k ∧ y < sa.length ∧ sa[y]! = x := by
  obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take] at hy
  refine ⟨y, by omega, by omega, ?_⟩
  rw [getElem!_pos sa y (by omega)]
  simp only [List.getElem_take]

/-- An element of a suffix of the array is a row at or after the cut. -/
private theorem mem_drop_row (sa : List Nat) (k : Nat) {x : Nat} (hx : x ∈ sa.drop k) :
    ∃ y, k ≤ y ∧ y < sa.length ∧ sa[y]! = x := by
  obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_drop] at hy
  refine ⟨k + y, by omega, by omega, ?_⟩
  rw [getElem!_pos sa (k + y) (by omega)]
  simp only [List.getElem_drop]

/-- And an element of a slice is a row inside it. -/
private theorem mem_slice_row (sa : List Nat) (k m : Nat) {x : Nat}
    (hx : x ∈ (sa.drop k).take m) : ∃ y, k ≤ y ∧ y < k + m ∧ y < sa.length ∧ sa[y]! = x := by
  obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take, List.length_drop] at hy
  refine ⟨k + y, by omega, by omega, by omega, ?_⟩
  rw [getElem!_pos sa (k + y) (by omega)]
  simp only [List.getElem_take, List.getElem_drop]

/-! ### Where a counting threshold puts a row -/

/-- Both counting quantities are `countP`s. -/
private theorem lexBelow_eq_countP (t p : List Nat) :
    lexBelow t p = (List.range t.length).countP (fun i => decide (suffix t i < p)) := by
  rw [lexBelow, List.countP_eq_length_filter]

private theorem matchCount_eq_countP (t p : List Nat) :
    matchCount t p = (List.range t.length).countP (fun i => decide (p <+: suffix t i)) := by
  rw [matchCount, List.countP_eq_length_filter]

/-- For a downward-closed `Q`, a row sits below the number of suffixes satisfying `Q` exactly when
its suffix satisfies `Q`. Both interval ends are such counts. -/
private theorem saPos_lt_countP_iff (t : List Nat) (Q : List Nat → Bool)
    (hdown : ∀ x y : List Nat, x ≤ y → Q y = true → Q x = true)
    {i : Nat} (hi : i < t.length) :
    saPos t i < (List.range t.length).countP (fun j => Q (suffix t j))
      ↔ Q (suffix t i) = true := by
  rw [saPos, ← List.countP_eq_length_filter]
  constructor
  · intro hlt
    by_contra hQ
    have hmono : (List.range t.length).countP (fun j => Q (suffix t j))
        ≤ (List.range t.length).countP (fun j => decide (suffix t j < suffix t i)) := by
      refine List.countP_mono_left ?_
      intro x _ hQx
      simp only [decide_eq_true_eq]
      exact List.not_le.mp (fun hle => hQ (hdown (suffix t i) (suffix t x) hle hQx))
    omega
  · intro hQ
    refine countP_lt_countP ?_ (List.mem_range.mpr hi) ?_ hQ
    · intro x _ hx
      simp only [decide_eq_true_eq] at hx
      exact hdown (suffix t x) (suffix t i) (List.le_of_lt hx) hQ
    · simp only [decide_eq_false_iff_not]
      exact List.lt_irrefl _

/-- "Sorts below `p`" is downward closed. -/
private theorem down_lexBelow (p : List Nat) :
    ∀ x y : List Nat, x ≤ y → decide (y < p) = true → decide (x < p) = true := by
  intro x y hle hy
  simp only [decide_eq_true_eq] at hy ⊢
  exact List.lt_of_le_of_lt hle hy

/-- And so is "sorts below `p` or begins with `p`", what the upper end counts. -/
private theorem down_lexBelowOrPrefix (p : List Nat) :
    ∀ x y : List Nat, x ≤ y → decide (y < p ∨ p <+: y) = true →
      decide (x < p ∨ p <+: x) = true := by
  intro x y hle hy
  simp only [decide_eq_true_eq] at hy ⊢
  rcases hy with hlt | hpre
  · exact Or.inl (List.lt_of_le_of_lt hle hlt)
  · by_cases hpx : p <+: x
    · exact Or.inr hpx
    · rcases List.le_iff_lt_or_eq.mp hle with hlt | rfl
      · exact Or.inl (lt_of_lt_of_prefix hlt hpre hpx)
      · exact Or.inr hpre

/-- The upper end counts the block and everything under it, and the two never overlap. -/
private theorem countP_below_or_prefix (t p : List Nat) :
    (List.range t.length).countP (fun i => decide (suffix t i < p ∨ p <+: suffix t i))
      = lexBelow t p + matchCount t p := by
  rw [lexBelow_eq_countP, matchCount_eq_countP]
  refine countP_split (fun x _ => ?_) (fun x _ hB => ?_)
  · simp only [Bool.decide_or]
  · simp only [decide_eq_true_eq] at hB
    simp only [decide_eq_false_iff_not]
    exact fun hpre => absurd hpre.le (List.not_le.mpr hB)

/-! ### One step of the search, as a count -/

/-- Counting suffixes satisfying `Q` whose preceding letter is `c` is counting positions holding
`c` whose next suffix satisfies `Q`. `hwrap` handles the sentinel's wrap. -/
private theorem countP_shift (t : List Nat) (s : Nat) (h : Terminated t s) (c : Nat)
    (Q : List Nat → Bool) (hwrap : c = s → Q (suffix t 0) = Q []) :
    (List.range t.length).countP
        (fun i => Q (suffix t i) && decide (t[(i + t.length - 1) % t.length]! = c))
      = (List.range t.length).countP
        (fun j => decide (t[j]! = c) && Q (suffix t (j + 1))) := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  obtain ⟨m, hm⟩ : ∃ m, t.length = m + 1 := ⟨t.length - 1, by omega⟩
  have hlast : t[m]! = s := by
    have hl := getElem!_last_of_terminated h
    rwa [hm, Nat.add_sub_cancel] at hl
  rw [hm]
  conv_lhs => rw [List.range_succ_eq_map]
  conv_rhs => rw [List.range_succ]
  rw [List.countP_cons, List.countP_map, List.countP_append, List.countP_singleton]
  have hends : (Q (suffix t 0) && decide (t[(0 + (m + 1) - 1) % (m + 1)]! = c))
      = (decide (t[m]! = c) && Q (suffix t (m + 1))) := by
    rw [Nat.zero_add, Nat.add_sub_cancel, Nat.mod_eq_of_lt (by omega : m < m + 1), hlast]
    have hnil : suffix t (m + 1) = [] := by
      rw [suffix, List.drop_eq_nil_of_le (by omega)]
    by_cases hcs : c = s
    · rw [hnil, hwrap hcs, Bool.and_comm]
    · have hsc : ¬ s = c := fun hcon => hcs hcon.symm
      simp only [hsc, decide_false, Bool.and_false, Bool.false_and]
  have hmid : (List.range m).countP
      ((fun i => Q (suffix t i) && decide (t[(i + (m + 1) - 1) % (m + 1)]! = c)) ∘ Nat.succ)
      = (List.range m).countP (fun j => decide (t[j]! = c) && Q (suffix t (j + 1))) := by
    refine List.countP_congr (fun x hx => ?_)
    have hxm : x < m := List.mem_range.mp hx
    simp only [Function.comp_apply]
    rw [(by omega : Nat.succ x + (m + 1) - 1 = x + (m + 1)), Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : x < m + 1), Bool.and_comm]
  rw [hmid, hends]

/-- One narrowing step: the new endpoint is `cLess c` plus the `c`s the old endpoint passed. -/
private theorem cLess_add_occ (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (c : Nat)
    (Q R : List Nat → Bool) (hwrap : c = s → Q (suffix t 0) = Q [])
    (hdown : ∀ x y : List Nat, x ≤ y → Q y = true → Q x = true)
    (hcons : ∀ (a : Nat) (x : List Nat),
      R (a :: x) = (decide (a < c) || (decide (a = c) && Q x))) :
    cLess t c + occ (bwtOfSa t sa) c ((List.range t.length).countP (fun i => Q (suffix t i)))
      = (List.range t.length).countP (fun i => R (suffix t i)) := by
  have hmem : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (hsa.1.mem_iff.mp ha)
  have hsalen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  -- A row sits below the old endpoint exactly when its suffix satisfies `Q`.
  have hrow : ∀ y, y < sa.length → (y < (List.range t.length).countP (fun i => Q (suffix t i))
      ↔ Q (suffix t sa[y]!) = true) := by
    intro y hy
    have hlt : sa[y]! < t.length := by
      rw [getElem!_pos sa y hy]; exact hmem _ (List.getElem_mem hy)
    have hx := saPos_lt_countP_iff t Q hdown hlt
    rwa [saPos_eq_count t sa hsa y hy] at hx
  have hQtake : ∀ a ∈ sa.take ((List.range t.length).countP (fun i => Q (suffix t i))),
      Q (suffix t a) = true := by
    intro a ha
    obtain ⟨y, hyk, hylen, rfl⟩ := mem_take_row sa _ ha
    exact (hrow y hylen).mp hyk
  have hQdrop : ∀ a ∈ sa.drop ((List.range t.length).countP (fun i => Q (suffix t i))),
      Q (suffix t a) = false := by
    intro a ha
    obtain ⟨y, hyk, hylen, rfl⟩ := mem_drop_row sa _ ha
    by_contra hcon
    have := (hrow y hylen).mpr (by simpa using hcon)
    omega
  -- The occurrences of `c` the old endpoint passed, as a count over the array's own rows.
  have hocc : occ (bwtOfSa t sa) c ((List.range t.length).countP (fun i => Q (suffix t i)))
      = (List.range t.length).countP
        (fun i => Q (suffix t i) && decide (t[(i + t.length - 1) % t.length]! = c)) := by
    rw [occ, ← List.countP_eq_length_filter, bwtOfSa, ← List.map_take, List.countP_map]
    have hbeq : ((fun d => d == c) ∘ fun p => t[(p + t.length - 1) % t.length]!)
        = fun i => decide (t[(i + t.length - 1) % t.length]! = c) := by
      funext i; simp only [Function.comp_apply, Bool.beq_eq_decide_eq]
    rw [hbeq, ← hsa.1.countP_eq (fun i => Q (suffix t i)
      && decide (t[(i + t.length - 1) % t.length]! = c))]
    conv_rhs => rw [← List.take_append_drop
      ((List.range t.length).countP (fun i => Q (suffix t i))) sa]
    rw [List.countP_append]
    have h1 : (sa.take ((List.range t.length).countP (fun i => Q (suffix t i)))).countP
        (fun i => Q (suffix t i) && decide (t[(i + t.length - 1) % t.length]! = c))
        = (sa.take ((List.range t.length).countP (fun i => Q (suffix t i)))).countP
          (fun i => decide (t[(i + t.length - 1) % t.length]! = c)) :=
      List.countP_congr (fun x hx => by simp only [hQtake x hx, Bool.true_and])
    have h2 : (sa.drop ((List.range t.length).countP (fun i => Q (suffix t i)))).countP
        (fun i => Q (suffix t i) && decide (t[(i + t.length - 1) % t.length]! = c)) = 0 :=
      List.countP_eq_zero.mpr (fun x hx => by simp only [hQdrop x hx, Bool.false_and,
        Bool.false_eq_true, not_false_eq_true])
    rw [h1, h2, Nat.add_zero]
  -- The whole step: the C array, then the shift.
  rw [hocc, countP_shift t s h c Q hwrap, cLess, ← List.countP_eq_length_filter]
  refine (countP_split (fun x hx => ?_) (fun x hx hB => ?_)).symm
  · have hxn : x < t.length := List.mem_range.mp hx
    rw [suffix_eq_cons hxn, hcons]
  · simp only [decide_eq_true_eq] at hB
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact Or.inl (by omega)

/-! ### What the search returns -/

/-- Before any character is read, the interval is the empty pattern's block: every row. -/
private theorem block_nil (t : List Nat) :
    0 = lexBelow t [] ∧ t.length = lexBelow t [] + matchCount t [] := by
  have hbelow : lexBelow t [] = 0 := by
    simp only [lexBelow, List.length_eq_zero_iff]
    exact List.filter_eq_nil_iff.mpr (fun a _ => by
      simp only [decide_eq_true_eq, List.not_lt_nil, not_false_eq_true])
  have hocc : matchCount t [] = t.length := by
    rw [matchCount, List.filter_eq_self.mpr (fun a _ => by
      simp only [decide_eq_true_eq, List.nil_prefix]), List.length_range]
  exact ⟨hbelow.symm, by rw [hbelow, hocc, Nat.zero_add]⟩

/-- Reading `c` in front of `q` carries `q`'s block to `c :: q`'s. -/
private theorem block_step (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (c : Nat) (q : List Nat)
    (hs : s ∉ (c :: q).dropLast) {lo hi : Nat}
    (hv : lo = lexBelow t q ∧ hi = lexBelow t q + matchCount t q) :
    (backwardStep (bwtOfSa t sa) (cLess t) c lo hi).1 = lexBelow t (c :: q) ∧
      (backwardStep (bwtOfSa t sa) (cLess t) c lo hi).2
        = lexBelow t (c :: q) + matchCount t (c :: q) := by
  obtain ⟨rfl, rfl⟩ := hv
  -- The sentinel may be read only as the pattern's last character, and then `q` is empty.
  have hcs : c = s → q = [] := by
    intro hcon
    by_contra hq
    rw [List.dropLast_cons_of_ne_nil hq, hcon] at hs
    exact hs List.mem_cons_self
  -- The lower end: one more character read, one more step of the C array.
  have h1 : cLess t c + occ (bwtOfSa t sa) c (lexBelow t q) = lexBelow t (c :: q) := by
    have hx := cLess_add_occ t s h sa hsa c (fun x => decide (x < q))
      (fun x => decide (x < c :: q)) (fun hc => by rw [hcs hc]; simp)
      (down_lexBelow q) (fun a x => by
        simp only [List.cons_lt_cons_iff, Bool.decide_or, Bool.decide_and])
    rwa [← lexBelow_eq_countP, ← lexBelow_eq_countP] at hx
  -- The upper end: the same step, carried by the block instead of what lies under it.
  have h2 : cLess t c + occ (bwtOfSa t sa) c (lexBelow t q + matchCount t q)
      = lexBelow t (c :: q) + matchCount t (c :: q) := by
    have hx := cLess_add_occ t s h sa hsa c (fun x => decide (x < q ∨ q <+: x))
      (fun x => decide (x < c :: q ∨ c :: q <+: x)) (fun hc => by rw [hcs hc]; simp)
      (down_lexBelowOrPrefix q) (fun a x => ?_)
    · rwa [countP_below_or_prefix t q, countP_below_or_prefix t (c :: q)] at hx
    · have hiff : (a :: x < c :: q ∨ c :: q <+: a :: x)
          ↔ (a < c ∨ (a = c ∧ (x < q ∨ q <+: x))) := by
        rw [List.cons_lt_cons_iff, List.cons_prefix_cons]
        constructor
        · rintro ((hlt | ⟨rfl, hlt⟩) | ⟨rfl, hpre⟩)
          · exact Or.inl hlt
          · exact Or.inr ⟨rfl, Or.inl hlt⟩
          · exact Or.inr ⟨rfl, Or.inr hpre⟩
        · rintro (hlt | ⟨rfl, hlt | hpre⟩)
          · exact Or.inl (Or.inl hlt)
          · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
          · exact Or.inr ⟨rfl, hpre⟩
      simp only [hiff, Bool.decide_or, Bool.decide_and]
  exact ⟨h1, h2⟩

/-- Backward search returns `p`'s block: it starts at `lexBelow t p` and is `matchCount t p`
wide. -/
theorem backwardSearch_eq (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    ∀ p : List Nat, s ∉ p.dropLast →
      backwardSearch (bwtOfSa t sa) (cLess t) p
        = (lexBelow t p, lexBelow t p + matchCount t p) := by
  have hsalen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  intro p
  induction p with
  | nil =>
    intro _
    have hlen : (bwtOfSa t sa).length = t.length := by
      rw [bwtOfSa, List.length_map, hsalen]
    have hbelow : lexBelow t [] = 0 := by
      simp only [lexBelow, List.length_eq_zero_iff]
      exact List.filter_eq_nil_iff.mpr (fun a _ => by
        simp only [decide_eq_true_eq, List.not_lt_nil, not_false_eq_true])
    have hocc : matchCount t [] = t.length := by
      rw [matchCount, List.filter_eq_self.mpr (fun a _ => by
        simp only [decide_eq_true_eq, List.nil_prefix]), List.length_range]
    rw [backwardSearch, List.foldr_nil, hlen, hbelow, hocc, Nat.zero_add]
  | cons c q ih =>
    intro hs
    have hsq : s ∉ q.dropLast := by
      intro hcon
      by_cases hq : q = []
      · rw [hq] at hcon; exact List.not_mem_nil hcon
      · rw [List.dropLast_cons_of_ne_nil hq] at hs
        exact hs (List.mem_cons_of_mem _ hcon)
    have hv := block_step t s h sa hsa c q hs
      (lo := lexBelow t q) (hi := lexBelow t q + matchCount t q) ⟨rfl, rfl⟩
    rw [backwardSearch, List.foldr_cons]
    rw [show q.foldr (fun c acc => backwardStep (bwtOfSa t sa) (cLess t) c acc.1 acc.2)
        (0, (bwtOfSa t sa).length) = backwardSearch (bwtOfSa t sa) (cLess t) q from rfl,
      ih hsq]
    exact Prod.ext hv.1 hv.2

/-- On a suffix array, `p`'s block holds exactly the rows whose suffix begins with `p`. -/
theorem BackwardSearch.rows_of_block (t sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩)
    (p : List Nat) (lo hi : Nat) (hlo : lo = lexBelow t p)
    (hhi : hi = lexBelow t p + matchCount t p) (r : Nat) :
    (lo ≤ r ∧ r < hi) ↔ (r < sa.length ∧ p <+: suffix t sa[r]!) := by
  subst hlo hhi
  have hmem : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (hsa.1.mem_iff.mp ha)
  have hsalen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hpos : ∀ r, r < sa.length → sa[r]! < t.length := by
    intro r hr
    rw [getElem!_pos sa r hr]
    exact hmem _ (List.getElem_mem hr)
  have hwide : lexBelow t p + matchCount t p ≤ t.length := by
    have hle : (List.range t.length).countP
        (fun i => decide (suffix t i < p ∨ p <+: suffix t i))
        ≤ (List.range t.length).length := List.countP_le_length
    rwa [countP_below_or_prefix t p, List.length_range] at hle
  constructor
  · rintro ⟨hlo, hhi⟩
    have hr : r < sa.length := by omega
    have hcount := saPos_eq_count t sa hsa r hr
    have hU : decide (suffix t sa[r]! < p ∨ p <+: suffix t sa[r]!) = true := by
      refine (saPos_lt_countP_iff t (fun x => decide (x < p ∨ p <+: x))
        (down_lexBelowOrPrefix p) (hpos r hr)).mp ?_
      rw [hcount, countP_below_or_prefix t p]
      exact hhi
    have hL : ¬ (decide (suffix t sa[r]! < p) = true) := by
      intro hcon
      have hlt := (saPos_lt_countP_iff t (fun x => decide (x < p)) (down_lexBelow p)
        (hpos r hr)).mpr hcon
      rw [hcount, ← lexBelow_eq_countP] at hlt
      omega
    simp only [decide_eq_true_eq] at hU hL
    exact ⟨hr, hU.resolve_left hL⟩
  · rintro ⟨hr, hpre⟩
    have hcount := saPos_eq_count t sa hsa r hr
    have hUtrue : decide (suffix t sa[r]! < p ∨ p <+: suffix t sa[r]!) = true := by
      simp only [decide_eq_true_eq]
      exact Or.inr hpre
    have hU : r < lexBelow t p + matchCount t p := by
      have hlt := (saPos_lt_countP_iff t (fun x => decide (x < p ∨ p <+: x))
        (down_lexBelowOrPrefix p) (hpos r hr)).mpr hUtrue
      rwa [hcount, countP_below_or_prefix t p] at hlt
    refine ⟨?_, hU⟩
    by_contra hcon
    have hlt : saPos t sa[r]!
        < (List.range t.length).countP (fun i => decide (suffix t i < p)) := by
      rw [hcount, ← lexBelow_eq_countP]
      omega
    have hb := (saPos_lt_countP_iff t (fun x => decide (x < p)) (down_lexBelow p)
      (hpos r hr)).mp hlt
    simp only [decide_eq_true_eq] at hb
    exact absurd hpre.le (List.not_le.mpr hb)

/-- Box invariant 1: a row lies in the returned interval exactly when its suffix begins with the
pattern. -/
theorem backwardSearch_spec (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (p : List Nat) (hp : s ∉ p.dropLast)
    (r : Nat) :
    ((backwardSearch (bwtOfSa t sa) (cLess t) p).1 ≤ r
        ∧ r < (backwardSearch (bwtOfSa t sa) (cLess t) p).2)
      ↔ (r < sa.length ∧ p <+: suffix t sa[r]!) := by
  rw [backwardSearch_eq t s h sa hsa p hp]
  exact BackwardSearch.rows_of_block t sa hsa p _ _ rfl rfl r

/-- On a suffix array, `BackwardSearch.Valid` is the pair
`(lexBelow t q, lexBelow t q + matchCount t q)` for what has been read, `q`. -/
theorem BackwardSearch.valid_iff (s : BackwardSearch.Stretch)
    (hsa : SuffixArray.Valid s.index) :
    BackwardSearch.Valid s ↔ (s.lo = lexBelow s.index.text s.read ∧
      s.hi = lexBelow s.index.text s.read + matchCount s.index.text s.read) := by
  obtain ⟨⟨t, sa⟩, pat, q, lo, hi, hq⟩ := s
  constructor
  · rintro ⟨-, hlo, hhi⟩
    unfold BackwardSearch.StretchStartsRight at hlo
    unfold BackwardSearch.StretchAsWideAsMatches at hhi
    exact ⟨hlo, by rw [hhi, hlo]⟩
  · rintro ⟨hlo, hhi⟩
    refine ⟨fun r => ?_, hlo, ?_⟩
    · rw [BackwardSearch.rows_of_block t sa hsa q lo hi hlo hhi r]
      constructor
      · rintro ⟨hr, hp⟩
        exact ⟨hr, by rw [getElem!_pos sa r hr] at hp; exact hp⟩
      · rintro ⟨hr, hp⟩
        exact ⟨hr, by rw [getElem!_pos sa r hr]; exact hp⟩
    · unfold BackwardSearch.StretchAsWideAsMatches
      rw [hhi, hlo]

/-- `BackwardSearch.Valid` holds before any letter is read: every row. -/
theorem BackwardSearch.valid_nil (a : SuffixArray) (hsa : SuffixArray.Valid a) (p : List Nat) :
    BackwardSearch.Valid ⟨a, p, [], 0, a.text.length, List.nil_suffix⟩ :=
  (BackwardSearch.valid_iff _ hsa).mpr (block_nil a.text)

/-- One step keeps `BackwardSearch.Valid`: reading the letter `c` before what has been read. -/
theorem BackwardSearch.valid_step {s : BackwardSearch.Stretch} {z : Nat}
    (h : Terminated s.index.text z) (hsa : SuffixArray.Valid s.index) (c : Nat)
    (hc : c :: s.read <:+ s.pattern) (hz : z ∉ (c :: s.read).dropLast)
    (hv : BackwardSearch.Valid s) :
    BackwardSearch.Valid ⟨s.index, s.pattern, c :: s.read,
      (backwardStep (bwtOfSa s.index.text s.index.positions) (cLess s.index.text) c s.lo s.hi).1,
      (backwardStep (bwtOfSa s.index.text s.index.positions) (cLess s.index.text) c s.lo s.hi).2,
      hc⟩ :=
  (BackwardSearch.valid_iff ⟨s.index, s.pattern, c :: s.read, _, _, hc⟩ hsa).mpr
    (block_step s.index.text z h s.index.positions hsa c s.read hz
      ((BackwardSearch.valid_iff s hsa).mp hv))

/-- Backward search ends in `BackwardSearch.Valid` for the whole pattern. -/
theorem BackwardSearch.valid_backwardSearch {a : SuffixArray} {z : Nat} (h : Terminated a.text z)
    (hsa : SuffixArray.Valid a) (p : List Nat) (hp : z ∉ p.dropLast) :
    BackwardSearch.Valid ⟨a, p, p,
      (backwardSearch (bwtOfSa a.text a.positions) (cLess a.text) p).1,
      (backwardSearch (bwtOfSa a.text a.positions) (cLess a.text) p).2, List.suffix_refl p⟩ := by
  rw [BackwardSearch.valid_iff _ hsa, backwardSearch_eq a.text z h a.positions hsa p hp]
  exact ⟨rfl, rfl⟩

/-- The count is the number of occurrences. -/
theorem fmCount_eq (t : List Nat) (s : Nat) (h : Terminated t s) (p : List Nat)
    (hp : s ∉ p.dropLast) :
    fmCount t p = ((List.range t.length).filter (fun i => decide (p <+: suffix t i))).length := by
  have hsa := valid_suffixArray t
  change (backwardSearch (bwtOfSorted t) (cLess t) p).2
      - (backwardSearch (bwtOfSorted t) (cLess t) p).1 = _
  rw [← bwt_eq_rotations t s h (suffixArray t) hsa, backwardSearch_eq t s h _ hsa p hp]
  change lexBelow t p + matchCount t p - lexBelow t p = matchCount t p
  omega

/-- The reported positions are exactly the matchCount, in suffix order. -/
theorem fmLocate_perm (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (p : List Nat) (hp : s ∉ p.dropLast) :
    (fmLocate t sa p).Perm
      ((List.range t.length).filter (fun i => decide (p <+: suffix t i))) := by
  have hrow : ∀ y, y < sa.length →
      ((lexBelow t p ≤ y ∧ y < lexBelow t p + matchCount t p) ↔ p <+: suffix t sa[y]!) := by
    intro y hy
    have hx := backwardSearch_spec t s h sa hsa p hp y
    rw [backwardSearch_eq t s h sa hsa p hp] at hx
    exact ⟨fun hq => (hx.mp hq).2, fun hq => hx.mpr ⟨hy, hq⟩⟩
  -- The array's matching rows are a slice of it: the ones the interval names.
  have hslice : sa.filter (fun i => decide (p <+: suffix t i))
      = (sa.drop (lexBelow t p)).take (matchCount t p) := by
    have hsplit : sa.take (lexBelow t p)
        ++ ((sa.drop (lexBelow t p)).take (matchCount t p)
          ++ (sa.drop (lexBelow t p)).drop (matchCount t p)) = sa := by
      rw [List.take_append_drop, List.take_append_drop]
    conv_lhs => rw [← hsplit]
    rw [List.filter_append, List.filter_append]
    have h1 : (sa.take (lexBelow t p)).filter (fun i => decide (p <+: suffix t i)) = [] := by
      refine List.filter_eq_nil_iff.mpr (fun a ha => ?_)
      obtain ⟨y, hy1, hy2, rfl⟩ := mem_take_row sa _ ha
      simp only [decide_eq_true_eq]
      exact fun hcon => absurd ((hrow y hy2).mpr hcon).1 (by omega)
    have h2 : ((sa.drop (lexBelow t p)).take (matchCount t p)).filter
        (fun i => decide (p <+: suffix t i))
        = (sa.drop (lexBelow t p)).take (matchCount t p) := by
      refine List.filter_eq_self.mpr (fun a ha => ?_)
      obtain ⟨y, hy1, hy2, hy3, rfl⟩ := mem_slice_row sa _ _ ha
      simp only [decide_eq_true_eq]
      exact (hrow y hy3).mp ⟨hy1, hy2⟩
    have h3 : ((sa.drop (lexBelow t p)).drop (matchCount t p)).filter
        (fun i => decide (p <+: suffix t i)) = [] := by
      rw [List.drop_drop]
      refine List.filter_eq_nil_iff.mpr (fun a ha => ?_)
      obtain ⟨y, hy1, hy2, rfl⟩ := mem_drop_row sa _ ha
      simp only [decide_eq_true_eq]
      exact fun hcon => absurd ((hrow y hy2).mpr hcon).2 (by omega)
    rw [h1, h2, h3, List.nil_append, List.append_nil]
  change ((sa.drop (backwardSearch (bwtOfSa t sa) (cLess t) p).1).take
      ((backwardSearch (bwtOfSa t sa) (cLess t) p).2
        - (backwardSearch (bwtOfSa t sa) (cLess t) p).1)).Perm _
  rw [backwardSearch_eq t s h sa hsa p hp]
  change ((sa.drop (lexBelow t p)).take
    (lexBelow t p + matchCount t p - lexBelow t p)).Perm _
  rw [Nat.add_sub_cancel_left, ← hslice]
  exact hsa.1.filter _

/-- Extraction: walk `lf` from row `r` for `len` steps reading the last column, and reverse. The
sampled start rule is `extractSampledM`. -/
def fmExtract (bwt : List Nat) (r len : Nat) : List Nat :=
  (lfWalk bwt len r).reverse

/-- From the row of position `(from + len) mod n`, `fmExtract` returns `t[from, from + len)`. -/
theorem fmExtract_eq (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (f len : Nat) (hfl : f + len ≤ t.length)
    (r : Nat) (hr : r < sa.length) (hrow : sa[r]! = (f + len) % t.length) :
    fmExtract (bwtOfSa t sa) r len = (t.drop f).take len := by
  have hpos : saPos t ((f + len) % t.length) = r := by
    rw [← hrow]; exact saPos_eq_count t sa hsa r hr
  rw [fmExtract, ← hpos, lfWalk_slice t s h sa hsa f len hfl, List.reverse_reverse]

/-- The same over `bwtOfSorted`. -/
theorem fmExtract_bwtOfSorted (t : List Nat) (s : Nat) (h : Terminated t s) (f len : Nat)
    (hfl : f + len ≤ t.length) :
    fmExtract (bwtOfSorted t) (saPos t ((f + len) % t.length)) len = (t.drop f).take len := by
  have hsa := valid_suffixArray t
  rw [← bwt_eq_rotations t s h (suffixArray t) hsa, fmExtract,
    lfWalk_slice t s h _ hsa f len hfl, List.reverse_reverse]

end AlgoDesign.Strings
