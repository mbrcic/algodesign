/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.RankSelect.Basic
public import AlgoDesign.Strings.Records.Spec

/-!
# A hit's record contains the hit

`recordOf` turns a text position into a record number with `rank`; `recordBounds` turns the number
back into an interval with `select`. `recordBounds_contains`: the interval contains the position,
when a record starts at position 0 (`hstart`). The lower bound needs only `hstart`, the upper only
`hi`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- The record position `i` falls in: one less than the number of starts at or before `i`. -/
def recordOf (b : List Bool) (i : Nat) : Nat := rank b (i + 1) - 1

/-- The half-open bounds `[start, end)` of record `id`: the `id`-th start, and the next one or the
end of the text. -/
def recordBounds (b : List Bool) (id : Nat) : Nat × Nat :=
  ((select b id).getD 0, (select b (id + 1)).getD b.length)

/-- A vector whose first bit is set has at least one start at or before every position. -/
theorem rank_pos_of_head (b : List Bool) (i : Nat) (hstart : b[0]! = true) :
    0 < rank b (i + 1) := by
  cases b with
  | nil => simp at hstart
  | cons x t =>
      have hx : x = true := by simpa [getElem!_def] using hstart
      subst hx
      simp [rank, List.take_succ_cons]

/-- The record a hit belongs to starts at or before the hit. Without `hstart`, `recordOf`'s
truncating subtraction hands positions before the first start to record 0. -/
theorem lower_le_of_recordOf (b : List Bool) (i : Nat) (hstart : b[0]! = true) :
    (recordBounds b (recordOf b i)).1 ≤ i := by
  have hpos := rank_pos_of_head b i hstart
  simp only [recordBounds]
  cases hs : select b (recordOf b i) with
  | none => simp
  | some p =>
      simp only [Option.getD_some]
      by_contra hlt
      have hmono : rank b (i + 1) ≤ rank b p := rank_mono b (by omega)
      have hrp : rank b p = recordOf b i := (rank_select b _ p hs).2
      simp only [recordOf] at hrp
      omega

/-- The record a hit belongs to ends after the hit. -/
theorem lt_snd_of_recordOf (b : List Bool) (i : Nat) (hi : i < b.length) :
    i < (recordBounds b (recordOf b i)).2 := by
  simp only [recordBounds]
  cases hs : select b (recordOf b i + 1) with
  | none => simpa using hi
  | some p =>
      simp only [Option.getD_some]
      by_contra hle
      have hmono : rank b (p + 1) ≤ rank b (i + 1) := rank_mono b (by omega)
      have hp := rank_select b _ p hs
      have hstep : rank b (p + 1) = rank b p + 1 := by rw [rank_succ b p, hp.1]; simp
      have hrp := hp.2
      simp only [recordOf] at hrp
      omega

/-- The record a hit names contains the hit, whichever part of the quote was found. -/
theorem recordBounds_contains (b : List Bool) (i : Nat) (hi : i < b.length)
    (hstart : b[0]! = true) :
    (recordBounds b (recordOf b i)).1 ≤ i ∧ i < (recordBounds b (recordOf b i)).2 :=
  ⟨lower_le_of_recordOf b i hstart, lt_snd_of_recordOf b i hi⟩

/-- `recordBounds_contains` under `FirstRecordAtStart` and at least one start. -/
theorem recordBounds_contains_of_firstRecordAtStart (b : List Bool) (i : Nat) (hi : i < b.length)
    (hv : Records.FirstRecordAtStart b) (hany : true ∈ b) :
    (recordBounds b (recordOf b i)).1 ≤ i ∧ i < (recordBounds b (recordOf b i)).2 :=
  recordBounds_contains b i hi (by
    cases b with
    | nil => simp at hany
    | cons x xs => simpa using hv hany)

/-- `rank` does not move across a stretch with no set bit in it. -/
theorem rank_eq_of_no_set_between (b : List Bool) (i j : Nat) (hij : i ≤ j)
    (h : ∀ k, i < k → k ≤ j → b[k]! = false) : rank b (j + 1) = rank b (i + 1) := by
  induction j with
  | zero => have hi0 : i = 0 := Nat.le_zero.mp hij; subst hi0; rfl
  | succ n ih =>
      rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · have hf : b[n + 1]! = false := h (n + 1) hlt (by omega)
        rw [rank_succ b (n + 1), hf]
        simpa using ih (by omega) fun k hk1 hk2 => h k hk1 (by omega)
      · have hie : i = n + 1 := by omega
        subst hie; rfl

/-- Two hits inside one record name the same quote. -/
theorem recordOf_eq_of_no_start_between (b : List Bool) (i j : Nat) (hij : i ≤ j)
    (h : ∀ k, i < k → k ≤ j → b[k]! = false) :
    recordOf b j = recordOf b i := by
  simp only [recordOf, rank_eq_of_no_set_between b i j hij h]

end AlgoDesign.Strings
