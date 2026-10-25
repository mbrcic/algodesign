/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.FMIndex.Spec
public import AlgoDesign.Strings.FMIndex.Decide
public import AlgoDesign.Strings.FMIndex.Search
public import AlgoDesign.Strings.FMIndex.Cost
public import AlgoDesign.Strings.FMIndex.Sampled
public import AlgoDesign.Strings.FMIndex.Alphabet
public import AlgoDesign.Strings.FMIndex.Parts
public import AlgoDesign.Strings.FMIndex.Sufficient

/-! The FM-index. Its contract is in `FMIndex/Spec.lean`; this file imports the whole structure. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace FMIndex

/-! ## The library's FM-index meets its contract

`Contract` in `FMIndex/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- A text of bytes without `$`, with its `$` appended, ends with one `$`. -/
theorem terminated_append {u : List Nat} (hu : PositiveBytes u) : Terminated (u ++ [0]) 0 :=
  ⟨by simp, fun c hc => (hu c (by simpa using hc)).1⟩

/-- The build indexes the text it is given: its column rebuilds that text with its `$`. -/
theorem invertBwt_build {t : List Nat} (h : Terminated t 0) (k : Nat) :
    invertBwt (build t k).bwt = t := by
  change invertBwt (bwtOfSa t (suffixArray t)) = t
  rw [bwt_eq_rotations t 0 h _ (valid_suffixArray t), invertBwt_bwt t 0 h]

/-- The FM-index as an occurrence finder, at the interval `sample`: build over the text with its `$`
appended, answer about the text without it, search by locate, and the invariant. -/
def finder (sample : Nat) : Occurrences FMIndex where
  build u := build (u ++ [0]) sample
  text := FMIndex.text
  search := locate
  Valid ix := ix.Valid ∧ ix.WellFormed

/-- Every text of bytes without `$` builds a valid, well-formed index, at an interval above one. -/
theorem valid_build_of_positiveBytes {k : Nat} (hk : 2 ≤ k) {u : List Nat}
    (hu : PositiveBytes u) :
    FMIndex.Valid (build (u ++ [0]) k) ∧ FMIndex.WellFormed (build (u ++ [0]) k) :=
  valid_build (terminated_append hu)
    (fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact (hu x hx).2
      · simp at hx; omega)
    (valid_suffixArray _) hk

/-- The index built from a text of bytes without `$` answers about that text. -/
theorem text_build_of_positiveBytes (k : Nat) {u : List Nat} (hu : PositiveBytes u) :
    (build (u ++ [0]) k).text = u := by
  change (invertBwt (build (u ++ [0]) k).bwt).dropLast = u
  rw [invertBwt_build (terminated_append hu)]
  simp

/-- The library's operations at the interval `sample`, above one, as the boxes name them; `countM`
and `locateM` are their counting. -/
def ops (sample : Nat) (hk : 2 ≤ sample) : Ops where
  build u := build (u ++ [0]) sample
  search := locate
  Valid := FMIndex.Valid
  count := count
  countM := countM
  locateM := locateM
  counted ix p := ⟨ret_countM ix p, ret_locateM ix p⟩
  buildValid _ hu := (valid_build_of_positiveBytes hk hu).1
  buildWellFormed _ hu := (valid_build_of_positiveBytes hk hu).2
  buildStores _ hu := text_build_of_positiveBytes sample hu

/-- The build keeps every `sample`-th position: the index it builds has the interval asked for. -/
theorem build_sample (sample : Nat) (hk : 2 ≤ sample) (u : List Nat) :
    ((ops sample hk).build u).sample = sample := rfl

/-- The occurrence finder the library's operations make is `finder sample`. -/
theorem finder_ops (sample : Nat) (hk : 2 ≤ sample) : (ops sample hk).finder = finder sample :=
  rfl

/-- **Promise:** the occurrence promise, on every valid, well-formed index. -/
theorem promise (k : Nat) : (finder k).Promise :=
  Occurrences.Promise.of_perm fun _ hv p => locate_perm_of_valid hv p

/-- **The library's FM-index meets its contract** (`Contract` in `FMIndex/Spec.lean`), at every
interval above one. -/
theorem contract {k : Nat} (hk : 2 ≤ k) : Contract (ops k hk) where
  promise := ⟨fun _ hv hw p => count_of_valid ⟨hv, hw⟩ p, promise k⟩
  invariants _ := Iff.rfl
  cost := ⟨fun ix _ _ p => time_countM_le ix p, fun _ hv hw p => time_locateM_le ⟨hv, hw⟩ p⟩

end FMIndex

end AlgoDesign.Strings
