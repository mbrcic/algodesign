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
  Valid := FMIndex.Valid

/-- The library's operations at the interval `sample`, as the boxes name them; `countM` and
`locateM` are their counting. -/
def ops (sample : Nat) : Ops where
  build u := build (u ++ [0]) sample
  search := locate
  Valid := FMIndex.Valid
  count := count
  countM := countM
  locateM := locateM
  counted ix p := ⟨ret_countM ix p, ret_locateM ix p⟩

/-- The build keeps every `sample`-th position: the index it builds has the interval asked for. -/
theorem build_sample (sample : Nat) (u : List Nat) : ((ops sample).build u).sample = sample := rfl

/-- The occurrence finder the library's operations make is `finder sample`. -/
theorem finder_ops (sample : Nat) : (ops sample).finder = finder sample := rfl

/-- **Promise:** the occurrence promise, on every text of bytes without `$`. -/
theorem promise {k : Nat} (hk : 0 < k) : (finder k).Promise PositiveBytes :=
  Occurrences.Promise.of_perm
    (fun u hu => valid_build (terminated_append hu)
      (fun x hx => by
        rcases List.mem_append.1 hx with hx | hx
        · exact (hu x hx).2
        · simp at hx; omega)
      (valid_suffixArray _) hk)
    (fun u hu => by
      change (invertBwt (build (u ++ [0]) k).bwt).dropLast = u
      rw [invertBwt_build (terminated_append hu)]
      simp)
    (fun _ hv p => locate_perm_of_valid hv p)

/-- **The library's FM-index meets its contract** (`Contract` in `FMIndex/Spec.lean`), at every
positive interval. -/
theorem contract {k : Nat} (hk : 0 < k) : Contract (ops k) where
  promise := ⟨fun _ hv p => count_of_valid hv p, promise hk⟩
  invariants _ := Iff.rfl
  cost := ⟨fun ix _ p => time_countM_le ix p, fun _ hv p => time_locateM_le hv p⟩

end FMIndex

end AlgoDesign.Strings
