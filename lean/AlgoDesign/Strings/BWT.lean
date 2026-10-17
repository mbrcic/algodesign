/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.BWT.Spec
public import AlgoDesign.Strings.BWT.Decide
public import AlgoDesign.Strings.BWT.Rotations
public import AlgoDesign.Strings.BWT.Invert

/-! The Burrows–Wheeler transform. Its contract is in `BWT/Spec.lean`; this file imports the whole
structure. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace BWT

/-! ## The library's transform meets its contract

`Contract` in `BWT/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The library's operations, as the box names them: the transform over the library's suffix
array, the inverse walk, and the suffixes read off the walk. -/
def ops : Ops := ⟨fun t => bwtOfSa t (suffixArray t), invertBwt, saOf, Valid⟩

/-- On a valid transform, the stored letters are the transform through the library's suffix
array. -/
theorem letters_eq {x : Transform} (hv : Valid x) :
    x.letters = bwtOfSa x.text (suffixArray x.text) :=
  (BWT.letterBeforeEachSuffix_iff x).1 hv.2.1

/-- **The library's Burrows–Wheeler transform meets its contract** (`Contract` in
`BWT/Spec.lean`). -/
theorem contract : Contract ops where
  promise := by
    refine ⟨fun x hv h => ?_, fun x hv h => ?_,
      fun t h => valid_bwtOfSa t h _ (valid_suffixArray t)⟩
    · change invertBwt x.letters = x.text
      rw [letters_eq hv, bwt_eq_rotations _ 0 h _ (valid_suffixArray _), invertBwt_bwt _ 0 h]
    · change SuffixArray.Valid ⟨x.text, saOf x.letters⟩
      rw [letters_eq hv, saOf_bwtOfSa h (valid_suffixArray _)]
      exact valid_suffixArray _
  invariants _ := Iff.rfl
  cost t := by
    change (bwtOfSa t (suffixArray t)).length = t.length
    rw [length_bwtOfSa, (valid_suffixArray t).1.length_eq, List.length_range]

end BWT

end AlgoDesign.Strings
