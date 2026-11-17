/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.SuffixArray.Spec
public import AlgoDesign.Strings.SuffixArray.Decide
public import AlgoDesign.Strings.SuffixArray.Basic
public import AlgoDesign.Strings.SuffixArray.Build
public import AlgoDesign.Strings.SuffixArray.Search
public import AlgoDesign.Strings.SuffixArray.LCP

/-! The suffix array. Its contract is in `SuffixArray/Spec.lean`; this file imports the whole
structure. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace SuffixArray

/-! ## The library's suffix array meets its contract

`Contract` in `SuffixArray/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The suffix array as an occurrence finder: build by prefix doubling, search by two binary
searches, and the box's two invariants. -/
def finder : Occurrences SuffixArray where
  build t := ⟨t, suffixArray t⟩
  text a := a.text
  search a p := search a.text a.positions p
  Valid := Valid

/-- On a suffix array, the positions with the text's end in front repeat nothing: the end is not a
stored position, and each stored position appears once. -/
theorem nodup_length_cons {t sa : List Nat} (h : Valid ⟨t, sa⟩) : (t.length :: sa).Nodup := by
  refine List.nodup_cons.2 ⟨fun hm => ?_, h.1.nodup_iff.2 List.nodup_range⟩
  have := List.mem_range.1 (h.1.mem_iff.1 hm)
  dsimp only at this
  omega

/-- **Promise:** the occurrence promise, on every text. -/
theorem promise : finder.Promise :=
  Occurrences.Promise.of_mem_iff (fun a h p i => mem_search_iff h p i)
    (fun a h p => by
      change (search a.text a.positions p).Nodup
      rw [search_eq_filter h]
      exact (nodup_length_cons h).filter _)

/-- The library's operations, as the box names them; `searchM` is its counting. -/
def ops : Ops where
  build t := ⟨t, suffixArray t⟩
  search a p := search a.text a.positions p
  Valid := Valid
  searchM a p := searchM a.text a.positions p
  counted a p := ret_searchM a.text a.positions p
  buildValid t := valid_suffixArray t
  buildStores _ := rfl

/-- The occurrence finder the library's operations make is `finder`. -/
theorem finder_ops : ops.finder = finder := rfl

/-- **The library's suffix array meets its contract** (`Contract` in `SuffixArray/Spec.lean`). -/
theorem contract : Contract ops where
  promise := promise
  invariants _ := Iff.rfl
  cost := ⟨fun _ h => by simpa using h.1.length_eq,
    fun a _ p => time_searchM_le a.text a.positions p⟩

end SuffixArray

end AlgoDesign.Strings
