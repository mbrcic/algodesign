/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.SuffixArray.Spec

/-!
# Suffix array: deciding the invariant

The invariant pieces and `Valid`, decided on a concrete array.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace SuffixArray

instance decidableEachPositionOnce (a : SuffixArray) : Decidable (EachPositionOnce a) :=
  by unfold EachPositionOnce; infer_instance

instance decidableSuffixesSorted (a : SuffixArray) : Decidable (SuffixesSorted a) :=
  by unfold SuffixesSorted; infer_instance

instance decidableValid (a : SuffixArray) : Decidable (Valid a) :=
  by unfold Valid; infer_instance

end SuffixArray

end AlgoDesign.Strings
