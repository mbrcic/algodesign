/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.BWT.Rotations

/-!
# Burrows–Wheeler transform: deciding the assumption and the invariant pieces

`Terminated`, the invariant pieces and `Valid`, decided on concrete lists; invariant 2 through the
library's suffix array, the only one a text has (`BWT.letterBeforeEachSuffix_iff`).
-/

@[expose] public section

namespace AlgoDesign.Strings

instance decidableTerminated (t : List Nat) (s : Nat) : Decidable (Terminated t s) :=
  by unfold Terminated; infer_instance

namespace BWT

instance (x : Transform) : Decidable (SameLetters x) :=
  by unfold SameLetters; infer_instance

instance (x : Transform) : Decidable (SentinelOnce x) :=
  by unfold SentinelOnce; infer_instance

instance decidableLetterBeforeEachSuffix (x : Transform) :
    Decidable (LetterBeforeEachSuffix x) :=
  decidable_of_iff _ (letterBeforeEachSuffix_iff x).symm

instance decidableValid (x : Transform) : Decidable (Valid x) :=
  inferInstanceAs (Decidable
    (SameLetters x ∧ LetterBeforeEachSuffix x ∧ SentinelOnce x))

end BWT

end AlgoDesign.Strings
