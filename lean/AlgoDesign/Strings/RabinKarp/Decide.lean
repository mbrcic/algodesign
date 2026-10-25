/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RabinKarp.Spec

/-!
# Rabin–Karp: deciding the scan's state

The scan's invariant pieces and `Valid`, decided on a concrete state.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace RabinKarp

instance (s : Scan) : Decidable (NumberMatchesWindow s) :=
  inferInstanceAs
    (Decidable (s.number = fingerprint s.base s.modulus (s.rest.take s.pattern.length)))

instance (s : Scan) : Decidable (FoundSoFarExact s) :=
  by unfold FoundSoFarExact; infer_instance

instance (s : Scan) : Decidable (Valid s) :=
  by unfold Valid; infer_instance

end RabinKarp

end AlgoDesign.Strings
