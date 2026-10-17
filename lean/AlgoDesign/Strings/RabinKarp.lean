/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RabinKarp.Spec
public import AlgoDesign.Strings.RabinKarp.Decide
public import AlgoDesign.Strings.RabinKarp.Search
public import AlgoDesign.Strings.RabinKarp.Cost
public import AlgoDesign.Strings.RabinKarp.Collision
public import AlgoDesign.Strings.RabinKarp.Expected

/-! Rabin–Karp. Its contract is in `RabinKarp/Spec.lean`; this file imports the whole algorithm. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace RabinKarp

/-! ## The library's Rabin–Karp meets its contract

`Contract` in `RabinKarp/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, for every base and every positive modulus, from the theorems the
files above prove. -/

/-- Rabin–Karp as an occurrence finder, in radix `base` modulo `q`: it prepares nothing (its value
is the text), and keeps no invariant between searches. -/
def finder (base q : Nat) : Occurrences (List Nat) where
  build t := t
  text t := t
  search t p := rabinKarpSearch base q t p
  Valid _ := True

/-- **Promise:** the occurrence promise, on every text. -/
theorem promise (base : Nat) {q : Nat} (hq : 0 < q) : (finder base q).Promise (fun _ => True) :=
  Occurrences.Promise.of_perm (fun _ _ => trivial) (fun _ _ => rfl) fun s _ p =>
    (rabinKarpSearch_eq_occurrenceList base hq s p).symm ▸ List.Perm.refl _

/-- The library's operations, as the box names them; `rabinKarpSearchM` is its counting. -/
def ops (base q : Nat) : Ops where
  base := base
  modulus := q
  finder := finder base q
  Valid := Valid
  searchM := rabinKarpSearchM base q
  counted := ret_rabinKarpSearchM base q

/-- **The library's Rabin–Karp meets its contract** (`Contract` in `RabinKarp/Spec.lean`), for every
base and every positive modulus. -/
theorem contract (base : Nat) {q : Nat} (hq : 0 < q) : Contract (ops base q) where
  promise := promise base hq
  invariants _ := Iff.rfl
  cost s p := by
    change (rabinKarpSearchM base q s p).time ≤
      (s.length + 1 - p.length) + p.length * candidateCount base q s p
    by_cases hp : p = []
    · simp [rabinKarpSearchM, hp]
    by_cases hlen : s.length < p.length
    · simp [rabinKarpSearchM, hp, hlen]
    exact (time_rabinKarpSearchM base hq s p hp (by omega)).le

end RabinKarp

end AlgoDesign.Strings
