/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Spec
public import AlgoDesign.Searching.LSM.Decide
public import AlgoDesign.Searching.LSM.Merge
public import AlgoDesign.Searching.LSM.Write
public import AlgoDesign.Searching.LSM.Compact
public import AlgoDesign.Searching.LSM.Flush
public import AlgoDesign.Searching.LSM.Invariant
public import AlgoDesign.Searching.LSM.Cost

/-! The LSM-tree. Its contract is in `LSM/Spec.lean`; this file imports
the whole structure. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace LSM

variable {α β : Type} [LinearOrder α]

/-! ## The library's LSM-tree meets its contract

`Contract` in `LSM/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The library's operations, as the box names them; `Store.getM` is its counting. Write and
delete are one `Store.write`, with a value or a tombstone. -/
def ops : Ops α β where
  empty := Store.empty
  write a b s := Store.write a (some b) s
  delete := Store.delete
  Valid := Store.Valid
  getM := Store.getM
  counted := Store.ret_getM

/-- The library's operations read with `Store.get`. -/
theorem get_ops : (ops : Ops α β).get = Store.get := rfl

/-- **The library's LSM-tree meets its contract** (`Contract` in `LSM/Spec.lean`). The cost of a
write, `WriteRewrites`, is argued, not proved. -/
theorem contract : Contract (ops : Ops α β) where
  promise :=
    ⟨⟨fun a b _ h => Store.get_write_self h.1 h.2.1.1 a (some b),
      fun _ _ _ _ h hca => Store.get_write_other h.1 h.2.1.1 (Ne.symm hca) _⟩,
     ⟨fun a _ h => Store.get_delete_self h.1 h.2.1.1 a,
      fun _ _ _ h hca => Store.get_delete_other h.1 h.2.1.1 (Ne.symm hca)⟩,
     fun sh a => Store.get_empty sh a,
     ⟨fun _ hsh => Store.valid_empty hsh,
      fun a b _ h => Store.valid_write h a (some b),
      fun a _ h => Store.valid_delete h a⟩⟩
  invariants _ := Iff.rfl
  cost a _ h := Store.time_getM_le h.2.1.1 a

end LSM

end AlgoDesign.Searching
