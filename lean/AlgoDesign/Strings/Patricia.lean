/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Spec
public import AlgoDesign.Strings.Patricia.Basic
public import AlgoDesign.Strings.Patricia.Compress
public import AlgoDesign.Strings.Patricia.Insert
public import AlgoDesign.Strings.Patricia.Build
public import AlgoDesign.Strings.Patricia.Sorted
public import AlgoDesign.Strings.Patricia.Remove
public import AlgoDesign.Strings.Patricia.Cost
public import AlgoDesign.Strings.Patricia.Query
public import AlgoDesign.Strings.Patricia.Decide

/-! The Patricia tree. Its contract is in `Patricia/Spec.lean`; this file imports the whole
structure. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ## The library's Patricia tree meets its contract

`Contract` in `Patricia/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The Patricia tree as a word map: its operations, and its invariant as `Valid`.

Implementer choice: the map's insert is `insert`, not the Rust's `insertSorted`. `insert` keeps
`Valid` and meets `InsertSpec` on every tree; `insertSorted` needs sorted children (`SortedHeads`),
which the box does not ask for, so taking it would add an invariant the box lacks. The two build
the same tree up to child order (`sortTree_insert`), which `get` does not see (`get_sortTree`);
the Python's insert, like `insert`, keeps no child order. -/
def wordMap {α : Type} : WordMap α (Patricia α) where
  empty := empty
  insert w a t := insert t w a
  remove w t := remove t w
  get w t := get t w
  keysWithPrefix p t := keysWithPrefix t p
  Valid := Valid

/-- **Promise:** the trie's. -/
theorem promise {α : Type} : (wordMap : WordMap α (Patricia α)).Promise where
  valid_empty := valid_empty
  get_empty w := by cases w <;> rfl
  valid_insert w a _ h := valid_insert w a h
  valid_remove w _ h := valid_remove w h
  insert_stores w a t _ := get_insert t w a
  remove_deletes w _ h := get_remove_of_valid h w
  others_unchanged w v t h hv :=
    ⟨fun a => get_insert_other t w v hv a,
      get_remove_other t h.noEmptyBranches h.distinctFirstLetters hv⟩
  lists_prefix p t h := WordMap.lists_prefix_of_words words p
    (mem_words_iff t h.noEmptyBranches h.distinctFirstLetters) (keysWithPrefix_perm t h p)
    (keysWithPrefix_sorted t h p)

/-- The library's operations, as the box names them; `getM` is its counting. -/
def ops {α : Type} : Ops α where
  empty := empty
  insert w a t := insert t w a
  remove w t := remove t w
  keysWithPrefix p t := keysWithPrefix t p
  Valid := Valid
  getM w t := getM t w
  counted w t := ret_getM t w

/-- The word map the library's operations make is `wordMap`. -/
theorem wordMap_ops {α : Type} : (ops : Ops α).wordMap = wordMap := rfl

/-- **The library's Patricia tree meets its contract** (`Contract` in `Patricia/Spec.lean`). -/
theorem contract {α : Type} : Contract (ops : Ops α) where
  promise := promise
  invariants _ := Iff.rfl
  cost := ⟨fun t h hne => nodeCount_le t h hne, fun w t => time_getM_le t w⟩

end Patricia

end AlgoDesign.Strings
