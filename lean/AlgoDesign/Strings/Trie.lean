/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Spec
public import AlgoDesign.Strings.Trie.Basic
public import AlgoDesign.Strings.Trie.Insert
public import AlgoDesign.Strings.Trie.Remove
public import AlgoDesign.Strings.Trie.Cost
public import AlgoDesign.Strings.Trie.Query

/-! The trie. Its contract is in `Trie/Spec.lean`; this file imports the whole structure. -/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

/-! ## The library's trie meets its contract

`Contract` in `Trie/Spec.lean` is the part of the contract that Lean checks; this proves the
library's operations meet it, from the theorems the files above prove. -/

/-- The trie as a word map: its operations, and its invariant as `Valid`. -/
def wordMap {α : Type} : WordMap α (Trie α) where
  empty := empty
  insert w a t := insert t w a
  remove w t := remove t w
  get w t := get t w
  keysWithPrefix p t := keysWithPrefix t p
  Valid := Valid

/-- **Promise:** the trie's. -/
theorem promise {α : Type} : (wordMap : WordMap α (Trie α)).Promise where
  get_empty w := by cases w <;> rfl
  insert_stores w a t _ := get_insert t w a
  remove_deletes w t h := get_remove t h.1 w
  others_unchanged _ _ t h hv := ⟨fun a => get_insert_other t hv a, get_remove_other t h.1 hv⟩
  lists_prefix p t h := WordMap.lists_prefix_of_words words p (fun w => mem_words_iff w t h.1)
    (keysWithPrefix_perm t h.1 p) (keysWithPrefix_sorted t h.1 p)

/-- The library's operations, as the box names them; `getM`, `insertM` and `removeM` are their
counting. -/
def ops {α : Type} : Ops α where
  empty := empty
  insert w a t := insert t w a
  remove w t := remove t w
  keysWithPrefix p t := keysWithPrefix t p
  Valid := Valid
  getM w t := getM t w
  insertM w a t := insertM t w a
  removeM w t := removeM t w
  counted w t := ⟨ret_getM t w, fun a => ret_insertM t w a, ret_removeM t w⟩
  emptyValid := valid_empty
  insertKeeps w a _ h := valid_insert w a h
  removeKeeps w _ h := valid_remove w h

/-- The word map the library's operations make is `wordMap`. -/
theorem wordMap_ops {α : Type} : (ops : Ops α).wordMap = wordMap := rfl

/-- **The library's trie meets its contract** (`Contract` in `Trie/Spec.lean`). -/
theorem contract {α : Type} : Contract (ops : Ops α) where
  promise := promise
  invariants _ := Iff.rfl
  cost := ⟨fun w t => time_getM_le t w, fun w a t => (time_insertM t w a).le,
    fun w t => time_removeM_le t w, fun t h => nodeCount_le t h⟩

end Trie

end AlgoDesign.Strings
