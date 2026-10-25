/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.WordMap

/-!
# Trie: the specification

Sources: the Strings chapter, "I remember how it starts"; Sedgewick and Wayne, *Algorithms*
(4th ed.), §5.2.

> **Goal:** look up words in a large dictionary.
>
> **Promise:** a map from words to values. Get gives a word's stored value, or nothing. Insert
> stores or replaces one word's value; remove deletes it. Other words stay unchanged. Every word
> that starts with a given prefix can be listed.
>
> **Idea:** tie common **prefixes**, the beginnings words share, together, so they are checked
> once for all the words that share them.
>
> **Invariants:**
>
> 1. A word is a path of letters from one common starting point to a mark that says it ends
>    there.
> 2. Paths leaving the same point carry different letters.
> 3. Every branch leads to a stored word.
>
> **Cost:** each operation grows with its word, not with the dictionary; memory, up to a node per
> letter stored.

The box, field by field. Read `Contract`, at the end of this file; `Trie.contract` proves the
library meets it.

- Goal [required] → `WordMap`: empty, insert, remove, get and the prefix listing.
- Promise [proved] → `WordMap.Promise`, the trie's.
- Idea [mentioned] → tie common prefixes together.
- Invariants [proved] →
  1 [required] the meaning of `get`: a word is found by following its letters from the root to a
    node carrying a value.
  2 [proved] `DistinctLetters`.
  3 [proved] `NoDeadBranches`.
  Not in the box: the empty map is valid, `Ops.emptyValid`, and insert and remove keep it,
  `Ops.insertKeeps` and `Ops.removeKeeps`.
- Cost [proved] → child steps for get, insert and remove; nodes for memory (`nodeCount`).
- Assumes [none] → the box assumes nothing.

Words: word = `List Nat`; letter = `Nat`; the mark that a word ends = a node's value.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- A trie over `Nat` symbols. A node carries an optional value and an association list of
children: **the key is the path**, so no node stores a symbol of its own. -/
inductive Trie (α : Type) where
  | node (value : Option α) (children : List (Nat × Trie α))

namespace Trie

/-- The trie holding nothing. -/
def empty {α : Type} : Trie α := .node none []

mutual

/-- The words stored, as paths from the root to nodes carrying a value. -/
def words {α : Type} : Trie α → List (List Nat)
  | .node v cs =>
      (match v with | some _ => [([] : List Nat)] | none => []) ++ wordsAux cs

/-- The words of a child list, each prefixed with the symbol its subtrie is filed under. -/
def wordsAux {α : Type} : List (Nat × Trie α) → List (List Nat)
  | [] => []
  | p :: rest => (words p.2).map (p.1 :: ·) ++ wordsAux rest

end

/-- Follow a key from the root, one symbol per child step. -/
def get {α : Type} : Trie α → List Nat → Option α
  | .node v _, [] => v
  | .node _ cs, c :: rest =>
      match cs.find? (fun p => p.1 == c) with
      | some p => get p.2 rest
      | none => none
termination_by structural _ k => k

mutual

/-- Box invariant 2: paths leaving the same point carry different letters. At every node, no two
children are filed under the same symbol. -/
def DistinctLetters {α : Type} : Trie α → Prop
  | .node _ cs => (cs.map (·.1)).Nodup ∧ DistinctLettersChildren cs

/-- `DistinctLetters` for every subtrie in a child list. -/
def DistinctLettersChildren {α : Type} : List (Nat × Trie α) → Prop
  | [] => True
  | p :: rest => DistinctLetters p.2 ∧ DistinctLettersChildren rest

end

mutual

/-- A trie node with no children carries a value, and so does every childless node beneath it. -/
def NoDeadBranchesNode {α : Type} : Trie α → Prop
  | .node v cs => (cs = [] → v ≠ none) ∧ NoDeadBranchesChildren cs

/-- Every child in a trie's child list is a `NoDeadBranchesNode`. -/
def NoDeadBranchesChildren {α : Type} : List (Nat × Trie α) → Prop
  | [] => True
  | p :: rest => NoDeadBranchesNode p.2 ∧ NoDeadBranchesChildren rest

end

/-- Box invariant 3: every branch leads to a stored word. No childless valueless node below the
root. The root is exempt, since the empty trie is one. -/
def NoDeadBranches {α : Type} : Trie α → Prop
  | .node _ cs => NoDeadBranchesChildren cs

mutual

/-- The number of nodes in a trie, its root included. -/
def nodeCount {α : Type} : Trie α → ℕ
  | .node _ cs => 1 + nodeCountChildren cs

/-- The number of nodes in the subtries of a child list. -/
def nodeCountChildren {α : Type} : List (Nat × Trie α) → ℕ
  | [] => 0
  | p :: rest => nodeCount p.2 + nodeCountChildren rest

end

/-! ## The contract

`Ops` names the operations the box speaks of; `Contract` is what they owe. `Trie.contract` proves
the library's operations meet it. -/

/-- The operations the box speaks of: the trie's word map, and a get that counts its steps. -/
structure Ops (α : Type) where
  /-- The map holding no word. -/
  empty : Trie α
  /-- Store a word's value, or replace it. -/
  insert : List Nat → α → Trie α → Trie α
  /-- Delete a word. -/
  remove : List Nat → Trie α → Trie α
  /-- The stored words that start with a given prefix. -/
  keysWithPrefix : List Nat → Trie α → List (List Nat)
  /-- The design's invariants. -/
  Valid : Trie α → Prop
  /-- Get, counting child steps. -/
  getM : List Nat → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Option α)
  /-- Insert, counting child steps. -/
  insertM : List Nat → α → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)
  /-- Remove, counting child steps. -/
  removeM : List Nat → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)
  /-- The counting versions answer as the operations do, so the costs are of the operations. -/
  counted : ∀ w t, (getM w t).ret = Trie.get t w ∧ (∀ a, (insertM w a t).ret = insert w a t) ∧
    (removeM w t).ret = remove w t
  /-- The empty map is valid. -/
  emptyValid : Valid empty
  /-- Insert keeps the invariants. -/
  insertKeeps : ∀ w a t, Valid t → Valid (insert w a t)
  /-- Remove keeps the invariants. -/
  removeKeeps : ∀ w t, Valid t → Valid (remove w t)

/-- The operations as a word map, looked up by `Trie.get`. -/
def Ops.wordMap {α : Type} (o : Ops α) : WordMap α (Trie α) where
  empty := o.empty
  insert := o.insert
  remove := o.remove
  get w t := Trie.get t w
  keysWithPrefix := o.keysWithPrefix
  Valid := o.Valid

/-- **Get grows with its word, not with the dictionary**: at most a child step per letter. -/
def Ops.GetGrowsWithWord {α : Type} (_o : Ops α)
    (counted : List Nat → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Option α)) : Prop :=
  ∀ w t, (counted w t).time ≤ w.length

/-- **Insert grows with its word, not with the dictionary**: at most a child step per letter. -/
def Ops.InsertGrowsWithWord {α : Type} (_o : Ops α)
    (counted : List Nat → α → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)) : Prop :=
  ∀ w a t, (counted w a t).time ≤ w.length

/-- **Remove grows with its word, not with the dictionary**: at most two child steps per letter,
a lookup and a walk. -/
def Ops.RemoveGrowsWithWord {α : Type} (_o : Ops α)
    (counted : List Nat → Trie α → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)) : Prop :=
  ∀ w t, (counted w t).time ≤ 2 * w.length

/-- **A legal trie**: the box's invariants 2 and 3; invariant 1 is the meaning of `get`. -/
def Valid {α : Type} (t : Trie α) : Prop := DistinctLetters t ∧ NoDeadBranches t

/-- **The trie's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. Costs count the steps the counting operations count themselves. -/
structure Contract {α : Type} (o : Ops α) : Prop where
  -- Goal: look up words in a large dictionary.
  /-- Promise: a map from words to values. -/
  promise : o.wordMap.Promise  -- a map from words to values
  -- Idea: tie common **prefixes**, the beginnings words share, together, so they are checked
  -- once for all the words that share them.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ t, o.Valid t ↔
    -- 1. a word is a path of letters to a mark: the meaning of `get`, by definition
    DistinctLetters t ∧  -- 2. paths leaving the same point carry different letters
    NoDeadBranches t     -- 3. every branch leads to a stored word
  /-- Cost: grows with the word, not the dictionary; memory, up to a node per letter stored. -/
  cost :
    o.GetGrowsWithWord o.getM ∧        -- get: child steps
    o.InsertGrowsWithWord o.insertM ∧  -- insert: child steps
    o.RemoveGrowsWithWord o.removeM ∧  -- remove: child steps, a lookup and a walk
    (∀ t, o.Valid t → nodeCount t ≤ (t.words.map List.length).sum + 1)  -- memory, besides the root
    -- listing by prefix costs the prefix plus its answers: not stated

end Trie

end AlgoDesign.Strings
