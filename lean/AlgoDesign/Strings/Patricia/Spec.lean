/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Sort
public import AlgoDesign.Strings.Trie
public import AlgoDesign.Strings.WordMap

/-!
# Patricia (path-compressed trie): the specification

Sources: the Strings chapter, "When the tree is bigger than the words"; Weiss §12.4.2 (compressed
trie, radix tree); Nipkow et al. §12.3; Morrison, PATRICIA (1968), its bit-level relative.

> **Goal:** the trie's job, when the words are long.
>
> **Promise:** the trie's.
>
> **Idea:** squeeze every chain into a single branch.
>
> **Invariants:**
>
> 1. A word is the path from the root, now several letters to a branch, to a mark that says it
>    ends there.
> 2. The branches leaving a node start with different letters.
> 3. Every node below the root where no word ends has two children or more.
> 4. Every branch carries at least one letter.
>
> **Cost:** at most two nodes per word, however long the words are, once one word is stored.

The box, field by field. Read `Contract`, at the end of this file; `Patricia.contract` proves the
library meets it.

- Goal [required] → `WordMap`, the trie's job: the same operations.
- Promise [proved] → `WordMap.Promise`, the trie's.
- Idea [mentioned] → squeeze every chain into a single branch.
- Invariants [proved] →
  1 [required] the meaning of `get`: a word is found by following the labels from the root,
    several letters to a branch, to a node carrying a value.
  2 [proved] `DistinctFirstLetters`.
  3 [proved] `BranchesUnlessWordEnds`.
  4 [proved] `NoEmptyBranches`.
  Not in the box: the empty map is valid, `Ops.emptyValid`, and insert and remove keep it,
  `Ops.insertKeeps` and `Ops.removeKeeps`.
- Cost [proved] → nodes per word (`nodeCount`); key symbols get compares, the trie's
  through the Goal.
- Assumes [none] → the box assumes nothing.

Words: word = `List Nat`; branch = an edge and its label, a `List Nat`; the mark that a word ends =
a node's value.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- A path-compressed trie: every edge carries a label, a run of symbols. -/
inductive Patricia (α : Type) where
  | node (value : Option α) (children : List (List Nat × Patricia α))

namespace Patricia

/-- The tree holding nothing. -/
def empty {α : Type} : Patricia α := .node none []

mutual

/-- The words stored, as the concatenated edge labels from the root to a node carrying a value. -/
def words {α : Type} : Patricia α → List (List Nat)
  | .node v cs =>
      (match v with | some _ => [([] : List Nat)] | none => []) ++ wordsAux cs

/-- The words of a child list, each prefixed with the label its subtree is filed under. -/
def wordsAux {α : Type} : List (List Nat × Patricia α) → List (List Nat)
  | [] => []
  | p :: rest => (words p.2).map (p.1 ++ ·) ++ wordsAux rest

end

mutual

/-- Follow a key from the root. The empty key asks for the node's own value; `c :: rest` goes to
the first child whose label begins with `c`, and no later sibling is tried. -/
def get {α : Type} : Patricia α → List Nat → Option α
  | .node v _, [] => v
  | .node _ cs, c :: rest => getAux cs c rest

/-- Find the edge whose label begins with `c`, match the rest of the label against `rest`, and
descend with what is left. An empty label is passed over. -/
def getAux {α : Type} : List (List Nat × Patricia α) → Nat → List Nat → Option α
  | [], _, _ => none
  | ([], _) :: ps, c, rest => getAux ps c rest
  | (c' :: lbl, t) :: ps, c, rest =>
      if c' = c then
        if lbl.isPrefixOf rest then get t (rest.drop lbl.length) else none
      else getAux ps c rest

end

/-- The letter each branch of a child list starts with, `none` for a branch with no letter. -/
@[simp] abbrev firstLetters {α : Type} (cs : List (List Nat × Patricia α)) : List (Option Nat) :=
  cs.map (·.1.head?)

mutual

/-- Box invariant 2: the branches leaving a node start with different letters. Within every child
list, the branches' first letters are distinct. -/
def DistinctFirstLetters {α : Type} : Patricia α → Prop
  | .node _ cs => (firstLetters cs).Nodup ∧ DistinctFirstLettersChildren cs

/-- `DistinctFirstLetters` for every subtree in a child list. -/
def DistinctFirstLettersChildren {α : Type} : List (List Nat × Patricia α) → Prop
  | [] => True
  | p :: rest => DistinctFirstLetters p.2 ∧ DistinctFirstLettersChildren rest

end

/-! ## Box invariants 3 and 4 -/

mutual

/-- A node below the root, and every node beneath it, carries a value or has two children or
more. -/
def BranchesUnlessWordEndsNode {α : Type} : Patricia α → Prop
  | .node v cs => (v ≠ none ∨ 2 ≤ cs.length) ∧ BranchesUnlessWordEndsChildren cs

/-- `BranchesUnlessWordEndsNode` for every child in a child list. -/
def BranchesUnlessWordEndsChildren {α : Type} : List (List Nat × Patricia α) → Prop
  | [] => True
  | p :: rest => BranchesUnlessWordEndsNode p.2 ∧ BranchesUnlessWordEndsChildren rest

end

/-- Box invariant 3: every node below the root where no word ends has two children or more. -/
def BranchesUnlessWordEnds {α : Type} : Patricia α → Prop
  | .node _ cs => BranchesUnlessWordEndsChildren cs

mutual

/-- Box invariant 4: every branch carries at least one letter, or `get` could never descend
through it. Every edge label below this node is non-empty. -/
def NoEmptyBranches {α : Type} : Patricia α → Prop
  | .node _ cs => NoEmptyBranchesChildren cs

/-- Every label in a child list, and every label beneath it, is non-empty. -/
def NoEmptyBranchesChildren {α : Type} : List (List Nat × Patricia α) → Prop
  | [] => True
  | p :: rest => p.1 ≠ [] ∧ NoEmptyBranches p.2 ∧ NoEmptyBranchesChildren rest

end

mutual

/-- The number of nodes in a Patricia tree, its root included. -/
def nodeCount {α : Type} : Patricia α → ℕ
  | .node _ cs => 1 + nodeCountChildren cs

/-- The number of nodes in the subtrees of a child list. -/
def nodeCountChildren {α : Type} : List (List Nat × Patricia α) → ℕ
  | [] => 0
  | p :: rest => nodeCount p.2 + nodeCountChildren rest

end

/-! ## The contract

`Ops` names the operations the box speaks of; `Contract` is what they owe. `Patricia.contract`
proves the library's operations meet it. -/

/-- The operations the box speaks of: the tree's word map, and a get that counts its steps. -/
structure Ops (α : Type) where
  /-- The map holding no word. -/
  empty : Patricia α
  /-- Store a word's value, or replace it. -/
  insert : List Nat → α → Patricia α → Patricia α
  /-- Delete a word. -/
  remove : List Nat → Patricia α → Patricia α
  /-- The stored words that start with a given prefix. -/
  keysWithPrefix : List Nat → Patricia α → List (List Nat)
  /-- The design's invariants. -/
  Valid : Patricia α → Prop
  /-- Get, counting key symbols compared against edge labels. -/
  getM : List Nat → Patricia α → Cslib.Algorithms.Lean.TimeM ℕ (Option α)
  /-- The counted get answers as get does, so the cost is of get. -/
  counted : ∀ w t, (getM w t).ret = Patricia.get t w
  /-- The empty map is valid. -/
  emptyValid : Valid empty
  /-- Insert keeps the invariants. -/
  insertKeeps : ∀ w a t, Valid t → Valid (insert w a t)
  /-- Remove keeps the invariants. -/
  removeKeeps : ∀ w t, Valid t → Valid (remove w t)

/-- The operations as a word map, looked up by `Patricia.get`. -/
def Ops.wordMap {α : Type} (o : Ops α) : WordMap α (Patricia α) where
  empty := o.empty
  insert := o.insert
  remove := o.remove
  get w t := Patricia.get t w
  keysWithPrefix := o.keysWithPrefix
  Valid := o.Valid

/-- **Get compares a key symbol per letter** at most, the trie's cost through the Goal. -/
def Ops.GetGrowsWithWord {α : Type} (_o : Ops α)
    (counted : List Nat → Patricia α → Cslib.Algorithms.Lean.TimeM ℕ (Option α)) : Prop :=
  ∀ w t, (counted w t).time ≤ w.length

/-- **A legal Patricia tree**: the box's invariants 2, 3 and 4; invariant 1 is the meaning of
`get`. -/
def Valid {α : Type} (t : Patricia α) : Prop :=
  DistinctFirstLetters t ∧ BranchesUnlessWordEnds t ∧ NoEmptyBranches t

/-- **The Patricia tree's contract**, the part of the design Lean checks, one field per box field
and one conjunct per box line. Costs count the steps the counting operations count themselves. -/
structure Contract {α : Type} (o : Ops α) : Prop where
  -- Goal: the trie's job, when the words are long.
  /-- Promise: the trie's. -/
  promise : o.wordMap.Promise  -- the trie's, a map from words to values
  -- Idea: squeeze every chain into a single branch.
  /-- Invariants: the box's four, in box order. -/
  invariants : ∀ t, o.Valid t ↔
    -- 1. a word is the path from the root to a mark: the meaning of `get`, by definition
    DistinctFirstLetters t ∧    -- 2. the branches leaving a node start with different letters
    BranchesUnlessWordEnds t ∧  -- 3. below the root, where no word ends: two children or more
    NoEmptyBranches t           -- 4. every branch carries at least one letter
  /-- Cost: at most two nodes per word, once one word is stored; get, a symbol per letter. -/
  cost :
    (∀ t, o.Valid t → t.words ≠ [] → nodeCount t ≤ 2 * t.words.length) ∧  -- nodes
    o.GetGrowsWithWord o.getM  -- get: key symbols compared, the trie's cost through the Goal

end Patricia

end AlgoDesign.Strings
