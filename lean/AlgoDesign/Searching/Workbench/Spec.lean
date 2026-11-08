/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.Finset.Max
public import AlgoDesign.Searching.SearchTree

/-!
# The design project's contract: an ordered set with "next larger"

Source: the Search chapter's design project. The box's top half is the problem, and it is fixed
before any candidate exists:

> **Goal:** keep the timers a service has set, and say which one fires next.
>
> **Promise:** a set of keys. Insert adds a key and says whether it was new; delete takes one out
> and says whether it was there; contains says whether a key is there; next larger gives the
> smallest key larger than a given one, or nothing. Every other key stays as it was.
>
> **Cost:** fetches per operation on block memory, then writes, then blocks in use.
>
> **Assumes:** about 50,000 timers, keys between 0 and 10^9 and nothing about how they spread;
> about 50 questions for every change.

The box, field by field. `Contract`, last in this file, is the part Lean checks; the plainest
candidate meets it (`reference_contract`), and a candidate that meets it keeps the search tree's
promise (`Contract.isSearchTree`).

- Goal [mentioned] → the timers and which one fires next: `Ops`'s operations; read as a search
  tree through `Ops.asTree`, the plainest candidate `reference`.
- Promise [required] → `Contract.promise`, on what a state means, from the empty set on, one
  part per clause: `Ops.StartsEmpty`, `Ops.InsertAdds`, `Ops.DeleteTakes`, `Ops.ContainsSays`,
  `Ops.NextLargerGives`.
- Idea [none] → the box has none: the candidate's own.
- Invariants [none] → the box has none: the candidate's own `Valid`.
  Not in the box: the empty set is valid, `Ops.emptyValid`, and insert and delete keep it,
  `Ops.insertKeeps` and `Ops.deleteKeeps`.
- Cost [measured] → fetches, writes and blocks, counted by the bench in a memory the candidate
  does not control.
- Assumes [measured] → the workload (`timers` in the bench), not stated here.

-/

@[expose] public section

namespace AlgoDesign.Searching.Workbench

/-- A candidate design: its states `S`, what each state means (the keys it holds), the state it
starts from, its four operations, and the invariants it claims (`Valid`). `insert` and `delete`
return their answer with the new state. -/
structure Ops (S : Type) where
  /-- The keys a state holds. -/
  meaning : S → Finset ℤ
  /-- The empty set. -/
  empty : S
  /-- Add a key; `true` if it was new. -/
  insert : ℤ → S → Bool × S
  /-- Take a key out; `true` if it was there. -/
  delete : ℤ → S → Bool × S
  /-- Is the key there? -/
  contains : ℤ → S → Bool
  /-- The smallest key larger than the given one, if any. -/
  nextLarger : ℤ → S → Option ℤ
  /-- The candidate's invariants: the bottom half of its box. -/
  Valid : S → Prop
  /-- The empty set is valid. -/
  emptyValid : Valid empty
  /-- Insert keeps the invariants. -/
  insertKeeps : ∀ k s, Valid s → Valid (insert k s).2
  /-- Delete keeps the invariants. -/
  deleteKeeps : ∀ k s, Valid s → Valid (delete k s).2

/-- **What "next larger" owes**: the search tree's statement (`SearchTree.NextLargerSpec`), on
integer keys. -/
abbrev NextLargerSpec (m : Finset ℤ) (k : ℤ) : Option ℤ → Prop := SearchTree.NextLargerSpec m k

variable {S : Type}

/-- Promise: a set of keys, starting empty: the empty state holds nothing. -/
def Ops.StartsEmpty (o : Ops S) : Prop := o.meaning o.empty = ∅

/-- Promise: insert adds a key and says whether it was new; every other key stays as it was. -/
def Ops.InsertAdds (o : Ops S) : Prop :=
  (∀ k s, o.Valid s → o.meaning (o.insert k s).2 = o.meaning s ∪ {k}) ∧  -- adds the key
  (∀ k s, o.Valid s → (o.insert k s).1 = decide (k ∉ o.meaning s))       -- says if it was new

/-- Promise: delete takes one out and says whether it was there; every other key stays as it
was. -/
def Ops.DeleteTakes (o : Ops S) : Prop :=
  (∀ k s, o.Valid s → o.meaning (o.delete k s).2 = o.meaning s \ {k}) ∧  -- takes it out
  (∀ k s, o.Valid s → (o.delete k s).1 = decide (k ∈ o.meaning s))        -- says if it was there

/-- Promise: contains says whether a key is there. -/
def Ops.ContainsSays (o : Ops S) : Prop :=
  ∀ k s, o.Valid s → (o.contains k s = true ↔ k ∈ o.meaning s)

/-- Promise: next larger gives the smallest key larger than a given one, or nothing. -/
def Ops.NextLargerGives (o : Ops S) : Prop :=
  ∀ k s, o.Valid s → NextLargerSpec (o.meaning s) k (o.nextLarger k s)

/-- **The design project's contract**, the part of it Lean checks; the box quoted at the top of this
file says how each claim is checked. It is the box's top half, which the human wrote: every
candidate owes all of it. The bottom half (idea, invariants) is the candidate's: its own `Valid`,
which must hold of the empty set and survive every change. The set laws are the search tree's
(`Contract.isSearchTree`); the answers and "next larger" are the design project's own. Cost is not
here: it is measured on the bench, outside the candidate's control. -/
structure Contract (o : Ops S) : Prop where
  -- Goal: keep the timers a service has set, and say which one fires next.
  /-- Promise: a set of keys, read through what each state means. -/
  promise :
    o.StartsEmpty ∧      -- a set of keys, starting empty
    o.InsertAdds ∧       -- insert adds a key and says whether it was new
    o.DeleteTakes ∧      -- delete takes one out and says whether it was there
    o.ContainsSays ∧     -- contains says whether a key is there
    o.NextLargerGives    -- next larger: the smallest key larger, or nothing
  -- Idea: none in the box; the candidate's own.
  -- Invariants: none in the box; the candidate's own `Valid`.
  -- Cost: fetches per operation on block memory, then writes, then blocks in use. Measured by
  -- the bench, not stated here.
  -- Assumes: about 50,000 timers, keys between 0 and 10^9 and nothing about how they spread;
  -- about 50 questions for every change.

end AlgoDesign.Searching.Workbench
