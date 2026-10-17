/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Sort
public import Cslib.Algorithms.Lean.TimeM
public import AlgoDesign.Strings.Occurrences

/-!
# Suffix array: the specification

Sources: the Strings chapter, "It was somewhere in the middle"; CLRS §32.5; Manber and Myers,
*Suffix arrays: a new method for on-line string searches* (SIAM J. Comput. 22(5), 1993).

> **Goal:** find any fragment, wherever it starts, in one fixed text asked many questions.
>
> **Promise:** every place the fragment starts, and nothing else.
>
> **Idea:** every occurrence is the beginning of a suffix.
>
> **Invariants:**
>
> 1. Every position of the text appears once, so no occurrence can be missed.
> 2. The suffixes are kept in sorted order, so the occurrences of any fragment lie side by side,
>    and finding one stretch finds them all.
>
> **Cost:** one stored position per letter beside the text, not the suffix tree's 34 bytes; a
> search grows with the fragment times $\log n$, plus one step per place found.
>
> **Assumes:** the text stays as it was when the array was built. Otherwise a search returns
> places where the fragment no longer is, and misses places where it now is.

The box, field by field. Read `Contract`, at the end of this file; `SuffixArray.contract` proves
the library meets it.

- Goal [required] → `Occurrences`: build and search, over a `SuffixArray`, a text with its
  positions; "one fixed text asked many questions" is the cost: built once, searched many times.
- Promise [proved] → `Occurrences.Promise`, on every text; the answer's order is not promised.
- Idea [mentioned] → every occurrence is the beginning of a suffix.
- Invariants [proved] →
  1 [proved] `EachPositionOnce`.
  2 [proved] `SuffixesSorted`.
- Cost [proved] → stored positions; letter comparisons per search, plus one step per place found.
  The suffix tree's 34 bytes is the book's comparison, not a claim here.
- Assumes [mentioned] → a `SuffixArray` holds its text beside its array, and one array is `Valid`
  for a text (`valid_unique`); a changed text with the old array is outside `Valid`.

Words: fragment = pattern = `List Nat`; place = a position; order = core `List.le`, lexicographic.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Suffix `i` of `t`. -/
def suffix (t : List Nat) (i : Nat) : List Nat := t.drop i

/-- **A suffix array**: a text and the positions of its suffixes, in the array's row order. -/
structure SuffixArray where
  /-- The text, fixed once the array is built. -/
  text : List Nat
  /-- The suffixes' starting positions, one per row. -/
  positions : List Nat

namespace SuffixArray

/-- Box invariant 1: every position of the text appears once, so no occurrence can be missed.
The positions are a permutation of the text's positions. -/
def EachPositionOnce (a : SuffixArray) : Prop := a.positions.Perm (List.range a.text.length)

/-- Box invariant 2: the suffixes are kept in sorted order, so the occurrences of any fragment lie
side by side, and finding one stretch finds them all. The suffixes the positions name are pairwise
`≤` in row order. -/
def SuffixesSorted (a : SuffixArray) : Prop := (a.positions.map (suffix a.text)).Pairwise (· ≤ ·)

/-! ## The contract

`Ops` names the operations the box speaks of; `Contract` is what they owe. `SuffixArray.contract`
proves the library's operations meet it. -/

/-- The operations the box speaks of: the occurrence finder, which builds a suffix array from a text
and searches it, and a search that counts its letter comparisons. -/
structure Ops where
  /-- Prepare a text for searching. -/
  build : List Nat → SuffixArray
  /-- Where a pattern occurs. -/
  search : SuffixArray → List Nat → List Nat
  /-- The design's invariants. -/
  Valid : SuffixArray → Prop
  /-- Search, counting `|p|` letter comparisons per probe and one step per place found. -/
  searchM : SuffixArray → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (List Nat)
  /-- The counted search answers as search does, so the cost is of the search. -/
  counted : ∀ a p, (searchM a p).ret = search a p

/-- The operations as an occurrence finder, answering about the text the array holds. -/
def Ops.finder (o : Ops) : Occurrences SuffixArray where
  build := o.build
  text a := a.text
  search := o.search
  Valid := o.Valid

/-- Promise: every place the fragment starts, and nothing else, on every text. The parts: every
place the fragment starts, `every`; and nothing else, `nothing_else`; every text builds a valid
array answering about it, `valid_build`, `text_build`. An empty fragment starts at every position
`0..n`. -/
def Ops.FindsEveryStart (o : Ops) : Prop :=
  o.finder.Promise (fun _ => True)

/-- **A legal suffix array**: the box's two invariants. -/
def Valid (a : SuffixArray) : Prop := EachPositionOnce a ∧ SuffixesSorted a

/-- **The suffix array's contract**, the part of the design Lean checks, one field per box field
and one conjunct per box line. Costs count the steps the counting search counts itself. -/
structure Contract (o : Ops) : Prop where
  -- Goal: find any fragment, wherever it starts, in one fixed text asked many questions.
  /-- Promise: every place the fragment starts, and nothing else, on every text. -/
  promise : o.FindsEveryStart  -- every place the fragment starts, and nothing else
  -- Idea: every occurrence is the beginning of a suffix.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ a, o.Valid a ↔
    EachPositionOnce a ∧  -- 1. every position of the text appears once
    SuffixesSorted a      -- 2. the suffixes are kept in sorted order
  /-- Cost: one position per letter; a search, the fragment times `log n`, plus the places. -/
  cost :
    (∀ a, o.Valid a → a.positions.length = a.text.length) ∧  -- memory: positions per letter
    (∀ a, o.Valid a → ∀ p, (o.searchM a p).time ≤
      2 * (p.length * (Nat.log2 a.positions.length + 1)) + (o.search a p).length)
    -- search: letter comparisons, `|p|` per probe of two binary searches, plus one per place
  -- Assumes: the text stays as it was when the array was built. Otherwise a search returns
  -- places where the fragment no longer is, and misses places where it now is.

end SuffixArray

end AlgoDesign.Strings
