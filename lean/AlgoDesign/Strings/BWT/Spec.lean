/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.SuffixArray.Spec

/-!
# Burrows–Wheeler transform: the specification

Sources: the Strings chapter, "Useful mess?"; Burrows and Wheeler, DEC SRC Research Report 124
(1994); Navarro, *Compact Data Structures*, §11.3.1; CLRS Problem 32-3.

> **Goal:** drop the suffix array, but keep what it told us: how the suffixes sort.
>
> **Promise:** from these letters alone, the text comes back exactly. The sorted suffixes come with
> it.
>
> **Idea:** store a permutation of the text's letters, chosen so a fixed rule can rebuild
> everything from it.
>
> **Invariants:**
>
> 1. It is a permutation of the text: the same letters, each as often, $n$ in all.
> 2. It follows the sorted suffixes: for each suffix, in their sorted order, the letter just
>    before it.
>
> **Cost:** $n$ letters, instead of the text plus $4n$.
>
> **Assumes:** the text ends with one `$`, found nowhere else. Otherwise it is rejected with an
> error.

The box, field by field. Read `Contract`, at the end of this file; `BWT.contract` proves the
library meets it.

- Goal [required] → `Ops`: the inverse and the suffixes take the stored letters alone, never the
  text or a suffix array. The value kept is a `Transform`, a text with its letters, so the
  invariants can speak of both.
- Promise [proved] → the text back exactly, and the suffixes in sorted order, from the letters of
  any valid transform of a text that ends with one `$`.
- Idea [mentioned] → a permutation of the text's letters a fixed rule can undo.
- Invariants [proved] →
  1 [proved] `SameLetters`.
  2 [proved] `LetterBeforeEachSuffix`.
  Not in the box: `SentinelOnce`, the box's assumption read on the letters.
- Cost [proved] → `n` letters; "instead of the text plus `4n`" is the book's comparison.
- Assumes [tested] → the text ends with one `$`: the hypothesis `Terminated t 0` of the promise,
  read on the letters as `SentinelOnce`; that any other text is rejected with an error, the tests
  check.

Words: text = `List Nat`, `$` = `0`; letters = `Transform.letters`; suffix `i` = `suffix t i`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- The box's assumption: `t` is terminated by `s`: `s` sits at the end and is strictly smaller than
everything before it, the chapter's `$`. For `$ = 0`, the smallest letter, "strictly smaller than
everything before it" is the box's "found nowhere else". Without it rotation order and suffix order
differ (`abaa`). -/
def Terminated (t : List Nat) (s : Nat) : Prop :=
  t.getLast? = some s ∧ ∀ c ∈ t.dropLast, s < c

/-- The letter just before suffix `p` of `t`, wrapping round to the last letter for `p = 0`;
nothing if `p` is not a position of `t`. -/
def letterBefore (t : List Nat) (p : Nat) : Option Nat := t[(p + t.length - 1) % t.length]?

/-- **A transform**: a text and the letters stored for it. -/
structure Transform where
  /-- The text. -/
  text : List Nat
  /-- The letters stored in its place, one per row. -/
  letters : List Nat

namespace BWT

/-- Box invariant 1: it is a permutation of the text: the same letters, each as often, `n` in
all. -/
def SameLetters (x : Transform) : Prop := x.letters.Perm x.text

/-- Box invariant 2: it follows the sorted suffixes: for each suffix, in their sorted order, the
letter just before it. Read through any suffix array of the text. -/
def LetterBeforeEachSuffix (x : Transform) : Prop :=
  ∀ positions, SuffixArray.Valid ⟨x.text, positions⟩ →
    x.letters.map some = positions.map (letterBefore x.text)

/-- The box's assumption, the text ends with one `$` found nowhere else, read on the letters: the
sentinel, `0`, stands among them exactly once. Implied by the text's `Terminated` and
`SameLetters`; kept because the letters alone can be checked for it. -/
def SentinelOnce (x : Transform) : Prop := x.letters.count 0 = 1

/-! ## The contract

`Ops` names the operations the box speaks of; `Contract` is what they owe. `BWT.contract` proves
the library's operations meet it. -/

/-- The operations the box speaks of: transform a text, and, from the stored letters alone, invert
it and read the suffixes in sorted order; and the transform's invariants. -/
structure Ops where
  /-- The letters stored for a text. -/
  transform : List Nat → List Nat
  /-- The text, rebuilt from the letters. -/
  invert : List Nat → List Nat
  /-- The suffixes' starting positions in sorted order, read from the letters. -/
  suffixes : List Nat → List Nat
  /-- The design's invariants. -/
  Valid : Transform → Prop

/-- Promise: from these letters alone, the text comes back exactly, for every valid transform of
a text that ends with one `$`. -/
def Ops.TextComesBack (o : Ops) : Prop :=
  ∀ x, o.Valid x → Terminated x.text 0 → o.invert x.letters = x.text

/-- Promise: the sorted suffixes come with it, from the letters alone, for every valid transform
of a text that ends with one `$`. -/
def Ops.SuffixesComeBack (o : Ops) : Prop :=
  ∀ x, o.Valid x → Terminated x.text 0 → SuffixArray.Valid ⟨x.text, o.suffixes x.letters⟩

/-- Not in the box: what the transform stores, for every text that ends with one `$`, is valid. -/
def Ops.KeepsInvariants (o : Ops) : Prop :=
  ∀ t, Terminated t 0 → o.Valid ⟨t, o.transform t⟩

/-- **A legal transform**: the box's two invariants, then its assumption read on the letters. -/
def Valid (x : Transform) : Prop := SameLetters x ∧ LetterBeforeEachSuffix x ∧ SentinelOnce x

/-- **The Burrows–Wheeler transform's contract**, the part of the design Lean checks, one field per
box field and one conjunct per box line; a conjunct not in the box says so. -/
structure Contract (o : Ops) : Prop where
  -- Goal: drop the suffix array, but keep what it told us: how the suffixes sort.
  /-- Promise: from the letters alone, the text comes back exactly, the sorted suffixes with it. -/
  promise :
    o.TextComesBack ∧     -- the text comes back exactly
    o.SuffixesComeBack ∧  -- the sorted suffixes come with it
    o.KeepsInvariants     -- not in the box: what it stores is valid
  -- Idea: store a permutation of the text's letters, chosen so a fixed rule can rebuild
  -- everything from it.
  /-- Invariants: the box's two, in box order, then one not in the box. -/
  invariants : ∀ x, o.Valid x ↔
    SameLetters x ∧             -- 1. a permutation of the text, `n` letters in all
    LetterBeforeEachSuffix x ∧  -- 2. for each suffix, in sorted order, the letter before it
    SentinelOnce x              -- not in the box: one `$` among the letters
  /-- Cost: `n` letters. -/
  cost : ∀ t, (o.transform t).length = t.length  -- letters stored per letter of the text
  -- Assumes: the text ends with one `$`, found nowhere else. Otherwise it is rejected with an
  -- error.

end BWT

end AlgoDesign.Strings
