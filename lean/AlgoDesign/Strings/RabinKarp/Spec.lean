/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.Occurrences

/-!
# Rabin–Karp: the specification

Sources: the Strings chapter, "Reading the whole book, every time"; CLRS §32.2; Karp and Rabin,
*Efficient randomized pattern-matching algorithms* (IBM J. Res. Dev. 31(2), 1987);
Motwani and Raghavan, *Randomized Algorithms*, §7.6.

> **Goal:** find every place a pattern occurs in a text.
>
> **Promise:** every occurrence, overlapping ones too, and nothing else.
>
> **Idea:** fingerprint the windows: compare small numbers that stand for them, not the windows
> themselves.
>
> **Invariants:**
>
> 1. Equal windows get equal numbers.
> 2. The number kept is always the current window's number, however far the window has slid.
> 3. Equal numbers only make a window a candidate: every candidate is checked letter by letter
>    before it is reported.
>
> **Cost:** one pass over the text, each slide updating the number from the previous window's in a
> few operations, plus a letter-by-letter check of the whole pattern at every candidate, real
> matches included.
>
> **Assumes:** a large prime modulus, picked at random, independently of the text. Otherwise many
> windows become false candidates. It is slower, never wrong.

The box, field by field. Read `Contract`, at the end of this file; `RabinKarp.contract` proves the
library meets it.

- Goal [required] → `Occurrences`: build, the text, and search; Rabin–Karp's value is the text.
- Promise [proved] → `Occurrences.Promise`, on every text.
- Idea [mentioned] → the number a window stands for is `fingerprint`.
- Invariants [proved] → on the scan's state, `Scan`, proved of the library's scan (`run_roll`), not
  asked of a candidate:
  1 [required] a window's number is a function of the window, so there is nothing to keep.
  2 [proved] `NumberMatchesWindow`.
  3 [proved] `FoundSoFarExact`.
  Not in the box: every text builds a valid value, `Ops.buildValid`, that answers about that text,
  `Ops.buildStores`; both are of the built value, not of the scan.
- Cost [proved] → one tick per window, plus the pattern's length per candidate (`candidateCount`).
- Assumes [proved] → `Contract` is a claim at one fixed modulus, and at modulus 1, where every
  window is a candidate, a naive scan meets it. The library meets it at every positive modulus,
  `RabinKarp.contract`, so "never wrong" needs no assumption; a random prime makes collisions rare,
  for the expected cost (`RabinKarp/Collision.lean`).

Words: window = `List Nat` of the pattern's length; number = `fingerprint`; candidate = a window
whose number equals the pattern's.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Value of a window under the radix-`base` fingerprint, reduced modulo `q`, by Horner's rule. -/
def fingerprint (base q : Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc c => (acc * base + c) % q) 0

/-- How many windows are candidates, their fingerprint equal to the pattern's: occurrences and
collisions together. -/
def candidateCount (base q : Nat) (text pat : List Nat) : Nat :=
  (List.range (text.length + 1 - pat.length)).countP
    fun j => decide (fingerprint base q ((text.drop j).take pat.length) = fingerprint base q pat)

namespace RabinKarp

/-- **The scan's state**, with its context. The scan reads `text` for `pattern`, its windows
numbered in radix `base` modulo `modulus`. It stands at position `start`, where the rest of the
text is `rest`; it carries `number` for the window there and has reported `found` so far. The
fields `rest_eq` and `start_le` tie the cursor to the text. -/
structure Scan where
  /-- The text being searched. -/
  text : List Nat
  /-- The pattern searched for. -/
  pattern : List Nat
  /-- The radix the windows are read in. -/
  base : Nat
  /-- The modulus the numbers are reduced by. -/
  modulus : Nat
  /-- The position the scan stands at: the start of the current window. -/
  start : Nat
  /-- The text from `start` on. -/
  rest : List Nat
  /-- The number carried for the current window. -/
  number : Nat
  /-- The positions reported so far. -/
  found : List Nat
  /-- The rest is the text from the cursor on. -/
  rest_eq : rest = text.drop start
  /-- The cursor is a position of the text, its end included. -/
  start_le : start ≤ text.length

/-- Box invariant 2: the number kept is always the current window's number, however far the window
has slid. As the scan's state: the number it carries is the current window's number. -/
def NumberMatchesWindow (s : Scan) : Prop :=
  s.number = fingerprint s.base s.modulus (s.rest.take s.pattern.length)

/-- Box invariant 3: equal numbers only make a window a candidate: every candidate is checked letter
by letter before it is reported. As the scan's state: what it has reported is exactly the
occurrences before the cursor, in increasing order. -/
def FoundSoFarExact (s : Scan) : Prop :=
  s.found = (occurrenceList s.text s.pattern).filter (· < s.start)

/-! ## The contract

`Ops` names the operations the box speaks of; `Contract` is what they owe. `RabinKarp.contract`
proves the library's operations meet it. -/

/-- The operations the box speaks of, in radix `base` modulo `modulus`, both given from outside:
the occurrence finder; the scan's invariants; and a search that counts its steps. -/
structure Ops (base modulus : Nat) where
  /-- Build, the text, and search. Rabin–Karp prepares nothing: its value is the text. -/
  finder : Occurrences (List Nat)
  /-- The design's invariants, on the scan's state. -/
  Valid : Scan → Prop
  /-- Search, counting one tick per window and the pattern's length per candidate. -/
  searchM : List Nat → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (List Nat)
  /-- The counted search answers as search does, so the cost is of the search. -/
  counted : ∀ s p, (searchM s p).ret = finder.search s p
  /-- Every text builds a valid value. -/
  buildValid : ∀ t, finder.Valid (finder.build t)
  /-- The value built from a text answers about that text. -/
  buildStores : ∀ t, finder.text (finder.build t) = t

/-- Promise: every occurrence, overlapping ones too, and nothing else, on every text. The parts:
every occurrence, overlapping ones too, `every`; and nothing else, `nothing_else`. An empty
pattern occurs at every position `0..n`. -/
def Ops.FindsEveryOccurrence {base modulus : Nat} (o : Ops base modulus) : Prop :=
  o.finder.Promise

/-- **One pass over the text, plus a full check of the pattern at every candidate**: the counted
search's ticks, one per window and the pattern's length per candidate. -/
def Ops.OnePassPlusChecks {base modulus : Nat} (o : Ops base modulus)
    (counted : List Nat → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (List Nat)) : Prop :=
  ∀ s p, (counted s p).time ≤
    ((o.finder.text s).length + 1 - p.length) +
      p.length * candidateCount base modulus (o.finder.text s) p

/-- **The scan's running state**: the box's lines 2 and 3. Line 1 needs no keeping (see the first
screen). -/
def Valid (s : Scan) : Prop := NumberMatchesWindow s ∧ FoundSoFarExact s

/-- **Rabin–Karp's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. Correctness asks only a positive modulus; the cost counts the steps the
counting search counts itself. -/
structure Contract {base modulus : Nat} (o : Ops base modulus) : Prop where
  -- Goal: find every place a pattern occurs in a text.
  /-- Promise: every occurrence, overlapping ones too, and nothing else, on every text. -/
  promise : o.FindsEveryOccurrence  -- every occurrence, overlapping ones too, and nothing else
  -- Idea: fingerprint the windows: compare small numbers that stand for them, not the windows
  -- themselves.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ s, o.Valid s ↔
    -- 1. equal windows get equal numbers: true by construction, a window's number is a
    --    function of the window
    NumberMatchesWindow s ∧  -- 2. the number kept is always the current window's number
    FoundSoFarExact s        -- 3. every candidate is checked letter by letter, then reported
  /-- Cost: one pass over the text, plus a full check of the pattern at every candidate. -/
  cost : o.OnePassPlusChecks o.searchM  -- a tick per window, the check per candidate
    -- each slide in a few operations: proved outside `Contract`, a fixed number of steps per
    -- slide, the same for every width
  -- Assumes: a large prime modulus, picked at random, independently of the text. Otherwise many
  -- windows become false candidates. It is slower, never wrong.

end RabinKarp

end AlgoDesign.Strings
