/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.BWT.Invert
public import AlgoDesign.Strings.Occurrences

/-!
# FM-index: the specification

Sources: the Strings chapter, "By heart" and "Give me the whole line"; Ferragina and Manzini,
*Opportunistic data structures with applications* (FOCS 2000); Navarro, *Compact Data
Structures*, §11.1.3–11.1.4 and §11.2.

> **Goal:** search the rearranged text directly, without rebuilding the text.
>
> **Promise:** how many times a fragment occurs.
>
> **Idea:** find the pattern from its end: first the suffixes that start with its last letter,
> then those that start with its last two letters, and so on, until the whole pattern.
>
> **Invariants:**
>
> 1. The rows kept so far are exactly the suffixes that start with the part of the pattern read
>    so far, and they are found from the rearranged letters alone.
>
> **Cost:** two counts per letter of the fragment, whatever the length of the text.
>
> **Assumes:** the fragment has no `$`. One that does gets zero matches, since `$` only marks the
> end of the text.

The box, field by field. Read `Contract`, at the end of this file, the part of both boxes Lean
checks; `FMIndex.contract` proves the library meets it at every positive interval.

- Goal [mentioned] → count takes the stored `FMIndex` and a fragment, never the text; "without
  rebuilding the text" Lean cannot rule out.
- Promise [proved] → the number of occurrences in `FMIndex.text`, the text without its `$`.
- Idea [mentioned] → find the pattern from its end, one letter at a time.
- Invariants [proved] → on backward search's state, `BackwardSearch.Stretch`, not on the index:
  1 [proved] on that state: `BackwardSearch.StretchHoldsMatches`, kept by the search.
- Cost [proved] → backward steps, two `occ` reads each, per letter of the fragment.
- Assumes [proved] → a fragment with a `$` occurs nowhere in the text without its `$`, so it gets
  zero matches.

> **Goal:** say where each match starts, without keeping the suffix array.
>
> **Promise:** every start position, each exactly once, in no particular order.
>
> **Idea:** keep a few positions, and walk to the nearest one.
>
> **Invariants, added to the FM-index's invariant 1:**
>
> 2. At fixed intervals along the text, a row keeps its own position, so every match is a short
>    walk from one.
>
> **Cost:** one kept position per interval; each match, fewer steps than the interval.

The box, field by field.

- Goal [required] → the stored parts hold no suffix array, only the kept positions and the rows that
  keep them; locate takes them, never the text.
- Promise [proved] → `Occurrences.Promise`, on every text of bytes without `$` (`PositiveBytes`).
- Idea [mentioned] → keep a few positions, and walk to the nearest one.
- Invariants [proved] → `FMIndex.Valid`, on the stored index:
  2 [proved] `PositionsKept`.
  Not in the box: `SentinelOnce`, `SmallerLettersCounted`, `WalkVisitsEveryRow`, `KeptRowsListed`,
  `LettersAreBytes`, `RateAtLeastOne`; the first is the transform's assumption.
- Cost [proved] → LF steps per match, fewer than the interval; one kept position per interval is
  invariant 2.
- Assumes [proved] → none of its own; the transform's, one `$` at the text's end, is
  `SentinelOnce` on the stored column.

Words: fragment = pattern = `List Nat`, `$` = `0`; the rearranged text = `FMIndex.bwt`; interval =
`FMIndex.sample`; a count = an `occ` read; walk = LF steps.
-/

@[expose] public section

namespace AlgoDesign.Strings

open Cslib.Algorithms.Lean

/-- The values below `σ` that occur in `t`, ascending. -/
def alphabetOf (σ : Nat) (t : List Nat) : List Nat := (List.range σ).filter (· ∈ t)

/-- The dense `C`: for each dense index, the count of the symbols before it. -/
def cDense (t syms : List Nat) : List Nat :=
  (List.range syms.length).map fun d => ((syms.take d).map fun a => t.count a).sum

/-- A stored FM-index: the parts it keeps, as plain lists. -/
structure FMIndex where
  /-- The rearranged text, the last column: one letter per row. -/
  bwt : List Nat
  /-- The `C` array: for each letter that occurs, in order, how many letters sort below it. -/
  c : List Nat
  /-- One mark per row: does this row keep its text position? -/
  marks : List Bool
  /-- The kept positions, in row order. -/
  saSamples : List Nat
  /-- For each kept position `0, sample, 2·sample, …`, the row that keeps it. -/
  isaSamples : List Nat
  /-- The interval between kept positions, the sampling rate. -/
  sample : Nat
  deriving Repr

/-- The text the index answers about: the one its column rebuilds, without its `$`. -/
def FMIndex.text (ix : FMIndex) : List Nat := (invertBwt ix.bwt).dropLast

/-- The row whose last letter is the sentinel, the row of text position `0`. -/
@[simp] abbrev FMIndex.sentinelRow (ix : FMIndex) : Nat := ix.bwt.idxOf 0

/-- The row `j` LF steps from the sentinel's row, the row of text position `(n - j) mod n`. -/
@[simp] abbrev FMIndex.rowAfter (ix : FMIndex) (j : Nat) : Nat := (lf ix.bwt)^[j] ix.sentinelRow

/-- The kept value a marked row `r` reads: the one its rank among the marked rows names, if there
is one. -/
@[simp] abbrev FMIndex.keptValueAt (ix : FMIndex) (r : Nat) : Option Nat :=
  ix.saSamples[(ix.marks.take r).count true]?

/-- The letters a column can hold are bytes: its alphabet is the bytes it holds, ascending. -/
@[simp] abbrev byteAlphabet (bwt : List Nat) : List Nat := alphabetOf 256 bwt

namespace FMIndex

/-- Invariant 2's last part: each marked row holds its own text position. The row `j` LF steps
from the sentinel's row, position `(n - j) mod n`, has an entry in `marks`, is marked exactly
when `sample` divides that position, and then keeps it. -/
def KeptPositionsCorrect (ix : FMIndex) : Prop :=
  0 ∈ ix.bwt → ∀ j, j < ix.bwt.length →
    ∃ h : ix.rowAfter j < ix.marks.length,
      (ix.marks[ix.rowAfter j] = true ↔ ix.sample ∣ (ix.bwt.length - j) % ix.bwt.length) ∧
      (ix.sample ∣ (ix.bwt.length - j) % ix.bwt.length →
        ix.keptValueAt (ix.rowAfter j) = some ((ix.bwt.length - j) % ix.bwt.length))

/-- Box invariant 2: at fixed intervals along the text, a row keeps its own position, so every match
is a short walk from one. The kept positions are the multiples of `sample` below `n`, each once; one
mark per row, one kept position per mark; and each marked row holds its own position. -/
def PositionsKept (ix : FMIndex) : Prop :=
  ix.saSamples.Perm
      ((List.range ((ix.bwt.length + ix.sample - 1) / ix.sample)).map (· * ix.sample)) ∧
    ix.marks.length = ix.bwt.length ∧ ix.marks.count true = ix.saSamples.length ∧
    KeptPositionsCorrect ix

/-- The transform's box assumption, the text ends with one `$` found nowhere else, read on the
column: the sentinel, `0`, stands in the column exactly once. -/
def SentinelOnce (ix : FMIndex) : Prop := ix.bwt.count 0 = 1

/-- Not in the box: the stored `C` is the dense prefix sum the column determines over its
byte alphabet. -/
def SmallerLettersCounted (ix : FMIndex) : Prop := ix.c = cDense ix.bwt (byteAlphabet ix.bwt)

/-- Not in the box: `lf` from row `0` visits all `n` rows once before it returns, and never
leaves the table. -/
def WalkVisitsEveryRow (ix : FMIndex) : Prop :=
  ((List.range ix.bwt.length).map (fun j => (lf ix.bwt)^[j] 0)).Nodup ∧
    (lf ix.bwt)^[ix.bwt.length] 0 = 0 ∧ ∀ r < ix.bwt.length, lf ix.bwt r < ix.bwt.length

/-- Not in the box: for each kept position `0, sample, 2·sample, …` the row holding it is
listed, a marked row whose kept value is that position. -/
def KeptRowsListed (ix : FMIndex) : Prop :=
  ix.isaSamples.length = (ix.bwt.length + ix.sample - 1) / ix.sample ∧
    ∀ j (h : j < ix.isaSamples.length), ix.isaSamples[j] < ix.bwt.length ∧
      ix.marks[ix.isaSamples[j]]? = some true ∧
      ix.keptValueAt ix.isaSamples[j] = some (j * ix.sample)

/-- Not in the box: every letter of the rearranged text is a byte. -/
def LettersAreBytes (ix : FMIndex) : Prop := ∀ x ∈ ix.bwt, x < 256

/-- Not in the box: the interval between kept positions is at least one. -/
def RateAtLeastOne (ix : FMIndex) : Prop := 0 < ix.sample

end FMIndex

namespace BackwardSearch

/-- **Backward search's running state**: the suffix array whose rows it names, the pattern, the
part of it read so far (its last letters), and the stretch of rows `[lo, hi)` kept. -/
structure Stretch where
  /-- The text and its suffix array, whose rows the stretch names. -/
  index : SuffixArray
  /-- The pattern searched for. -/
  pattern : List Nat
  /-- The part of the pattern read so far: its last letters. -/
  read : List Nat
  /-- The stretch's first row. -/
  lo : Nat
  /-- One past the stretch's last row. -/
  hi : Nat
  /-- What has been read is the end of the pattern. -/
  read_suffix : read <:+ pattern

/-- The suffix at row `r` of a suffix array, for a row of the table. -/
@[simp] abbrev suffixAtRow (a : SuffixArray) (r : Nat) (h : r < a.positions.length) : List Nat :=
  suffix a.text a.positions[r]

/-- Box invariant 1: the rows kept so far are exactly the suffixes that start with the part of the
pattern read so far, and they are found from the rearranged letters alone. Row `r` is in
`[lo, hi)` iff it is a row of the table whose suffix begins with what has been read. The second
half is held by the signature: `backwardSearch` reads only the column and the `C` counts. -/
def StretchHoldsMatches (s : Stretch) : Prop :=
  ∀ r, (s.lo ≤ r ∧ r < s.hi) ↔ ∃ h : r < s.index.positions.length,
    s.read <+: suffixAtRow s.index r h

end BackwardSearch

/-! ## The contract

`Ops` names the operations the two boxes speak of; `Contract` is what they owe. `FMIndex.contract`
proves the library's operations meet it. -/

namespace FMIndex

/-- The texts an FM-index is built for: bytes, none of them the sentinel `0`, which the build
appends. -/
def PositiveBytes (u : List Nat) : Prop := ∀ x ∈ u, 0 < x ∧ x < 256

/-- The operations the boxes speak of: the occurrence finder (build, locate, and the invariant),
count, and versions of count and locate that count their steps (backward steps for count, LF
steps for locate). -/
structure Ops where
  /-- Build an index of a text. -/
  build : List Nat → FMIndex
  /-- Where each match starts. -/
  search : FMIndex → List Nat → List Nat
  /-- The design's invariants. -/
  Valid : FMIndex → Prop
  /-- How many times a fragment occurs. -/
  count : FMIndex → List Nat → Nat
  /-- Count, counting backward steps. -/
  countM : FMIndex → List Nat → TimeM ℕ Nat
  /-- Locate, counting LF steps. -/
  locateM : FMIndex → List Nat → TimeM ℕ (List Nat)
  /-- The counting versions answer as the operations do, so the costs are of the operations. -/
  counted : ∀ ix p, (countM ix p).ret = count ix p ∧ (locateM ix p).ret = search ix p

/-- The operations as an occurrence finder, answering about `FMIndex.text`. -/
def Ops.finder (o : Ops) : Occurrences FMIndex where
  build := o.build
  text := FMIndex.text
  search := o.search
  Valid := o.Valid

/-- Promise: how many times a fragment occurs, on every valid index. -/
def Ops.CountsMatches (o : Ops) : Prop :=
  ∀ ix, o.Valid ix → ∀ p, o.count ix p = (occurrenceList ix.text p).length

/-- Promise: every start position, each exactly once, in no particular order, on every
text of bytes without `$`. The parts: every start position, `every`; each exactly once,
`once_each`; and nothing else, `nothing_else`; in no particular order: none is asked; every such
text builds a valid index answering about it, `valid_build`, `text_build`. -/
def Ops.LocatesMatches (o : Ops) : Prop :=
  o.finder.Promise PositiveBytes

/-- **A legal FM-index**: box invariant 2, the transform's assumption, then pieces not in the box.
Box invariant 1 is on backward search's state, not on the index. -/
def Valid (ix : FMIndex) : Prop :=
  PositionsKept ix ∧ SentinelOnce ix ∧ SmallerLettersCounted ix ∧ WalkVisitsEveryRow ix ∧
    KeptRowsListed ix ∧ LettersAreBytes ix ∧ RateAtLeastOne ix

/-- **The FM-index's contract**, the part of both boxes Lean checks, one field per box field and one
conjunct per box line. Costs count the steps the counting operations count themselves. -/
structure Contract (o : Ops) : Prop where
  -- Goal: search the rearranged text directly, without rebuilding the text. Say where each match
  -- starts, without keeping the suffix array.
  /-- Promise: how many times a fragment occurs, and where each match starts. -/
  promise :
    o.CountsMatches ∧   -- how many times a fragment occurs
    o.LocatesMatches    -- every start position, each exactly once
  -- Idea: find the pattern from its end: first the suffixes that start with its last letter,
  -- then those that start with its last two letters, and so on, until the whole pattern. Keep a
  -- few positions, and walk to the nearest one.
  /-- Invariants: the boxes' two, in box order, then pieces not in the box. -/
  invariants : ∀ ix, o.Valid ix ↔
    -- 1. the rows kept are the suffixes that start with what was read: on backward search's
    --    state, not the index, `BackwardSearch.StretchHoldsMatches`, proved kept by the search
    PositionsKept ix ∧          -- 2. at fixed intervals, a row keeps its own position
    SentinelOnce ix ∧           -- not in the box: one `$` in the column
    SmallerLettersCounted ix ∧  -- not in the box: the stored `C`
    WalkVisitsEveryRow ix ∧     -- not in the box: `lf` visits every row once
    KeptRowsListed ix ∧         -- not in the box: the row of each kept position
    LettersAreBytes ix ∧        -- not in the box: the letters are bytes
    RateAtLeastOne ix           -- not in the box: the interval is at least one
  /-- Cost: two counts per letter of the fragment; each match, fewer steps than the interval. -/
  cost :
    (∀ ix, o.Valid ix → ∀ p, (o.countM ix p).time ≤ p.length) ∧  -- count: backward steps
    (∀ ix, o.Valid ix → ∀ p,
      (o.locateM ix p).time ≤ o.count ix p * (ix.sample - 1))     -- locate: LF steps
    -- one kept position per interval: invariant 2, `PositionsKept`
  -- Assumes: the fragment has no `$`. One that does gets zero matches, since `$` only marks the
  -- end of the text.

end FMIndex

end AlgoDesign.Strings
