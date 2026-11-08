/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic

/-!
# Records and the corpus: the specification

Sources: the Strings chapter, "From a hit to the whole quote"; Navarro, *Compact Data Structures*,
§4.2–4.3, with the bitvector marking record starts.

The corpus joins many records into one text, a separator after each, and marks where each record
starts in a bitvector. `recordOf` turns a hit in the joined text into the number of the record
holding it, with one `rank`; `recordBounds` turns the number into the record's start and end,
with two `select`s. `Corpus.find` lists the records that contain a fragment, each once. A
supporting structure with no box of its own: `FindSpec` and `QuoteSpec` say what finding and
quoting owe.

- Not in the box → `FirstRecordAtStart` (`Records.Valid`) →
  `recordBounds_contains_of_firstRecordAtStart` (`Quote.lean`).
- Not in the box → `SentinelBelowSeparator`, `SentinelBelowRecords`,
  `SeparatorOutsideRecords` (`Corpus.WellFormed`) → `terminated_text`, `findObligation`
  (`Corpus.lean`).

Operations and proofs: `Quote.lean` (`recordOf`, `recordBounds`, `recordBounds_contains`),
`Corpus.lean` (`Corpus.find`, `findObligation` for `FindSpec`, `quoteObligation` for `QuoteSpec`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Records

/-- Not in the box: if any record starts, one starts at position 0. The guard admits the
empty corpus, whose bit vector is `[false]`. -/
def FirstRecordAtStart (b : List Bool) : Prop := true ∈ b → b.head? = some true

instance decidableFirstRecordAtStart (b : List Bool) : Decidable (FirstRecordAtStart b) :=
  by unfold FirstRecordAtStart; infer_instance

/-- The start bits' invariant: `FirstRecordAtStart`. -/
def Valid (b : List Bool) : Prop := FirstRecordAtStart b

instance decidableValid (b : List Bool) : Decidable (Valid b) :=
  by unfold Valid; infer_instance

end Records

namespace Corpus

/-- The records joined into one text: each record followed by `sep`, except the last, which is
followed by the sentinel `s`. The empty corpus is the sentinel alone. -/
def text (sep s : Nat) : List (List Nat) → List Nat
  | [] => [s]
  | [r] => r ++ [s]
  | r :: rs => r ++ [sep] ++ text sep s rs

/-- The record starts, one bit per position of `text`: a record of length `L` spans `L + 1`
positions, the first of them set. -/
def starts : List (List Nat) → List Bool
  | [] => [false]
  | [r] => true :: List.replicate r.length false
  | r :: rs => (true :: List.replicate r.length false) ++ starts rs

/-- Not in the box: the sentinel sorts below the separator. -/
def SentinelBelowSeparator (sep s : Nat) : Prop := s < sep

/-- Not in the box: the sentinel sorts below every byte of every record. -/
def SentinelBelowRecords (s : Nat) (rs : List (List Nat)) : Prop := ∀ r ∈ rs, ∀ x ∈ r, s < x

/-- Not in the box: no record holds the separator, which keeps a match inside one record. -/
def SeparatorOutsideRecords (sep : Nat) (rs : List (List Nat)) : Prop :=
  ∀ r ∈ rs, ∀ x ∈ r, x ≠ sep

/-- The corpus the build accepts, an input condition rather than an invariant. -/
def WellFormed (sep s : Nat) (rs : List (List Nat)) : Prop :=
  SentinelBelowSeparator sep s ∧ SentinelBelowRecords s rs ∧ SeparatorOutsideRecords sep rs

/-- What a find owes: for every fragment, the numbers of the records that contain it, ascending,
each once. -/
def FindSpec (rs : List (List Nat)) (ans : List Nat → List Nat) : Prop :=
  ∀ p, ans p =
    (List.range rs.length).filter (fun id => decide (∃ h : id < rs.length, p <:+: rs[id]))

/-- What a quote owes: for every record, the text from its start up to the byte that closes it is
that record, whole. -/
def QuoteSpec (rs : List (List Nat)) (txt : List Nat) (bounds : Nat → Nat × Nat) : Prop :=
  ∀ id (h : id < rs.length), txt.extract (bounds id).1 ((bounds id).2 - 1) = rs[id]

instance (sep s : Nat) : Decidable (SentinelBelowSeparator sep s) :=
  by unfold SentinelBelowSeparator; infer_instance

instance (s : Nat) (rs : List (List Nat)) : Decidable (SentinelBelowRecords s rs) :=
  by unfold SentinelBelowRecords; infer_instance

instance (sep : Nat) (rs : List (List Nat)) : Decidable (SeparatorOutsideRecords sep rs) :=
  by unfold SeparatorOutsideRecords; infer_instance

instance (sep s : Nat) (rs : List (List Nat)) : Decidable (WellFormed sep s rs) :=
  inferInstanceAs (Decidable
    (SentinelBelowSeparator sep s ∧ SentinelBelowRecords s rs ∧ SeparatorOutsideRecords sep rs))

end Corpus

end AlgoDesign.Strings
