/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.FMIndex.Spec

/-!
# FM-index: deciding the invariant pieces

The stored index's pieces and `Valid`, and box invariant 1 on backward search's state, decided on
concrete values. `StretchHoldsMatches` quantifies over every row; rows at or past both `hi` and the
table's end are on neither side, so checking the rows below `hi` plus the table's length decides it
(`stretchHoldsMatches_iff_below`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace FMIndex

instance decidableKeptPositionsCorrect (ix : FMIndex) : Decidable (KeptPositionsCorrect ix) :=
  by unfold KeptPositionsCorrect; infer_instance

instance decidablePositionsKept (ix : FMIndex) : Decidable (PositionsKept ix) :=
  by unfold PositionsKept; infer_instance

instance decidableSentinelOnce (ix : FMIndex) : Decidable (SentinelOnce ix) :=
  by unfold SentinelOnce; infer_instance

instance decidableSmallerLettersCounted (ix : FMIndex) : Decidable (SmallerLettersCounted ix) :=
  by unfold SmallerLettersCounted; infer_instance

instance decidableWalkVisitsEveryRow (ix : FMIndex) : Decidable (WalkVisitsEveryRow ix) :=
  by unfold WalkVisitsEveryRow; infer_instance

instance decidableKeptRowsListed (ix : FMIndex) : Decidable (KeptRowsListed ix) :=
  by unfold KeptRowsListed; infer_instance

instance decidableLettersAreBytes (ix : FMIndex) : Decidable (LettersAreBytes ix) :=
  by unfold LettersAreBytes; infer_instance

instance decidableRateAtLeastOne (ix : FMIndex) : Decidable (RateAtLeastOne ix) :=
  by unfold RateAtLeastOne; infer_instance

instance decidableValid (ix : FMIndex) : Decidable (Valid ix) :=
  by unfold Valid; infer_instance

end FMIndex

namespace BackwardSearch

/-- Rows at or past both `hi` and the table's end are on neither side, so checking the rows below
`hi + n` decides `StretchHoldsMatches`. -/
theorem stretchHoldsMatches_iff_below (s : Stretch) :
    StretchHoldsMatches s ↔ ∀ r, r < s.hi + s.index.positions.length →
      ((s.lo ≤ r ∧ r < s.hi) ↔ ∃ h : r < s.index.positions.length,
        s.read <+: suffixAtRow s.index r h) := by
  refine ⟨fun h r _ => h r, fun h r => ?_⟩
  by_cases hr : r < s.hi + s.index.positions.length
  · exact h r hr
  · constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro ⟨h1, -⟩; omega

instance (s : Stretch) : Decidable (StretchHoldsMatches s) :=
  decidable_of_iff _ (stretchHoldsMatches_iff_below s).symm

end BackwardSearch

end AlgoDesign.Strings
