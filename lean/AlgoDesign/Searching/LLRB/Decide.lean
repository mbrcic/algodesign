/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Spec

/-! # LLRB: deciding the invariants

Each piece of `Valid`, and `Valid` itself, decides on a concrete tree, so `decide` checks a
small tree and a separate Lean–Rust check evaluates them. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace LLRB

variable {α : Type}

instance decidableAll (p : α → Prop) [DecidablePred p] : ∀ t : LLRB α, Decidable (All p t)
  | leaf => inferInstanceAs (Decidable True)
  | node _ l k r =>
      haveI := decidableAll p l
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p k ∧ All p r))

instance decidableIsRed : ∀ t : LLRB α, Decidable (IsRed t)
  | leaf => inferInstanceAs (Decidable False)
  | node c _ _ _ => inferInstanceAs (Decidable (c = .red))

variable [LinearOrder α]

instance decidableSorted : ∀ t : LLRB α, Decidable (Sorted t)
  | leaf => inferInstanceAs (Decidable True)
  | node _ l k r =>
      haveI := decidableSorted l
      haveI := decidableSorted r
      inferInstanceAs (Decidable (All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r))

instance decidableRootBlack : ∀ t : LLRB α, Decidable (RootBlack t)
  | leaf => inferInstanceAs (Decidable True)
  | node c _ _ _ => inferInstanceAs (Decidable (c = .black))

instance decidableLeftLeaning : ∀ t : LLRB α, Decidable (LeftLeaning t)
  | leaf => inferInstanceAs (Decidable True)
  | node _ l _ r =>
      haveI := decidableLeftLeaning l
      haveI := decidableLeftLeaning r
      inferInstanceAs (Decidable (¬ r.IsRed ∧ LeftLeaning l ∧ LeftLeaning r))

instance decidableNoRedRed : ∀ t : LLRB α, Decidable (NoRedRed t)
  | leaf => inferInstanceAs (Decidable True)
  | node c l _ r =>
      haveI := decidableNoRedRed l
      haveI := decidableNoRedRed r
      inferInstanceAs (Decidable ((c = .red → ¬ l.IsRed ∧ ¬ r.IsRed) ∧ NoRedRed l ∧ NoRedRed r))

instance decidableBlackHeightOk (t : LLRB α) : Decidable (BlackHeightOk t) :=
  by unfold BlackHeightOk; infer_instance

instance decidableValid (t : LLRB α) : Decidable (Valid t) :=
  inferInstanceAs (Decidable
    (Sorted t ∧ RootBlack t ∧ LeftLeaning t ∧ NoRedRed t ∧ BlackHeightOk t))

end LLRB

end AlgoDesign.Searching
