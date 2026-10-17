/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Spec

/-! # LSM-tree: deciding the invariants

Each piece of `Store.Valid`, and `Store.Valid` itself, decides on a concrete store, so `decide`
checks a small store and the Lean–Rust comparison evaluates them. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace Run

variable {α β : Type} [LinearOrder α]

instance (r : Run α β) : Decidable (Sorted r) := inferInstanceAs (Decidable (List.Pairwise _ r))

instance (r : Run α β) : Decidable (Clean r) :=
  inferInstanceAs (Decidable (∀ p ∈ r, p.2 ≠ none))

end Run

namespace LSM

variable {α β : Type} [LinearOrder α]

instance (sh : Shape) : Decidable sh.Usable :=
  inferInstanceAs (Decidable (1 ≤ sh.capacity ∧ 2 ≤ sh.ratio ∧ 1 ≤ sh.level0Runs))

namespace Store

instance decWithinBudgetFrom (sh : Shape) :
    ∀ (i : Nat) (ls : List (List (Run α β))), Decidable (WithinBudgetFrom sh i ls)
  | _, [] => isTrue trivial
  | _, [_] => isTrue trivial
  | i, l :: m :: rest =>
      have := decWithinBudgetFrom sh (i + 1) (m :: rest)
      inferInstanceAs (Decidable ((∀ r ∈ l.head?, r.length ≤ sh.budget i) ∧
        WithinBudgetFrom sh (i + 1) (m :: rest)))

instance (s : Store α β) : Decidable (RunsSorted s) :=
  inferInstanceAs (Decidable (Run.Sorted s.memtable ∧ ∀ r ∈ s.levels.flatten, Run.Sorted r))

instance (s : Store α β) : Decidable (FewRuns s) :=
  inferInstanceAs (Decidable ((s.levels.headD []).length ≤ s.shape.level0Runs ∧
    ∀ l ∈ s.levels.tail, l.length ≤ 1))

instance (s : Store α β) : Decidable (LevelsWithinBudget s) :=
  inferInstanceAs (Decidable (WithinBudgetFrom s.shape 1 s.levels.tail))

instance (s : Store α β) : Decidable (FewBatches s) :=
  inferInstanceAs (Decidable (FewRuns s ∧ LevelsWithinBudget s))

instance (s : Store α β) : Decidable (RunsNonEmpty s) :=
  inferInstanceAs (Decidable (∀ r ∈ s.levels.flatten, r ≠ []))

instance (s : Store α β) : Decidable (OldestRunClean s) :=
  inferInstanceAs (Decidable (∀ r ∈ s.levels.tail.flatten.getLast?, Run.Clean r))

instance (s : Store α β) : Decidable (ShapeUsable s) :=
  inferInstanceAs (Decidable s.shape.Usable)

instance (s : Store α β) : Decidable (Valid s) :=
  inferInstanceAs (Decidable (RunsSorted s ∧ FewBatches s ∧ RunsNonEmpty s ∧
    OldestRunClean s ∧ ShapeUsable s))

end Store

end LSM

end AlgoDesign.Searching
