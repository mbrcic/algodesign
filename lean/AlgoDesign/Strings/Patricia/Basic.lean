/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Spec

/-!
# Patricia: the box pieces as the proofs read them

Not the contract (that is `Spec.lean`'s `Valid`), but the readings of its pieces the proofs use:
`Valid` taken apart, a child list's pieces read edge by edge, and a node's pieces read as its own
subtree's.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

theorem Valid.distinctFirstLetters {α : Type} {t : Patricia α} (h : Valid t) :
    DistinctFirstLetters t := h.1

theorem Valid.branchesUnlessWordEnds {α : Type} {t : Patricia α} (h : Valid t) :
    BranchesUnlessWordEnds t := h.2.1

theorem Valid.noEmptyBranches {α : Type} {t : Patricia α} (h : Valid t) : NoEmptyBranches t :=
  h.2.2

/-- `NoEmptyBranchesChildren`, read edge by edge. -/
theorem noEmptyBranchesChildren_iff {α : Type} :
    (cs : List (List Nat × Patricia α)) →
      NoEmptyBranchesChildren cs ↔ ∀ e ∈ cs, e.1 ≠ [] ∧ NoEmptyBranches e.2
  | [] => by simp [NoEmptyBranchesChildren]
  | p :: rest => by
      simp only [NoEmptyBranchesChildren, noEmptyBranchesChildren_iff rest, List.mem_cons,
        forall_eq_or_imp, and_assoc]

/-- `BranchesUnlessWordEndsChildren`, read edge by edge. -/
theorem branchesUnlessWordEndsChildren_iff {α : Type} :
    (cs : List (List Nat × Patricia α)) →
      BranchesUnlessWordEndsChildren cs ↔ ∀ e ∈ cs, BranchesUnlessWordEndsNode e.2
  | [] => by simp [BranchesUnlessWordEndsChildren]
  | p :: rest => by
      simp only [BranchesUnlessWordEndsChildren, branchesUnlessWordEndsChildren_iff rest,
        List.mem_cons, forall_eq_or_imp]

/-- Every label in a child list with `NoEmptyBranchesChildren` is non-empty. -/
theorem NoEmptyBranchesChildren.labels_ne {α : Type} {cs : List (List Nat × Patricia α)}
    (h : NoEmptyBranchesChildren cs) : ∀ e ∈ cs, e.1 ≠ [] :=
  fun e he => ((noEmptyBranchesChildren_iff cs).mp h e he).1

/-- A node below the root that branches unless a word ends there makes a subtree that does: the
node condition is the root exemption's stronger form. -/
theorem BranchesUnlessWordEndsNode.root {α : Type} {t : Patricia α}
    (h : BranchesUnlessWordEndsNode t) : BranchesUnlessWordEnds t := by
  cases t with
  | node v cs => exact h.2

/-- The empty tree is `Valid`: the root is exempt from box lines 3 and 4, and it has no branches to
repeat a letter. -/
theorem valid_empty {α : Type} : Valid (.node none [] : Patricia α) :=
  ⟨⟨List.nodup_nil, trivial⟩, trivial, trivial⟩

end Patricia

end AlgoDesign.Strings
