/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie
public import AlgoDesign.Strings.Patricia.Sorted

/-!
# Trie and Patricia: deciding the validity predicates
`Bool`-valued mirrors of the Trie and Patricia validity predicates, each proved equivalent to its
`Prop`, so they can be evaluated on a concrete tree.
-/

@[expose] public section

namespace AlgoDesign.Strings.Decide

variable {α : Type}

/-! ## The trie -/

mutual

/-- `Bool` mirror of `Trie.DistinctLetters`. -/
def distinctLettersB : Trie α → Bool
  | .node _ cs => decide ((cs.map (·.1)).Nodup) && distinctLettersChildrenB cs

/-- `Bool` mirror of `Trie.DistinctLettersChildren`. -/
def distinctLettersChildrenB : List (Nat × Trie α) → Bool
  | [] => true
  | p :: rest => distinctLettersB p.2 && distinctLettersChildrenB rest

end

mutual

/-- `Bool` mirror of `Trie.NoDeadBranchesNode`: a childless node carries a value. -/
def noDeadBranchesNodeB : Trie α → Bool
  | .node v cs => (!cs.isEmpty || v.isSome) && noDeadBranchesChildrenB cs

/-- `Bool` mirror of `Trie.NoDeadBranchesChildren`. -/
def noDeadBranchesChildrenB : List (Nat × Trie α) → Bool
  | [] => true
  | p :: rest => noDeadBranchesNodeB p.2 && noDeadBranchesChildrenB rest

end

/-- `Bool` mirror of `Trie.NoDeadBranches`: the root is exempt, as in the library. -/
def noDeadBranchesB : Trie α → Bool
  | .node _ cs => noDeadBranchesChildrenB cs

/-- `Bool` mirror of `Trie.Valid`. -/
def trieValidB (t : Trie α) : Bool := distinctLettersB t && noDeadBranchesB t

mutual

theorem distinctLettersB_iff : (t : Trie α) → (distinctLettersB t = true ↔ Trie.DistinctLetters t)
  | .node v cs => by
      simp [distinctLettersB, Trie.DistinctLetters, distinctLettersChildrenB_iff cs]

theorem distinctLettersChildrenB_iff :
    (cs : List (Nat × Trie α)) →
      (distinctLettersChildrenB cs = true ↔ Trie.DistinctLettersChildren cs)
  | [] => by simp [distinctLettersChildrenB, Trie.DistinctLettersChildren]
  | p :: rest => by
      simp [distinctLettersChildrenB, Trie.DistinctLettersChildren, distinctLettersB_iff p.2,
          distinctLettersChildrenB_iff rest]

end

mutual

theorem noDeadBranchesNodeB_iff : (t : Trie α) →
    (noDeadBranchesNodeB t = true ↔ Trie.NoDeadBranchesNode t)
  | .node v cs => by
      cases v <;> cases cs <;>
        simp [noDeadBranchesNodeB, Trie.NoDeadBranchesNode, noDeadBranchesChildrenB_iff]

theorem noDeadBranchesChildrenB_iff :
    (cs : List (Nat × Trie α)) →
        (noDeadBranchesChildrenB cs = true ↔ Trie.NoDeadBranchesChildren cs)
  | [] => by simp [noDeadBranchesChildrenB, Trie.NoDeadBranchesChildren]
  | p :: rest => by
      simp [noDeadBranchesChildrenB, Trie.NoDeadBranchesChildren, noDeadBranchesNodeB_iff p.2,
        noDeadBranchesChildrenB_iff rest]

end

theorem noDeadBranchesB_iff (t : Trie α) : noDeadBranchesB t = true ↔ Trie.NoDeadBranches t := by
  cases t with
  | node v cs => simp [noDeadBranchesB, Trie.NoDeadBranches, noDeadBranchesChildrenB_iff cs]

/-- The mirror decides the invariant `Trie.valid_insert` and `Trie.valid_remove` keep. -/
theorem trieValidB_iff (t : Trie α) : trieValidB t = true ↔ Trie.Valid t := by
  simp [trieValidB, Trie.Valid, distinctLettersB_iff, noDeadBranchesB_iff]

/-! ## The Patricia tree -/

mutual

/-- `Bool` mirror of `Patricia.DistinctFirstLetters`, on `head?` as the library states it. -/
def distinctFirstLettersB : Patricia α → Bool
  | .node _ cs => decide ((cs.map (·.1.head?)).Nodup) && distinctFirstLettersChildrenB cs

/-- `Bool` mirror of `Patricia.DistinctFirstLettersChildren`. -/
def distinctFirstLettersChildrenB : List (List Nat × Patricia α) → Bool
  | [] => true
  | p :: rest => distinctFirstLettersB p.2 && distinctFirstLettersChildrenB rest

end

mutual

/-- `Bool` mirror of `Patricia.SortedHeads`. -/
def sortedHeadsB : Patricia α → Bool
  | .node _ cs =>
      decide (cs.Pairwise (fun e f => Patricia.headSym e < Patricia.headSym f)) &&
        sortedHeadsAuxB cs

/-- `Bool` mirror of `Patricia.SortedHeadsAux`. -/
def sortedHeadsAuxB : List (List Nat × Patricia α) → Bool
  | [] => true
  | p :: rest => sortedHeadsB p.2 && sortedHeadsAuxB rest

end

mutual

/-- `Bool` mirror of `Patricia.BranchesUnlessWordEndsNode`. -/
def branchesUnlessWordEndsNodeB : Patricia α → Bool
  | .node v cs => (v.isSome || decide (2 ≤ cs.length)) && branchesUnlessWordEndsChildrenB cs

/-- `Bool` mirror of `Patricia.BranchesUnlessWordEndsChildren`. -/
def branchesUnlessWordEndsChildrenB : List (List Nat × Patricia α) → Bool
  | [] => true
  | p :: rest => branchesUnlessWordEndsNodeB p.2 && branchesUnlessWordEndsChildrenB rest

end

/-- `Bool` mirror of `Patricia.BranchesUnlessWordEnds`: the root is exempt, as in the library. -/
def branchesUnlessWordEndsB : Patricia α → Bool
  | .node _ cs => branchesUnlessWordEndsChildrenB cs

mutual

/-- `Bool` mirror of `Patricia.NoEmptyBranches`. -/
def noEmptyBranchesNodeB : Patricia α → Bool
  | .node _ cs => noEmptyBranchesChildrenB cs

/-- `Bool` mirror of `Patricia.NoEmptyBranchesChildren`. -/
def noEmptyBranchesChildrenB : List (List Nat × Patricia α) → Bool
  | [] => true
  | p :: rest => !p.1.isEmpty && noEmptyBranchesNodeB p.2 && noEmptyBranchesChildrenB rest

end

/-- `Bool` mirror of `Patricia.NoEmptyBranches`. -/
def noEmptyBranchesB (t : Patricia α) : Bool := noEmptyBranchesNodeB t

/-- `Bool` mirror of `Patricia.Valid`, its pieces in the same order. -/
def patriciaValidB (t : Patricia α) : Bool :=
  distinctFirstLettersB t && branchesUnlessWordEndsB t && noEmptyBranchesB t

mutual

theorem distinctFirstLettersB_iff :
    (t : Patricia α) → (distinctFirstLettersB t = true ↔ Patricia.DistinctFirstLetters t)
  | .node v cs => by
      simp [distinctFirstLettersB, Patricia.DistinctFirstLetters,
        distinctFirstLettersChildrenB_iff cs]

theorem distinctFirstLettersChildrenB_iff :
    (cs : List (List Nat × Patricia α)) →
      (distinctFirstLettersChildrenB cs = true ↔ Patricia.DistinctFirstLettersChildren cs)
  | [] => by simp [distinctFirstLettersChildrenB, Patricia.DistinctFirstLettersChildren]
  | p :: rest => by
      simp [distinctFirstLettersChildrenB, Patricia.DistinctFirstLettersChildren,
        distinctFirstLettersB_iff p.2, distinctFirstLettersChildrenB_iff rest]

end

mutual

theorem sortedHeadsB_iff :
    (t : Patricia α) → (sortedHeadsB t = true ↔ Patricia.SortedHeads t)
  | .node v cs => by
      simp [sortedHeadsB, Patricia.SortedHeads, sortedHeadsAuxB_iff cs]

theorem sortedHeadsAuxB_iff :
    (cs : List (List Nat × Patricia α)) →
      (sortedHeadsAuxB cs = true ↔ Patricia.SortedHeadsAux cs)
  | [] => by simp [sortedHeadsAuxB, Patricia.SortedHeadsAux]
  | p :: rest => by
      simp [sortedHeadsAuxB, Patricia.SortedHeadsAux, sortedHeadsB_iff p.2,
        sortedHeadsAuxB_iff rest]

end

mutual

theorem branchesUnlessWordEndsNodeB_iff :
    (t : Patricia α) →
        (branchesUnlessWordEndsNodeB t = true ↔ Patricia.BranchesUnlessWordEndsNode t)
  | .node v cs => by
      cases v <;>
        simp [branchesUnlessWordEndsNodeB, Patricia.BranchesUnlessWordEndsNode,
            branchesUnlessWordEndsChildrenB_iff cs]

theorem branchesUnlessWordEndsChildrenB_iff :
    (cs : List (List Nat × Patricia α)) →
      (branchesUnlessWordEndsChildrenB cs = true ↔ Patricia.BranchesUnlessWordEndsChildren cs)
  | [] => by simp [branchesUnlessWordEndsChildrenB, Patricia.BranchesUnlessWordEndsChildren]
  | p :: rest => by
      simp [branchesUnlessWordEndsChildrenB, Patricia.BranchesUnlessWordEndsChildren,
          branchesUnlessWordEndsNodeB_iff p.2,
        branchesUnlessWordEndsChildrenB_iff rest]

end

theorem branchesUnlessWordEndsB_iff (t : Patricia α) :
    branchesUnlessWordEndsB t = true ↔ Patricia.BranchesUnlessWordEnds t := by
  cases t with
  | node v cs => simp [branchesUnlessWordEndsB, Patricia.BranchesUnlessWordEnds,
      branchesUnlessWordEndsChildrenB_iff cs]

mutual

theorem noEmptyBranchesNodeB_iff :
    (t : Patricia α) → (noEmptyBranchesNodeB t = true ↔ Patricia.NoEmptyBranches t)
  | .node v cs => by
      simp [noEmptyBranchesNodeB, Patricia.NoEmptyBranches, noEmptyBranchesChildrenB_iff cs]

theorem noEmptyBranchesChildrenB_iff :
    (cs : List (List Nat × Patricia α)) →
      (noEmptyBranchesChildrenB cs = true ↔ Patricia.NoEmptyBranchesChildren cs)
  | [] => by simp [noEmptyBranchesChildrenB, Patricia.NoEmptyBranchesChildren]
  | p :: rest => by
      simp [noEmptyBranchesChildrenB, Patricia.NoEmptyBranchesChildren,
        noEmptyBranchesNodeB_iff p.2, noEmptyBranchesChildrenB_iff rest, and_assoc]

end

theorem noEmptyBranchesB_iff (t : Patricia α) :
    noEmptyBranchesB t = true ↔ Patricia.NoEmptyBranches t :=
  noEmptyBranchesNodeB_iff t

/-- The mirror decides the invariant `Patricia.valid_insert`, `Patricia.valid_insertSorted` and
`Patricia.valid_remove` keep. -/
theorem patriciaValidB_iff (t : Patricia α) : patriciaValidB t = true ↔ Patricia.Valid t := by
  simp [patriciaValidB, Patricia.Valid, distinctFirstLettersB_iff, branchesUnlessWordEndsB_iff,
    noEmptyBranchesB_iff, and_assoc]

end AlgoDesign.Strings.Decide

/-! ## The decisions

Each piece of `Trie.Valid` and `Patricia.Valid` is decidable through its proved `Bool` mirror, so
`decide` on a concrete tree says which piece fails. -/

namespace AlgoDesign.Strings

open AlgoDesign.Strings.Decide

instance {α : Type} (t : Trie α) : Decidable (Trie.DistinctLetters t) :=
  decidable_of_iff _ (distinctLettersB_iff t)

instance {α : Type} (t : Trie α) : Decidable (Trie.NoDeadBranches t) :=
  decidable_of_iff _ (noDeadBranchesB_iff t)

instance {α : Type} (t : Trie α) : Decidable (Trie.Valid t) :=
  decidable_of_iff _ (trieValidB_iff t)

instance {α : Type} (t : Patricia α) : Decidable (Patricia.DistinctFirstLetters t) :=
  decidable_of_iff _ (distinctFirstLettersB_iff t)

instance {α : Type} (t : Patricia α) : Decidable (Patricia.BranchesUnlessWordEnds t) :=
  decidable_of_iff _ (branchesUnlessWordEndsB_iff t)

instance {α : Type} (t : Patricia α) : Decidable (Patricia.NoEmptyBranches t) :=
  decidable_of_iff _ (noEmptyBranchesB_iff t)

instance {α : Type} (t : Patricia α) : Decidable (Patricia.Valid t) :=
  decidable_of_iff _ (patriciaValidB_iff t)

end AlgoDesign.Strings
