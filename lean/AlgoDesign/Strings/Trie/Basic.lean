/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Spec

/-!
# Trie: small facts the proofs share

Not the contract (that is `Spec.lean`'s `Valid`): how the per-node form of box invariant 3 gives the
invariant itself, and that the empty trie has it.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

theorem NoDeadBranchesNode.noDeadBranches {α : Type} {t : Trie α} (h : NoDeadBranchesNode t) :
    NoDeadBranches t := by
  cases t with
  | node v cs => exact h.2

theorem noDeadBranches_empty {α : Type} : NoDeadBranches (Trie.empty : Trie α) := trivial

end Trie

end AlgoDesign.Strings
