/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Spec

/-! # B-tree: deciding the invariants

Each piece of `Valid`, and `Valid` itself, decides on a concrete tree, so `decide` checks a
small tree and the Lean–Rust comparison evaluates them. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace BTree

variable {α : Type} [LinearOrder α]

instance (bt : BTree α) : Decidable (KeysInOrder bt) :=
  by unfold KeysInOrder; infer_instance

mutual

/-- `OneMoreChild` decides on a concrete tree. -/
def decidableOneMoreChild : (bt : BTree α) → Decidable (OneMoreChild bt)
  | leaf _ => inferInstanceAs (Decidable True)
  | node ks cs =>
      haveI := decidableChildrenOneMoreChild cs
      inferInstanceAs (Decidable (cs.length = ks.length + 1 ∧ ChildrenOneMoreChild cs))

/-- `ChildrenOneMoreChild` decides on a concrete child list. -/
def decidableChildrenOneMoreChild : (cs : List (BTree α)) → Decidable (ChildrenOneMoreChild cs)
  | [] => inferInstanceAs (Decidable True)
  | c :: cs =>
      haveI := decidableOneMoreChild c
      haveI := decidableChildrenOneMoreChild cs
      inferInstanceAs (Decidable (OneMoreChild c ∧ ChildrenOneMoreChild cs))

end

instance (bt : BTree α) : Decidable (OneMoreChild bt) := decidableOneMoreChild bt

mutual

/-- `NodeHalfFull` decides on a concrete tree. -/
def decidableNodeHalfFull (deg : ℕ) : (bt : BTree α) → Decidable (NodeHalfFull deg bt)
  | leaf ks =>
      inferInstanceAs (Decidable (deg - 1 ≤ ks.length ∧ ks.length ≤ 2 * deg - 1))
  | node ks cs =>
      haveI := decidableChildrenHalfFull deg cs
      inferInstanceAs (Decidable (deg - 1 ≤ ks.length ∧ ks.length ≤ 2 * deg - 1 ∧
        ChildrenHalfFull deg cs))

/-- `ChildrenHalfFull` decides on a concrete child list. -/
def decidableChildrenHalfFull (deg : ℕ) : (cs : List (BTree α)) →
    Decidable (ChildrenHalfFull deg cs)
  | [] => inferInstanceAs (Decidable True)
  | c :: cs =>
      haveI := decidableNodeHalfFull deg c
      haveI := decidableChildrenHalfFull deg cs
      inferInstanceAs (Decidable (NodeHalfFull deg c ∧ ChildrenHalfFull deg cs))

end

instance (deg : ℕ) (bt : BTree α) : Decidable (NodeHalfFull deg bt) :=
  decidableNodeHalfFull deg bt

instance (deg : ℕ) (bt : BTree α) : Decidable (HalfFullToFull deg bt) :=
  by unfold HalfFullToFull; infer_instance

instance : (bt : BTree α) → Decidable (RootBranches bt)
  | leaf _ => inferInstanceAs (Decidable True)
  | node _ cs => inferInstanceAs (Decidable (2 ≤ cs.length))

instance (bt : BTree α) : Decidable (SameDepth bt) :=
  by unfold SameDepth; infer_instance

instance (deg : ℕ) (bt : BTree α) : Decidable (Valid deg bt) :=
  by unfold Valid; infer_instance

end BTree

end AlgoDesign.Searching
