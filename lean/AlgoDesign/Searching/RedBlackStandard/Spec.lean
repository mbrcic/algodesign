/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Defs.LinearOrder
public import AlgoDesign.Searching.RangeQuery

/-!
# Standard red-black tree: the specification

Sources: the Search chapter, "Appendix: how the standard red-black tree relates to the
left-leaning"; Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), Ch. 13.

- Ordering → `Sorted` → `sorted_insert` (`Insert.lean`), `sorted_delete` (`Delete.lean`).
- CLRS property 2 → `RootBlack`; property 4 → `NoRedRed`; property 5 → `BlackHeightOk` →
  `valid_insert` (`Insert.lean`), `valid_delete` (`Delete.lean`); together `height_le_two_log`
  (`Balance.lean`). Properties 1 and 3 hold by the datatype.

Operations and proofs: `Basic.lean` (rotations, `bheight`, `size`, `height`), `Search.lean`,
`Insert.lean` (`insertSpec`), `Delete.lean` (`deleteSpec`), `Cost.lean` (search and insert),
`Rotations.lean` (at most two rotations per insert, three per delete).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- A node's color. -/
inductive Color where
  /-- Red. -/
  | red
  /-- Black. -/
  | black
  deriving Repr, DecidableEq

/-- A red-black tree of keys, each node colored. `leaf` is CLRS's NIL, implicitly black. -/
inductive RBTree (α : Type) : Type where
  /-- The empty tree — CLRS's NIL, implicitly black. -/
  | leaf : RBTree α
  /-- A node, colored, with a left subtree, a key, and a right subtree. -/
  | node (color : Color) (left : RBTree α) (key : α) (right : RBTree α) : RBTree α
  deriving Repr, DecidableEq

namespace RBTree

variable {α : Type}

/-- Is `a` a key of the tree? Same role as `BST.Mem`. -/
def Mem (a : α) : RBTree α → Prop
  | leaf => False
  | node _ l k r => Mem a l ∨ a = k ∨ Mem a r

/-- Every key in the tree satisfies `p`. Same role as `BST.All`. -/
def All (p : α → Prop) : RBTree α → Prop
  | leaf => True
  | node _ l k r => All p l ∧ p k ∧ All p r

variable [LinearOrder α]

omit [LinearOrder α] in
/-- The keys in order. -/
def toList : RBTree α → List α
  | leaf => []
  | node _ l k r => toList l ++ k :: toList r

/-- The keys are in order, as in `BST.Sorted`. -/
def Sorted : RBTree α → Prop
  | leaf => True
  | node _ l k r => All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r

/-- CLRS property 2: the root is black. A leaf counts as black. -/
def RootBlack : RBTree α → Prop
  | leaf => True
  | node c _ _ _ => c = .black

/-- Is this node (or leaf) black? Says nothing about its descendants. -/
def IsBlack : RBTree α → Prop
  | leaf => True
  | node c _ _ _ => c = .black

/-- CLRS property 4: a red node's children are both black. -/
def NoRedRed : RBTree α → Prop
  | leaf => True
  | node c l _ r => (c = .red → l.IsBlack ∧ r.IsBlack) ∧ NoRedRed l ∧ NoRedRed r

/-- The black-height of a tree if every root-to-leaf path agrees on it, `none` otherwise. `leaf`
counts as one black node (CLRS property 3). -/
def blackHeight : RBTree α → Option ℕ
  | leaf => some 1
  | node c l _ r => do
      let bl ← l.blackHeight
      let br ← r.blackHeight
      if bl = br then some (bl + if c = .black then 1 else 0) else none

/-- CLRS property 5: every root-to-leaf path has the same number of black nodes. -/
def BlackHeightOk (t : RBTree α) : Prop := t.blackHeight ≠ none

/-- **A legal red-black tree**: ordering plus CLRS properties 2, 4 and 5 (1 and 3 hold by the
datatype). -/
def Valid (t : RBTree α) : Prop := Sorted t ∧ RootBlack t ∧ NoRedRed t ∧ BlackHeightOk t

omit [LinearOrder α] in
instance decidableAll (p : α → Prop) [DecidablePred p] : ∀ t : RBTree α, Decidable (All p t)
  | leaf => inferInstanceAs (Decidable True)
  | node _ l k r =>
      haveI := decidableAll p l
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p k ∧ All p r))

instance decidableSorted : ∀ t : RBTree α, Decidable (Sorted t)
  | leaf => inferInstanceAs (Decidable True)
  | node _ l k r =>
      haveI := decidableSorted l
      haveI := decidableSorted r
      inferInstanceAs (Decidable (All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r))

instance decidableRootBlack : ∀ t : RBTree α, Decidable (RootBlack t)
  | leaf => inferInstanceAs (Decidable True)
  | node c _ _ _ => inferInstanceAs (Decidable (c = .black))

instance decidableIsBlack : ∀ t : RBTree α, Decidable (IsBlack t)
  | leaf => inferInstanceAs (Decidable True)
  | node c _ _ _ => inferInstanceAs (Decidable (c = .black))

instance decidableNoRedRed : ∀ t : RBTree α, Decidable (NoRedRed t)
  | leaf => inferInstanceAs (Decidable True)
  | node c l _ r =>
      haveI := decidableNoRedRed l
      haveI := decidableNoRedRed r
      inferInstanceAs (Decidable ((c = .red → l.IsBlack ∧ r.IsBlack) ∧ NoRedRed l ∧ NoRedRed r))

instance decidableBlackHeightOk (t : RBTree α) : Decidable (BlackHeightOk t) :=
  by unfold BlackHeightOk; infer_instance

instance decidableValid (t : RBTree α) : Decidable (Valid t) :=
  by unfold Valid; infer_instance

/-- **What any insertion of `a` owes**: the key set gains exactly `a`, and a legal tree stays
legal. -/
def InsertSpec (a : α) (before after : RBTree α) : Prop :=
  (∀ b, Mem b after ↔ (b = a ∨ Mem b before)) ∧ (Valid before → Valid after)

/-- **What any deletion of `a` owes**: the key set loses exactly `a`, and a legal tree stays
legal. -/
def DeleteSpec (a : α) (before after : RBTree α) : Prop :=
  (∀ b, Mem b after ↔ (b ≠ a ∧ Mem b before)) ∧ (Valid before → Valid after)

end RBTree

end AlgoDesign.Searching
