/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Nodup

/-!
# Treap: the specification

Sources: the Search chapter, "Self-adjusting and learned structures"; Motwani and Raghavan,
*Randomized Algorithms*, §8.1–8.2; Seidel and Aragon, rotate-up insertion.

- Invariant → `Sorted`, a BST on keys → `sorted_insert` (`Insert.lean`), `sorted_delete`
  (`Delete.lean`).
- Invariant → `HeapOrdered`, a max-heap on priorities → `heapOrdered_insert` (`Insert.lean`),
  `heapOrdered_delete` (`Delete.lean`). `Valid` is both: `valid_insert`, `valid_delete`.
- With distinct keys and distinct priorities, exactly one valid treap holds a given set of pairs →
  `existsUnique_of_nodup`, `eq_of_insertSpec`, `eq_of_deleteSpec` (`Unique.lean`).

Operations and proofs: `Split.lean` (`split`), `Join.lean` (`join`), `Insert.lean` (rotate-up,
`insertSpec`), `Delete.lean` (rotate-down, `deleteSpec`; `delete_eq_deleteJoin`). The expected
`O(log n)` height under random priorities is not proved.
-/

@[expose] public section

namespace AlgoDesign.Searching

/-- A treap: a binary tree of keys, each node also carrying a `ℕ` priority. -/
inductive Treap (α : Type) : Type where
  /-- The empty tree. -/
  | leaf : Treap α
  /-- A node with a left subtree, a key, a priority, and a right subtree. -/
  | node (left : Treap α) (key : α) (priority : ℕ) (right : Treap α) : Treap α
  deriving Repr, DecidableEq

namespace Treap

variable {α : Type}

/-- `a` is a key of the tree. -/
def Mem (a : α) : Treap α → Prop
  | leaf => False
  | node l k _ r => Mem a l ∨ a = k ∨ Mem a r

/-- Every key in the tree satisfies `p`. -/
def All (p : α → Prop) : Treap α → Prop
  | leaf => True
  | node l k _ r => All p l ∧ p k ∧ All p r

/-- Every priority in the tree satisfies `q`. -/
def AllPriority (q : ℕ → Prop) : Treap α → Prop
  | leaf => True
  | node l _ p r => AllPriority q l ∧ q p ∧ AllPriority q r

/-- The max-heap invariant: every priority below a node is `≤` the node's. Stated for whole
subtrees, not only children, since rotations and `join` move whole subtrees. -/
def HeapOrdered : Treap α → Prop
  | leaf => True
  | node l _ p r => AllPriority (· ≤ p) l ∧ AllPriority (· ≤ p) r ∧ HeapOrdered l ∧ HeapOrdered r

variable [LinearOrder α]

/-- The BST invariant: every key in the left subtree is less than the node's key, every key in the
right subtree greater, throughout. -/
def Sorted : Treap α → Prop
  | leaf => True
  | node l k _ r => All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r

/-- A legal treap: sorted on keys and heap-ordered on priorities. -/
def Valid (t : Treap α) : Prop := Sorted t ∧ HeapOrdered t

omit [LinearOrder α] in
instance decidableAll (p : α → Prop) [DecidablePred p] : ∀ t : Treap α, Decidable (All p t)
  | leaf => inferInstanceAs (Decidable True)
  | node l k _ r =>
      haveI := decidableAll p l
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p k ∧ All p r))

omit [LinearOrder α] in
instance decidableAllPriority (q : ℕ → Prop) [DecidablePred q] :
    ∀ t : Treap α, Decidable (AllPriority q t)
  | leaf => inferInstanceAs (Decidable True)
  | node l _ p r =>
      haveI := decidableAllPriority q l
      haveI := decidableAllPriority q r
      inferInstanceAs (Decidable (AllPriority q l ∧ q p ∧ AllPriority q r))

omit [LinearOrder α] in
instance decidableHeapOrdered : ∀ t : Treap α, Decidable (HeapOrdered t)
  | leaf => inferInstanceAs (Decidable True)
  | node l _ p r =>
      haveI := decidableHeapOrdered l
      haveI := decidableHeapOrdered r
      inferInstanceAs (Decidable
        (AllPriority (· ≤ p) l ∧ AllPriority (· ≤ p) r ∧ HeapOrdered l ∧ HeapOrdered r))

instance decidableSorted : ∀ t : Treap α, Decidable (Sorted t)
  | leaf => inferInstanceAs (Decidable True)
  | node l k _ r =>
      haveI := decidableSorted l
      haveI := decidableSorted r
      inferInstanceAs (Decidable (All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r))

instance decidableValid (t : Treap α) : Decidable (Valid t) :=
  by unfold Valid; infer_instance

/-- Look up the priority stored at key `a`, following the BST search path. -/
def priorityOf (a : α) : Treap α → Option ℕ
  | leaf => none
  | node l k p r => if a < k then priorityOf a l else if k < a then priorityOf a r else some p

/-! ## What an update owes

The obligations name priorities as well as keys: the priorities determine the tree. -/

/-- The insertion obligation: the key set gains exactly `a`; no other key's priority changes, and a
key already present keeps its priority; a key that was absent ends up at the priority it was given;
validity is preserved. With distinct priorities it admits one tree (`eq_of_insertSpec`). -/
def InsertSpec (a : α) (pr : ℕ) (before after : Treap α) : Prop :=
  (∀ b, Mem b after ↔ (b = a ∨ Mem b before)) ∧
  (∀ b, (b ≠ a ∨ Mem a before) → priorityOf b after = priorityOf b before) ∧
  (¬ Mem a before → priorityOf a after = some pr) ∧
  (Valid before → Valid after)

/-- The deletion obligation: the key set loses exactly `a`; no surviving key's priority changes;
validity is preserved. With distinct priorities it admits one tree (`eq_of_deleteSpec`); on a tie
it does not fix which child is lifted. -/
def DeleteSpec (a : α) (before after : Treap α) : Prop :=
  (∀ b, Mem b after ↔ (b ≠ a ∧ Mem b before)) ∧
  (∀ b, b ≠ a → priorityOf b after = priorityOf b before) ∧
  (Valid before → Valid after)

end Treap

end AlgoDesign.Searching
