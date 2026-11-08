/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Spec

/-!
# 2-3 trees, and the LLRB as their binary encoding: the specification

Sources: the Search chapter, "Where LLRB actually comes from"; Sedgewick and Wayne, *Algorithms*
(4th ed.), §3.3; Nipkow et al., *Functional Algorithms, Verified!*, the 2-3 tree chapter.

- Key order → `Sorted` → `sorted_insert` (`Insert.lean`), `sorted_delete` (`Delete.lean`).
- All leaves at one depth → `SameDepth` → `sameDepth_insert` (`Insert.lean`), `sameDepth_delete`
  (`Delete.lean`); the same as LLRB black balance: `sameDepth_iff_blackHeightOk`
  (`Encoding.lean`).
- The encoding `toLlrb` is a bijection onto `LLRBColors` trees → `ofLlrb_toLlrb`,
  `toLlrb_injective`, `llrbColors_toLlrb`, `exists_twoThree_of_llrbColors` (`Encoding.lean`).

Operations and proofs: `Encoding.lean` (the bijection, keys through it), `Insert.lean` (the 2-3
insert; `toLlrb_insert`: `LLRB.insert` computes it), `Delete.lean` (the 2-3 delete),
`DeleteLLRB.lean` (`deleteTop_toLlrb`: `LLRB.deleteTop` leaves a balanced sorted 2-3 tree with the
same keys and height as the 2-3 delete, not always the same tree).
-/

@[expose] public section

namespace AlgoDesign.Searching

/-- A 2-3 tree: every internal node holds one key and two children, or two keys and three. -/
inductive T23 (α : Type) : Type where
  /-- The empty tree. -/
  | leaf : T23 α
  /-- A 2-node: one key, two children. -/
  | two (l : T23 α) (k : α) (r : T23 α) : T23 α
  /-- A 3-node: keys `a < b`, children below `a`, between them, and above `b`. -/
  | three (l : T23 α) (a : α) (m : T23 α) (b : α) (r : T23 α) : T23 α

namespace T23

variable {α : Type}

/-- Is `x` a key of the tree? -/
def Mem (x : α) : T23 α → Prop
  | leaf => False
  | two l k r => Mem x l ∨ x = k ∨ Mem x r
  | three l a m b r => Mem x l ∨ x = a ∨ Mem x m ∨ x = b ∨ Mem x r

/-- Every key in the tree satisfies `p`. -/
def All (p : α → Prop) : T23 α → Prop
  | leaf => True
  | two l k r => All p l ∧ p k ∧ All p r
  | three l a m b r => All p l ∧ p a ∧ All p m ∧ p b ∧ All p r

variable [LinearOrder α]

/-- The keys in order. -/
def toList : T23 α → List α
  | leaf => []
  | two l k r => toList l ++ k :: toList r
  | three l a m b r => toList l ++ a :: (toList m ++ b :: toList r)

/-- Key order: a 3-node's keys are in order, and each child's keys lie in the interval its
position leaves them. -/
def Sorted : T23 α → Prop
  | leaf => True
  | two l k r => All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r
  | three l a m b r =>
      a < b ∧ All (· < a) l ∧ All (fun x => a < x ∧ x < b) m ∧ All (b < ·) r ∧
        Sorted l ∧ Sorted m ∧ Sorted r

/-- Height, counted down the leftmost path; in a balanced 2-3 tree every path has it. -/
def height : T23 α → ℕ
  | leaf => 0
  | two l _ _ => height l + 1
  | three l _ _ _ _ => height l + 1

/-- All leaves at the same depth. -/
def SameDepth : T23 α → Prop
  | leaf => True
  | two l _ r => height l = height r ∧ SameDepth l ∧ SameDepth r
  | three l _ m _ r =>
      height l = height m ∧ height m = height r ∧ SameDepth l ∧ SameDepth m ∧ SameDepth r

/-- **A legal 2-3 tree**: key order and balance. That every node holds one key and two children
or two keys and three is the type itself. -/
def Valid (t : T23 α) : Prop := Sorted t ∧ SameDepth t

omit [LinearOrder α] in
instance decidableAll (p : α → Prop) [DecidablePred p] : ∀ t : T23 α, Decidable (All p t)
  | leaf => inferInstanceAs (Decidable True)
  | two l k r =>
      haveI := decidableAll p l
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p k ∧ All p r))
  | three l a m b r =>
      haveI := decidableAll p l
      haveI := decidableAll p m
      haveI := decidableAll p r
      inferInstanceAs (Decidable (All p l ∧ p a ∧ All p m ∧ p b ∧ All p r))

instance decidableSorted : ∀ t : T23 α, Decidable (Sorted t)
  | leaf => inferInstanceAs (Decidable True)
  | two l k r =>
      haveI := decidableSorted l
      haveI := decidableSorted r
      inferInstanceAs (Decidable (All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r))
  | three l a m b r =>
      haveI := decidableSorted l
      haveI := decidableSorted m
      haveI := decidableSorted r
      inferInstanceAs (Decidable (a < b ∧ All (· < a) l ∧ All (fun x => a < x ∧ x < b) m ∧
        All (b < ·) r ∧ Sorted l ∧ Sorted m ∧ Sorted r))

instance decidableSameDepth : ∀ t : T23 α, Decidable (SameDepth t)
  | leaf => inferInstanceAs (Decidable True)
  | two l _ r =>
      haveI := decidableSameDepth l
      haveI := decidableSameDepth r
      inferInstanceAs (Decidable (height l = height r ∧ SameDepth l ∧ SameDepth r))
  | three l _ m _ r =>
      haveI := decidableSameDepth l
      haveI := decidableSameDepth m
      haveI := decidableSameDepth r
      inferInstanceAs (Decidable (height l = height m ∧ height m = height r ∧ SameDepth l ∧
        SameDepth m ∧ SameDepth r))

instance decidableValid (t : T23 α) : Decidable (Valid t) :=
  by unfold Valid; infer_instance

/-- The color conditions of a legal LLRB, without key order: `LLRB.Valid` minus `Sorted`, piece
for piece. -/
def LLRBColors (u : LLRB α) : Prop :=
  LLRB.RootBlack u ∧ LLRB.LeftLeaning u ∧ LLRB.NoRedRed u ∧ LLRB.BlackHeightOk u

/-- The binary encoding. A 3-node's smaller key goes on a red link to the **left**, which is the
left-leaning convention; leaning right instead would be a second encoding of the same 3-node. -/
def toLlrb : T23 α → LLRB α
  | leaf => .leaf
  | two l k r => .node .black (toLlrb l) k (toLlrb r)
  | three l a m b r => .node .black (.node .red (toLlrb l) a (toLlrb m)) b (toLlrb r)

end T23

end AlgoDesign.Searching
