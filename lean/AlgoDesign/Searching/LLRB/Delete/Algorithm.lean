/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Balance

/-!
# LLRB: the deletion algorithm

Sedgewick's recursive helpers `deleteMin` and `delete`, which push a red link down ahead of
themselves with `moveRedLeft`/`moveRedRight` and repair on the way up with `fixUp`, and the
top-level `deleteMinTop`/`deleteTop`, which first `prime` the root. `size` shrinks at every
recursive call even through the restructuring, which is what the termination proofs here use.
Their correctness is in `Delete/DeleteMin.lean`, `Delete/Mem.lean` and `Delete.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

omit [LinearOrder α] in
theorem size_rotateLeft (t : LLRB α) : (rotateLeft t).size = t.size := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [rotateLeft]
  omega

omit [LinearOrder α] in
theorem size_rotateRight (t : LLRB α) : (rotateRight t).size = t.size := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩ <;> simp [rotateRight]
  omega

omit [LinearOrder α] in
theorem size_flipColors (t : LLRB α) : (flipColors t).size = t.size := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [flipColors]

/-! ### Delete: `moveRedLeft`, `moveRedRight`, `deleteMin`, `delete`

Red links are pushed down before descending and repaired on return. The intermediate predicates
(`NotTwoNode`, `LeftLeaningBelowRoot`, `NotTwoNodeEither`) never weaken `Valid`. -/

/-- Sedgewick's `moveRedLeft`: before descending into a left child that is a bare 2-node, borrow
from the right sibling by `flipColors`, with `rotateRight` + `rotateLeft` when that sibling has a
red left child. Total; the `leaf` fallback is unreachable on a valid tree. -/
def moveRedLeft (h : LLRB α) : LLRB α :=
  let h1 := flipColors h
  if h1.right.left.isRed then
    match h1 with
    | node c l k r => flipColors (rotateLeft (node c l k (rotateRight r)))
    | leaf => h1
  else h1

/-- Sedgewick's `moveRedRight`, symmetric to `moveRedLeft`. -/
def moveRedRight (h : LLRB α) : LLRB α :=
  let h1 := flipColors h
  if h1.left.left.isRed then flipColors (rotateRight h1) else h1

omit [LinearOrder α] in
theorem size_moveRedLeft (t : LLRB α) : (moveRedLeft t).size = t.size := by
  have hfc := size_flipColors t
  have key : ∀ h1 : LLRB α, (match h1 with
      | node c l k r => flipColors (rotateLeft (node c l k (rotateRight r)))
      | leaf => h1).size = h1.size := by
    intro h1
    rcases h1 with _ | ⟨c, l, k, r⟩
    · rfl
    · simp [size_flipColors, size_rotateLeft, size_rotateRight]
  simp only [moveRedLeft]
  split_ifs
  · rw [key]; exact hfc
  · exact hfc

omit [LinearOrder α] in
theorem size_moveRedRight (t : LLRB α) : (moveRedRight t).size = t.size := by
  have hfc := size_flipColors t
  simp only [moveRedRight]
  split_ifs
  · rw [size_flipColors, size_rotateRight]; exact hfc
  · exact hfc

/-- The smallest key, if any: the leftmost node, as in `BST.min?`. -/
def min? : LLRB α → Option α
  | leaf => none
  | node _ l k _ => some ((min? l).getD k)

omit [LinearOrder α] in
@[simp] theorem min?_leaf : min? (leaf : LLRB α) = none := rfl

/-- **`min?` is correct**: on a `Sorted` tree, a returned `m` is present and a lower bound. -/
theorem min?_correct {t : LLRB α} (ht : Sorted t) {m : α} (hm : min? t = some m) :
    Mem m t ∧ All (m ≤ ·) t := by
  induction t with
  | leaf => simp at hm
  | node c l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    have heq : (min? l).getD k = m := by unfold min? at hm; exact Option.some.inj hm
    cases hl' : min? l with
    | none =>
      rw [hl', Option.getD_none] at heq
      subst heq
      have hlleaf : l = leaf := by
        cases l with
        | leaf => rfl
        | node _ _ _ _ => simp [min?] at hl'
      subst hlleaf
      exact ⟨Or.inr (Or.inl rfl), trivial, le_refl _, hr.imp (fun _ h => le_of_lt h)⟩
    | some m' =>
      rw [hl', Option.getD_some] at heq
      subst heq
      obtain ⟨hmem, hle⟩ := ihl hsl hl'
      have hmk : m' < k := hl.of_mem hmem
      exact ⟨Or.inl hmem, hle, le_of_lt hmk, hr.imp (fun x hx => le_of_lt (lt_trans hmk hx))⟩

omit [LinearOrder α] in
theorem min?_eq_none_iff {t : LLRB α} : min? t = none ↔ t = leaf := by
  cases t with
  | leaf => simp
  | node _ _ _ _ => simp [min?]

omit [LinearOrder α] in
theorem min?_node_of_ne_leaf {c : Color} {l : LLRB α} {k : α} {r : LLRB α} (hl : l ≠ leaf) :
    min? (node c l k r) = min? l := by
  cases l with
  | leaf => exact absurd rfl hl
  | node _ _ _ _ => simp [min?]

omit [LinearOrder α] in
theorem min?_flipColors (t : LLRB α) : min? (flipColors t) = min? t := by
  rcases t with _ | ⟨c, l, k, r⟩
  · rfl
  · rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
      simp [flipColors, min?]

omit [LinearOrder α] in
theorem min?_rotateLeft (t : LLRB α) : min? (rotateLeft t) = min? t := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩
  · rfl
  · rfl
  · simp [rotateLeft, min?]

omit [LinearOrder α] in
theorem min?_rotateRight (t : LLRB α) : min? (rotateRight t) = min? t := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩
  · rfl
  · rfl
  · simp [rotateRight, min?]

omit [LinearOrder α] in
/-- Either branch of `moveRedLeft`'s guard keeps `size`. -/
theorem size_ite_moveRedLeft (b : Bool) (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    (if b then moveRedLeft (node c l k r) else node c l k r).size = (node c l k r).size := by
  split_ifs with h
  · exact size_moveRedLeft _
  · rfl

omit [LinearOrder α] in
/-- Symmetric to `size_ite_moveRedLeft`. -/
theorem size_ite_moveRedRight (b : Bool) (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    (if b then moveRedRight (node c l k r) else node c l k r).size = (node c l k r).size := by
  split_ifs with h
  · exact size_moveRedRight _
  · rfl

omit [LinearOrder α] in
/-- Whichever branch `rotateRight`'s use-or-don't-use guard takes, it never changes `size`. -/
theorem size_ite_rotateRight (b : Bool) (t : LLRB α) :
    (if b then rotateRight t else t).size = t.size := by
  split_ifs with h
  · exact size_rotateRight _
  · rfl

-- `hh` is read only by `decreasing_by`, which the unused-variables linter does not see.
set_option linter.unusedVariables false in
/-- Sedgewick's `deleteMin` (exercise 3.3.40): `moveRedLeft` on the way down before a bare
2-node, `fixUp` on the way up. Well-founded on `size`: `moveRedLeft` keeps the size
(`size_ite_moveRedLeft`), so the left child it descends into is smaller. -/
def deleteMin : LLRB α → LLRB α
  | leaf => leaf
  | node _ leaf _ r => r
  | node c l k r =>
      match hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
      with
      | leaf => leaf
      | node c' l' k' r' => fixUp (node c' (deleteMin l') k' r')
termination_by t => t.size
decreasing_by
  have hsize : (node c' l' k' r').size = (node c l k r).size := by
    rw [← hh]
    split_ifs with h
    · exact size_moveRedLeft _
    · rfl
  simp only [size_node] at hsize ⊢
  omega

-- `hh1`, `hh2` and `hh3` are read only by `decreasing_by`, which the unused-variables linter
-- does not see.
set_option linter.unusedVariables false in
/-- Sedgewick's `delete` (exercises 3.3.39–3.3.41): `moveRedLeft`/`moveRedRight` on the way down
so the node recursed into is never a bare 2-node; an interior key is replaced by the right
subtree's minimum, which `deleteMin` removes; `fixUp` on the way up. After a borrowing step the
comparison is against the current top key (`k1`, then `k2`), not the original `k`. A node with an
empty right child is spliced out only when `a = k1`. Well-founded on `size`, like `deleteMin`. -/
def delete (a : α) : LLRB α → LLRB α
  | leaf => leaf
  | node c l k r =>
      if a < k then
        match hh1 :
            (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r) with
        | leaf => leaf
        | node c1 l1 k1 r1 => fixUp (node c1 (delete a l1) k1 r1)
      else
        match hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r) with
        | leaf => leaf
        | node c1 l1 k1 leaf => if a = k1 then l1 else fixUp (node c1 l1 k1 leaf)
        | node c1 l1 k1 (node cr1 rl1 rk1 rr1) =>
            match hh3 :
                (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
                    moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
                  else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) with
            | leaf => leaf
            | node c2 l2 k2 r2 =>
                if a = k2 then
                  match r2.min? with
                  | some m => fixUp (node c2 l2 m (deleteMin r2))
                  | none => l2
                else
                  fixUp (node c2 l2 k2 (delete a r2))
termination_by t => t.size
decreasing_by
  · have hsize : (node c1 l1 k1 r1).size = (node c l k r).size := by
      rw [← hh1]
      split_ifs with h
      · exact size_moveRedLeft _
      · rfl
    simp only [size_node] at hsize ⊢
    omega
  · have hsize2 : (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size = (node c l k r).size := by
      rw [← hh2]
      split_ifs with h
      · exact size_rotateRight _
      · rfl
    have hsize3 : (node c2 l2 k2 r2).size = (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size := by
      rw [← hh3]
      split_ifs with h
      · exact size_moveRedRight _
      · rfl
    simp only [size_node] at hsize2 hsize3 ⊢
    omega

/-- Force the root's link black (`algs4`'s `root.color = BLACK`). -/
def blacken : LLRB α → LLRB α
  | leaf => leaf
  | node _ l k r => node .black l k r

/-- Force the root's link red when neither child is red -- `algs4`'s
`if (!isRed(root.left) && !isRed(root.right)) root.color = RED;`. This is the step that
*establishes* the `NotTwoNode` precondition the deletion recursion runs on. -/
def prime : LLRB α → LLRB α
  | leaf => leaf
  | node c l k r => if !l.isRed && !r.isRed then node .red l k r else node c l k r

/-- Delete the minimum key, top level: prime, recurse, blacken. -/
def deleteMinTop (t : LLRB α) : LLRB α := blacken (deleteMin (prime t))

/-- Delete `a`, top level: check, then prime, recurse, blacken. The `search` first (Sedgewick's
`if (!contains(key)) return;`) keeps a deletion that removes nothing from rearranging the tree. -/
def deleteTop (a : α) (t : LLRB α) : LLRB α :=
  if search a t then blacken (delete a (prime t)) else t

end LLRB

end AlgoDesign.Searching
