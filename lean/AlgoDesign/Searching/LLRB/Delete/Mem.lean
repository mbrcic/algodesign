/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Delete.DeleteMin

/-!
# LLRB deletion: membership and ordering

`mem_delete_iff` and `sorted_delete`: general `delete` removes exactly its key, and keeps the
ordering. The color invariants are `Delete.lean`'s.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-! ### General `delete`: membership and ordering

Same color-blind/color-aware split as `insert`'s and `deleteMin`'s: `Mem` and `Sorted` never look
at a link's color, so they transfer through `rotateRight`/`moveRedLeft`/`moveRedRight`/`fixUp`
unconditionally. What makes `delete` harder than `deleteMin` is not the invariants but the *shape*
of its recursion: ten reduction cases rather than four, four of which are unreachable branches the
equation compiler still generates (a restructuring step is matched against `leaf`, which it can
never be). The `delete_lt`/`delete_ge_*` lemmas below name each reachable reduction once, so the
proofs that follow case on `delete.induct` without ever re-deriving what `delete` unfolds to. -/

omit [LinearOrder α] in
/-- `min?` returns a key that is actually present. Weaker than `min?_correct` (no lower-bound
claim) but, unlike it, needs no `Sorted` hypothesis -- which is what lets `mem_delete` below stay
color-blind *and* order-blind, matching `mem_deleteMin`'s scope. -/
theorem mem_of_min? {t : LLRB α} {m : α} (h : min? t = some m) : Mem m t := by
  induction t generalizing m with
  | leaf => simp [min?] at h
  | node c l k r ihl ihr =>
    simp only [min?, Option.some.injEq] at h
    cases hl : min? l with
    | none =>
      rw [hl, Option.getD_none] at h
      exact Or.inr (Or.inl h.symm)
    | some m' =>
      rw [hl, Option.getD_some] at h
      subst h
      exact Or.inl (ihl hl)

omit [LinearOrder α] in
theorem moveRedRight_eq_leaf_iff {t : LLRB α} : moveRedRight t = leaf ↔ t = leaf := by
  simp only [moveRedRight]
  split_ifs with h
  · simp [flipColors_eq_leaf_iff, rotateRight_eq_leaf_iff]
  · simp [flipColors_eq_leaf_iff]

omit [LinearOrder α] in
/-- Mirror of `moveRedLeft_left_ne_leaf`: `moveRedRight` never collapses a nonempty right child
down to `leaf`. This is what rules out `delete`'s "found the key, but its right subtree is empty
after borrowing" branch -- the equation compiler generates it, but it can never be taken. -/
theorem moveRedRight_right_ne_leaf {c : Color} {l : LLRB α} {k : α} {r : LLRB α} (hr : r ≠ leaf) :
    (moveRedRight (node c l k r)).right ≠ leaf := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩
  · exact absurd rfl hr
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> (try cases cl) <;>
    (try rcases ll with _ | ⟨cll, lll, llk, llr⟩) <;> (try cases cll) <;>
    simp [moveRedRight, flipColors, rotateRight, Color.flip, left, right, isRed]

omit [LinearOrder α] in
/-- `moveRedRight_right_ne_leaf` in the form `delete`'s own guard produces it: whichever branch the
"borrow from the right" guard takes, the right child of the result is still nonempty. -/
theorem ite_moveRedRight_right_ne_leaf {b : Bool} {c1 : Color} {l1 : LLRB α} {k1 : α}
    {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (hh : (if b then moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c' l' k' r') : r' ≠ leaf := by
  split at hh
  · have hne := moveRedRight_right_ne_leaf (c := c1) (l := l1) (k := k1)
      (r := node cr1 rl1 rk1 rr1) (by simp)
    rw [hh] at hne
    simpa [right] using hne
  · injection hh with e1 e2 e3 e4
    rw [← e4]
    simp

omit [LinearOrder α] in
/-- Transfers a `Mem` fact across one of `delete`'s restructuring guards, whichever branch it took.
Stated over an arbitrary `f` so the same lemma serves all three guards
(`rotateRight`, `moveRedLeft`, `moveRedRight`). -/
theorem mem_of_ite_eq {f : LLRB α → LLRB α} (hf : ∀ t x, Mem x (f t) ↔ Mem x t)
    {b : Bool} {t : LLRB α} {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (hh : (if b then f t else t) = node c' l' k' r') (x : α) :
    Mem x (node c' l' k' r') ↔ Mem x t := by
  split at hh
  · rw [← hh]; exact hf t x
  · rw [← hh]

/-- `Sorted` counterpart of `mem_of_ite_eq`. -/
theorem sorted_of_ite_eq {f : LLRB α → LLRB α} (hf : ∀ t : LLRB α, Sorted t → Sorted (f t))
    {b : Bool} {t : LLRB α} {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (ht : Sorted t) (hh : (if b then f t else t) = node c' l' k' r') :
    Sorted (node c' l' k' r') := by
  split at hh
  · rw [← hh]; exact hf t ht
  · rw [← hh]; exact ht

/-! `delete`'s five reachable reductions, named once each. Every hypothesis is exactly what
`delete.induct` hands back for that case, so downstream proofs pass them straight through. -/

/-- Descending left: `a` is below this node's key. -/
theorem delete_lt {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : a < k)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
            = node c' l' k' r') :
    delete a (node c l k r) = fixUp (node c' (delete a l') k' r') := by
  simp only [delete]
  split
  case isFalse hcon => exact absurd hak hcon
  case isTrue =>
    split
    · rename_i heq
      exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl

/-- Found the key with an empty right child: splice the node out, keeping its left subtree.
Sedgewick's `key.compareTo(h.key) == 0 && h.right == null` arm. -/
theorem delete_ge_splice {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} (hak : ¬ a < k)
    (hh : (if l.isRed then rotateRight (node c l k r) else node c l k r) = node c1 l1 a leaf) :
    delete a (node c l k r) = l1 := by
  simp only [delete]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      simp
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)

/-- Empty right child but the key doesn't match: nothing to remove here, just rebalance. -/
theorem delete_ge_fixUp {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} (hak : ¬ a < k)
    (hh : (if l.isRed then rotateRight (node c l k r) else node c l k r) = node c1 l1 k1 leaf)
    (hne : ¬ a = k1) :
    delete a (node c l k r) = fixUp (node c1 l1 k1 leaf) := by
  simp only [delete]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      simp [hne]
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)

/-- Found the key with a nonempty right child: copy the right subtree's minimum up over it and
`deleteMin` that minimum away -- the in-order-successor step, mirroring `BST.delete`. -/
theorem delete_ge_succ {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c' : Color} {l' r' : LLRB α} {m : α} (hak : ¬ a < k)
    (hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r)
             = node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    (hh3 : (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
              moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c' l' a r')
    (hmin : min? r' = some m) :
    delete a (node c l k r) = fixUp (node c' l' m (deleteMin r')) := by
  simp only [delete]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh2) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      injection e4 with f1 f2 f3 f4
      subst f1; subst f2; subst f3; subst f4
      split
      · rename_i heq'; exact absurd (heq'.symm.trans hh3) (by simp)
      · rename_i heq'
        have heq3 := heq'.symm.trans hh3
        injection heq3 with g1 g2 g3 g4
        subst g1; subst g2; subst g3; subst g4
        simp [hmin]

/-- Descending right: `a` is above this node's key (after the borrowing steps, which can change
which key sits at the root -- hence the comparison against `k'`, not the original `k`). -/
theorem delete_ge_rec {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : ¬ a < k)
    (hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r)
             = node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    (hh3 : (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
              moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c' l' k' r')
    (hne : ¬ a = k') :
    delete a (node c l k r) = fixUp (node c' l' k' (delete a r')) := by
  simp only [delete]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh2) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      injection e4 with f1 f2 f3 f4
      subst f1; subst f2; subst f3; subst f4
      split
      · rename_i heq'; exact absurd (heq'.symm.trans hh3) (by simp)
      · rename_i heq'
        have heq3 := heq'.symm.trans hh3
        injection heq3 with g1 g2 g3 g4
        subst g1; subst g2; subst g3; subst g4
        simp [hne]

/-- **`delete` never introduces a key that was absent from its input** -- the general-deletion
counterpart of `mem_deleteMin`, and like it a one-way statement needing neither ordering nor color
invariants. Four of `delete.induct`'s ten cases are discharged as unreachable: a restructuring step
(`moveRedLeft`/`rotateRight`/`moveRedRight`) is matched against `leaf`, which none of them can
return from a `node`. -/
theorem mem_delete (a : α) (t : LLRB α) (b : α) : Mem b (delete a t) → Mem b t := by
  induction t using delete.induct (a := a) with
  | case1 => intro h; simp [delete] at h
  | case2 c l k r hak hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    intro hmem
    rw [delete_lt hak hh, mem_fixUp, mem_node] at hmem
    rw [← mem_of_ite_eq (f := moveRedLeft) mem_moveRedLeft hh b, mem_node]
    rcases hmem with h | rfl | h
    · exact Or.inl (ih h)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h)
  | case4 c l k r hak hh =>
    exfalso
    revert hh
    split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    intro hmem
    rw [delete_ge_splice hak hh] at hmem
    rw [← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh b, mem_node]
    exact Or.inl hmem
  | case6 c l k r hak c1 l1 k1 hh hne =>
    intro hmem
    rw [delete_ge_fixUp hak hh hne, mem_fixUp] at hmem
    exact (mem_of_ite_eq (f := rotateRight) mem_rotateRight hh b).mp hmem
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    exfalso
    revert hh3
    split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    intro hmem
    rw [delete_ge_succ hak hh2 hh3 hmin, mem_fixUp, mem_node] at hmem
    rw [← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh2 b,
      ← mem_of_ite_eq (f := moveRedRight) mem_moveRedRight hh3 b, mem_node]
    rcases hmem with h | rfl | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (mem_of_min? hmin))
    · exact Or.inr (Or.inr (mem_deleteMin r' b h))
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    intro hmem
    rw [delete_ge_rec hak hh2 hh3 hne, mem_fixUp, mem_node] at hmem
    rw [← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh2 b,
      ← mem_of_ite_eq (f := moveRedRight) mem_moveRedRight hh3 b, mem_node]
    rcases hmem with h | rfl | h
    · exact Or.inl h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (ih h))

/-- `moveRedLeft`'s root key is never smaller than the original's.

This is the fact LLRB needs and standard red-black does not. `RedBlackStandard.del` recurses on
the *original* node, so `a < k` applies directly to the key it descends past. LLRB's `delete`
applies `moveRedLeft` *first* and then recurses, so the node it descends into may carry a
different root key, and `a < k` says nothing about it until this is established.

Both branches of `moveRedLeft` are benign: the fall-through leaves the root key alone, and the
rotating branch lifts a key out of the *right* subtree, which sortedness puts above `k`. -/
theorem le_root_moveRedLeft {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (ht : Sorted (node c l k r)) {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (heq : moveRedLeft (node c l k r) = node c' l' k' r') : k ≤ k' := by
  obtain ⟨_, hkr, _, _⟩ := ht
  rw [moveRedLeft] at heq
  split at heq
  · -- rotating branch: the new root is lifted out of `r`, so sortedness puts it above `k`
    rename_i hred
    cases r with
    | leaf => cases l <;> simp [flipColors, LLRB.right, LLRB.left, LLRB.isRed] at hred
    | node cr rl rk rr =>
      cases rl with
      | leaf => cases l <;> simp [flipColors, LLRB.right, LLRB.left, LLRB.isRed] at hred
      | node crl rll rlk rlr =>
        have hlt : k < rlk := hkr.of_mem (by simp [Mem])
        cases l <;>
          simp only [flipColors, rotateLeft, rotateRight, node.injEq] at heq <;>
          obtain ⟨_, _, rfl, _⟩ := heq <;>
          exact le_of_lt hlt
  · -- fall-through: `flipColors` only recolors, so the root key is untouched
    rename_i hred
    cases l <;> cases r <;> simp only [flipColors, node.injEq] at heq <;>
      obtain ⟨_, _, rfl, _⟩ := heq <;> exact le_refl _

/-- `rotateRight`'s root key is never larger than the original's: it lifts a key out of the
*left* subtree, which sortedness puts below `k`. The mirror of `le_root_moveRedLeft`, needed on
the right-hand descent. -/
theorem root_rotateRight_le {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (ht : Sorted (node c l k r)) {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (heq : rotateRight (node c l k r) = node c' l' k' r') : k' ≤ k := by
  obtain ⟨hlk, _, _, _⟩ := ht
  cases l with
  | leaf =>
    simp only [rotateRight, node.injEq] at heq
    obtain ⟨_, _, rfl, _⟩ := heq; exact le_refl _
  | node cl ll lk lr =>
    simp only [rotateRight, node.injEq] at heq
    obtain ⟨_, _, rfl, _⟩ := heq
    exact le_of_lt (hlk.of_mem (by simp [Mem]))

/-- `moveRedRight`'s root key is never larger than the original's -- the mirror of
`le_root_moveRedLeft`, lifting out of the left subtree instead of the right. -/
theorem root_moveRedRight_le {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (ht : Sorted (node c l k r)) {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (heq : moveRedRight (node c l k r) = node c' l' k' r') : k' ≤ k := by
  obtain ⟨hlk, _, _, _⟩ := ht
  rw [moveRedRight] at heq
  split at heq
  · -- rotating branch: `rotateRight` on the whole node lifts the left child's own key
    rename_i hred
    cases l with
    | leaf => cases r <;> simp [flipColors, LLRB.left, LLRB.isRed] at hred
    | node cl ll lk lr =>
      have hlt : lk < k := hlk.of_mem (by simp [Mem])
      -- `hred` forces `ll` to be a red node, which is also what makes the outer `flipColors`
      -- reduce; `r` is split only so that the inner one does.
      cases ll <;> cases r <;>
        simp only [isRed, left, flipColors, rotateRight, node.injEq,
          Bool.false_eq_true] at hred heq <;>
        obtain ⟨_, _, rfl, _⟩ := heq <;>
        exact le_of_lt hlt
  · -- fall-through: `flipColors` only recolors
    rename_i hred
    cases l <;> cases r <;> simp only [flipColors, node.injEq] at heq <;>
      obtain ⟨_, _, rfl, _⟩ := heq <;> exact le_refl _

/-- **Target**: general deletion removes exactly `a`. -/
theorem mem_delete_iff {t : LLRB α} (ht : Sorted t) (a b : α) :
    Mem b (delete a t) ↔ b ≠ a ∧ Mem b t := by
  induction t using delete.induct (a := a) with
  | case1 => simp [delete, Mem]
  | case2 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    -- descend left. `a < k`, and `le_root_moveRedLeft` carries that past the rotation to `k'`,
    -- so `a` is neither the new root nor anywhere in the new right subtree.
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedLeft h) ht hh
    have hak' : a < k' := by
      rcases hb : (!l.isRed && !l.left.isRed) with _ | _
      · simp only [hb, Bool.false_eq_true] at hh
        cases hh; exact hak
      · simp only [hb] at hh
        exact lt_of_lt_of_le hak (le_root_moveRedLeft ht hh)
    rw [delete_lt hak hh, mem_fixUp, mem_node,
      ← mem_of_ite_eq (f := moveRedLeft) mem_moveRedLeft hh b, mem_node]
    constructor
    · rintro (h | rfl | h)
      · exact ⟨(ih hsl').mp h |>.1, Or.inl ((ih hsl').mp h).2⟩
      · exact ⟨ne_of_gt hak', Or.inr (Or.inl rfl)⟩
      · exact ⟨ne_of_gt (lt_trans hak' (hr'gt.of_mem h)), Or.inr (Or.inr h)⟩
    · rintro ⟨hne, h | rfl | h⟩
      · exact Or.inl ((ih hsl').mpr ⟨hne, h⟩)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
  | case4 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    -- the node holding `a` has no right child: splice it out, keeping only its left subtree.
    -- Sortedness is what says nothing else was lost -- everything in `l1` is strictly below `a`.
    have hs : Sorted (node c1 l1 a leaf) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh
    rw [delete_ge_splice hak hh,
      ← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh b, mem_node]
    constructor
    · intro h
      exact ⟨ne_of_lt (hs.1.of_mem h), Or.inl h⟩
    · rintro ⟨hne, h | rfl | h⟩
      · exact h
      · exact absurd rfl hne
      · simp [Mem] at h
  | case6 c l k r hak c1 l1 k1 hh hne =>
    -- right child empty and this is not the key: the walk has run out of tree, so `a` is absent
    -- and the result is the node unchanged. `root_rotateRight_le` is what places `a` above `k1`.
    have hs : Sorted (node c1 l1 k1 leaf) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh
    have hk1k : k1 ≤ k := by
      rcases hb : l.isRed with _ | _
      · simp only [hb, Bool.false_eq_true] at hh; cases hh; exact le_refl _
      · simp only [hb] at hh; exact root_rotateRight_le ht hh
    have hk1a : k1 < a := lt_of_le_of_ne (le_trans hk1k (not_lt.mp hak)) (Ne.symm hne)
    have hna : ¬ Mem a (node c1 l1 k1 leaf) := by
      rw [mem_node]
      rintro (h | rfl | h)
      · exact absurd (hs.1.of_mem h) (not_lt.mpr (le_of_lt hk1a))
      · exact lt_irrefl a hk1a
      · simp [Mem] at h
    rw [delete_ge_fixUp hak hh hne, mem_fixUp,
      ← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh b]
    constructor
    · intro h
      exact ⟨fun hba => hna (hba ▸ h), h⟩
    · exact fun h => h.2
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    exfalso; revert hh3; split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    -- the key is here and both children are present: replace it with the right subtree's
    -- minimum `m` and delete `m` from there. `mem_deleteMin_iff` is what makes this exact --
    -- `m` moves up rather than being lost, and nothing else in `r'` is disturbed.
    have hs2 : Sorted (node c1 l1 k1 (node cr1 rl1 rk1 rr1)) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh2
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedRight h) hs2 hh3
    have hmem_m : Mem m r' := mem_of_min? hmin
    have ham : a < m := hr'gt.of_mem hmem_m
    rw [delete_ge_succ hak hh2 hh3 hmin, mem_fixUp, mem_node,
      ← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh2 b,
      ← mem_of_ite_eq (f := moveRedRight) mem_moveRedRight hh3 b, mem_node,
      mem_deleteMin_iff hsr' hmin b]
    constructor
    · rintro (h | rfl | ⟨h, _⟩)
      · exact ⟨ne_of_lt (hl'lt.of_mem h), Or.inl h⟩
      · exact ⟨ne_of_gt ham, Or.inr (Or.inr hmem_m)⟩
      · exact ⟨ne_of_gt (hr'gt.of_mem h), Or.inr (Or.inr h)⟩
    · rintro ⟨hne, h | rfl | h⟩
      · exact Or.inl h
      · exact absurd rfl hne
      · by_cases hbm : b = m
        · exact Or.inr (Or.inl hbm)
        · exact Or.inr (Or.inr ⟨h, hbm⟩)
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    -- descend right. The two root-key lemmas chain: `k' ≤ k1 ≤ k ≤ a`, and `a ≠ k'` makes it
    -- strict, so `a` is neither this node nor anywhere in its left subtree.
    have hs2 : Sorted (node c1 l1 k1 (node cr1 rl1 rk1 rr1)) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh2
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedRight h) hs2 hh3
    have hk1k : k1 ≤ k := by
      rcases hb : l.isRed with _ | _
      · simp only [hb, Bool.false_eq_true] at hh2; cases hh2; exact le_refl _
      · simp only [hb] at hh2; exact root_rotateRight_le ht hh2
    have hk'k1 : k' ≤ k1 := by
      rcases hb : (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed) with _ | _
      · simp only [hb, Bool.false_eq_true] at hh3; cases hh3; exact le_refl _
      · simp only [hb] at hh3; exact root_moveRedRight_le hs2 hh3
    have hk'a : k' < a :=
      lt_of_le_of_ne (le_trans hk'k1 (le_trans hk1k (not_lt.mp hak))) (Ne.symm hne)
    rw [delete_ge_rec hak hh2 hh3 hne, mem_fixUp, mem_node,
      ← mem_of_ite_eq (f := rotateRight) mem_rotateRight hh2 b,
      ← mem_of_ite_eq (f := moveRedRight) mem_moveRedRight hh3 b, mem_node]
    constructor
    · rintro (h | rfl | h)
      · exact ⟨ne_of_lt (lt_trans (hl'lt.of_mem h) hk'a), Or.inl h⟩
      · exact ⟨ne_of_lt hk'a, Or.inr (Or.inl rfl)⟩
      · exact ⟨((ih hsr').mp h).1, Or.inr (Or.inr ((ih hsr').mp h).2)⟩
    · rintro ⟨hne2, h | rfl | h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((ih hsr').mpr ⟨hne2, h⟩))

/-- **`delete` preserves `Sorted`** -- the other color-blind half of general deletion, mirroring
`sorted_deleteMin`.

The in-order-successor case is the one that genuinely needs `mem_deleteMin_iff` rather than the
weaker one-way `mem_deleteMin`: after the successor `m` is copied up over the deleted key, the new
node's right subtree is `deleteMin r'`, and `Sorted` demands every key there be *strictly* above
`m`. One-way membership only gives `m ≤ ·` (from `min?_correct`); it takes the exact
characterization -- `deleteMin` drops `m` itself and nothing else -- to rule out the tie. -/
theorem sorted_delete {t : LLRB α} (ht : Sorted t) (a : α) : Sorted (delete a t) := by
  induction t using delete.induct (a := a) with
  | case1 => simpa [delete] using ht
  | case2 c l k r hak hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedLeft h) ht hh
    rw [delete_lt hak hh]
    exact sorted_fixUp ⟨all_of_forall_mem fun x hx => hl'lt.of_mem (mem_delete a l' x hx),
      hr'gt, ih hsl', hsr'⟩
  | case4 c l k r hak hh =>
    exfalso
    revert hh
    split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    have hs : Sorted (node c1 l1 a leaf) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh
    rw [delete_ge_splice hak hh]
    exact hs.2.2.1
  | case6 c l k r hak c1 l1 k1 hh hne =>
    have hs : Sorted (node c1 l1 k1 leaf) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh
    rw [delete_ge_fixUp hak hh hne]
    exact sorted_fixUp hs
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    exfalso
    revert hh3
    split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    have hs2 : Sorted (node c1 l1 k1 (node cr1 rl1 rk1 rr1)) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh2
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedRight h) hs2 hh3
    obtain ⟨hmem_m, hle_m⟩ := min?_correct hsr' hmin
    have ham : a < m := hr'gt.of_mem hmem_m
    rw [delete_ge_succ hak hh2 hh3 hmin]
    refine sorted_fixUp ⟨all_of_forall_mem fun x hx => lt_trans (hl'lt.of_mem hx) ham, ?_, hsl',
      sorted_deleteMin hsr'⟩
    refine all_of_forall_mem fun x hx => ?_
    obtain ⟨hxr', hxm⟩ := (mem_deleteMin_iff hsr' hmin x).mp hx
    exact lt_of_le_of_ne (hle_m.of_mem hxr') (Ne.symm hxm)
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    have hs2 : Sorted (node c1 l1 k1 (node cr1 rl1 rk1 rr1)) :=
      sorted_of_ite_eq (fun _ h => sorted_rotateRight h) ht hh2
    obtain ⟨hl'lt, hr'gt, hsl', hsr'⟩ :=
      sorted_of_ite_eq (fun _ h => sorted_moveRedRight h) hs2 hh3
    rw [delete_ge_rec hak hh2 hh3 hne]
    exact sorted_fixUp ⟨hl'lt,
      all_of_forall_mem fun x hx => hr'gt.of_mem (mem_delete a r' x hx), hsl', ih hsr'⟩

end LLRB

end AlgoDesign.Searching
