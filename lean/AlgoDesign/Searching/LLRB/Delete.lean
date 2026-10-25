/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Delete.Mem

/-!
# LLRB: deletion

The top-level deletion and its correctness: why the priming step is not optional, `delete_spec`
(general deletion preserves every color invariant), `valid_deleteTop`, and `deleteTopSpec`:
`deleteTop` discharges `DeleteSpec` on a valid tree; and `DeleteCost`, delete's comparisons,
argued. The algorithm is in `Delete/Algorithm.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-- **What any deletion of `a` owes**: the key set loses exactly `a`, and a legal tree stays legal.
The per-operation form the proofs discharge; the promise, `SearchTree.Promise`, states the same
for every operation at once. -/
def DeleteSpec (a : α) (before after : LLRB α) : Prop :=
  (∀ b, Mem b after ↔ (b ≠ a ∧ Mem b before)) ∧ (Valid before → Valid after)

/-! ### Top-level deletion: the priming step, and why it is not optional

`deleteMin` and `delete` above are Sedgewick's *recursive helpers*, not entry points -- the same
split as `insertAux` vs `insert`. Both carry a precondition their recursion depends on: the node
about to be descended into must not be a bare 2-node, stated here as `NotTwoNode` (a spare red link
at the root or its left child).

That precondition is **not** implied by `Valid`, and this is worth being explicit about, because it
makes `valid_deleteMin` inapplicable on its own. `Valid` forces a *black* root (`RootBlack`), so
`NotTwoNode t = t.IsRed ∨ t.left.IsRed` can only ever hold via a red left child -- and plenty of
perfectly valid trees have neither, starting with the one-element tree `node .black leaf x leaf`.
Feeding the raw recursion a tree that fails the precondition does not merely block the proof, it
breaks the algorithm: deleting a key that *is* present via the unprimed recursion can violate
the color invariants.

`algs4`'s `RedBlackBST.delete` handles this with a recoloring dance around the recursive call, and
that is what `prime`/`blacken` below reproduce: force the root red before descending (which
*establishes* `NotTwoNode`, since a red root satisfies it outright), then force it black again on
the way out.

`deleteMinTop`/`deleteTop` are therefore the declarations a caller should use; `valid_deleteMinTop`
below needs no precondition beyond `Valid` itself. -/

omit [LinearOrder α] in
@[simp] theorem mem_blacken (t : LLRB α) (b : α) : Mem b (blacken t) ↔ Mem b t := by
  cases t <;> exact Iff.rfl

omit [LinearOrder α] in
@[simp] theorem mem_prime (t : LLRB α) (b : α) : Mem b (prime t) ↔ Mem b t := by
  cases t with
  | leaf => exact Iff.rfl
  | node c l k r => simp only [prime]; split_ifs <;> exact Iff.rfl

theorem sorted_blacken {t : LLRB α} (ht : Sorted t) : Sorted (blacken t) := by
  cases t <;> exact ht

theorem sorted_prime {t : LLRB α} (ht : Sorted t) : Sorted (prime t) := by
  cases t with
  | leaf => exact ht
  | node c l k r => simp only [prime]; split_ifs <;> exact ht

omit [LinearOrder α] in
theorem rootBlack_blacken (t : LLRB α) : RootBlack (blacken t) := by
  cases t with
  | leaf => trivial
  | node c l k r => rfl

omit [LinearOrder α] in
theorem leftLeaning_blacken {t : LLRB α} (h : LeftLeaning t) : LeftLeaning (blacken t) := by
  cases t <;> exact h

omit [LinearOrder α] in
theorem noRedRed_blacken {t : LLRB α} (h : NoRedRed t) : NoRedRed (blacken t) := by
  cases t with
  | leaf => exact h
  | node c l k r => exact ⟨by simp, h.2.1, h.2.2⟩

omit [LinearOrder α] in
theorem balanced_blacken {t : LLRB α} (h : Balanced t) : Balanced (blacken t) := by
  cases t <;> exact h

omit [LinearOrder α] in
/-- Priming preserves every structural invariant and, crucially, *establishes* `NotTwoNode`.

Note where `LeftLeaning` does the work: it forces `r.isRed = false`, so the guard
`!l.isRed && !r.isRed` collapses to `!l.isRed`. Either the left child is already red (and
`NotTwoNode` holds through it, with the tree left untouched), or it isn't -- and then recoloring
the root red is safe for `NoRedRed` precisely because *both* children are known black. -/
theorem prime_spec {t : LLRB α} (hne : t ≠ leaf) (hbal : Balanced t) (hll : LeftLeaning t)
    (hnrr : NoRedRed t) :
    Balanced (prime t) ∧ LeftLeaning (prime t) ∧ NoRedRed (prime t) ∧ NotTwoNode (prime t) := by
  cases t with
  | leaf => exact absurd rfl hne
  | node c l k r =>
    have hrf : r.isRed = false := isRed_eq_false hll.1
    cases hlf : l.isRed with
    | true =>
      have hp : prime (node c l k r) = node c l k r := by simp [prime, hlf]
      rw [hp]
      exact ⟨hbal, hll, hnrr, Or.inr (isRed_iff.mp hlf)⟩
    | false =>
      have hp : prime (node c l k r) = node .red l k r := by simp [prime, hlf, hrf]
      rw [hp]
      exact ⟨hbal, hll, ⟨fun _ => ⟨isRed_eq_false_iff.mp hlf, hll.1⟩, hnrr.2.1, hnrr.2.2⟩,
        Or.inl rfl⟩

omit [LinearOrder α] in
/-- `prime` only recolors the root, so it cannot move the minimum. -/
@[simp] theorem min?_prime (t : LLRB α) : min? (prime t) = min? t := by
  cases t with
  | leaf => rfl
  | node c l k r => simp only [prime]; split <;> rfl

/-- **`deleteMinTop` takes a legal LLRB tree to a legal LLRB tree** -- with no side condition
beyond `Valid`, unlike `valid_deleteMin`, which cannot be applied to (for instance) a one-element
tree. Priming is exactly what closes that gap. -/
theorem valid_deleteMinTop {t : LLRB α} (hv : Valid t) : Valid (deleteMinTop t) := by
  obtain ⟨hs, hrb, hll, hnrr, hbh⟩ := hv
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  by_cases hne : t = leaf
  · subst hne
    have hleaf : deleteMinTop (leaf : LLRB α) = leaf := by
      simp [deleteMinTop, prime, deleteMin, blacken]
    rw [hleaf]
    exact ⟨trivial, trivial, trivial, trivial, Option.some_ne_none _⟩
  · obtain ⟨hpb, hpl, hpn, hpt⟩ := prime_spec hne hbal hll hnrr
    obtain ⟨-, hdb, hdl, hdn, -⟩ := deleteMin_spec hpb hpl hpn hpt
    exact ⟨sorted_blacken (sorted_deleteMin (sorted_prime hs)), rootBlack_blacken _,
      leftLeaning_blacken hdl, noRedRed_blacken hdn,
      blackHeightOk_iff_balanced.mpr (balanced_blacken hdb)⟩

/-- **`deleteMinTop` removes exactly the minimum** -- the key-set half of the public
minimum-removal, which `valid_deleteMinTop` alone does not give. Without it, a `deleteMinTop`
that returned its argument untouched would satisfy every theorem stated about it.

Inherited from `mem_deleteMin_iff` on the recursive helper; `prime` is transparent to both
membership and `min?`, and `blacken` to membership. -/
theorem mem_deleteMinTop_iff {t : LLRB α} (ht : Sorted t) {m : α} (hm : min? t = some m)
    (b : α) : Mem b (deleteMinTop t) ↔ Mem b t ∧ b ≠ m := by
  simp only [deleteMinTop, mem_blacken]
  rw [mem_deleteMin_iff (sorted_prime ht) (by simpa using hm) b, mem_prime]

/-- `deleteTop` never invents a key. Inherited from `mem_delete`; needs no precondition. -/
theorem mem_deleteTop (a : α) (t : LLRB α) (b : α) : Mem b (deleteTop a t) → Mem b t := by
  intro h
  simp only [deleteTop] at h
  split at h
  · simp only [mem_blacken] at h
    exact (mem_prime t b).mp (mem_delete a (prime t) b h)
  · exact h

/-- **`deleteTop` removes exactly `a`** -- the exact characterization, strengthening the one-way
`mem_deleteTop` above to an `iff` and matching `RedBlackStandard.mem_delete`.

This is what closes the last semantic gap in LLRB deletion: `valid_deleteTop` already said the
result is a legal tree, but "legal" is satisfied by a tree that dropped the wrong key, or several.
Together they say deletion does exactly one thing. -/
theorem mem_deleteTop_iff {t : LLRB α} (ht : Sorted t) (a b : α) :
    Mem b (deleteTop a t) ↔ b ≠ a ∧ Mem b t := by
  simp only [deleteTop]
  split
  · simp only [mem_blacken]
    rw [mem_delete_iff (sorted_prime ht) a b, mem_prime]
  · -- `a` is not in the tree, so the tree already answers: nothing named `a` to exclude.
    rename_i hs
    have hna : ¬ Mem a t := fun hm => by
      rw [(search_correct ht a).mpr hm] at hs; exact absurd hs (by simp)
    exact ⟨fun hb => ⟨fun hba => hna (hba ▸ hb), hb⟩, fun h => h.2⟩

/-- `deleteTop` preserves the ordering. Inherited from `sorted_delete`. -/
theorem sorted_deleteTop {t : LLRB α} (ht : Sorted t) (a : α) : Sorted (deleteTop a t) := by
  simp only [deleteTop]
  split
  · exact sorted_blacken (sorted_delete (sorted_prime ht) a)
  · exact ht

/-! ### General `delete`: the color invariants

The last and hardest piece. `deleteMin`'s descent stays on the left spine, where `moveRedLeft`
restores the strict invariant before every recursive call, so `deleteMin_spec` can assume
`LeftLeaning ∧ NotTwoNode` throughout. General `delete` cannot: `moveRedRight` hands the
right-descent path a subtree that is genuinely only `LeftLeaningBelowRoot` -- black-rooted with a
red *right* link.

Four facts about the recursion shape what follows:

* `moveRedLeft` and `moveRedRight` are only ever called on a **red-rooted** node, without exception.
  So `moveRedLeft_spec`/`moveRedRight_spec`'s existing red-root input shapes suffice -- neither
  needs generalizing.
* Only the **right**-descent target is ever relaxed. The left-descent target is always strict, which
  is why `case3` below can discharge the relaxed alternative outright.
* In the relaxed state the branch taken is always `¬ a < k`, because both borrowing steps only ever
  move a *smaller* key to the root. So the relaxed state does no borrowing at all (`rotateRight`'s
  guard fails because its left child is black, `moveRedRight`'s because its right child is red) and
  hands straight off to a strict-state child. It is transient, never nested.
* `(delete a t).IsRed → t.IsRed` survives unchanged, so the conclusion is parallel to
  `deleteMin_spec`'s rather than needing weakening.

`DeleteOk` writes these facts down. -/

/-- `a` sits at or above `t`'s root key (vacuous for `leaf`). -/
def KeyLe (a : α) : LLRB α → Prop
  | leaf => True
  | node _ _ k _ => ¬ a < k

/-- `t`'s root key sits strictly below `x` (vacuous for `leaf`). -/
def KeyLt : LLRB α → α → Prop
  | leaf, _ => True
  | node _ _ k _, x => k < x

/-- The shape `delete`'s recursion actually runs on: either the strict LLRB shape with a spare red
link on the left spine, or -- only ever on the right-descent path -- the temporarily right-leaning
shape `moveRedRight` produces, in which case `a` is known to sit at or above this node's own key,
so the recursion goes right and never asks `moveRedLeft` to borrow from a black-rooted node. -/
def DeleteOk (a : α) (t : LLRB α) : Prop :=
  t = leaf ∨ (LeftLeaning t ∧ NotTwoNode t) ∨
  (¬ t.left.IsRed ∧ t.right.IsRed ∧ LeftLeaning t.left ∧ LeftLeaning t.right ∧ KeyLe a t)

theorem keyLt_of_sorted {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (hs : Sorted (node c l k r)) : KeyLt l k := by
  cases l with
  | leaf => trivial
  | node cl ll lk lr => exact hs.1.2.1

theorem rotateRight_guard_spec {a : α} {c : Color} {l r : LLRB α} {k : α}
    (hs : Sorted (node c l k r)) (hbal : Balanced (node c l k r)) (hnrr : NoRedRed (node c l k r))
    (hok : DeleteOk a (node c l k r)) (hak : ¬ a < k)
    {c1 : Color} {l1 : LLRB α} {k1 : α} {r1 : LLRB α}
    (hh : (if l.isRed then rotateRight (node c l k r) else node c l k r) = node c1 l1 k1 r1) :
    bheight (node c1 l1 k1 r1) = bheight (node c l k r) ∧
    Balanced (node c1 l1 k1 r1) ∧ NoRedRed (node c1 l1 k1 r1) ∧
    Sorted (node c1 l1 k1 r1) ∧ LeftLeaning l1 ∧ LeftLeaning r1 ∧
    ¬ a < k1 ∧ ¬ l1.IsRed ∧ (r1.IsRed ∨ c1 = Color.red) ∧
    ((node c1 l1 k1 r1).IsRed → (node c l k r).IsRed) := by
  by_cases hlred : l.IsRed
  · rcases l with _ | ⟨cl, ll, lk, lr⟩
    · exact absurd hlred (by simp [IsRed])
    have hcl : cl = Color.red := hlred
    subst hcl
    have hcb : c = Color.black := by
      cases c with
      | red => exact absurd hlred (hnrr.1 rfl).1
      | black => rfl
    subst hcb
    have hll : LeftLeaning (node Color.black (node Color.red ll lk lr) k r) := by
      rcases hok with hlf | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd hlf (by simp)
      · exact h
      · exact absurd (show (node Color.red ll lk lr).IsRed from rfl) (by simpa [left] using h)
    have hlkk : lk < k := hs.1.2.1
    have hsr := sorted_rotateRight hs
    split at hh
    case isFalse hg => exact absurd isRed_red hg
    case isTrue =>
      have hrot : rotateRight (node Color.black (node Color.red ll lk lr) k r)
          = node Color.black ll lk (node Color.red lr k r) := rfl
      rw [hrot] at hh
      rw [hrot] at hsr
      injection hh with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      obtain ⟨hbh, hbl, hbr⟩ := hbal
      obtain ⟨hbh2, hbll, hblr⟩ := hbl
      obtain ⟨-, hl_nrr, hr_nrr⟩ := hnrr
      obtain ⟨hnr2, hll_nrr, hlr_nrr⟩ := hl_nrr
      obtain ⟨hllb, hlrb⟩ := hnr2 rfl
      obtain ⟨hrnr, hlll, hrll⟩ := hll
      obtain ⟨-, hlll1, hlll2⟩ := hlll
      have e_ll_r : bheight ll = bheight r := by simpa [bheight] using hbh
      refine ⟨by simp [bheight], ⟨by simpa [bheight] using hbh2, hbll,
          ⟨by omega, hblr, hbr⟩⟩,
        ⟨by simp, hll_nrr, ⟨fun _ => ⟨hlrb, hrnr⟩, hlr_nrr, hr_nrr⟩⟩,
        hsr, hlll1, ⟨hrnr, hlll2, hrll⟩, ?_, hllb, Or.inl rfl, by simp [IsRed]⟩
      exact fun hc => hak (lt_trans hc hlkk)
  · split at hh
    case isTrue hg => exact absurd (isRed_iff.mp hg) hlred
    case isFalse =>
      injection hh with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      have hlr : LeftLeaning l ∧ LeftLeaning r ∧ (r.IsRed ∨ c = Color.red) := by
        rcases hok with hlf | ⟨h, hntn⟩ | ⟨-, hrred, hlll, hrll, -⟩
        · exact absurd hlf (by simp)
        · refine ⟨h.2.1, h.2.2, Or.inr ?_⟩
          rcases hntn with hc | hc
          · exact hc
          · exact absurd (by simpa [left] using hc) hlred
        · exact ⟨hlll, hrll, Or.inl (by simpa [right] using hrred)⟩
      exact ⟨rfl, hbal, hnrr, hs, hlr.1, hlr.2.1, hak, hlred, hlr.2.2, id⟩

theorem moveRedRight_deleteOk {a : α} {l rl rr : LLRB α} {k rk : α}
    (ht_ll : LeftLeaning (node Color.red l k (node Color.black rl rk rr)))
    (ht_nrr : NoRedRed (node Color.red l k (node Color.black rl rk rr)))
    (ht_bal : Balanced (node Color.red l k (node Color.black rl rk rr)))
    (hrl : ¬ rl.IsRed) (hak : ¬ a < k) (hlk : KeyLt l k) :
    ((moveRedRight (node Color.red l k (node Color.black rl rk rr))).IsRed →
      ¬ (moveRedRight (node Color.red l k (node Color.black rl rk rr))).left.IsRed) ∧
    ((LeftLeaning (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right ∧
      NotTwoNode (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right) ∨
    ((¬ (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right.left.IsRed ∧
      (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right.right.IsRed ∧
      LeftLeaning (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right.left ∧
      LeftLeaning (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right.right ∧
      KeyLe a (moveRedRight (node Color.red l k (node Color.black rl rk rr))).right) ∧
      KeyLt (moveRedRight (node Color.red l k (node Color.black rl rk rr))) k)) := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;>
    (try rcases ll with _ | ⟨cll, lll, llk, llr⟩) <;> (try cases cl) <;> (try cases cll) <;>
    (try have := bheight_pos rl) <;> (try have := bheight_pos rr) <;>
    (try have := bheight_pos lr) <;> (try have := bheight_pos lll) <;>
    (try have := bheight_pos llr) <;>
    simp_all [moveRedRight, flipColors, rotateRight, Color.flip, isRed, left, right,
      KeyLe, KeyLt, NotTwoNode, LeftLeaning, NoRedRed, IsRed, bheight, Balanced]

omit [LinearOrder α] in
theorem fixUp_isRed_cases {c : Color} {l r : LLRB α} {k : α}
    (hnl : NoRedRed l) (hnr : NoRedRed r) (hll : LeftLeaning l) (hlr : LeftLeaning r)
    (h : (fixUp (node c l k r)).IsRed) : c = Color.red ∨ (l.IsRed ∧ r.IsRed) := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
    (try rcases ll with _ | ⟨cll, lll, llk, llr⟩) <;>
    (try rcases rl with _ | ⟨crl, rll, rlk, rlr⟩) <;>
    (try rcases rr with _ | ⟨crr, rrl, rrk, rrr⟩) <;>
    cases c <;> (try cases cl) <;> (try cases cr) <;> (try cases cll) <;>
    (try cases crl) <;> (try cases crr) <;>
    simp_all [fixUp, rotateLeft, flipColors, Color.flip, isRed, left, right,
      LeftLeaning, NoRedRed, IsRed]

theorem moveRedRight_guard_spec {a : α} {c1 : Color} {l1 : LLRB α} {k1 : α}
    {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c2 : Color} {l2 : LLRB α} {k2 : α} {r2 : LLRB α}
    (hs1 : Sorted (node c1 l1 k1 (node cr1 rl1 rk1 rr1)))
    (hbal1 : Balanced (node c1 l1 k1 (node cr1 rl1 rk1 rr1)))
    (hnrr1 : NoRedRed (node c1 l1 k1 (node cr1 rl1 rk1 rr1)))
    (hll1 : LeftLeaning l1) (hllr1 : LeftLeaning (node cr1 rl1 rk1 rr1))
    (hak1 : ¬ a < k1) (hl1nr : ¬ l1.IsRed)
    (hred1 : (node cr1 rl1 rk1 rr1).IsRed ∨ c1 = Color.red)
    (hh3 : (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
              moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c2 l2 k2 r2) :
    bheight (node c2 l2 k2 r2) = bheight (node c1 l1 k1 (node cr1 rl1 rk1 rr1)) ∧
    Balanced (node c2 l2 k2 r2) ∧ NoRedRed (node c2 l2 k2 r2) ∧
    Sorted (node c2 l2 k2 r2) ∧ LeftLeaning l2 ∧
    (c2 = Color.red → ¬ l2.IsRed ∧ ¬ r2.IsRed) ∧
    ((node c2 l2 k2 r2).IsRed → (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).IsRed) ∧
    ((node c1 l1 k1 (node cr1 rl1 rk1 rr1)).IsRed ∨ ¬ l2.IsRed) ∧
    ((LeftLeaning r2 ∧ NotTwoNode r2) ∨
      ((¬ r2.left.IsRed ∧ r2.right.IsRed ∧ LeftLeaning r2.left ∧ LeftLeaning r2.right ∧
        KeyLe a r2) ∧ k2 < k1)) := by
  split at hh3
  case isFalse hg =>
    injection hh3 with e1 e2 e3 e4
    subst e1; subst e2; subst e3; subst e4
    have hntn : NotTwoNode (node cr1 rl1 rk1 rr1) := by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_and_or,
        Bool.not_eq_false] at hg
      rcases hg with hg | hg
      · exact Or.inl (isRed_iff.mp (by simpa using hg))
      · exact Or.inr (isRed_iff.mp (by simpa [left] using hg))
    exact ⟨rfl, hbal1, hnrr1, hs1, hll1, hnrr1.1, id, Or.inr hl1nr, Or.inl ⟨hllr1, hntn⟩⟩
  case isTrue hg =>
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg
    have hrnr : ¬ (node cr1 rl1 rk1 rr1).IsRed := isRed_eq_false_iff.mp (by simpa using hg.1)
    have hrlnr : ¬ rl1.IsRed := isRed_eq_false_iff.mp (by simpa using hg.2)
    have hcr1 : cr1 = Color.black := by
      cases cr1 with
      | red => exact absurd (show (node Color.red rl1 rk1 rr1).IsRed from rfl) hrnr
      | black => rfl
    subst hcr1
    have hc1 : c1 = Color.red := by
      rcases hred1 with h | h
      · exact absurd h hrnr
      · exact h
    subst hc1
    have hll : LeftLeaning (node Color.red l1 k1 (node Color.black rl1 rk1 rr1)) :=
      ⟨hrnr, hll1, hllr1⟩
    have hspec := moveRedRight_spec (l := l1) (rl := rl1) (rr := rr1) (k := k1) (rk := rk1)
      hll hnrr1 hbal1 hrlnr
    have hextra := moveRedRight_deleteOk (a := a) (l := l1) (rl := rl1) (rr := rr1) (k := k1)
      (rk := rk1) hll hnrr1 hbal1 hrlnr hak1 (keyLt_of_sorted hs1)
    have hsm : Sorted (moveRedRight (node Color.red l1 k1 (node Color.black rl1 rk1 rr1))) :=
      sorted_moveRedRight hs1
    rw [hh3] at hspec hextra hsm
    obtain ⟨hlll, hlnrr, hlbal, -, hrnrr, hrbal, hbheq, hcr', hbhpres, -⟩ := hspec
    obtain ⟨hcl', hdisj⟩ := hextra
    simp only [left, right] at hlll hlnrr hlbal hrnrr hrbal hbheq hcr' hcl' hdisj
    refine ⟨hbhpres, ⟨hbheq, hlbal, hrbal⟩,
      ⟨fun hc => ⟨hcl' (by simpa [IsRed] using hc), hcr' (by simpa [IsRed] using hc)⟩,
        hlnrr, hrnrr⟩, hsm, hlll, ?_, fun _ => rfl, Or.inl rfl, ?_⟩
    · intro hc
      exact ⟨hcl' (by simpa [IsRed] using hc), hcr' (by simpa [IsRed] using hc)⟩
    · rcases hdisj with h | ⟨h, hk⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, by simpa [KeyLt] using hk⟩

/-- **`delete` preserves every color invariant**, under the precondition `DeleteOk`.
Black height is preserved exactly, and a red root only ever comes back from a red root. -/
theorem delete_spec {t : LLRB α} (a : α) :
    Sorted t → Balanced t → NoRedRed t → DeleteOk a t →
    bheight (delete a t) = bheight t ∧ Balanced (delete a t) ∧
    LeftLeaning (delete a t) ∧ NoRedRed (delete a t) ∧
    ((delete a t).IsRed → t.IsRed) := by
  induction t using delete.induct (a := a) with
  | case1 =>
    intro _ _ _ _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [delete, Balanced, LeftLeaning, NoRedRed, IsRed, bheight]
  | case2 c l k r hak hh =>
    intro _ _ _ _
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    intro hs hbal hnrr hok
    -- the relaxed shape forces `¬ a < k`, so here we are necessarily in the strict shape
    have hstrict : LeftLeaning (node c l k r) ∧ NotTwoNode (node c l k r) := by
      rcases hok with hlf | h | ⟨-, -, -, -, hkey⟩
      · exact absurd hlf (by simp)
      · exact h
      · exact absurd hak (by simpa [KeyLe] using hkey)
    obtain ⟨ht_ll, ht_ntn⟩ := hstrict
    rw [delete_lt hak hh]
    split at hh
    case isTrue hguard =>
      obtain ⟨hlnotred, hllnotred⟩ : ¬ l.IsRed ∧ ¬ l.left.IsRed := by
        have hb : l.isRed = false ∧ l.left.isRed = false := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        exact ⟨isRed_eq_false_iff.mp hb.1, isRed_eq_false_iff.mp hb.2⟩
      have hc : c = Color.red := isRed_of_notTwoNode ht_ntn hlnotred
      subst hc
      rcases l with _ | ⟨cl, ll, lk, lr⟩
      · -- `l = leaf`: `Balanced` forces `r = leaf` too, and `moveRedLeft` is then the identity
        have hrleaf : r = leaf := by
          rcases r with _ | ⟨cr, rl, rk, rr⟩
          · rfl
          · exfalso
            have hcr : cr = Color.black := by
              cases cr with
              | red => exact absurd (show (node Color.red rl rk rr).IsRed from rfl) ht_ll.1
              | black => rfl
            subst hcr
            have := bheight_pos rl
            have h1 : bheight (leaf : LLRB α) = bheight (node Color.black rl rk rr) := hbal.1
            simp [bheight] at h1
            omega
        subst hrleaf
        have hml : moveRedLeft (node Color.red (leaf : LLRB α) k leaf)
            = node Color.red leaf k leaf := by
          simp [moveRedLeft, flipColors, left, right, isRed]
        rw [hml] at hh
        injection hh with e1 e2 e3 e4
        subst e1; subst e2; subst e3; subst e4
        have hdl : delete a (leaf : LLRB α) = leaf := by simp [delete]
        rw [hdl]
        have hfx : fixUp (node Color.red (leaf : LLRB α) k leaf) = node Color.red leaf k leaf := by
          simp [fixUp, left, right, isRed]
        rw [hfx]
        exact ⟨rfl, hbal, ht_ll, hnrr, fun _ => rfl⟩
      have hcl : cl = Color.black := by
        cases cl with
        | red => exact absurd (show (node Color.red ll lk lr).IsRed from rfl) hlnotred
        | black => rfl
      subst hcl
      have hspec := moveRedLeft_spec (ll := ll) (lr := lr) (r := r) (k := k) (lk := lk)
        ht_ll hnrr hbal hllnotred
      rw [hh] at hspec
      obtain ⟨hl'_ll, hl'_nrr, hl'_bal, hr'_ll, hr'_nrr, hr'_bal, hbh', hcr', hcl', hbh_pres,
        hntn_l'⟩ := hspec
      have hs' : Sorted (node c' l' k' r') := by rw [← hh]; exact sorted_moveRedLeft hs
      obtain ⟨hbhd, hbald, hlld, hnrrd, hredd⟩ :=
        ih hs'.2.2.1 hl'_bal hl'_nrr (Or.inr (Or.inl ⟨hl'_ll, hntn_l'⟩))
      have hc' : c' = Color.red → ¬ (delete a l').IsRed ∧ ¬ r'.IsRed := fun hred =>
        ⟨fun hdred => hcl' hred (hredd hdred), hcr' hred⟩
      obtain ⟨hbh3, hbal3, hll3, hnrr3, -⟩ :=
        fixUp_delete_spec (c := c') (l := delete a l') (r := r') (k := k')
          hlld hr'_ll hnrrd hr'_nrr hbald hr'_bal (by rw [hbhd]; exact hbh') hc'
      refine ⟨?_, hbal3, hll3, hnrr3, fun _ => rfl⟩
      rw [hbh3, hbhd]
      exact hbh_pres
    case isFalse hguard =>
      injection hh with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      have hntn_l : NotTwoNode l := by
        have hb : l.isRed = true ∨ l.left.isRed = true := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        rcases hb with hb | hb
        · exact Or.inl (isRed_iff.mp hb)
        · exact Or.inr (isRed_iff.mp hb)
      obtain ⟨hbhd, hbald, hlld, hnrrd, hredd⟩ :=
        ih hs.2.2.1 hbal.2.1 hnrr.2.1 (Or.inr (Or.inl ⟨ht_ll.2.1, hntn_l⟩))
      have hc' : c = Color.red → ¬ (delete a l).IsRed ∧ ¬ r.IsRed := fun hred =>
        ⟨fun hdred => (hnrr.1 hred).1 (hredd hdred), (hnrr.1 hred).2⟩
      obtain ⟨hbh3, hbal3, hll3, hnrr3, hred3⟩ :=
        fixUp_delete_spec (c := c) (l := delete a l) (r := r) (k := k)
          hlld ht_ll.2.2 hnrrd hnrr.2.2 hbald hbal.2.2 (by rw [hbhd]; exact hbal.1) hc'
      refine ⟨by rw [hbh3, hbhd]; simp [bheight], hbal3, hll3, hnrr3, ?_⟩
      intro hred
      rcases hred3 hred with hc | hr
      · exact hc
      · exact absurd hr ht_ll.1
  | case4 c l k r hak hh =>
    intro _ _ _ _
    exfalso; revert hh; split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    intro hs hbal hnrr hok
    obtain ⟨hbh, hbal1, hnrr1, hs1, hll1, hllr, hak1, hl1nr, hred1, hisred⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh
    have hc1 : c1 = Color.red := by
      rcases hred1 with h | h
      · exact absurd h (by simp [IsRed])
      · exact h
    subst hc1
    rw [delete_ge_splice hak hh]
    exact ⟨by simpa [bheight] using hbh, hbal1.2.1, hll1, hnrr1.2.1, fun h => absurd h hl1nr⟩
  | case6 c l k r hak c1 l1 k1 hh hne =>
    intro hs hbal hnrr hok
    obtain ⟨hbh, hbal1, hnrr1, hs1, hll1, hllr, hak1, hl1nr, hred1, hisred⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh
    have hc1 : c1 = Color.red := by
      rcases hred1 with h | h
      · exact absurd h (by simp [IsRed])
      · exact h
    subst hc1
    rw [delete_ge_fixUp hak hh hne]
    obtain ⟨hbh3, hbal3, hll3, hnrr3, -⟩ :=
      fixUp_delete_spec (c := Color.red) (l := l1) (r := leaf) (k := k1)
        hll1 trivial hnrr1.2.1 trivial hbal1.2.1 trivial hbal1.1
        (fun _ => ⟨hl1nr, by simp [IsRed]⟩)
    refine ⟨?_, hbal3, hll3, hnrr3, fun _ => hisred rfl⟩
    rw [hbh3]
    simpa [bheight] using hbh
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    intro _ _ _ _
    exfalso; revert hh3; split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    intro hs hbal hnrr hok
    obtain ⟨hbh1, hbal1, hnrr1, hs1, hll1, hllr1, hak1, hl1nr, hred1, hisred1⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh2
    obtain ⟨hbh2, hbal2, hnrr2, hs2, hll2, hc2, hisred2, hl2red, hdisj⟩ :=
      moveRedRight_guard_spec hs1 hbal1 hnrr1 hll1 hllr1 hak1 hl1nr hred1 hh3
    -- the relaxed branch would force `a < k1`, contradicting this branch's own guard
    obtain ⟨hllr2, hntn2⟩ : LeftLeaning r' ∧ NotTwoNode r' := by
      rcases hdisj with h | ⟨-, hk⟩
      · exact h
      · exact absurd hk (by simpa using hak1)
    obtain ⟨hbhd, hbald, hlld, hnrrd, hredd⟩ :=
      deleteMin_spec hbal2.2.2 hllr2 hnrr2.2.2 hntn2
    rw [delete_ge_succ hak hh2 hh3 hmin]
    obtain ⟨hbh3, hbal3, hll3, hnrr3, -⟩ :=
      fixUp_delete_spec (c := c') (l := l') (r := deleteMin r') (k := m)
        hll2 hlld hnrr2.2.1 hnrrd hbal2.2.1 hbald (by rw [hbhd]; exact hbal2.1)
        (fun hc => ⟨(hc2 hc).1, fun hd => (hc2 hc).2 (hredd hd)⟩)
    refine ⟨?_, hbal3, hll3, hnrr3, ?_⟩
    · rw [hbh3]
      have he : bheight (node c' l' a r')
          = bheight l' + (if c' = Color.black then 1 else 0) := rfl
      rw [← he, hbh2]; exact hbh1
    · intro hred
      rcases fixUp_isRed_cases hnrr2.2.1 hnrrd hll2 hlld hred with hc | ⟨hl2r, -⟩
      · exact hisred1 (hisred2 (by simpa [IsRed] using hc))
      · rcases hl2red with h | h
        · exact hisred1 h
        · exact absurd hl2r h
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    intro _ _ _ _
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    intro hs hbal hnrr hok
    obtain ⟨hbh1, hbal1, hnrr1, hs1, hll1, hllr1, hak1, hl1nr, hred1, hisred1⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh2
    obtain ⟨hbh2, hbal2, hnrr2, hs2, hll2, hc2, hisred2, hl2red, hdisj⟩ :=
      moveRedRight_guard_spec hs1 hbal1 hnrr1 hll1 hllr1 hak1 hl1nr hred1 hh3
    have hok2 : DeleteOk a r' := by
      rcases hdisj with h | ⟨h, -⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨hbhd, hbald, hlld, hnrrd, hredd⟩ := ih hs2.2.2.2 hbal2.2.2 hnrr2.2.2 hok2
    rw [delete_ge_rec hak hh2 hh3 hne]
    obtain ⟨hbh3, hbal3, hll3, hnrr3, -⟩ :=
      fixUp_delete_spec (c := c') (l := l') (r := delete a r') (k := k')
        hll2 hlld hnrr2.2.1 hnrrd hbal2.2.1 hbald (by rw [hbhd]; exact hbal2.1)
        (fun hc => ⟨(hc2 hc).1, fun hd => (hc2 hc).2 (hredd hd)⟩)
    refine ⟨?_, hbal3, hll3, hnrr3, ?_⟩
    · rw [hbh3]
      have he : bheight (node c' l' k' r')
          = bheight l' + (if c' = Color.black then 1 else 0) := rfl
      rw [← he, hbh2]; exact hbh1
    · intro hred
      rcases fixUp_isRed_cases hnrr2.2.1 hnrrd hll2 hlld hred with hc | ⟨hl2r, -⟩
      · exact hisred1 (hisred2 (by simpa [IsRed] using hc))
      · rcases hl2red with h | h
        · exact hisred1 h
        · exact absurd hl2r h

/-- **`deleteTop` takes a legal LLRB tree to a legal LLRB tree.** With `valid_insert` and
`valid_deleteMinTop`, this completes the structure: every public operation is verified. -/
theorem valid_deleteTop {t : LLRB α} (hv : Valid t) (a : α) : Valid (deleteTop a t) := by
  have hv' := hv
  obtain ⟨hs, hrb, hll, hnrr, hbh⟩ := hv
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  simp only [deleteTop]
  split
  case isFalse => exact hv'
  by_cases hne : t = leaf
  · subst hne
    have h2 : delete a (leaf : LLRB α) = leaf := by simp [delete]
    simp only [prime, h2, blacken]
    exact ⟨trivial, trivial, trivial, trivial, Option.some_ne_none _⟩
  · obtain ⟨hpb, hpl, hpn, hpt⟩ := prime_spec hne hbal hll hnrr
    obtain ⟨-, hdb, hdl, hdn, -⟩ :=
      delete_spec a (sorted_prime hs) hpb hpn (Or.inr (Or.inl ⟨hpl, hpt⟩))
    exact ⟨sorted_blacken (sorted_delete (sorted_prime hs) a), rootBlack_blacken _,
      leftLeaning_blacken hdl, noRedRed_blacken hdn,
      blackHeightOk_iff_balanced.mpr (balanced_blacken hdb)⟩

/-- **`deleteTop` discharges `DeleteSpec`** on a legal tree, assembled from `mem_deleteTop_iff` and
`valid_deleteTop`. The `Valid` hypothesis is what makes the key-set half available: on an unsorted
tree the descent can walk past the side `a` is on. -/
theorem deleteTopSpec {{t : LLRB α}} (hv : Valid t) (a : α) : DeleteSpec a t (deleteTop a t) :=
  ⟨mem_deleteTop_iff hv.1 a, fun h => valid_deleteTop h a⟩

/-- **Argued, not proved:** a delete that counts as search counts, one three-way comparison per
node on the path it walks down (to the key, then on to its successor), answers as the delete does,
and takes at most `2 log₂(n + 1)` of them. The bound is on the walk itself: its moves restructure
the path as it goes, so the walk can be longer than the tree's height before it began, but not
longer than the bound. The membership test before the walk is a search, bounded by `Contract.cost`.
Lean has no counted delete, by choice, so `Contract` does not include it. -/
def DeleteCost (o : Ops α) (deleteM : α → LLRB α → TimeM ℕ (LLRB α)) : Prop :=
  (∀ a t, (deleteM a t).ret = o.tree.delete a t) ∧
    o.tree.Within deleteM (fun n => 2 * Nat.log2 (n + 1))

end LLRB

end AlgoDesign.Searching
