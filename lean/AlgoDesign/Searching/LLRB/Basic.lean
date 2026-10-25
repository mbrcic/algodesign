/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Spec
public import AlgoDesign.Searching.RedBlackStandard.Basic

/-!
# LLRB: structural bookkeeping

The helpers and lemmas the operations share: `isRed`/`left`/`right` (the `Bool`-valued helpers
Sedgewick's pseudocode uses), `All` and `Mem` lemmas, `bheight`/`Balanced` (a total stand-in for
`blackHeight`, bridged back by `blackHeight_eq_some_iff`), `size`/`height`, and `toList` against
`Mem`. The specification they serve is in `Spec.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}

/-- Is `a` a key of the tree? Same role as `BST.Mem`. -/
def Mem (a : α) : LLRB α → Prop
  | leaf => False
  | node _ l k r => Mem a l ∨ a = k ∨ Mem a r

/-- Is the link into this node red? `Bool`-valued, for use in the algorithms themselves — see
`IsRed` for the `Prop`-valued version the invariants are stated with. Named after Sedgewick's own
`isRed(h)` helper, used throughout his pseudocode. -/
def isRed : LLRB α → Bool
  | leaf => false
  | node .red _ _ _ => true
  | node .black _ _ _ => false

/-- The left subtree (`leaf` itself, for a `leaf`). -/
def left : LLRB α → LLRB α
  | leaf => leaf
  | node _ l _ _ => l

/-- The right subtree (`leaf` itself, for a `leaf`). -/
def right : LLRB α → LLRB α
  | leaf => leaf
  | node _ _ _ r => r

theorem All.of_mem {p : α → Prop} {t : LLRB α} (h : All p t) {a : α} (ha : Mem a t) : p a := by
  induction t with
  | leaf => cases ha
  | node _ l k r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    rcases ha with ha | rfl | ha
    · exact ihl hl ha
    · exact hk
    · exact ihr hr ha

variable [LinearOrder α]

/-! ### A total black height

`blackHeight` is `Option`-valued; the proofs run on `bheight`, its left spine read as a plain `ℕ`,
and `Balanced`, which says every path agrees with it. `blackHeightOk_iff_balanced` bridges the two
back. -/

/-- The number of black links from the root down the *left* spine -- a total stand-in for
`blackHeight`'s partial `Option ℕ` version, used only as a proof device. Counts `leaf` itself as
contributing one black link, matching `blackHeight`'s own convention. -/
def bheight : LLRB α → ℕ
  | leaf => 1
  | node c l _ _ => bheight l + if c = .black then 1 else 0

/-- Every root-to-leaf path has the same number of black links as `bheight` counts down the left
spine -- the total, structurally-recursive counterpart to `BlackHeightOk`'s `Option`-based "every
path agrees" formulation. Equivalent to it: see `blackHeight_eq_some_iff`. -/
def Balanced : LLRB α → Prop
  | leaf => True
  | node _ l _ r => bheight l = bheight r ∧ Balanced l ∧ Balanced r

omit [LinearOrder α] in
/-- The `Bool`-valued `isRed` reflects the `Prop`-valued `IsRed` — the "not red" direction, which
is the one the fix-up guards are driven by. -/
theorem isRed_eq_false {t : LLRB α} (h : ¬ t.IsRed) : t.isRed = false := by
  cases t with
  | leaf => rfl
  | node c _ _ _ => cases c with
    | red => exact absurd rfl h
    | black => rfl

omit [LinearOrder α] in
/-- `isRed` on a node reached by a red link. -/
theorem isRed_red {l r : LLRB α} {k : α} : (node .red l k r).isRed = true := rfl

omit [LinearOrder α] in
/-- A black root link is in particular not a red one. -/
theorem not_isRed_of_rootBlack {t : LLRB α} (h : RootBlack t) : ¬ t.IsRed := by
  cases t with
  | leaf => exact id
  | node c _ _ _ => intro hc; subst hc; exact Color.noConfusion h

omit [LinearOrder α] in
/-- A balanced tree's `blackHeight` is defined, and agrees with `bheight`. -/
theorem blackHeight_of_balanced {t : LLRB α} (h : Balanced t) :
    t.blackHeight = some (bheight t) := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hl, hr⟩ := h
    simp [blackHeight, ihl hl, ihr hr, hbh, bheight]

omit [LinearOrder α] in
/-- Converse of `blackHeight_of_balanced`: a defined `blackHeight` forces `Balanced`, and pins the
value to `bheight`. -/
theorem balanced_of_blackHeight {t : LLRB α} {n : ℕ} (h : t.blackHeight = some n) :
    Balanced t ∧ bheight t = n := by
  induction t generalizing n with
  | leaf => simpa [blackHeight, Balanced, bheight, eq_comm] using h
  | node c l k r ihl ihr =>
    rcases hl : l.blackHeight with _ | bl
    · rw [blackHeight, hl] at h; simp at h
    rcases hr : r.blackHeight with _ | br
    · rw [blackHeight, hl, hr] at h; simp at h
    obtain ⟨hbl, hbl'⟩ := ihl hl
    obtain ⟨hbr, hbr'⟩ := ihr hr
    rw [blackHeight, hl, hr] at h
    by_cases hc : c = Color.black <;> simp [hc] at h <;>
      exact ⟨⟨by omega, hbl, hbr⟩, by simp [bheight, hc]; omega⟩

omit [LinearOrder α] in
/-- Bridges the total `bheight`/`Balanced` pair back to the `blackHeight`/`BlackHeightOk`
spec, so nothing downstream needs to touch the awkward `Option`-`do` definition directly. -/
theorem blackHeight_eq_some_iff {t : LLRB α} {n : ℕ} :
    t.blackHeight = some n ↔ Balanced t ∧ bheight t = n :=
  ⟨balanced_of_blackHeight, fun h => h.2 ▸ blackHeight_of_balanced h.1⟩

omit [LinearOrder α] in
theorem blackHeightOk_iff_balanced {t : LLRB α} : BlackHeightOk t ↔ Balanced t := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact (blackHeight_eq_some_iff.mp hn).1
  · intro h
    simp [BlackHeightOk, blackHeight_of_balanced h]

/-! ### `size`, needed to justify termination of `deleteMin`/`delete`

Sedgewick's `deleteMin`/`delete` recurse into a subtree that has first been run through
`moveRedLeft`/`moveRedRight` — a rotation-based restructuring, not a shrink — so the recursive call
below isn't on a literal subterm of the original input the way `insertAux`'s is, and Lean's
structural-recursion checker can't see termination on its own. `size` (total node count) is the
well-founded measure that closes the gap: `flipColors`/`rotateLeft`/`rotateRight` (and hence
`moveRedLeft`/`moveRedRight`, built from them) never change it, so the transformed tree is exactly
as big as the input, and its `.left`/`.right` child is still strictly smaller than the whole. -/

omit [LinearOrder α] in
/-- Number of nodes. The box's bounds are in `SearchTree.size`, the number of keys held; on a valid
tree the two agree (`tree_size`). -/
def size : LLRB α → ℕ
  | leaf => 0
  | node _ l _ r => l.size + r.size + 1

/-! ### The keys as a list, and range queries

`range` is a specification: the keys the bounds admit, in order. Color plays no part. -/

omit [LinearOrder α] in
@[simp] theorem toList_leaf : toList (leaf : LLRB α) = [] := rfl

omit [LinearOrder α] in
@[simp] theorem toList_node (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    toList (node c l k r) = toList l ++ k :: toList r := rfl

omit [LinearOrder α] in
/-- **`toList` observes exactly `Mem`.** -/
theorem mem_toList {a : α} : ∀ t : LLRB α, a ∈ toList t ↔ Mem a t
  | leaf => by simp [Mem]
  | node _ l k r => by
      simp only [toList_node, List.mem_append, List.mem_cons, Mem,
        mem_toList l, mem_toList r]

omit [LinearOrder α] in
@[simp] theorem size_leaf : size (leaf : LLRB α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem size_node (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    size (node c l k r) = l.size + r.size + 1 := rfl

omit [LinearOrder α] in
@[simp] theorem height_leaf : height (leaf : LLRB α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem height_node (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    height (node c l k r) = max (height l) (height r) + 1 := rfl

omit [LinearOrder α] in
theorem size_left_lt {c : Color} {l : LLRB α} {k : α} {r : LLRB α} :
    l.size < (node c l k r).size := by simp only [size_node]; omega

omit [LinearOrder α] in
theorem size_right_lt {c : Color} {l : LLRB α} {k : α} {r : LLRB α} :
    r.size < (node c l k r).size := by simp only [size_node]; omega

end LLRB

end AlgoDesign.Searching
