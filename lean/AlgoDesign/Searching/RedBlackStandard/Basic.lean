/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Spec

/-!
# Red-black tree: structural bookkeeping

What the operations share: `Color.flip`, `Mem`/`All` lemmas, the general (either-leaning)
rotations `rotateLeft`/`rotateRight` with `isRed` and `blacken`, `bheight`/`Balanced` (a total
stand-in for `blackHeight`, bridged back by `blackHeight_eq_some_iff`), `size`/`height`, and
`toList` against `Mem`. The specification they serve is in `Spec.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- Flip red ↔ black — what `LLRB.flipColors` does to each of the three links it touches
(shared here rather than duplicated in `LLRB`, since `Color` itself is shared). -/
def Color.flip : Color → Color
  | .red => .black
  | .black => .red

namespace RBTree

variable {α : Type}

theorem All.of_mem {p : α → Prop} {t : RBTree α} (h : All p t) {a : α} (ha : Mem a t) : p a := by
  induction t with
  | leaf => cases ha
  | node _ l k r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    rcases ha with ha | rfl | ha
    · exact ihl hl ha
    · exact hk
    · exact ihr hr ha

variable [LinearOrder α]

/-! ### `Mem`/`All` helper lemmas

Small helpers in `LLRB`'s style, needed by the color-blind rotation/fixup lemmas below and by
nothing above. -/

omit [LinearOrder α] in
@[simp] theorem mem_leaf (a : α) : Mem a (leaf : RBTree α) ↔ False := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem mem_node (a : α) (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    Mem a (node c l k r) ↔ Mem a l ∨ a = k ∨ Mem a r := Iff.rfl

omit [LinearOrder α] in
theorem All.imp {p q : α → Prop} (h : ∀ a, p a → q a) : ∀ {t : RBTree α}, All p t → All q t
  | leaf, _ => trivial
  | node _ _ _ _, ⟨hl, hk, hr⟩ => ⟨hl.imp (fun _ => h _), h _ hk, hr.imp (fun _ => h _)⟩

omit [LinearOrder α] in
theorem all_of_forall_mem {p : α → Prop} {t : RBTree α} (h : ∀ b, Mem b t → p b) : All p t := by
  induction t with
  | leaf => trivial
  | node _ l k r ihl ihr =>
    exact ⟨ihl (fun b hb => h b (Or.inl hb)), h k (Or.inr (Or.inl rfl)),
      ihr (fun b hb => h b (Or.inr (Or.inr hb)))⟩

/-! ### General (either-leaning) rotation

Unlike `LLRB.rotateLeft`, which only ever rotates left of a red *right* link (and forces the
demoted node's color to red as part of that single-purpose move), CLRS's `RB-INSERT-FIXUP`/
`RB-DELETE-FIXUP` rotate freely in *both* directions and never touch any node's color as part of a
rotation — CLRS keeps rotation and recoloring as two separate operations (`LEFT-ROTATE`/
`RIGHT-ROTATE` vs. explicit `.color =` assignments), and this section follows that split. -/

/-- CLRS's `LEFT-ROTATE`: the root's right child comes up to take the root's place, the old root
becomes its new left child. No node's color changes. Only meaningful (and only ever called) when
the root actually has a right child to rotate up; the fallback case returns the input unchanged,
since there's nothing to rotate. -/
def rotateLeft : RBTree α → RBTree α
  | node cx lx kx (node cy ly ky ry) => node cy (node cx lx kx ly) ky ry
  | t => t

/-- CLRS's `RIGHT-ROTATE`, symmetric to `rotateLeft`. -/
def rotateRight : RBTree α → RBTree α
  | node cx (node cy ly ky ry) kx rx => node cy ly ky (node cx ry kx rx)
  | t => t

/-- Is the node's own color red? `Bool`-valued, for use inside `insertFixupL`/`insertFixupR`'s
executable guards below — mirrors `LLRB.isRed`, though here it reads the color off the node
itself rather than off the link into it (see `Color`'s docstring on `RBTree.node` for why that
distinction doesn't matter). `leaf` (NIL) counts as not red, matching CLRS's "every NIL is
black". -/
def isRed : RBTree α → Bool
  | node .red _ _ _ => true
  | _ => false

/-- Force a node's own color to black, leaving its children untouched — CLRS's `.color = BLACK`
assignment. Used both by `insert` (to force the *root* black at the very end, since the fixup
loop can leave it red) and inside `insertFixupL`/`insertFixupR`'s Case 1 and Case 3 recolorings. -/
def blacken : RBTree α → RBTree α
  | leaf => leaf
  | node _ l k r => node .black l k r

omit [LinearOrder α] in
theorem mem_rotateLeft (t : RBTree α) (b : α) : Mem b (rotateLeft t) ↔ Mem b t := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [rotateLeft]
  tauto

omit [LinearOrder α] in
theorem mem_rotateRight (t : RBTree α) (b : α) : Mem b (rotateRight t) ↔ Mem b t := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩ <;> simp [rotateRight]
  tauto

omit [LinearOrder α] in
theorem mem_blacken (t : RBTree α) (b : α) : Mem b (blacken t) ↔ Mem b t := by
  cases t <;> simp [blacken]

theorem sorted_rotateLeft {t : RBTree α} (ht : Sorted t) : Sorted (rotateLeft t) := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩
  · trivial
  · exact ht
  · obtain ⟨hl, hr, hsl, hsr⟩ := ht
    obtain ⟨hrl_lt, hk_lt_rk, hrr_lt⟩ := hr
    obtain ⟨hrl_bound, hrr_bound, hsrl, hsrr⟩ := hsr
    exact ⟨⟨hl.imp (fun _ hx => lt_trans hx hk_lt_rk), hk_lt_rk, hrl_bound⟩, hrr_bound,
      ⟨hl, hrl_lt, hsl, hsrl⟩, hsrr⟩

theorem sorted_rotateRight {t : RBTree α} (ht : Sorted t) : Sorted (rotateRight t) := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩
  · trivial
  · exact ht
  · obtain ⟨hl, hr, hsl, hsr⟩ := ht
    obtain ⟨hll_lt_k, hlk_lt_k, hlr_lt_k⟩ := hl
    obtain ⟨hll_bound, hlr_bound, hsll, hslr⟩ := hsl
    exact ⟨hll_bound, ⟨hlr_bound, hlk_lt_k, hr.imp (fun _ hx => lt_trans hlk_lt_k hx)⟩, hsll,
      ⟨hlr_lt_k, hr, hslr, hsr⟩⟩

theorem sorted_blacken {t : RBTree α} (ht : Sorted t) : Sorted (blacken t) := by
  cases t <;> exact ht

omit [LinearOrder α] in
theorem all_rotateLeft {p : α → Prop} (t : RBTree α) : All p (rotateLeft t) ↔ All p t := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [rotateLeft, All]
  tauto

omit [LinearOrder α] in
theorem all_rotateRight {p : α → Prop} (t : RBTree α) : All p (rotateRight t) ↔ All p t := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩ <;> simp [rotateRight, All]
  tauto

omit [LinearOrder α] in
theorem all_blacken {p : α → Prop} (t : RBTree α) : All p (blacken t) ↔ All p t := by
  cases t <;> simp [blacken, All]

/-! ### A total black height

`blackHeight` is `Option`-valued; the proofs run on `bheight`, its left spine read as a plain `ℕ`,
and `Balanced`, which says every path agrees with it. `blackHeightOk_iff_balanced` bridges the two
back. -/

/-- The number of black nodes from the root down the *left* spine -- a total stand-in for
`blackHeight`'s partial `Option ℕ` version, used only as a proof device (identical in spirit, and
in code, to `LLRB.bheight`). Counts `leaf` itself as contributing one black node, matching
`blackHeight`'s own convention. -/
def bheight : RBTree α → ℕ
  | leaf => 1
  | node c l _ _ => bheight l + if c = .black then 1 else 0

/-- Every root-to-leaf path has the same number of black nodes as `bheight` counts down the left
spine -- the total, structurally-recursive counterpart to `BlackHeightOk`'s `Option`-based "every
path agrees" formulation. Equivalent to it: see `blackHeight_eq_some_iff`. -/
def Balanced : RBTree α → Prop
  | leaf => True
  | node _ l _ r => bheight l = bheight r ∧ Balanced l ∧ Balanced r

omit [LinearOrder α] in
/-- A balanced tree's `blackHeight` is defined, and agrees with `bheight`. -/
theorem blackHeight_of_balanced {t : RBTree α} (h : Balanced t) :
    t.blackHeight = some (bheight t) := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hl, hr⟩ := h
    simp [blackHeight, ihl hl, ihr hr, hbh, bheight]

omit [LinearOrder α] in
/-- Converse of `blackHeight_of_balanced`: a defined `blackHeight` forces `Balanced`, and pins the
value to `bheight`. -/
theorem balanced_of_blackHeight {t : RBTree α} {n : ℕ} (h : t.blackHeight = some n) :
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
theorem blackHeight_eq_some_iff {t : RBTree α} {n : ℕ} :
    t.blackHeight = some n ↔ Balanced t ∧ bheight t = n :=
  ⟨balanced_of_blackHeight, fun h => h.2 ▸ blackHeight_of_balanced h.1⟩

omit [LinearOrder α] in
theorem blackHeightOk_iff_balanced {t : RBTree α} : BlackHeightOk t ↔ Balanced t := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.mp h
    exact (blackHeight_eq_some_iff.mp hn).1
  · intro h
    simp [BlackHeightOk, blackHeight_of_balanced h]

omit [LinearOrder α] in
/-- `bheight` never hits zero -- even `leaf` alone contributes one black node. Needed by the
`delete`-side color-invariant proofs below: a spliced-out black root forces a `bheight ... = 1`
hypothesis on some subtree, and `omega` needs this lower bound to see that a resulting `bheight x =
0` (from a genuinely-unreachable branch) is actually a contradiction. -/
theorem bheight_pos (t : RBTree α) : 1 ≤ bheight t := by
  induction t with
  | leaf => simp [bheight]
  | node c l k r ihl _ => cases c <;> simp only [bheight] <;> omega

omit [LinearOrder α] in
@[simp] theorem IsBlack_leaf : IsBlack (leaf : RBTree α) := trivial

omit [LinearOrder α] in
@[simp] theorem IsBlack_node (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    IsBlack (node c l k r) ↔ c = .black := Iff.rfl

/-! ### The keys as a list, and range queries

`range` is a specification: the keys the bounds admit, in order. Color plays no part. -/

omit [LinearOrder α] in
@[simp] theorem toList_leaf : toList (leaf : RBTree α) = [] := rfl

omit [LinearOrder α] in
@[simp] theorem toList_node (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    toList (node c l k r) = toList l ++ k :: toList r := rfl

omit [LinearOrder α] in
/-- **`toList` observes exactly `Mem`.** -/
theorem mem_toList {a : α} : ∀ t : RBTree α, a ∈ toList t ↔ Mem a t
  | leaf => by simp [Mem]
  | node _ l k r => by
      simp only [toList_node, List.mem_append, List.mem_cons, Mem,
        mem_toList l, mem_toList r]

/-- Number of keys. Computed, not cached — same role as `BST.size`. -/
def size : RBTree α → ℕ
  | leaf => 0
  | node _ l _ r => l.size + r.size + 1

omit [LinearOrder α] in
@[simp] theorem size_leaf : size (leaf : RBTree α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem size_node (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    size (node c l k r) = l.size + r.size + 1 := rfl

/-- Longest root-to-leaf path, in edges. `leaf` (NIL) has height 0. -/
def height : RBTree α → ℕ
  | leaf => 0
  | node _ l _ r => max (height l) (height r) + 1

omit [LinearOrder α] in
@[simp] theorem height_leaf : height (leaf : RBTree α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem height_node (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    height (node c l k r) = max (height l) (height r) + 1 := rfl

end RBTree

end AlgoDesign.Searching
