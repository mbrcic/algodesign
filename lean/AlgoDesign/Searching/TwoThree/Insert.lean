/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.TwoThree.Encoding

/-!
# 2-3 trees: insertion

The textbook 2-3 insert (`insert`: a 4-node splits and passes its middle key up), which keeps a
tree balanced and sorted and adds exactly its key (`sameDepth_insert`, `sorted_insert`,
`mem_insert`); and `toLlrb_insert`: `LLRB.insert` on an encoding computes the encoding of this
insert, level by level (`insertAux_toLlrb`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace T23

variable {α : Type}
variable [LinearOrder α]

/-! ### Insert: into the leaf, split a 4-node, pass its middle key up -/

/-- What inserting into a subtree hands back to its parent: a tree of the same height (`done`), or
the two halves of a split 4-node with the middle key between them, to be absorbed one level up
(`up`). -/
inductive Ins (α : Type) : Type where
  /-- The subtree absorbed the key and kept its height. -/
  | done (t : T23 α) : Ins α
  /-- The subtree split: a middle key to pass up, with the 2-nodes either side of it. -/
  | up (l : T23 α) (k : α) (r : T23 α) : Ins α

/-- Sedgewick's 2-3 insert (*Algorithms*, 4th ed., §3.3). Search to the bottom; a new key at a
leaf position arrives as a key passed up from below. A 2-node that receives a key becomes a
3-node. A 3-node that receives one is momentarily a 4-node; it splits into two 2-nodes and passes
its middle key up to its own parent. A key already present leaves the tree unchanged. -/
def ins (x : α) : T23 α → Ins α
  | leaf => .up leaf x leaf
  | two l k r =>
      if x < k then
        match ins x l with
        | .done l' => .done (two l' k r)
        | .up p q s => .done (three p q s k r)
      else if k < x then
        match ins x r with
        | .done r' => .done (two l k r')
        | .up p q s => .done (three l k p q s)
      else .done (two l k r)
  | three l a m b r =>
      if x < a then
        match ins x l with
        | .done l' => .done (three l' a m b r)
        | .up p q s => .up (two p q s) a (two m b r)
      else if a < x then
        if x < b then
          match ins x m with
          | .done m' => .done (three l a m' b r)
          | .up p q s => .up (two l a p) q (two s b r)
        else if b < x then
          match ins x r with
          | .done r' => .done (three l a m b r')
          | .up p q s => .up (two l a m) b (two p q s)
        else .done (three l a m b r)
      else .done (three l a m b r)

/-- Insert `x`. A key passed up out of the root becomes a new 2-node root, the only way a 2-3 tree
grows taller. -/
def insert (x : α) (t : T23 α) : T23 α :=
  match ins x t with
  | .done t' => t'
  | .up l k r => two l k r

/-- The heights `ins` hands back: `done` keeps the height, and `up`'s two halves each have it. -/
def Ins.Fits (h : ℕ) : Ins α → Prop
  | .done t => SameDepth t ∧ height t = h
  | .up l _ r => SameDepth l ∧ SameDepth r ∧ height l = h ∧ height r = h

theorem ins_fits (x : α) : ∀ t : T23 α, SameDepth t → (ins x t).Fits (height t)
  | leaf, _ => by simp [ins, Ins.Fits, SameDepth, height]
  | two l k r, ⟨hlr, hl, hr⟩ => by
      have ihl := ins_fits x l hl
      have ihr := ins_fits x r hr
      unfold ins
      split_ifs
      · rcases h : ins x l with l' | ⟨p, q, s⟩ <;> rw [h] at ihl <;>
          simp_all [Ins.Fits, SameDepth, height]
      · rcases h : ins x r with r' | ⟨p, q, s⟩ <;> rw [h] at ihr <;>
          simp_all [Ins.Fits, SameDepth, height]
      · simp [Ins.Fits, SameDepth, height, hlr, hl, hr]
  | three l a m b r, ⟨hlm, hmr, hl, hm, hr⟩ => by
      have ihl := ins_fits x l hl
      have ihm := ins_fits x m hm
      have ihr := ins_fits x r hr
      unfold ins
      split_ifs
      · rcases h : ins x l with l' | ⟨p, q, s⟩ <;> rw [h] at ihl <;>
          simp_all [Ins.Fits, SameDepth, height]
      · rcases h : ins x m with m' | ⟨p, q, s⟩ <;> rw [h] at ihm <;>
          simp_all [Ins.Fits, SameDepth, height]
      · rcases h : ins x r with r' | ⟨p, q, s⟩ <;> rw [h] at ihr <;>
          simp_all [Ins.Fits, SameDepth, height]
      · simp [Ins.Fits, SameDepth, height, hlm, hmr, hl, hm, hr]
      · simp [Ins.Fits, SameDepth, height, hlm, hmr, hl, hm, hr]

/-- **Insert keeps a 2-3 tree balanced.** No rebalancing step exists to get wrong: every leaf
stays at one depth because the tree only grows at the root. -/
theorem sameDepth_insert {t : T23 α} (ht : SameDepth t) (x : α) : SameDepth (insert x t) := by
  have h := ins_fits x t ht
  unfold insert
  rcases hi : ins x t with t' | ⟨l, k, r⟩ <;> rw [hi] at h
  · exact h.1
  · exact ⟨h.2.2.1.trans h.2.2.2.symm, h.1, h.2.1⟩

/-! ### The LLRB insert is the 2-3 insert -/

/-- The encoding of what `ins` hands back: `done t` is `t`'s encoding, black-rooted; `up l k r` is
the key passed up, on a red link, over the encodings of the two halves. -/
def Ins.toLlrb : Ins α → LLRB α
  | .done t => T23.toLlrb t
  | .up l k r => .node .red (T23.toLlrb l) k (T23.toLlrb r)

omit [LinearOrder α] in
@[simp] theorem isRed_toLlrb (t : T23 α) : (toLlrb t).isRed = false := by
  cases t <;> rfl

omit [LinearOrder α] in
@[simp] theorem isRed_node_red (l : LLRB α) (k : α) (r : LLRB α) :
    (LLRB.node .red l k r).isRed = true := rfl

omit [LinearOrder α] in
@[simp] theorem isRed_node_black (l : LLRB α) (k : α) (r : LLRB α) :
    (LLRB.node .black l k r).isRed = false := rfl

omit [LinearOrder α] in
/-- **A color flip is a 2-3 split.** A 4-node with keys `a < b < c` over `l m r s`, encoded as a
black node with two red children, becomes under `flipColors` the key `b` passed up on a red link
over two 2-nodes `(l a m)` and `(r c s)`: what the 2-3 tree does to a 4-node, in the LLRB's
notation. -/
theorem flipColors_fourNode (l m r s : T23 α) (a b c : α) :
    LLRB.flipColors (.node .black (.node .red (toLlrb l) a (toLlrb m)) b
      (.node .red (toLlrb r) c (toLlrb s))) = (Ins.up (two l a m) b (two r c s)).toLlrb :=
  rfl

/-- **LLRB's recursive insert is the 2-3 insert, step for step.** On the encoding of a sorted
2-3 tree, `LLRB.insertAux` returns the encoding of what `ins` hands back: every `fixUp` on the
way up turns a key passed up from below into exactly the 2-3 node that absorbs or splits it.
Balance is not needed; key order at 3-nodes is, because the LLRB compares against a 3-node's
larger key first and the 2-3 insert against its smaller one. -/
theorem insertAux_toLlrb (x : α) : ∀ t : T23 α, Sorted t →
    LLRB.insertAux x (toLlrb t) = (ins x t).toLlrb
  | leaf, _ => rfl
  | two l k r, ⟨_, _, hsl, hsr⟩ => by
      have ihl := insertAux_toLlrb x l hsl
      have ihr := insertAux_toLlrb x r hsr
      simp only [toLlrb, LLRB.insertAux, ins]
      by_cases hxk : x < k
      · simp only [hxk, ↓reduceIte, ihl]
        rcases ins x l with l' | ⟨p, q, s⟩ <;>
          simp [Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right]
      · by_cases hkx : k < x
        · simp only [hxk, hkx, ↓reduceIte, ihr]
          rcases ins x r with r' | ⟨p, q, s⟩ <;>
            simp [Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right,
              LLRB.rotateLeft]
        · simp [hxk, hkx, Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right]
  | three l a m b r, ⟨hab, _, _, _, hsl, hsm, hsr⟩ => by
      have ihl := insertAux_toLlrb x l hsl
      have ihm := insertAux_toLlrb x m hsm
      have ihr := insertAux_toLlrb x r hsr
      simp only [toLlrb, LLRB.insertAux, ins]
      by_cases hxa : x < a
      · have hxb : x < b := lt_trans hxa hab
        simp only [hxa, hxb, ↓reduceIte, ihl]
        rcases ins x l with l' | ⟨p, q, s⟩ <;>
          simp [Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right,
            LLRB.rotateRight, LLRB.flipColors, Color.flip]
      · by_cases hax : a < x
        · by_cases hxb : x < b
          · simp only [hxa, hax, hxb, ↓reduceIte, ihm]
            rcases ins x m with m' | ⟨p, q, s⟩ <;>
              simp [Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right,
                LLRB.rotateLeft, LLRB.rotateRight, LLRB.flipColors, Color.flip]
          · by_cases hbx : b < x
            · simp only [hxa, hax, hxb, hbx, ↓reduceIte, ihr]
              rcases ins x r with r' | ⟨p, q, s⟩ <;>
                simp [Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right,
                  LLRB.flipColors, Color.flip]
            · simp [hxa, hax, hxb, hbx, Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left,
                LLRB.right]
        · have hxa' : x = a := le_antisymm (not_lt.mp hax) (not_lt.mp hxa)
          subst hxa'
          simp [hab, Ins.toLlrb, toLlrb, LLRB.fixUp, LLRB.left, LLRB.right]

/-- **The LLRB insert is the 2-3 insert**: inserting into the encoding of a sorted 2-3 tree gives
the encoding of the 2-3 tree's insert, duplicates included (both leave the tree unchanged). The
root is black on both sides: the LLRB blackens a red root, which is a key passed up out of the
root, and the 2-3 insert makes that key a new 2-node root. -/
theorem toLlrb_insert {t : T23 α} (ht : Sorted t) (x : α) :
    toLlrb (insert x t) = LLRB.insert x (toLlrb t) := by
  unfold insert LLRB.insert
  rw [insertAux_toLlrb x t ht]
  rcases ins x t with t' | ⟨l, k, r⟩
  · cases t' <;> rfl
  · rfl

/-- Insert keeps a 2-3 tree sorted: read off the LLRB's `sorted_insert` through the encoding. -/
theorem sorted_insert {t : T23 α} (ht : Sorted t) (x : α) : Sorted (insert x t) := by
  rw [← sorted_toLlrb_iff, toLlrb_insert ht]
  exact LLRB.sorted_insert ((sorted_toLlrb_iff t).mpr ht) x

/-- Insert adds exactly `x`. -/
theorem mem_insert {t : T23 α} (ht : Sorted t) (x y : α) :
    Mem y (insert x t) ↔ y = x ∨ Mem y t := by
  rw [← mem_toLlrb, toLlrb_insert ht, LLRB.mem_insert, mem_toLlrb]

end T23

end AlgoDesign.Searching
