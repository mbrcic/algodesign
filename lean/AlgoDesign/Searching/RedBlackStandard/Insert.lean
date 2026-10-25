/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Balance

/-!
# Red-black tree: insertion

CLRS's `RB-INSERT` and `RB-INSERT-FIXUP` (`ins`, `insertFixupL`/`insertFixupR`, the root blackened
by `insert`): `mem_insert` and `sorted_insert` are the color-blind half, `valid_insert` the color
invariants, and `insertSpec`: `insert` discharges `InsertSpec`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

/-! ### `insert` + `RB-INSERT-FIXUP`

Without parent pointers, the recursion's return plays CLRS's climb from `z` to `z.p.p`: the fixup
loop body runs once per level. -/

/-- One step of `RB-INSERT-FIXUP`, when the just-recursed-into child `l` was the **left** one
(CLRS's "`z.p` is `z.p.p.left`"). Rewrites only when this node `c` is black:
* **Case 1** (uncle `r` red): recolor `l` and `r` black, this node red; the violation moves up.
* **Case 2** (uncle black, red `l.right`): `LEFT-ROTATE` at `l`, then Case 3.
* **Case 3** (uncle black, red `l.left`): recolor `l` black, this node red, `RIGHT-ROTATE`.
Otherwise nothing changes. -/
def insertFixupL (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : RBTree α :=
  match c, l with
  | .black, node .red ll _lk lr =>
      if !ll.isRed && !lr.isRed then node c l k r
      else if r.isRed then node .red (blacken l) k (blacken r)
      else if lr.isRed then rotateRight (node .red (blacken (rotateLeft l)) k r)
      else rotateRight (node .red (blacken l) k r)
  | _, _ => node c l k r

/-- Symmetric to `insertFixupL`: the just-recursed-into child was the **right** one. -/
def insertFixupR (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : RBTree α :=
  match c, r with
  | .black, node .red rl _rk rr =>
      if !rl.isRed && !rr.isRed then node c l k r
      else if l.isRed then node .red (blacken l) k (blacken r)
      else if rl.isRed then rotateLeft (node .red l k (blacken (rotateRight r)))
      else rotateLeft (node .red l k (blacken r))
  | _, _ => node c l k r

/-- Insert `a` as a red leaf by BST descent, running the fixup step on the way back up from every
recursive call. A duplicate key is a no-op. The root is blackened by `insert`. -/
def ins (a : α) : RBTree α → RBTree α
  | leaf => node .red leaf a leaf
  | node c l k r =>
      if a < k then insertFixupL c (ins a l) k r
      else if k < a then insertFixupR c l k (ins a r)
      else node c l k r

/-- Insert `a`, then force the root black (CLRS's final `T.root.color = BLACK`): Case 1 can leave
a red root. -/
def insert (a : α) (t : RBTree α) : RBTree α := blacken (ins a t)

/-! #### `insert` preserves `Sorted` and `Mem` (color plays no part) -/

omit [LinearOrder α] in
theorem mem_insertFixupL (c : Color) (l : RBTree α) (k : α) (r : RBTree α) (b : α) :
    Mem b (insertFixupL c l k r) ↔ Mem b (node c l k r) := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;>
    simp only [insertFixupL]
  split_ifs <;>
    simp [Mem, mem_blacken, mem_rotateLeft, mem_rotateRight]

omit [LinearOrder α] in
theorem mem_insertFixupR (c : Color) (l : RBTree α) (k : α) (r : RBTree α) (b : α) :
    Mem b (insertFixupR c l k r) ↔ Mem b (node c l k r) := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;>
    simp only [insertFixupR]
  split_ifs <;>
    simp [Mem, mem_blacken, mem_rotateLeft, mem_rotateRight]

theorem mem_ins (t : RBTree α) (a b : α) : Mem b (ins a t) ↔ b = a ∨ Mem b t := by
  induction t with
  | leaf => simp [ins]
  | node c l k r ihl ihr =>
    unfold ins
    split
    · rename_i h
      rw [mem_insertFixupL]
      simp only [mem_node, ihl]
      tauto
    · split
      · rename_i h h'
        rw [mem_insertFixupR]
        simp only [mem_node, ihr]
        tauto
      · rename_i h h'
        have hka : k = a := le_antisymm (not_lt.mp h) (not_lt.mp h')
        simp only [mem_node]
        constructor
        · rintro (hl | rfl | hr) <;> tauto
        · rintro (rfl | hl | rfl | hr) <;> tauto

theorem All.ins {p : α → Prop} {t : RBTree α} (h : All p t) {a : α} (ha : p a) :
    All p (ins a t) :=
  all_of_forall_mem fun b hb =>
    ((mem_ins t a b).mp hb).elim (fun hba => by rw [hba]; exact ha) h.of_mem

theorem sorted_insertFixupL {c : Color} {l : RBTree α} {k : α} {r : RBTree α}
    (ht : Sorted (node c l k r)) : Sorted (insertFixupL c l k r) := by
  have hcase1 : Sorted (node .red (blacken l) k (blacken r)) :=
    ⟨(all_blacken l).mpr ht.1, (all_blacken r).mpr ht.2.1,
      sorted_blacken ht.2.2.1, sorted_blacken ht.2.2.2⟩
  have hcase3 : Sorted (node .red (blacken l) k r) :=
    ⟨(all_blacken l).mpr ht.1, ht.2.1, sorted_blacken ht.2.2.1, ht.2.2.2⟩
  have hcase2 : Sorted (node .red (blacken (rotateLeft l)) k r) :=
    ⟨(all_blacken (rotateLeft l)).mpr ((all_rotateLeft l).mpr ht.1), ht.2.1,
      sorted_blacken (sorted_rotateLeft ht.2.2.1), ht.2.2.2⟩
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;>
    simp only [insertFixupL] <;>
    first
      | exact ht
      | (split_ifs <;>
          first
            | exact ht
            | exact hcase1
            | exact sorted_rotateRight hcase3
            | exact sorted_rotateRight hcase2)

theorem sorted_insertFixupR {c : Color} {l : RBTree α} {k : α} {r : RBTree α}
    (ht : Sorted (node c l k r)) : Sorted (insertFixupR c l k r) := by
  have hcase1 : Sorted (node .red (blacken l) k (blacken r)) :=
    ⟨(all_blacken l).mpr ht.1, (all_blacken r).mpr ht.2.1,
      sorted_blacken ht.2.2.1, sorted_blacken ht.2.2.2⟩
  have hcase3 : Sorted (node .red l k (blacken r)) :=
    ⟨ht.1, (all_blacken r).mpr ht.2.1, ht.2.2.1, sorted_blacken ht.2.2.2⟩
  have hcase2 : Sorted (node .red l k (blacken (rotateRight r))) :=
    ⟨ht.1, (all_blacken (rotateRight r)).mpr ((all_rotateRight r).mpr ht.2.1), ht.2.2.1,
      sorted_blacken (sorted_rotateRight ht.2.2.2)⟩
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;>
    simp only [insertFixupR] <;>
    first
      | exact ht
      | (split_ifs <;>
          first
            | exact ht
            | exact hcase1
            | exact sorted_rotateLeft hcase3
            | exact sorted_rotateLeft hcase2)

theorem sorted_ins {t : RBTree α} (ht : Sorted t) (a : α) : Sorted (ins a t) := by
  induction t with
  | leaf => simp [ins, Sorted, All]
  | node c l k r ihl ihr =>
    unfold ins
    split
    · rename_i h
      obtain ⟨hl, hr, hsl, hsr⟩ := ht
      exact sorted_insertFixupL ⟨hl.ins h, hr, ihl hsl, hsr⟩
    · split
      · rename_i h h'
        obtain ⟨hl, hr, hsl, hsr⟩ := ht
        exact sorted_insertFixupR ⟨hl, hr.ins h', hsl, ihr hsr⟩
      · exact ht

theorem mem_insert (t : RBTree α) (a b : α) : Mem b (insert a t) ↔ b = a ∨ Mem b t := by
  unfold insert
  rw [mem_blacken]
  exact mem_ins t a b

theorem sorted_insert {t : RBTree α} (ht : Sorted t) (a : α) : Sorted (insert a t) :=
  sorted_blacken (sorted_ins ht a)

/-! ### `insert` preserves the color invariants (`RootBlack`, `NoRedRed`, `BlackHeightOk`)

A violation can survive one level and be repaired one level up, so the induction uses the
color-conditional `ins_spec`, with `bheight`/`Balanced` standing in for `blackHeight`. -/

/-- **CLRS property 4, relaxed at the root only**: both children are `NoRedRed`, but the root may
sit red over a red child. The shape `ins` leaves for the next level's fixup to repair. -/
def NoRedRed2 : RBTree α → Prop
  | leaf => True
  | node _ l _ r => NoRedRed l ∧ NoRedRed r

omit [LinearOrder α] in
/-- `NoRedRed` implies `NoRedRed2`. -/
theorem noRedRed2_of_noRedRed {t : RBTree α} (h : NoRedRed t) : NoRedRed2 t := by
  cases t with
  | leaf => trivial
  | node c l k r => exact ⟨h.2.1, h.2.2⟩

omit [LinearOrder α] in
/-- Blackening the root turns `NoRedRed2` into `NoRedRed`. -/
theorem noRedRed_blacken_iff {t : RBTree α} : NoRedRed (blacken t) ↔ NoRedRed2 t := by
  cases t <;> simp [blacken, NoRedRed, NoRedRed2, IsBlack]

omit [LinearOrder α] in
/-- `blacken` changes only the root's color, so it keeps `Balanced`. -/
theorem balanced_blacken {t : RBTree α} (h : Balanced t) : Balanced (blacken t) := by
  cases t <;> exact h

/-- **At most one of a node's two children is red.** `NoRedRed2` alone allows both; the fixup's
Cases 2/3 need the sibling of the violating side black. -/
def AtMostOneRedChild : RBTree α → Prop
  | leaf => True
  | node _ l _ r => l.IsBlack ∨ r.IsBlack

omit [LinearOrder α] in
/-- `insertFixupL`'s effect on `l'`, the `ins` output on the left: `Balanced` against `r`, and fully
`NoRedRed` or (only when `c` isn't red) `NoRedRed2` with `AtMostOneRedChild`. `hcr`: a red `c`
forces `r` black. If `c` isn't red the result is fully `NoRedRed` (Cases 1-3 resolve it); if `c`
is red the step does not rewrite and the result keeps one violation on one side. -/
theorem insertFixupL_spec {c : Color} {l' r : RBTree α} {k : α}
    (hr_nrr : NoRedRed r) (hr_bal : Balanced r) (hl'_bal : Balanced l')
    (hl'_nrr_or : NoRedRed l' ∨ (c ≠ .red ∧ NoRedRed2 l' ∧ AtMostOneRedChild l'))
    (hcr : c = .red → r.IsBlack) (hbh : bheight l' = bheight r) :
    bheight (insertFixupL c l' k r) = bheight l' + (if c = .black then 1 else 0) ∧
    Balanced (insertFixupL c l' k r) ∧
    (c ≠ .red → NoRedRed (insertFixupL c l' k r)) ∧
    (c = .red → NoRedRed2 (insertFixupL c l' k r) ∧ AtMostOneRedChild (insertFixupL c l' k r)) := by
  rcases l' with _ | ⟨cl, _ | ⟨cll, lll, llk, llr⟩, lk, _ | ⟨clr, lrl, lrk, lrr⟩⟩ <;>
    rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
    cases c <;> (try cases cl) <;> (try cases cll) <;> (try cases clr) <;> (try cases cr) <;>
    simp_all [insertFixupL, rotateLeft, rotateRight, blacken, isRed, NoRedRed, NoRedRed2,
      AtMostOneRedChild, Balanced, bheight, IsBlack] <;>
    omega

omit [LinearOrder α] in
/-- Symmetric to `insertFixupL_spec`, for a violation coming from the *right* recursive call. -/
theorem insertFixupR_spec {c : Color} {l r' : RBTree α} {k : α}
    (hl_nrr : NoRedRed l) (hl_bal : Balanced l) (hr'_bal : Balanced r')
    (hr'_nrr_or : NoRedRed r' ∨ (c ≠ .red ∧ NoRedRed2 r' ∧ AtMostOneRedChild r'))
    (hcl : c = .red → l.IsBlack) (hbh : bheight l = bheight r') :
    bheight (insertFixupR c l k r') = bheight l + (if c = .black then 1 else 0) ∧
    Balanced (insertFixupR c l k r') ∧
    (c ≠ .red → NoRedRed (insertFixupR c l k r')) ∧
    (c = .red → NoRedRed2 (insertFixupR c l k r') ∧ AtMostOneRedChild (insertFixupR c l k r')) := by
  rcases r' with _ | ⟨cr, _ | ⟨crl, rll, rlk, rlr⟩, rk, _ | ⟨crr, rrl, rrk, rrr⟩⟩ <;>
    rcases l with _ | ⟨cl, ll, lk, lr⟩ <;>
    cases c <;> (try cases cr) <;> (try cases crl) <;> (try cases crr) <;> (try cases cl) <;>
    simp_all [insertFixupR, rotateLeft, rotateRight, blacken, isRed, NoRedRed, NoRedRed2,
      AtMostOneRedChild, Balanced, bheight, IsBlack] <;>
    omega

/-- The strengthened induction hypothesis for `ins`: from a black-rooted input the result is fully
`NoRedRed`; otherwise it may be red-rooted with one violation on one side (`NoRedRed2` and
`AtMostOneRedChild`). Mirrors `LLRB.insertAux_spec`. -/
theorem ins_spec {t : RBTree α} (a : α) (ht_bal : Balanced t) (ht_nrr : NoRedRed t) :
    bheight (ins a t) = bheight t ∧ Balanced (ins a t) ∧
    (t.IsBlack → NoRedRed (ins a t)) ∧
    (¬ t.IsBlack → NoRedRed2 (ins a t) ∧ AtMostOneRedChild (ins a t)) := by
  induction t with
  | leaf =>
    refine ⟨rfl, ?_, ?_, ?_⟩ <;>
      simp [ins, Balanced, NoRedRed, NoRedRed2, AtMostOneRedChild, IsBlack]
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hbl, hbr⟩ := ht_bal
    obtain ⟨hnr, hl_nrr, hr_nrr⟩ := ht_nrr
    unfold ins
    split
    · -- a < k: violation (if any) comes from the left recursive call
      obtain ⟨hb1, hb2, hb3, hb4⟩ := ihl hbl hl_nrr
      have hdisj : NoRedRed (ins a l) ∨
          (c ≠ .red ∧ NoRedRed2 (ins a l) ∧ AtMostOneRedChild (ins a l)) := by
        by_cases hlb : l.IsBlack
        · exact Or.inl (hb3 hlb)
        · obtain ⟨p1, p2⟩ := hb4 hlb
          exact Or.inr ⟨fun hc => absurd (hnr hc).1 hlb, p1, p2⟩
      have hcr : c = .red → r.IsBlack := fun hc => (hnr hc).2
      obtain ⟨e1, e2, e3, e4⟩ := insertFixupL_spec hr_nrr hbr hb2 hdisj hcr (by omega)
      refine ⟨by simp only [bheight]; rw [e1, hb1], e2, ?_, ?_⟩
      · intro hib
        have hc : c ≠ .red := by
          cases c with
          | red => exact Color.noConfusion hib
          | black => exact fun h => Color.noConfusion h
        exact e3 hc
      · intro hib
        have hc : c = .red := by
          cases c with
          | red => rfl
          | black => exact absurd rfl hib
        exact e4 hc
    · split
      · -- a > k: violation (if any) comes from the right recursive call
        obtain ⟨hb1, hb2, hb3, hb4⟩ := ihr hbr hr_nrr
        have hdisj : NoRedRed (ins a r) ∨
            (c ≠ .red ∧ NoRedRed2 (ins a r) ∧ AtMostOneRedChild (ins a r)) := by
          by_cases hrb' : r.IsBlack
          · exact Or.inl (hb3 hrb')
          · obtain ⟨p1, p2⟩ := hb4 hrb'
            exact Or.inr ⟨fun hc => absurd (hnr hc).2 hrb', p1, p2⟩
        have hcl : c = .red → l.IsBlack := fun hc => (hnr hc).1
        obtain ⟨e1, e2, e3, e4⟩ := insertFixupR_spec hl_nrr hbl hb2 hdisj hcl (by omega)
        refine ⟨by simp only [bheight]; rw [e1], e2, ?_, ?_⟩
        · intro hib
          have hc : c ≠ .red := by
            cases c with
            | red => exact Color.noConfusion hib
            | black => exact fun h => Color.noConfusion h
          exact e3 hc
        · intro hib
          have hc : c = .red := by
            cases c with
            | red => rfl
            | black => exact absurd rfl hib
          exact e4 hc
      · -- a = k: no change
        refine ⟨rfl, ⟨hbh, hbl, hbr⟩, fun _ => ⟨hnr, hl_nrr, hr_nrr⟩, ?_⟩
        intro hib
        have hc : c = .red := by
          cases c with
          | red => rfl
          | black => exact absurd rfl hib
        exact ⟨⟨hl_nrr, hr_nrr⟩, Or.inl (hnr hc).1⟩

/-- **`insert` produces a legal standard red-black tree from a legal one.** -/
theorem valid_insert {t : RBTree α} (ht : Valid t) (a : α) : Valid (insert a t) := by
  obtain ⟨hs, hrb, hnrr, hbh⟩ := ht
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hib : t.IsBlack := by cases t with
    | leaf => trivial
    | node c l k r => exact hrb
  obtain ⟨e1, e2, e3, -⟩ := ins_spec a hbal hnrr
  have hnrr' : NoRedRed (ins a t) := e3 hib
  refine ⟨sorted_insert hs a, ?_, ?_, ?_⟩
  · change RootBlack (blacken (ins a t))
    cases (ins a t) <;> simp [RootBlack, blacken]
  · exact noRedRed_blacken_iff.mpr (noRedRed2_of_noRedRed hnrr')
  · exact blackHeightOk_iff_balanced.mpr (balanced_blacken e2)

/-- **`insert` discharges `InsertSpec`**, assembled from `mem_insert` and `valid_insert`. -/
theorem insertSpec (t : RBTree α) (a : α) : InsertSpec a t (insert a t) :=
  ⟨mem_insert t a, fun hv => valid_insert hv a⟩

end RBTree

end AlgoDesign.Searching
