/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.TwoThree.Delete

/-!
# 2-3 trees: the LLRB delete, read as a 2-3 delete

`deleteTop_toLlrb`: `LLRB.deleteTop` on an encoding is the encoding of a balanced sorted 2-3 tree
with the same keys in order as `delete`, though not in general `delete`'s tree; and
`bheight_deleteTop`: the two deletions leave trees of the same height.
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace T23

variable {α : Type}
variable [LinearOrder α]

/-- **What the LLRB delete computes, read as a 2-3 tree.** Deleting from the encoding of a
balanced sorted 2-3 tree gives the encoding of a balanced sorted 2-3 tree that holds the same keys,
in the same order, as the 2-3 `delete`. The two trees need not be the same tree
(`AlgoDesignTests/Searching.lean` pins one where they differ): the LLRB restructures on the way
down, and the 2-3 delete only on the way back up. -/
theorem deleteTop_toLlrb {t : T23 α} (hb : SameDepth t) (hs : Sorted t) (x : α) :
    ∃ t', SameDepth t' ∧ Sorted t' ∧ LLRB.deleteTop x (toLlrb t) = toLlrb t' ∧
      toList t' = toList (delete x t) := by
  have hv : LLRB.Valid (toLlrb t) := by
    obtain ⟨h1, h2, h3, h4⟩ := llrbColors_toLlrb hb
    exact ⟨(sorted_toLlrb_iff t).mpr hs, h1, h2, h3, h4⟩
  obtain ⟨hs', h1, h2, h3, h4⟩ := LLRB.valid_deleteTop hv x
  obtain ⟨t', hb', he⟩ :=
    exists_twoThree_of_llrbColors ⟨h1, h2, h3, h4⟩
  have hst' : Sorted t' := (sorted_toLlrb_iff t').mp (he ▸ hs')
  refine ⟨t', hb', hst', he.symm, ?_⟩
  refine eq_of_pairwise_of_mem_iff ((sorted_iff_pairwise t').mp hst')
    ((sorted_iff_pairwise _).mp (sorted_delete hs x)) fun y => ?_
  rw [← mem_iff_mem_toList, ← mem_iff_mem_toList, mem_delete hs, ← mem_toLlrb, he,
    LLRB.mem_deleteTop_iff ((sorted_toLlrb_iff t).mpr hs), mem_toLlrb]

/-! ### The two deletions shorten the tree together

`LLRB.deleteTop` and `delete` build different trees, but the LLRB's black height after a delete is
always the 2-3 tree's height plus one (`bheight_deleteTop`). The LLRB delete keeps black height
below the root (`LLRB.delete_spec`), so the question is only whether the root link comes back red,
and on a 2-node root, which `prime` reddens, it comes back red exactly when the 2-3 delete keeps the
height (`isRed_delete_red2`, with `isRed_deleteMin_red2` for the successor). The induction follows
the 2-3 tree: every shape the LLRB delete meets on the way down is a reddened encoded 2-node, an
encoded 3-node, or the right-leaning node `moveRedRight` leaves after borrowing. -/

section

open LLRB

omit [LinearOrder α] in
@[simp] theorem isRed_llrb_leaf : (LLRB.leaf : LLRB α).isRed = false := rfl

omit [LinearOrder α] in
@[simp] theorem isRed_llrb_red (l : LLRB α) (k : α) (r : LLRB α) :
    (node .red l k r).isRed = true := rfl

omit [LinearOrder α] in
@[simp] theorem isRed_llrb_black (l : LLRB α) (k : α) (r : LLRB α) :
    (node .black l k r).isRed = false := rfl

end

omit [LinearOrder α] in
open LLRB in
theorem fixUp_eq_self {c : Color} {L R : LLRB α} {k : α} (hL : L.isRed = false)
    (hR : R.isRed = false) : fixUp (node c L k R) = node c L k R := by
  simp [fixUp, LLRB.left, LLRB.right, hL, hR]

omit [LinearOrder α] in
open LLRB in
theorem isRed_fixUp_mergeLeft {D R1 R2 : LLRB α} {k c : α}
    (hD : D.isRed = true → D.left.isRed = false) (hR2 : R2.isRed = false) :
    (fixUp (node .black D k (node .red R1 c R2))).isRed = D.isRed := by
  rcases D with _ | ⟨cD, DL, dk, DR⟩
  · simp [fixUp, rotateLeft, LLRB.left, LLRB.right, hR2]
  · cases cD
    · have := hD rfl
      simp_all [fixUp, flipColors, LLRB.left, LLRB.right, Color.flip]
    · simp [fixUp, rotateLeft, LLRB.left, LLRB.right, hR2]

omit [LinearOrder α] in
open LLRB in
theorem isRed_fixUp_mergeRight {D L1 L2 : LLRB α} {k a : α} (hL1 : L1.isRed = false) :
    (fixUp (node .black (node .red L1 a L2) k D)).isRed = D.isRed := by
  rcases D with _ | ⟨cD, DL, dk, DR⟩
  · simp [fixUp, LLRB.left, LLRB.right, hL1]
  · cases cD <;> simp [fixUp, flipColors, LLRB.left, LLRB.right, hL1,
      Color.flip]

/-- Did the subtree keep its height? -/
def Del.isSame : Del α → Bool
  | .same _ => true
  | .short _ => false

/-- The encoding of a 2-node with its root link recolored red: the shape `LLRB.deleteTop`'s
`prime` makes of a 2-node root, and the shape the LLRB delete hands down when it merges. -/
abbrev red2 (l : T23 α) (k : α) (r : T23 α) : LLRB α := .node .red (toLlrb l) k (toLlrb r)

omit [LinearOrder α] in
theorem inv_toLlrb {t : T23 α} (hb : SameDepth t) :
    LLRB.Balanced (toLlrb t) ∧ LLRB.LeftLeaning (toLlrb t) ∧ LLRB.NoRedRed (toLlrb t) :=
  ⟨(balanced_toLlrb_iff t).mpr hb, (shape_toLlrb t).2.1, (shape_toLlrb t).2.2⟩

omit [LinearOrder α] in
theorem inv_red2 {l r : T23 α} {k : α} (hb : SameDepth (two l k r)) :
    LLRB.Balanced (red2 l k r) ∧ LLRB.LeftLeaning (red2 l k r) ∧ LLRB.NoRedRed (red2 l k r) ∧
      LLRB.NotTwoNode (red2 l k r) := by
  obtain ⟨hh, hl, hr⟩ := hb
  obtain ⟨bl, ll, nl⟩ := inv_toLlrb hl
  obtain ⟨br, lr, nr⟩ := inv_toLlrb hr
  refine ⟨⟨by simp [bheight_toLlrb, hh], bl, br⟩, ⟨(shape_toLlrb r).1, ll, lr⟩,
    ⟨fun _ => ⟨(shape_toLlrb l).1, (shape_toLlrb r).1⟩, nl, nr⟩, Or.inl rfl⟩

omit [LinearOrder α] in
theorem notTwoNode_three (l : T23 α) (a : α) (m : T23 α) (b : α) (r : T23 α) :
    LLRB.NotTwoNode (toLlrb (three l a m b r)) := Or.inr rfl

omit [LinearOrder α] in
theorem isRed_noRedRed {D : LLRB α} (h : LLRB.NoRedRed D) :
    D.isRed = true → D.left.isRed = false := by
  rcases D with _ | ⟨c, l, k, r⟩
  · simp
  · intro hr
    have hc : c = .red := by cases c <;> simp_all
    exact LLRB.isRed_eq_false (h.1 hc).1

omit [LinearOrder α] in
theorem splitMin_two_eq (l : T23 α) (k : α) (r : T23 α) :
    splitMin (two l k r) = (match splitMin l with
      | none => some (k, .short r)
      | some (x, l') => some (x, node21 l' k r)) := rfl

omit [LinearOrder α] in
/-- Removing the minimum of a 3-node never shortens it. -/
theorem splitMin_three {l : T23 α} {a : α} {m : T23 α} {b : α} {r : T23 α} {y : α} {d : Del α}
    (h : splitMin (three l a m b r) = some (y, d)) : d.isSame = true := by
  simp only [splitMin] at h
  split at h
  · cases h; rfl
  · cases h
    rename_i x l' _
    rcases l' with l' | l' <;> rcases m with _ | ⟨m1, b1, m2⟩ | ⟨m1, b1, m2, c1, m3⟩ <;> rfl

omit [LinearOrder α] in
/-- **`deleteMin` on a reddened 2-node keeps its red root exactly when the 2-3 minimum removal
keeps the height.** -/
theorem isRed_deleteMin_red2 : ∀ (n : ℕ) (l : T23 α) (k : α) (r : T23 α), height l = n →
    SameDepth (two l k r) → ∀ y d, splitMin (two l k r) = some (y, d) →
    (LLRB.deleteMin (red2 l k r)).isRed = d.isSame := by
  intro n
  induction n with
  | zero =>
    intro l k r hl hb y d hs
    have hl0 : l = leaf := height_eq_zero_iff.mp hl
    subst hl0
    have hr0 : r = leaf := height_eq_zero_iff.mp (by simpa [height] using hb.1.symm)
    subst hr0
    simp only [splitMin, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    simp [red2, toLlrb, LLRB.deleteMin, Del.isSame]
  | succ n ih =>
    intro l k r hl hb y d hs
    obtain ⟨hh, hbl, hbr⟩ := hb
    rcases l with _ | ⟨l1, a, l2⟩ | ⟨l1, a, m, b, l2⟩
    · simp [height] at hl
    · -- a 2-node on the left: `moveRedLeft` borrows from a 3-node sibling or merges with a 2-node
      rcases r with _ | ⟨r1, c, r2⟩ | ⟨r1, c, m2, d', r2⟩
      · simp [height] at hh
      · -- merge: the recursion enters the reddened left 2-node
        have hmv : LLRB.deleteMin (red2 (two l1 a l2) k (two r1 c r2)) =
            LLRB.fixUp (.node .black (LLRB.deleteMin (red2 l1 a l2)) k
              (.node .red (toLlrb r1) c (toLlrb r2))) :=
          LLRB.deleteMin_node (by simp [toLlrb]) (by
            simp [red2, toLlrb, LLRB.moveRedLeft, LLRB.flipColors, LLRB.left, LLRB.right,
              Color.flip])
        obtain ⟨b1, l1', n1, t1⟩ := inv_red2 hbl
        have hnrr := (LLRB.deleteMin_spec b1 l1' n1 t1).2.2.2.1
        rw [hmv, isRed_fixUp_mergeLeft (isRed_noRedRed hnrr) (isRed_toLlrb r2)]
        rcases hsl : splitMin (two l1 a l2) with _ | ⟨x, dl⟩
        · exact absurd (splitMin_eq_none_iff.mp hsl) (by simp)
        · rw [splitMin_two_eq, hsl] at hs
          cases hs
          rw [ih l1 a l2 (by simpa [height] using hl) hbl _ dl hsl]
          cases dl <;> rfl
      · -- borrow from the 3-node sibling: the recursion enters an encoded 3-node
        have hbt : SameDepth (three l1 a l2 k r1) := by
          simp only [SameDepth, height] at hh hbl hbr ⊢
          exact ⟨hbl.1, by omega, hbl.2.1, hbl.2.2, hbr.2.2.1⟩
        have hmv : LLRB.deleteMin (red2 (two l1 a l2) k (three r1 c m2 d' r2)) =
            LLRB.fixUp (.node .red (LLRB.deleteMin (toLlrb (three l1 a l2 k r1))) c
              (.node .black (toLlrb m2) d' (toLlrb r2))) :=
          LLRB.deleteMin_node (by simp [toLlrb]) (by
            simp [toLlrb, LLRB.moveRedLeft, LLRB.flipColors, LLRB.left, LLRB.right,
              LLRB.rotateLeft, LLRB.rotateRight, Color.flip])
        obtain ⟨b1, l1', n1⟩ := inv_toLlrb hbt
        have hblack := (LLRB.deleteMin_spec b1 l1' n1 (notTwoNode_three _ _ _ _ _)).2.2.2.2
        have hD : (LLRB.deleteMin (toLlrb (three l1 a l2 k r1))).isRed = false :=
          LLRB.isRed_eq_false (fun h => by simpa [toLlrb, LLRB.IsRed] using hblack h)
        rw [hmv, fixUp_eq_self hD rfl]
        rcases hsl : splitMin (two l1 a l2) with _ | ⟨x, dl⟩
        · exact absurd (splitMin_eq_none_iff.mp hsl) (by simp)
        · rw [splitMin_two_eq, hsl] at hs
          cases hs
          cases dl <;> rfl
    · -- a 3-node on the left: no borrowing; the left subtree keeps a black root
      have hdm : LLRB.deleteMin (red2 (three l1 a m b l2) k r) =
          LLRB.fixUp (.node .red (LLRB.deleteMin (toLlrb (three l1 a m b l2))) k (toLlrb r)) :=
        LLRB.deleteMin_node (by simp [toLlrb]) (by simp [toLlrb, LLRB.left])
      obtain ⟨b1, l1', n1⟩ := inv_toLlrb hbl
      have hblack := (LLRB.deleteMin_spec b1 l1' n1 (notTwoNode_three _ _ _ _ _)).2.2.2.2
      have hD : (LLRB.deleteMin (toLlrb (three l1 a m b l2))).isRed = false :=
        LLRB.isRed_eq_false (fun h => by simpa [toLlrb, LLRB.IsRed] using hblack h)
      rw [hdm, fixUp_eq_self hD (isRed_toLlrb r)]
      rcases hsl : splitMin (three l1 a m b l2) with _ | ⟨x, l'⟩
      · exact absurd (splitMin_eq_none_iff.mp hsl) (by simp)
      · rw [splitMin_two_eq, hsl] at hs
        cases hs
        have := splitMin_three hsl
        rcases l' with l' | l' <;> simp_all [node21, Del.isSame]

omit [LinearOrder α] in
theorem isSame_node31 (d : Del α) (a : α) (m : T23 α) (b : α) (r : T23 α) :
    (node31 d a m b r).isSame = true := by
  cases d <;> cases m <;> rfl

omit [LinearOrder α] in
theorem isSame_node32 (l : T23 α) (a : α) (d : Del α) (b : α) (r : T23 α) :
    (node32 l a d b r).isSame = true := by
  cases d <;> cases r <;> rfl

omit [LinearOrder α] in
theorem isSame_node33 (l : T23 α) (a : α) (m : T23 α) (b : α) (d : Del α) :
    (node33 l a m b d).isSame = true := by
  cases d <;> cases m <;> rfl

/-- Deleting from a 3-node never shortens it: a merge below takes one of its two keys. -/
theorem isSame_del_three (x : α) (l : T23 α) (a : α) (m : T23 α) (b : α) (r : T23 α) :
    (del x (three l a m b r)).isSame = true := by
  simp only [del]
  split_ifs <;> (try split) <;>
    first | exact isSame_node31 .. | exact isSame_node32 .. | exact isSame_node33 .. | rfl

theorem sorted_of_infix {s t : T23 α} (ht : Sorted t) (h : toList s <:+: toList t) :
    Sorted s :=
  (sorted_iff_pairwise s).mpr (((sorted_iff_pairwise t).mp ht).sublist h.sublist)

theorem mem_left_of_lt {l r : T23 α} {k x : α} (hs : Sorted (two l k r))
    (hx : Mem x (two l k r)) (h : x < k) : Mem x l := by
  rcases hx with hx | rfl | hx
  · exact hx
  · exact absurd h (lt_irrefl _)
  · exact absurd ((all_iff_forall _ r).mp hs.2.1 x ((mem_iff_mem_toList x r).mp hx))
      (not_lt.mpr (le_of_lt h))

theorem mem_right_of_gt {l r : T23 α} {k x : α} (hs : Sorted (two l k r))
    (hx : Mem x (two l k r)) (h : k < x) : Mem x r := by
  rcases hx with hx | rfl | hx
  · exact absurd ((all_iff_forall _ l).mp hs.1 x ((mem_iff_mem_toList x l).mp hx))
      (not_lt.mpr (le_of_lt h))
  · exact absurd h (lt_irrefl _)
  · exact hx

/-- Deleting from an encoded 3-node leaves a black root (`LLRB.delete_spec`'s last clause). -/
theorem isRed_delete_three {l : T23 α} {a : α} {m : T23 α} {b : α} {r : T23 α}
    (hb : SameDepth (three l a m b r)) (hs : Sorted (three l a m b r)) (x : α) :
    (LLRB.delete x (toLlrb (three l a m b r))).isRed = false := by
  obtain ⟨b1, l1, n1⟩ := inv_toLlrb hb
  have h := (LLRB.delete_spec x ((sorted_toLlrb_iff _).mpr hs) b1 n1
    (Or.inr (Or.inl ⟨l1, notTwoNode_three _ _ _ _ _⟩))).2.2.2.2
  exact LLRB.isRed_eq_false (fun hr => by simpa [toLlrb, LLRB.IsRed] using h hr)

omit [LinearOrder α] in
theorem isRed_deleteMin_three {l : T23 α} {a : α} {m : T23 α} {b : α} {r : T23 α}
    (hb : SameDepth (three l a m b r)) :
    (LLRB.deleteMin (toLlrb (three l a m b r))).isRed = false := by
  obtain ⟨b1, l1, n1⟩ := inv_toLlrb hb
  have h := (LLRB.deleteMin_spec b1 l1 n1 (notTwoNode_three _ _ _ _ _)).2.2.2.2
  exact LLRB.isRed_eq_false (fun hr => by simpa [toLlrb, LLRB.IsRed] using h hr)

/-- The shape `moveRedRight` leaves when it borrows from a 3-node: a black node whose right link
is red. Deleting below it (a key at or above its own) leaves a black root. -/
theorem isRed_delete_relaxed {l2 r1 r2 : T23 α} {k c x : α} (hs : Sorted (two l2 k (two r1 c r2)))
    (hb2 : SameDepth l2) (hbr : SameDepth (two r1 c r2)) (hh : height l2 = height r1)
    (hkx : ¬ x < k) :
    (LLRB.delete x (.node .black (toLlrb l2) k (.node .red (toLlrb r1) c (toLlrb r2)))).isRed =
      false := by
  have hsl : LLRB.Sorted (.node .black (toLlrb l2) k (.node .red (toLlrb r1) c (toLlrb r2))) :=
    (sorted_toLlrb_iff (two l2 k (two r1 c r2))).mpr hs
  obtain ⟨b2, ll2, n2⟩ := inv_toLlrb hb2
  obtain ⟨br, llr, nr, -⟩ := inv_red2 hbr
  have h := (LLRB.delete_spec x hsl ⟨by simp [LLRB.bheight, bheight_toLlrb, hh], b2, br⟩
    ⟨fun h => absurd h (by simp), n2, nr⟩
    (Or.inr (Or.inr ⟨(shape_toLlrb l2).1, rfl, ll2, llr, hkx⟩))).2.2.2.2
  exact LLRB.isRed_eq_false (fun hr => by simpa [LLRB.IsRed] using h hr)

/-- **`delete` on a reddened 2-node keeps its red root exactly when the 2-3 delete keeps the
height**, for a key that is present. -/
theorem isRed_delete_red2 (x : α) : ∀ (n : ℕ) (l : T23 α) (k : α) (r : T23 α), height l = n →
    SameDepth (two l k r) → Sorted (two l k r) → Mem x (two l k r) →
    (LLRB.delete x (red2 l k r)).isRed = (del x (two l k r)).isSame := by
  intro n
  induction n with
  | zero =>
    intro l k r hl hb hs hx
    have hl0 : l = leaf := height_eq_zero_iff.mp hl
    subst hl0
    have hr0 : r = leaf := height_eq_zero_iff.mp (by simpa [height] using hb.1.symm)
    subst hr0
    have hxk : x = k := by simpa [Mem] using hx
    subst hxk
    have : LLRB.delete x (red2 leaf x leaf) = .leaf :=
      LLRB.delete_ge_splice (c1 := .red) (l1 := .leaf) (lt_irrefl x) (by simp [toLlrb])
    rw [this]
    simp [del, splitMin, Del.isSame]
  | succ n ih =>
    intro l k r hl hb hs hx
    have hb' := hb
    obtain ⟨hh, hbl, hbr⟩ := hb'
    have hh2 : (if (toLlrb l).isRed then LLRB.rotateRight (red2 l k r) else red2 l k r) =
        red2 l k r := by simp
    rcases l with _ | ⟨l1, a, l2⟩ | ⟨l1, a, m, b, l2⟩
    · simp [height] at hl
    all_goals rcases r with _ | ⟨r1, c, r2⟩ | ⟨r1, c, m2, d', r2⟩
    all_goals try (simp [height] at hh; done)
    all_goals rcases lt_trichotomy x k with hxk | hxk | hxk
    -- the left child is a 2-node, the right child a 2-node: both descents merge
    · have hdel : del x (two (two l1 a l2) k (two r1 c r2)) =
          node21 (del x (two l1 a l2)) k (two r1 c r2) := by simp [del, hxk]
      have hdl : LLRB.delete x (red2 (two l1 a l2) k (two r1 c r2)) =
          LLRB.fixUp (.node .black (LLRB.delete x (red2 l1 a l2)) k
            (.node .red (toLlrb r1) c (toLlrb r2))) :=
        LLRB.delete_lt hxk (by
          simp [toLlrb, LLRB.moveRedLeft, LLRB.flipColors, LLRB.left, LLRB.right, Color.flip])
      have hsr : LLRB.Sorted (red2 l1 a l2) := (sorted_toLlrb_iff (two l1 a l2)).mpr hs.2.2.1
      obtain ⟨b1, ll1, n1, t1⟩ := inv_red2 hbl
      have hn := (LLRB.delete_spec x hsr b1 n1 (Or.inr (Or.inl ⟨ll1, t1⟩))).2.2.2.1
      rw [hdl, isRed_fixUp_mergeLeft (isRed_noRedRed hn) (isRed_toLlrb r2),
        ih l1 a l2 (by simpa [height] using hl) hbl hs.2.2.1 (mem_left_of_lt hs hx hxk), hdel]
      generalize del x (two l1 a l2) = D
      cases D <;> rfl
    · -- 2-node, 2-node, the key itself: merge, then the successor comes up from the right
      subst hxk
      rcases hsr : splitMin (two r1 c r2) with _ | ⟨y, dr⟩
      · exact absurd (splitMin_eq_none_iff.mp hsr) (by simp)
      have hdel : del x (two (two l1 a l2) x (two r1 c r2)) = node22 (two l1 a l2) y dr := by
        simp [del, hsr]
      obtain ⟨m, hm⟩ : ∃ m, LLRB.min? (red2 r1 c r2) = some m := ⟨_, rfl⟩
      have hdl : LLRB.delete x (red2 (two l1 a l2) x (two r1 c r2)) =
          LLRB.fixUp (.node .black (.node .red (toLlrb l1) a (toLlrb l2)) m
            (LLRB.deleteMin (red2 r1 c r2))) :=
        LLRB.delete_ge_succ (lt_irrefl x) hh2 (by
          simp [toLlrb, LLRB.moveRedRight, LLRB.flipColors, LLRB.left,
            Color.flip]) hm
      rw [hdl, isRed_fixUp_mergeRight (isRed_toLlrb l1),
        isRed_deleteMin_red2 _ r1 c r2 rfl hbr y dr hsr, hdel]
      cases dr <;> rfl
    · -- 2-node, 2-node, above the key: merge and descend right
      have hkx : ¬ x < k := not_lt.mpr (le_of_lt hxk)
      have hdel : del x (two (two l1 a l2) k (two r1 c r2)) =
          node22 (two l1 a l2) k (del x (two r1 c r2)) := by simp [del, hxk, hkx]
      have hdl : LLRB.delete x (red2 (two l1 a l2) k (two r1 c r2)) =
          LLRB.fixUp (.node .black (.node .red (toLlrb l1) a (toLlrb l2)) k
            (LLRB.delete x (red2 r1 c r2))) :=
        LLRB.delete_ge_rec hkx hh2 (by
          simp [toLlrb, LLRB.moveRedRight, LLRB.flipColors, LLRB.left,
            Color.flip]) (ne_of_gt hxk)
      have hr1 : height r1 = n := by simp [height] at hl hh; omega
      rw [hdl, isRed_fixUp_mergeRight (isRed_toLlrb l1),
        ih r1 c r2 hr1 hbr hs.2.2.2 (mem_right_of_gt hs hx hxk), hdel]
      generalize del x (two r1 c r2) = D
      cases D <;> rfl
    · -- 2-node, 3-node, below the key: borrow from the right sibling
      have hdel : del x (two (two l1 a l2) k (three r1 c m2 d' r2)) =
          node21 (del x (two l1 a l2)) k (three r1 c m2 d' r2) := by simp [del, hxk]
      have hbt : SameDepth (three l1 a l2 k r1) := by
        simp only [SameDepth, height] at hh hbl hbr ⊢
        exact ⟨hbl.1, by omega, hbl.2.1, hbl.2.2, hbr.2.2.1⟩
      have hst : Sorted (three l1 a l2 k r1) :=
        sorted_of_infix hs ⟨[], c :: (toList m2 ++ d' :: toList r2), by simp [toList]⟩
      have hdl : LLRB.delete x (red2 (two l1 a l2) k (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (LLRB.delete x (toLlrb (three l1 a l2 k r1))) c
            (.node .black (toLlrb m2) d' (toLlrb r2))) :=
        LLRB.delete_lt hxk (by
          simp [toLlrb, LLRB.moveRedLeft, LLRB.flipColors, LLRB.rotateLeft, LLRB.rotateRight,
            LLRB.left, LLRB.right, Color.flip])
      rw [hdl, fixUp_eq_self (isRed_delete_three hbt hst x) rfl, hdel]
      generalize del x (two l1 a l2) = D
      cases D <;> rfl
    · -- 2-node, 3-node, the key itself: the successor comes from the 3-node, which keeps height
      subst hxk
      rcases hsr : splitMin (three r1 c m2 d' r2) with _ | ⟨y, dr⟩
      · exact absurd (splitMin_eq_none_iff.mp hsr) (by simp)
      have hdel : del x (two (two l1 a l2) x (three r1 c m2 d' r2)) =
          node22 (two l1 a l2) y dr := by simp [del, hsr]
      obtain ⟨m, hm⟩ : ∃ m, LLRB.min? (toLlrb (three r1 c m2 d' r2)) = some m := ⟨_, rfl⟩
      have hdl : LLRB.delete x (red2 (two l1 a l2) x (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (toLlrb (two l1 a l2)) m
            (LLRB.deleteMin (toLlrb (three r1 c m2 d' r2)))) :=
        LLRB.delete_ge_succ (lt_irrefl x) hh2 (by simp [toLlrb]) hm
      rw [hdl, fixUp_eq_self (isRed_toLlrb _) (isRed_deleteMin_three hbr), hdel]
      have := splitMin_three hsr
      cases dr
      · rfl
      · simp [Del.isSame] at this
    · -- 2-node, 3-node, above the key: the 3-node keeps its height
      have hkx : ¬ x < k := not_lt.mpr (le_of_lt hxk)
      have hdel : del x (two (two l1 a l2) k (three r1 c m2 d' r2)) =
          node22 (two l1 a l2) k (del x (three r1 c m2 d' r2)) := by simp [del, hxk, hkx]
      have hdl : LLRB.delete x (red2 (two l1 a l2) k (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (toLlrb (two l1 a l2)) k
            (LLRB.delete x (toLlrb (three r1 c m2 d' r2)))) :=
        LLRB.delete_ge_rec hkx hh2 (by simp [toLlrb]) (ne_of_gt hxk)
      rw [hdl, fixUp_eq_self (isRed_toLlrb _) (isRed_delete_three hbr hs.2.2.2 x), hdel]
      have := isSame_del_three x r1 c m2 d' r2
      generalize del x (three r1 c m2 d' r2) = D at this ⊢
      cases D
      · rfl
      · simp [Del.isSame] at this
    · -- 3-node, 2-node, below the key: the 3-node keeps its height
      have hdel : del x (two (three l1 a m b l2) k (two r1 c r2)) =
          node21 (del x (three l1 a m b l2)) k (two r1 c r2) := by simp [del, hxk]
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) k (two r1 c r2)) =
          LLRB.fixUp (.node .red (LLRB.delete x (toLlrb (three l1 a m b l2))) k
            (toLlrb (two r1 c r2))) :=
        LLRB.delete_lt hxk (by simp [toLlrb, LLRB.left])
      rw [hdl, fixUp_eq_self (isRed_delete_three hbl hs.2.2.1 x) (isRed_toLlrb _), hdel]
      have := isSame_del_three x l1 a m b l2
      generalize del x (three l1 a m b l2) = D at this ⊢
      cases D
      · rfl
      · simp [Del.isSame] at this
    · -- 3-node, 2-node, the key itself: `moveRedRight` borrows from the 3-node
      subst hxk
      rcases hsr : splitMin (two r1 c r2) with _ | ⟨y, dr⟩
      · exact absurd (splitMin_eq_none_iff.mp hsr) (by simp)
      have hdel : del x (two (three l1 a m b l2) x (two r1 c r2)) =
          node22 (three l1 a m b l2) y dr := by simp [del, hsr]
      have hbx : b < x := hs.1.2.2.2.1
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) x (two r1 c r2)) =
          LLRB.fixUp (.node .red (.node .black (toLlrb l1) a (toLlrb m)) b
            (LLRB.delete x (.node .black (toLlrb l2) x (.node .red (toLlrb r1) c (toLlrb r2))))) :=
        LLRB.delete_ge_rec (lt_irrefl x) hh2 (by
          simp [toLlrb, LLRB.moveRedRight, LLRB.flipColors, LLRB.rotateRight, LLRB.left,
            Color.flip]) (ne_of_gt hbx)
      have hrel := isRed_delete_relaxed (x := x)
        (sorted_of_infix hs ⟨toList l1 ++ a :: (toList m ++ [b]), [], by simp [toList]⟩)
        hbl.2.2.2.2 hbr (by simp only [SameDepth, height] at hh hbl hbr; omega) (lt_irrefl x)
      rw [hdl, fixUp_eq_self rfl hrel, hdel]
      cases dr <;> rfl
    · -- 3-node, 2-node, above the key: borrow, then descend right
      have hkx : ¬ x < k := not_lt.mpr (le_of_lt hxk)
      have hdel : del x (two (three l1 a m b l2) k (two r1 c r2)) =
          node22 (three l1 a m b l2) k (del x (two r1 c r2)) := by simp [del, hxk, hkx]
      have hbx : b < x := lt_trans hs.1.2.2.2.1 hxk
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) k (two r1 c r2)) =
          LLRB.fixUp (.node .red (.node .black (toLlrb l1) a (toLlrb m)) b
            (LLRB.delete x (.node .black (toLlrb l2) k (.node .red (toLlrb r1) c (toLlrb r2))))) :=
        LLRB.delete_ge_rec hkx hh2 (by
          simp [toLlrb, LLRB.moveRedRight, LLRB.flipColors, LLRB.rotateRight, LLRB.left,
            Color.flip]) (ne_of_gt hbx)
      have hrel := isRed_delete_relaxed (x := x)
        (sorted_of_infix hs ⟨toList l1 ++ a :: (toList m ++ [b]), [], by simp [toList]⟩)
        hbl.2.2.2.2 hbr (by simp only [SameDepth, height] at hh hbl hbr; omega) hkx
      rw [hdl, fixUp_eq_self rfl hrel, hdel]
      generalize del x (two r1 c r2) = D
      cases D <;> rfl
    · -- 3-node, 3-node, below the key
      have hdel : del x (two (three l1 a m b l2) k (three r1 c m2 d' r2)) =
          node21 (del x (three l1 a m b l2)) k (three r1 c m2 d' r2) := by simp [del, hxk]
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) k (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (LLRB.delete x (toLlrb (three l1 a m b l2))) k
            (toLlrb (three r1 c m2 d' r2))) :=
        LLRB.delete_lt hxk (by simp [toLlrb, LLRB.left])
      rw [hdl, fixUp_eq_self (isRed_delete_three hbl hs.2.2.1 x) (isRed_toLlrb _), hdel]
      have := isSame_del_three x l1 a m b l2
      generalize del x (three l1 a m b l2) = D at this ⊢
      cases D
      · rfl
      · simp [Del.isSame] at this
    · -- 3-node, 3-node, the key itself
      subst hxk
      rcases hsr : splitMin (three r1 c m2 d' r2) with _ | ⟨y, dr⟩
      · exact absurd (splitMin_eq_none_iff.mp hsr) (by simp)
      have hdel : del x (two (three l1 a m b l2) x (three r1 c m2 d' r2)) =
          node22 (three l1 a m b l2) y dr := by simp [del, hsr]
      obtain ⟨m', hm⟩ : ∃ m', LLRB.min? (toLlrb (three r1 c m2 d' r2)) = some m' := ⟨_, rfl⟩
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) x (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (toLlrb (three l1 a m b l2)) m'
            (LLRB.deleteMin (toLlrb (three r1 c m2 d' r2)))) :=
        LLRB.delete_ge_succ (lt_irrefl x) hh2 (by simp [toLlrb]) hm
      rw [hdl, fixUp_eq_self (isRed_toLlrb _) (isRed_deleteMin_three hbr), hdel]
      cases dr <;> rfl
    · -- 3-node, 3-node, above the key
      have hkx : ¬ x < k := not_lt.mpr (le_of_lt hxk)
      have hdel : del x (two (three l1 a m b l2) k (three r1 c m2 d' r2)) =
          node22 (three l1 a m b l2) k (del x (three r1 c m2 d' r2)) := by simp [del, hxk, hkx]
      have hdl : LLRB.delete x (red2 (three l1 a m b l2) k (three r1 c m2 d' r2)) =
          LLRB.fixUp (.node .red (toLlrb (three l1 a m b l2)) k
            (LLRB.delete x (toLlrb (three r1 c m2 d' r2)))) :=
        LLRB.delete_ge_rec hkx hh2 (by simp [toLlrb]) (ne_of_gt hxk)
      rw [hdl, fixUp_eq_self (isRed_toLlrb _) (isRed_delete_three hbr hs.2.2.2 x), hdel]
      generalize del x (three r1 c m2 d' r2) = D
      cases D <;> rfl

/-- Deleting an absent key changes nothing. -/
theorem del_of_not_mem (x : α) : ∀ t : T23 α, ¬ Mem x t → del x t = .same t
  | leaf, _ => rfl
  | two l k r, hn => by
    have hl := del_of_not_mem x l (fun h => hn (Or.inl h))
    have hr := del_of_not_mem x r (fun h => hn (Or.inr (Or.inr h)))
    rcases lt_trichotomy x k with h | rfl | h
    · simp [del, h, hl, node21]
    · exact absurd (Or.inr (Or.inl rfl)) hn
    · simp [del, h, not_lt.mpr (le_of_lt h), hr, node22]
  | three l a m b r, hn => by
    have hl := del_of_not_mem x l (fun h => hn (Or.inl h))
    have hm := del_of_not_mem x m (fun h => hn (Or.inr (Or.inr (Or.inl h))))
    have hr := del_of_not_mem x r (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))))
    rcases lt_trichotomy x a with h | rfl | h
    · simp [del, h, hl, node31]
    · exact absurd (Or.inr (Or.inl rfl)) hn
    · rcases lt_trichotomy x b with h' | rfl | h'
      · simp [del, h, h', not_lt.mpr (le_of_lt h), hm, node32]
      · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hn
      · simp [del, h, h', not_lt.mpr (le_of_lt h), not_lt.mpr (le_of_lt h'), hr, node33]

omit [LinearOrder α] in
theorem bheight_blacken (D : LLRB α) :
    LLRB.bheight (LLRB.blacken D) = LLRB.bheight D + if D.isRed then 1 else 0 := by
  rcases D with _ | ⟨c, l, k, r⟩
  · rfl
  · cases c <;> simp [LLRB.blacken, LLRB.bheight]

/-- **The two deletions leave trees of the same height.** On the encoding of a balanced sorted 2-3
tree, `LLRB.deleteTop`'s black height is one more than the 2-3 `delete`'s height, exactly as for
an encoding (`bheight_toLlrb`): the LLRB delete shortens the tree precisely when the 2-3 delete
does, although the two trees can differ. -/
theorem bheight_deleteTop {t : T23 α} (hb : SameDepth t) (hs : Sorted t) (x : α) :
    LLRB.bheight (LLRB.deleteTop x (toLlrb t)) = height (delete x t) + 1 := by
  unfold LLRB.deleteTop delete
  by_cases hsearch : LLRB.search x (toLlrb t) = true
  · simp only [hsearch, ↓reduceIte]
    have hmem : Mem x t := (mem_toLlrb x t).mp
      ((LLRB.search_correct ((sorted_toLlrb_iff t).mpr hs) x).mp hsearch)
    have hfit := del_fits x t hb
    rcases t with _ | ⟨l, k, r⟩ | ⟨l, a, m, b, r⟩
    · exact absurd hmem id
    · have hp : LLRB.prime (toLlrb (two l k r)) = red2 l k r := by
        simp [LLRB.prime, toLlrb]
      obtain ⟨b1, l1, n1, t1⟩ := inv_red2 hb
      have hsr : LLRB.Sorted (red2 l k r) := (sorted_toLlrb_iff (two l k r)).mpr hs
      have hbh := (LLRB.delete_spec x hsr b1 n1 (Or.inr (Or.inl ⟨l1, t1⟩))).1
      rw [hp, bheight_blacken, hbh, isRed_delete_red2 x _ l k r rfl hb hs hmem]
      simp only [LLRB.bheight, bheight_toLlrb] at hbh ⊢
      rcases hd : del x (two l k r) with u | u <;> rw [hd] at hfit <;>
        simp_all [Del.Fits, Del.isSame, Del.tree, height]
    · have hp : LLRB.prime (toLlrb (three l a m b r)) = toLlrb (three l a m b r) := by
        simp [LLRB.prime, toLlrb]
      obtain ⟨b1, l1, n1⟩ := inv_toLlrb hb
      have hbh := (LLRB.delete_spec x ((sorted_toLlrb_iff _).mpr hs) b1 n1
        (Or.inr (Or.inl ⟨l1, notTwoNode_three _ _ _ _ _⟩))).1
      rw [hp, bheight_blacken, hbh, isRed_delete_three hb hs x, bheight_toLlrb]
      have := isSame_del_three x l a m b r
      rcases hd : del x (three l a m b r) with u | u <;> rw [hd] at hfit this <;>
        simp_all [Del.Fits, Del.isSame, Del.tree]
  · simp only [hsearch, ↓reduceIte, Bool.false_eq_true]
    have hn : ¬ Mem x t := fun h => hsearch ((LLRB.search_correct
      ((sorted_toLlrb_iff t).mpr hs) x).mpr ((mem_toLlrb x t).mpr h))
    rw [del_of_not_mem x t hn, bheight_toLlrb]
    rfl

end T23

end AlgoDesign.Searching
