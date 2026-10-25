/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.TwoThree.Insert

/-!
# 2-3 trees: deletion

The functional 2-3 delete of Nipkow et al., checked arm for arm against `Tree23_Set.thy`: it keeps
a tree balanced and sorted and removes exactly its key (`sameDepth_delete`, `sorted_delete`,
`mem_delete`; in order, `toList_delete`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace T23

variable {α : Type}
variable [LinearOrder α]

/-! ### Delete: remove from the bottom, repair an underflow on the way up -/

/-- What deleting from a subtree hands back to its parent: a tree of the same height (`same`), or
one level shorter (`short`), an underflow the parent must repair. -/
inductive Del (α : Type) : Type where
  /-- The subtree kept its height. -/
  | same (t : T23 α)
  /-- The subtree lost a level. -/
  | short (t : T23 α)

/-- The tree inside, whichever height it has. -/
def Del.tree : Del α → T23 α
  | .same t => t
  | .short t => t

/-- Repair at a 2-node whose left child came back from a delete. A short child borrows from a
3-node sibling, or merges with a 2-node sibling and the separating key into one 3-node, which
leaves this node empty, so the underflow passes up. The `leaf` sibling arm is never reached on a
balanced tree; it keeps the keys. -/
def node21 : Del α → α → T23 α → Del α
  | .same l, a, r => .same (two l a r)
  | .short l, a, two m b r => .short (three l a m b r)
  | .short l, a, three m b n c r => .same (two (two l a m) b (two n c r))
  | .short l, a, leaf => .same (two l a leaf)

/-- Repair at a 2-node whose right child came back from a delete; mirror of `node21`. -/
def node22 : T23 α → α → Del α → Del α
  | l, a, .same r => .same (two l a r)
  | two l b m, a, .short r => .short (three l b m a r)
  | three l b m c n, a, .short r => .same (two (two l b m) c (two n a r))
  | leaf, a, .short r => .same (two leaf a r)

/-- Repair at a 3-node whose left child came back from a delete, using the middle sibling. A
3-node never underflows: a merge takes one of its two keys. -/
def node31 : Del α → α → T23 α → α → T23 α → Del α
  | .same l, a, m, b, r => .same (three l a m b r)
  | .short l, a, two m1 b1 m2, c, r => .same (two (three l a m1 b1 m2) c r)
  | .short l, a, three m1 b1 m2 c1 m3, d, r => .same (three (two l a m1) b1 (two m2 c1 m3) d r)
  | .short l, a, leaf, b, r => .same (three l a leaf b r)

/-- Repair at a 3-node whose middle child came back from a delete, using the right sibling. -/
def node32 : T23 α → α → Del α → α → T23 α → Del α
  | l, a, .same m, b, r => .same (three l a m b r)
  | l, a, .short m, b, two r1 c r2 => .same (two l a (three m b r1 c r2))
  | l, a, .short m, b, three r1 c r2 d r3 => .same (three l a (two m b r1) c (two r2 d r3))
  | l, a, .short m, b, leaf => .same (three l a m b leaf)

/-- Repair at a 3-node whose right child came back from a delete, using the middle sibling. -/
def node33 : T23 α → α → T23 α → α → Del α → Del α
  | l, a, m, b, .same r => .same (three l a m b r)
  | l, a, two m1 b1 m2, c, .short r => .same (two l a (three m1 b1 m2 c r))
  | l, a, three m1 b1 m2 c1 m3, d, .short r => .same (three l a (two m1 b1 m2) c1 (two m3 d r))
  | l, a, leaf, b, .short r => .same (three l a leaf b r)

/-- Remove the smallest key, returning it with what is left: walk left to the bottom, take the key,
repair on the way up. `none` on the empty tree. -/
def splitMin : T23 α → Option (α × Del α)
  | leaf => none
  | two l a r =>
      match splitMin l with
      | none => some (a, .short r)
      | some (x, l') => some (x, node21 l' a r)
  | three l a m b r =>
      match splitMin l with
      | none => some (a, .same (two m b r))
      | some (x, l') => some (x, node31 l' a m b r)

/-- The 2-3 delete. Search for `x`; a key found in an internal node is replaced by its successor,
removed from the bottom of the subtree to its right by `splitMin`; a key found at the bottom is
removed there. Each level repairs an underflow from below with `node21` … `node33`. An absent key
leaves the tree as it was. -/
def del (x : α) : T23 α → Del α
  | leaf => .same leaf
  | two l a r =>
      if x < a then node21 (del x l) a r
      else if a < x then node22 l a (del x r)
      else match splitMin r with
        | some (a', r') => node22 l a' r'
        | none => .short l
  | three l a m b r =>
      if x < a then node31 (del x l) a m b r
      else if a < x then
        if x < b then node32 l a (del x m) b r
        else if b < x then node33 l a m b (del x r)
        else match splitMin r with
          | some (b', r') => node33 l a m b' r'
          | none => .same (two l a m)
      else match splitMin m with
        | some (a', m') => node32 l a' m' b r
        | none => .same (two l b r)

omit [LinearOrder α] in
/-- The repairs move keys between nodes and never reorder them. -/
theorem toList_node21 (d : Del α) (a : α) (r : T23 α) :
    toList (node21 d a r).tree = toList d.tree ++ a :: toList r := by
  cases d <;> cases r <;> simp [node21, Del.tree, toList]

omit [LinearOrder α] in
theorem toList_node22 (l : T23 α) (a : α) (d : Del α) :
    toList (node22 l a d).tree = toList l ++ a :: toList d.tree := by
  cases d <;> cases l <;> simp [node22, Del.tree, toList]

omit [LinearOrder α] in
theorem toList_node31 (d : Del α) (a : α) (m : T23 α) (b : α) (r : T23 α) :
    toList (node31 d a m b r).tree = toList d.tree ++ a :: (toList m ++ b :: toList r) := by
  cases d <;> cases m <;> simp [node31, Del.tree, toList]

omit [LinearOrder α] in
theorem toList_node32 (l : T23 α) (a : α) (d : Del α) (b : α) (r : T23 α) :
    toList (node32 l a d b r).tree = toList l ++ a :: (toList d.tree ++ b :: toList r) := by
  cases d <;> cases r <;> simp [node32, Del.tree, toList]

omit [LinearOrder α] in
theorem toList_node33 (l : T23 α) (a : α) (m : T23 α) (b : α) (d : Del α) :
    toList (node33 l a m b d).tree = toList l ++ a :: (toList m ++ b :: toList d.tree) := by
  cases d <;> cases m <;> simp [node33, Del.tree, toList]

omit [LinearOrder α] in
theorem splitMin_eq_none_iff {t : T23 α} : splitMin t = none ↔ t = leaf := by
  cases t with
  | leaf => simp [splitMin]
  | two l a r => simp only [splitMin]; split <;> simp
  | three l a m b r => simp only [splitMin]; split <;> simp

omit [LinearOrder α] in
theorem toList_splitMin : ∀ {t : T23 α} {x : α} {d : Del α}, splitMin t = some (x, d) →
    toList t = x :: toList d.tree
  | leaf, _, _, h => by simp [splitMin] at h
  | two l a r, x, d, h => by
      simp only [splitMin] at h
      split at h
      · rename_i hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [splitMin_eq_none_iff.mp hl, toList, Del.tree]
      · rename_i x' l' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [toList, toList_node21, toList_splitMin hl]
  | three l a m b r, x, d, h => by
      simp only [splitMin] at h
      split at h
      · rename_i hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [splitMin_eq_none_iff.mp hl, toList, Del.tree]
      · rename_i x' l' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [toList, toList_node31, toList_splitMin hl]

/-- Erasing below the separator erases from the left part only. -/
theorem erase_append_cons_of_lt {L R : List α} {a x : α}
    (hR : ∀ y ∈ R, a < y) (hx : x < a) : (L ++ a :: R).erase x = L.erase x ++ a :: R := by
  by_cases hxL : x ∈ L
  · exact List.erase_append_left _ hxL
  · have hxR : x ∉ a :: R := by
      simp only [List.mem_cons, not_or]
      exact ⟨ne_of_lt hx, fun h => lt_asymm hx (hR x h)⟩
    rw [List.erase_append_right _ hxL, List.erase_of_not_mem hxL, List.erase_of_not_mem hxR]

theorem erase_append_cons_of_gt {L R : List α} {a x : α} (hL : ∀ y ∈ L, y < a) (hx : a < x) :
    (L ++ a :: R).erase x = L ++ a :: R.erase x := by
  have hxL : x ∉ L := fun h => lt_asymm hx (hL x h)
  rw [List.erase_append_right _ hxL, List.erase_cons_tail (by simpa using ne_of_lt hx)]

theorem erase_append_cons_self {L R : List α} {a : α} (hL : ∀ y ∈ L, y < a) :
    (L ++ a :: R).erase a = L ++ R := by
  have haL : a ∉ L := fun h => lt_irrefl a (hL a h)
  rw [List.erase_append_right _ haL, List.erase_cons_head]

/-- **The 2-3 delete removes exactly its key from the in-order list.** -/
theorem toList_del (x : α) : ∀ t : T23 α, (toList t).Pairwise (· < ·) →
    toList (del x t).tree = (toList t).erase x
  | leaf, _ => by simp [del, Del.tree, toList]
  | two l a r, hs => by
      simp only [toList, List.pairwise_append, List.pairwise_cons, List.mem_cons] at hs
      obtain ⟨pl, ⟨har, pr⟩, hla⟩ := hs
      have hL : ∀ y ∈ toList l, y < a := fun y hy => hla y hy a (Or.inl rfl)
      simp only [del, toList]
      split_ifs with h1 h2
      · rw [toList_node21, toList_del x l pl, erase_append_cons_of_lt har h1]
      · rw [toList_node22, toList_del x r pr, erase_append_cons_of_gt hL h2]
      · have hxa : x = a := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hxa
        rw [erase_append_cons_self hL]
        split
        · rename_i a' r' hm
          rw [toList_node22, toList_splitMin hm]
        · rename_i hm
          simp [splitMin_eq_none_iff.mp hm, Del.tree, toList]
  | three l a m b r, hs => by
      simp only [toList, List.pairwise_append, List.pairwise_cons, List.mem_cons,
        List.mem_append] at hs
      obtain ⟨pl, ⟨ham, pm, ⟨hbr, pr⟩, hmb⟩, hla⟩ := hs
      have hL : ∀ y ∈ toList l, y < a := fun y hy => hla y hy a (Or.inl rfl)
      have hAR : ∀ y ∈ toList m ++ b :: toList r, a < y := by
        intro y hy
        simpa [List.mem_append, List.mem_cons] using ham y (by simpa using hy)
      have hM : ∀ y ∈ toList m, y < b := fun y hy => hmb y hy b (Or.inl rfl)
      simp only [del, toList]
      split_ifs with h1 h2 h3 h4
      · rw [toList_node31, toList_del x l pl, erase_append_cons_of_lt hAR h1]
      · rw [toList_node32, toList_del x m pm, erase_append_cons_of_gt hL h2,
          erase_append_cons_of_lt hbr h3]
      · rw [toList_node33, toList_del x r pr, erase_append_cons_of_gt hL h2,
          erase_append_cons_of_gt hM h4]
      · have hxb : x = b := le_antisymm (not_lt.mp h4) (not_lt.mp h3)
        subst hxb
        rw [erase_append_cons_of_gt hL h2, erase_append_cons_self hM]
        split
        · rename_i b' r' hm
          rw [toList_node33, toList_splitMin hm]
        · rename_i hm
          simp [splitMin_eq_none_iff.mp hm, Del.tree, toList]
      · have hxa : x = a := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst hxa
        rw [erase_append_cons_self hL]
        split
        · rename_i a' m' hm
          rw [toList_node32, toList_splitMin hm]
          simp
        · rename_i hm
          simp [splitMin_eq_none_iff.mp hm, Del.tree, toList]

/-- Delete `x`. -/
def delete (x : α) (t : T23 α) : T23 α := (del x t).tree

theorem toList_delete {t : T23 α} (hs : Sorted t) (x : α) :
    toList (delete x t) = (toList t).erase x :=
  toList_del x t ((sorted_iff_pairwise t).mp hs)

/-- **Delete removes exactly `x`.** -/
theorem mem_delete {t : T23 α} (hs : Sorted t) (x y : α) :
    Mem y (delete x t) ↔ y ≠ x ∧ Mem y t := by
  have hnd : (toList t).Nodup := ((sorted_iff_pairwise t).mp hs).imp ne_of_lt
  rw [mem_iff_mem_toList, mem_iff_mem_toList, toList_delete hs, hnd.mem_erase_iff]

/-- Delete keeps a 2-3 tree sorted. -/
theorem sorted_delete {t : T23 α} (hs : Sorted t) (x : α) : Sorted (delete x t) := by
  rw [sorted_iff_pairwise, toList_delete hs]
  exact ((sorted_iff_pairwise t).mp hs).sublist (List.erase_sublist)

/-- The heights `del` hands back from a subtree of height `h`: `same` keeps `h`, `short` is one
lower, and either way the tree is balanced. -/
def Del.Fits (h : ℕ) : Del α → Prop
  | .same t => SameDepth t ∧ height t = h
  | .short t => SameDepth t ∧ height t + 1 = h

omit [LinearOrder α] in
theorem node21_fits {h : ℕ} {d : Del α} (hd : d.Fits h) (a : α) {r : T23 α} (hr : SameDepth r)
    (hrh : height r = h) : (node21 d a r).Fits (h + 1) := by
  cases d <;> cases r <;> simp_all [node21, Del.Fits, SameDepth, height] <;> omega

omit [LinearOrder α] in
theorem node22_fits {h : ℕ} {l : T23 α} (hl : SameDepth l) (hlh : height l = h) (a : α)
    {d : Del α} (hd : d.Fits h) : (node22 l a d).Fits (h + 1) := by
  cases d <;> cases l <;> simp_all [node22, Del.Fits, SameDepth, height] <;> omega

omit [LinearOrder α] in
theorem node31_fits {h : ℕ} {d : Del α} (hd : d.Fits h) (a : α) {m : T23 α} (hm : SameDepth m)
    (hmh : height m = h) (b : α) {r : T23 α} (hr : SameDepth r) (hrh : height r = h) :
    (node31 d a m b r).Fits (h + 1) := by
  cases d <;> cases m <;> simp_all [node31, Del.Fits, SameDepth, height] <;> omega

omit [LinearOrder α] in
theorem node32_fits {h : ℕ} {l : T23 α} (hl : SameDepth l) (hlh : height l = h) (a : α)
    {d : Del α} (hd : d.Fits h) (b : α) {r : T23 α} (hr : SameDepth r) (hrh : height r = h) :
    (node32 l a d b r).Fits (h + 1) := by
  cases d <;> cases r <;> simp_all [node32, Del.Fits, SameDepth, height] <;> omega

omit [LinearOrder α] in
theorem node33_fits {h : ℕ} {l : T23 α} (hl : SameDepth l) (hlh : height l = h) (a : α)
    {m : T23 α} (hm : SameDepth m) (hmh : height m = h) (b : α) {d : Del α} (hd : d.Fits h) :
    (node33 l a m b d).Fits (h + 1) := by
  cases d <;> cases m <;> simp_all [node33, Del.Fits, SameDepth, height] <;> omega

omit [LinearOrder α] in
theorem height_eq_zero_iff {t : T23 α} : height t = 0 ↔ t = leaf := by
  cases t <;> simp [height]

omit [LinearOrder α] in
theorem splitMin_fits : ∀ {t : T23 α} {x : α} {d : Del α}, SameDepth t →
    splitMin t = some (x, d) → d.Fits (height t)
  | leaf, _, _, _, h => by simp [splitMin] at h
  | two l a r, x, d, hb, h => by
      obtain ⟨hlr, hl, hr⟩ := hb
      simp only [splitMin] at h
      split at h
      · rename_i hl0
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl0 := splitMin_eq_none_iff.mp hl0
        subst hl0
        have hr0 : r = leaf := height_eq_zero_iff.mp (by simpa [height] using hlr.symm)
        subst hr0
        simp [Del.Fits, SameDepth, height]
      · rename_i x' l' hl'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact node21_fits (splitMin_fits hl hl') a hr hlr.symm
  | three l a m b r, x, d, hb, h => by
      obtain ⟨hlm, hmr, hl, hm, hr⟩ := hb
      simp only [splitMin] at h
      split at h
      · rename_i hl0
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl0 := splitMin_eq_none_iff.mp hl0
        subst hl0
        have hm0 : m = leaf := height_eq_zero_iff.mp (by simpa [height] using hlm.symm)
        subst hm0
        have hr0 : r = leaf := height_eq_zero_iff.mp (by simpa [height] using hmr.symm)
        subst hr0
        simp [Del.Fits, SameDepth, height]
      · rename_i x' l' hl'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact node31_fits (splitMin_fits hl hl') a hm hlm.symm b hr (hlm.trans hmr).symm

/-- `del` hands back a balanced tree of the same height or one lower. -/
theorem del_fits (x : α) : ∀ t : T23 α, SameDepth t → (del x t).Fits (height t)
  | leaf, _ => by simp [del, Del.Fits, SameDepth, height]
  | two l a r, ⟨hlr, hl, hr⟩ => by
      simp only [del, height]
      split_ifs with h1 h2
      · exact node21_fits (del_fits x l hl) a hr hlr.symm
      · rw [hlr]; exact node22_fits hl hlr a (del_fits x r hr)
      · split
        · rename_i a' r' hm
          rw [hlr]; exact node22_fits hl hlr a' (splitMin_fits hr hm)
        · rename_i hm
          have hr0 := splitMin_eq_none_iff.mp hm
          subst hr0
          have hl0 : l = leaf := height_eq_zero_iff.mp (by simpa [height] using hlr)
          subst hl0
          simp [Del.Fits, SameDepth, height]
  | three l a m b r, ⟨hlm, hmr, hl, hm, hr⟩ => by
      simp only [del, height]
      split_ifs with h1 h2 h3 h4
      · exact node31_fits (del_fits x l hl) a hm hlm.symm b hr (hlm.trans hmr).symm
      · rw [hlm]; exact node32_fits hl hlm a (del_fits x m hm) b hr hmr.symm
      · rw [hlm, hmr]; exact node33_fits hl (hlm.trans hmr) a hm hmr b (del_fits x r hr)
      · split
        · rename_i b' r' hsm
          rw [hlm, hmr]; exact node33_fits hl (hlm.trans hmr) a hm hmr b' (splitMin_fits hr hsm)
        · rename_i hsm
          have hr0 := splitMin_eq_none_iff.mp hsm
          subst hr0
          have hm0 : m = leaf := height_eq_zero_iff.mp (by simpa [height] using hmr)
          subst hm0
          have hl0 : l = leaf := height_eq_zero_iff.mp (by simpa [height] using hlm)
          subst hl0
          simp [Del.Fits, SameDepth, height]
      · split
        · rename_i a' m' hsm
          rw [hlm]; exact node32_fits hl hlm a' (splitMin_fits hm hsm) b hr hmr.symm
        · rename_i hsm
          have hm0 := splitMin_eq_none_iff.mp hsm
          subst hm0
          have hr0 : r = leaf := height_eq_zero_iff.mp (by simpa [height] using hmr.symm)
          subst hr0
          have hl0 : l = leaf := height_eq_zero_iff.mp (by simpa [height] using hlm)
          subst hl0
          simp [Del.Fits, SameDepth, height]

/-- **Delete keeps a 2-3 tree balanced**: the tree shrinks only at the root. -/
theorem sameDepth_delete {t : T23 α} (ht : SameDepth t) (x : α) : SameDepth (delete x t) := by
  have h := del_fits x t ht
  unfold delete
  rcases hd : del x t with t' | t' <;> rw [hd] at h <;> exact h.1

/-- Two strictly increasing lists with the same members are the same list. -/
theorem eq_of_pairwise_of_mem_iff : ∀ {l₁ l₂ : List α}, l₁.Pairwise (· < ·) →
    l₂.Pairwise (· < ·) → (∀ y, y ∈ l₁ ↔ y ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (by simp)) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((h a).1 (by simp)) with hab | ha
        · exact hab
        · rcases List.mem_cons.mp ((h b).2 (by simp)) with hba | hb
          · exact hba.symm
          · exact absurd (lt_trans (h₂.1 a ha) (h₁.1 b hb)) (lt_irrefl b)
      subst hab
      congr 1
      refine eq_of_pairwise_of_mem_iff h₁.2 h₂.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · rcases List.mem_cons.mp ((h y).1 (List.mem_cons_of_mem a hy)) with hya | hy'
        · exact absurd (hya ▸ h₁.1 y hy) (lt_irrefl y)
        · exact hy'
      · rcases List.mem_cons.mp ((h y).2 (List.mem_cons_of_mem a hy)) with hya | hy'
        · exact absurd (hya ▸ h₂.1 y hy) (lt_irrefl y)
        · exact hy'

end T23

end AlgoDesign.Searching
