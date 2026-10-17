/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Basic

/-!
# Treap: split

`split`, which cuts a treap at a key into the keys below and above it, with what it keeps:
membership (`mem_split`), both invariants, and every priority (`priorityOf_split`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}
variable [LinearOrder α]

/-! ### `split`

Seidel and Aragon's `split a t`: the keys `< a` and the keys `> a` (a key equal to `a` is dropped),
every node reused as it was, no priority moved. With `join`, the primitive of join-based set
operations (Blelloch, Ferizovic and Sun). -/

/-- Split `t` at `a`: the keys below `a` and the keys above it, a key equal to `a` dropped. -/
def split (a : α) : Treap α → Treap α × Treap α
  | leaf => (leaf, leaf)
  | node l k p r =>
      if a < k then ((split a l).1, node (split a l).2 k p r)
      else if k < a then (node l k p (split a r).1, (split a r).2)
      else (l, r)

/-- **`split` is correct on keys**: it partitions exactly at `a`, dropping `a` itself if present. -/
theorem mem_split {t : Treap α} (ht : Sorted t) (a b : α) :
    (Mem b (split a t).1 ↔ Mem b t ∧ b < a) ∧ (Mem b (split a t).2 ↔ Mem b t ∧ a < b) := by
  induction t with
  | leaf => simp [split]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold split
    split
    · rename_i hak
      obtain ⟨e1, e2⟩ := ihl hsl
      constructor
      · rw [e1, mem_node]
        constructor
        · rintro ⟨hbl, hba⟩
          exact ⟨Or.inl hbl, hba⟩
        · rintro ⟨(hbl | rfl | hbr), hba⟩
          · exact ⟨hbl, hba⟩
          · exact absurd hba (lt_asymm hak)
          · exact absurd hba (lt_asymm (lt_trans hak (hr.of_mem hbr)))
      · simp only [mem_node, e2]
        constructor
        · rintro (⟨hbl, hab⟩ | rfl | hbr)
          · exact ⟨Or.inl hbl, hab⟩
          · exact ⟨Or.inr (Or.inl rfl), hak⟩
          · exact ⟨Or.inr (Or.inr hbr), lt_trans hak (hr.of_mem hbr)⟩
        · rintro ⟨(hbl | rfl | hbr), hab⟩
          · exact Or.inl ⟨hbl, hab⟩
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hbr)
    · rename_i hak
      split
      · rename_i hka
        obtain ⟨e1, e2⟩ := ihr hsr
        constructor
        · simp only [mem_node, e1]
          constructor
          · rintro (hbl | rfl | ⟨hbr, hba⟩)
            · exact ⟨Or.inl hbl, lt_trans (hl.of_mem hbl) hka⟩
            · exact ⟨Or.inr (Or.inl rfl), hka⟩
            · exact ⟨Or.inr (Or.inr hbr), hba⟩
          · rintro ⟨(hbl | rfl | hbr), hba⟩
            · exact Or.inl hbl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr ⟨hbr, hba⟩)
        · rw [e2, mem_node]
          constructor
          · rintro ⟨hbr, hba⟩
            exact ⟨Or.inr (Or.inr hbr), hba⟩
          · rintro ⟨(hbl | rfl | hbr), hba⟩
            · exact absurd hba (lt_asymm (lt_trans (hl.of_mem hbl) hka))
            · exact absurd hba (lt_asymm hka)
            · exact ⟨hbr, hba⟩
      · rename_i hka
        have hkey : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
        subst hkey
        constructor
        · rw [mem_node]
          constructor
          · intro hbl
            exact ⟨Or.inl hbl, hl.of_mem hbl⟩
          · rintro ⟨(hbl | rfl | hbr), hbk⟩
            · exact hbl
            · exact absurd hbk (lt_irrefl _)
            · exact absurd hbk (not_lt.mpr (le_of_lt (hr.of_mem hbr)))
        · rw [mem_node]
          constructor
          · intro hbr
            exact ⟨Or.inr (Or.inr hbr), hr.of_mem hbr⟩
          · rintro ⟨(hbl | rfl | hbr), hkb⟩
            · exact absurd hkb (not_lt.mpr (le_of_lt (hl.of_mem hbl)))
            · exact absurd hkb (lt_irrefl _)
            · exact hbr

/-- `All p` is preserved by `split`, on both halves — `split` never invents a key, so anything that
held of every key in `t` still holds of every key in each half. -/
theorem All.split {p : α → Prop} {t : Treap α} (h : All p t) (a : α) :
    All p (split a t).1 ∧ All p (split a t).2 := by
  induction t with
  | leaf => simp [Treap.split]
  | node l k pr r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    unfold Treap.split
    split
    · exact ⟨(ihl hl).1, (ihl hl).2, hk, hr⟩
    · split
      · exact ⟨⟨hl, hk, (ihr hr).1⟩, (ihr hr).2⟩
      · exact ⟨hl, hr⟩

/-- `AllPriority q` is preserved by `split`, on both halves — same reasoning as `All.split`, but for
priorities. -/
theorem AllPriority.split {q : ℕ → Prop} {t : Treap α} (h : AllPriority q t) (a : α) :
    AllPriority q (split a t).1 ∧ AllPriority q (split a t).2 := by
  induction t with
  | leaf => simp [Treap.split]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hp, hr⟩ := h
    unfold Treap.split
    split
    · exact ⟨(ihl hl).1, (ihl hl).2, hp, hr⟩
    · split
      · exact ⟨⟨hl, hp, (ihr hr).1⟩, (ihr hr).2⟩
      · exact ⟨hl, hr⟩

/-- **`split` preserves the BST invariant on both halves**, and each half is correctly bounded
relative to the splitting key `a`. -/
theorem sorted_split {t : Treap α} (ht : Sorted t) (a : α) :
    Sorted (split a t).1 ∧ Sorted (split a t).2 ∧
    All (· < a) (split a t).1 ∧ All (a < ·) (split a t).2 := by
  induction t with
  | leaf => simp [split]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold split
    split
    · rename_i hak
      obtain ⟨hsl1, hsl2, hsl3, hsl4⟩ := ihl hsl
      refine ⟨hsl1, ⟨(hl.split a).2, hr, hsl2, hsr⟩, hsl3, hsl4, hak,
        hr.imp (fun _ hx => lt_trans hak hx)⟩
    · rename_i hak
      split
      · rename_i hka
        obtain ⟨hsr1, hsr2, hsr3, hsr4⟩ := ihr hsr
        refine ⟨⟨hl, (hr.split a).1, hsl, hsr1⟩, hsr2,
          ⟨hl.imp (fun _ hx => lt_trans hx hka), hka, hsr3⟩, hsr4⟩
      · rename_i hka
        have hkey : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
        subst hkey
        exact ⟨hsl, hsr, hl, hr⟩

/-- **`split` preserves heap-order on both halves.** -/
theorem heapOrdered_split {t : Treap α} (ht : HeapOrdered t) (a : α) :
    HeapOrdered (split a t).1 ∧ HeapOrdered (split a t).2 := by
  induction t with
  | leaf => simp [split]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hhl, hhr⟩ := ht
    unfold Treap.split
    split
    · obtain ⟨hh1, hh2⟩ := ihl hhl
      exact ⟨hh1, (hl.split a).2, hr, hh2, hhr⟩
    · split
      · obtain ⟨hh1, hh2⟩ := ihr hhr
        exact ⟨⟨hl, (hr.split a).1, hhl, hh1⟩, hh2⟩
      · exact ⟨hhl, hhr⟩

/-- `split` never moves a priority to a different node, so a lookup that lands on the correct side
finds exactly what it would have found in the original tree. -/
theorem priorityOf_split (a b : α) : ∀ t : Treap α,
    (b < a → priorityOf b (split a t).1 = priorityOf b t) ∧
    (a < b → priorityOf b (split a t).2 = priorityOf b t) := by
  intro t
  induction t with
  | leaf => simp [split]
  | node l k p r ihl ihr =>
    simp only [split]
    split_ifs with hak hka
    · refine ⟨fun hba => ?_, fun hab => ?_⟩
      · rw [ihl.1 hba, priorityOf_left (lt_trans hba hak)]
      · by_cases hbk : b < k
        · rw [priorityOf_left hbk, priorityOf_left hbk, ihl.2 hab]
        · by_cases hkb : k < b
          · rw [priorityOf_right hkb, priorityOf_right hkb]
          · have : b = k := le_antisymm (not_lt.mp hkb) (not_lt.mp hbk)
            subst this
            rw [priorityOf_root, priorityOf_root]
    · refine ⟨fun hba => ?_, fun hab => ?_⟩
      · by_cases hbk : b < k
        · rw [priorityOf_left hbk, priorityOf_left hbk]
        · by_cases hkb : k < b
          · rw [priorityOf_right hkb, priorityOf_right hkb, ihr.1 hba]
          · have : b = k := le_antisymm (not_lt.mp hkb) (not_lt.mp hbk)
            subst this
            rw [priorityOf_root, priorityOf_root]
      · rw [ihr.2 hab, priorityOf_right (lt_trans hka hab)]
    · have hka' : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
      subst hka'
      exact ⟨fun hba => (priorityOf_left hba).symm, fun hab => (priorityOf_right hab).symm⟩

end Treap

end AlgoDesign.Searching
