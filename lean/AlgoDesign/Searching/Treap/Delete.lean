/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Join

/-!
# Treap: deletion

`delete` rotates the node down under its higher-priority child until it is a leaf, then drops it;
`deleteJoin` replaces it by the `join` of its children, and `delete_eq_deleteJoin` proves the two
are one function. `deleteSpec`: `delete` discharges `DeleteSpec`.
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}
variable [LinearOrder α]

/-! ### `deleteJoin`

Delete `a` by replacing its node with the `join` of its children. The proofs are carried by this
form; `delete_eq_deleteJoin` says it equals `delete`. -/

/-- Delete `a` by replacing its node with the `join` of its children. -/
def deleteJoin (a : α) : Treap α → Treap α
  | leaf => leaf
  | node l k p r =>
      if a < k then node (deleteJoin a l) k p r
      else if k < a then node l k p (deleteJoin a r)
      else join l r

/-- **`deleteJoin` is correct on keys**: it removes exactly `a` and nothing else. Needs `Sorted`,
same as `BST.mem_delete` — without it, nothing rules out `a` occurring *again* somewhere inside `l`
or `r` even after the node actually storing `k = a` is spliced out via `join`. -/
theorem mem_deleteJoin {t : Treap α} (ht : Sorted t) (a b : α) :
    Mem b (Treap.deleteJoin a t) ↔ b ≠ a ∧ Mem b t := by
  induction t with
  | leaf => simp [Treap.deleteJoin]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold Treap.deleteJoin
    split
    · rename_i hak
      rw [mem_node, ihl hsl, mem_node]
      constructor
      · rintro (⟨hba, hbl⟩ | rfl | hbr)
        · exact ⟨hba, Or.inl hbl⟩
        · exact ⟨(ne_of_lt hak).symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨fun h => absurd h.symm (ne_of_lt (lt_trans hak (hr.of_mem hbr))),
            Or.inr (Or.inr hbr)⟩
      · rintro ⟨hba, hbl | rfl | hbr⟩
        · exact Or.inl ⟨hba, hbl⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hbr)
    · rename_i hak hka
      split
      · rename_i hka'
        rw [mem_node, ihr hsr, mem_node]
        constructor
        · rintro (hbl | rfl | ⟨hba, hbr⟩)
          · exact ⟨ne_of_lt (lt_trans (hl.of_mem hbl) hka'), Or.inl hbl⟩
          · exact ⟨ne_of_lt hka', Or.inr (Or.inl rfl)⟩
          · exact ⟨hba, Or.inr (Or.inr hbr)⟩
        · rintro ⟨hba, hbl | rfl | hbr⟩
          · exact Or.inl hbl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr ⟨hba, hbr⟩)
      · rename_i hka'
        have hkey : k = a := le_antisymm (not_lt.mp hka) (not_lt.mp hka')
        rw [mem_join, mem_node]
        constructor
        · rintro (hbl | hbr)
          · refine ⟨?_, Or.inl hbl⟩
            have : b < a := hkey ▸ hl.of_mem hbl
            exact ne_of_lt this
          · refine ⟨?_, Or.inr (Or.inr hbr)⟩
            have : a < b := hkey ▸ hr.of_mem hbr
            exact (ne_of_lt this).symm
        · rintro ⟨hba, hbl | rfl | hbr⟩
          · exact Or.inl hbl
          · exact absurd hkey hba
          · exact Or.inr hbr

/-- **`deleteJoin` preserves the BST invariant.** -/
theorem sorted_deleteJoin {t : Treap α} (ht : Sorted t) (a : α) :
    Sorted (Treap.deleteJoin a t) := by
  induction t with
  | leaf => simp [Treap.deleteJoin]
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold Treap.deleteJoin
    split
    · rename_i hak
      have hl' : All (· < k) (Treap.deleteJoin a l) :=
        all_of_forall_mem (fun b hb => hl.of_mem ((mem_deleteJoin hsl a b).mp hb).2)
      exact ⟨hl', hr, ihl hsl, hsr⟩
    · rename_i hak hka
      split
      · rename_i hka'
        have hr' : All (k < ·) (Treap.deleteJoin a r) :=
          all_of_forall_mem (fun b hb => hr.of_mem ((mem_deleteJoin hsr a b).mp hb).2)
        exact ⟨hl, hr', hsl, ihr hsr⟩
      · exact sorted_join hsl hsr (fun x y hx hy => lt_trans (hl.of_mem hx) (hr.of_mem hy))

/-- `AllPriority q` is preserved by `deleteJoin`: it only ever removes nodes. -/
theorem AllPriority.deleteJoin {q : ℕ → Prop} {t : Treap α} (ht : AllPriority q t) (a : α) :
    AllPriority q (Treap.deleteJoin a t) := by
  induction t with
  | leaf => trivial
  | node l k p r ihl ihr =>
    obtain ⟨hl, hp, hr⟩ := ht
    unfold Treap.deleteJoin
    split
    · exact ⟨ihl hl, hp, hr⟩
    · split
      · exact ⟨hl, hp, ihr hr⟩
      · exact hl.join hr

/-- **`deleteJoin` preserves heap-order.** -/
theorem heapOrdered_deleteJoin {t : Treap α} (ht : HeapOrdered t) (a : α) :
    HeapOrdered (Treap.deleteJoin a t) := by
  induction t with
  | leaf => trivial
  | node l k p r ihl ihr =>
    obtain ⟨hl, hr, hhl, hhr⟩ := ht
    unfold Treap.deleteJoin
    split
    · exact ⟨hl.deleteJoin a, hr, ihl hhl, hhr⟩
    · split
      · exact ⟨hl, hr.deleteJoin a, hhl, ihr hhr⟩
      · exact heapOrdered_join hhl hhr

/-- **`deleteJoin` produces a legal treap from a legal one.** -/
theorem valid_deleteJoin {t : Treap α} (ht : Valid t) (a : α) : Valid (Treap.deleteJoin a t) :=
  ⟨sorted_deleteJoin ht.1 a, heapOrdered_deleteJoin ht.2 a⟩

/-! ### `delete`: rotate the node down

The book's procedure (Seidel and Aragon): find the node holding `a`, rotate it down, each time
lifting the child of higher priority (the right one on a tie), until it is a leaf, and drop it.
`removeRoot_eq_join` proves the rotations compute `join` of the children, so `delete` equals
`deleteJoin` (`delete_eq_deleteJoin`). -/

/-- Which child `removeRoot` lifts: the left one when it is the only child or has the strictly
higher priority, the right one otherwise, so the right one on a tie. -/
def liftsLeft : Treap α → Treap α → Bool
  | leaf, _ => false
  | node _ _ _ _, leaf => true
  | node _ _ lp _, node _ _ rp _ => decide (rp < lp)

/-- Rotate the root down until it is a leaf, then drop it (Seidel–Aragon): while it has a child,
rotate the child `liftsLeft` picks above it and follow the old root down. Lifting the
higher-priority child is what keeps heap order on the way down. -/
def removeRoot : Treap α → Treap α
  | leaf => leaf
  | node leaf _ _ leaf => leaf
  | node l k p r =>
      if liftsLeft l r then
        match _h : rotateRight (node l k p r) with
        | leaf => leaf
        | node l' k' p' r' => node l' k' p' (removeRoot r')
      else
        match _h : rotateLeft (node l k p r) with
        | leaf => leaf
        | node l' k' p' r' => node (removeRoot l') k' p' r'
termination_by t => sizeOf t
decreasing_by
  · cases l <;> simp only [rotateRight, node.injEq] at _h <;> obtain ⟨-, -, -, rfl⟩ := _h <;>
      simp_wf <;> omega
  · cases r <;> simp only [rotateLeft, node.injEq] at _h <;> obtain ⟨rfl, -, -, -⟩ := _h <;>
      simp_wf <;> omega

omit [LinearOrder α] in
theorem removeRoot_leaf_left (k : α) (p : ℕ) : ∀ r : Treap α, removeRoot (node leaf k p r) = r
  | leaf => by simp [removeRoot]
  | node rl rk rp rr => by
      rw [removeRoot]
      · simp [liftsLeft, rotateLeft, removeRoot_leaf_left k p rl]
      · simp

omit [LinearOrder α] in
theorem removeRoot_leaf_right (k : α) (p : ℕ) : ∀ l : Treap α, removeRoot (node l k p leaf) = l
  | leaf => by simp [removeRoot]
  | node ll lk lp lr => by
      rw [removeRoot]
      · simp [liftsLeft, rotateRight, removeRoot_leaf_right k p lr]
      · simp

omit [LinearOrder α] in
/-- **Rotating the root down is `join` of its children.** Unconditional: no validity, no distinct
priorities, and the same tie rule on both sides. -/
theorem removeRoot_eq_join (k : α) (p : ℕ) (l r : Treap α) :
    removeRoot (node l k p r) = join l r := by
  induction l, r using join.induct generalizing k p with
  | case1 r => rw [removeRoot_leaf_left]; simp [join]
  | case2 l =>
    cases l with
    | leaf => simp [removeRoot, join]
    | node ll lk lp lr => rw [removeRoot_leaf_right]; simp [join]
  | case3 ll lk lp lr rl rk rp rr hlt ih =>
    rw [removeRoot]
    · simp [liftsLeft, rotateRight, hlt, join, ih]
    · simp
  | case4 ll lk lp lr rl rk rp rr hge ih =>
    rw [removeRoot]
    · simp [liftsLeft, rotateLeft, hge, join, ih]
    · simp

/-- Delete `a`: descend as a BST search does, and remove the node holding `a` by rotating it down
(`removeRoot`). A key that is absent leaves the tree unchanged. -/
def delete (a : α) : Treap α → Treap α
  | leaf => leaf
  | node l k p r =>
      if a < k then node (delete a l) k p r
      else if k < a then node l k p (delete a r)
      else removeRoot (node l k p r)

/-- At the node holding the key, `delete` is `removeRoot`: it rotates the node down. -/
theorem delete_node_self (l : Treap α) (k : α) (p : ℕ) (r : Treap α) :
    delete k (node l k p r) = removeRoot (node l k p r) := by
  simp [delete, lt_irrefl]

/-- **Rotating down and joining are the same deletion**, on every tree: no validity, no distinct
keys or priorities needed. -/
theorem delete_eq_deleteJoin (a : α) : ∀ t : Treap α, delete a t = deleteJoin a t
  | leaf => rfl
  | node l k p r => by
      simp only [delete, deleteJoin, delete_eq_deleteJoin a l, delete_eq_deleteJoin a r,
        removeRoot_eq_join]

/-- **`delete` is correct on keys**: it removes exactly `a` and nothing else. -/
theorem mem_delete {t : Treap α} (ht : Sorted t) (a b : α) :
    Mem b (Treap.delete a t) ↔ b ≠ a ∧ Mem b t := by
  rw [delete_eq_deleteJoin]; exact mem_deleteJoin ht a b

/-- **`delete` preserves the BST invariant.** -/
theorem sorted_delete {t : Treap α} (ht : Sorted t) (a : α) : Sorted (Treap.delete a t) := by
  rw [delete_eq_deleteJoin]; exact sorted_deleteJoin ht a

/-- `AllPriority q` is preserved by `delete`: it only ever removes nodes. -/
theorem AllPriority.delete {q : ℕ → Prop} {t : Treap α} (ht : AllPriority q t) (a : α) :
    AllPriority q (Treap.delete a t) := by
  rw [delete_eq_deleteJoin]; exact ht.deleteJoin a

/-- **`delete` preserves heap-order.** -/
theorem heapOrdered_delete {t : Treap α} (ht : HeapOrdered t) (a : α) :
    HeapOrdered (Treap.delete a t) := by
  rw [delete_eq_deleteJoin]; exact heapOrdered_deleteJoin ht a

/-- **`delete` produces a legal treap from a legal one.** -/
theorem valid_delete {t : Treap α} (ht : Valid t) (a : α) : Valid (Treap.delete a t) :=
  ⟨sorted_delete ht.1 a, heapOrdered_delete ht.2 a⟩

/-- `deleteJoin` leaves every other key's priority where it was. -/
theorem priorityOf_deleteJoin_other {a b : α} (hb : b ≠ a) :
    ∀ t : Treap α, Sorted t → priorityOf b (deleteJoin a t) = priorityOf b t := by
  intro t
  induction t with
  | leaf => intro _; rfl
  | node l k p r ihl ihr =>
    intro ht
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    simp only [deleteJoin]
    split_ifs with h1 h2
    · rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]; exact ihl hsl
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]
    · rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]; exact ihr hsr
    · have hak : a = k := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst hak
      rw [priorityOf_join hsl hsr (fun x y hx hy => lt_trans (hl.of_mem hx) (hr.of_mem hy))]
      rcases lt_trichotomy b a with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_eq_none_of_not_mem hsr
          (fun hm => lt_asymm hbk (hr.of_mem hm)), Option.or_none]
      · exact absurd rfl hb
      · rw [priorityOf_right hkb, priorityOf_eq_none_of_not_mem hsl
          (fun hm => lt_asymm hkb (hl.of_mem hm)), Option.none_or]

/-- **`delete` moves no other key's priority.** Its rotations carry each surviving node's priority
along with its key; proved through `delete_eq_deleteJoin`. -/
theorem priorityOf_delete_other {a b : α} (hb : b ≠ a) (t : Treap α) (ht : Sorted t) :
    priorityOf b (Treap.delete a t) = priorityOf b t := by
  rw [delete_eq_deleteJoin]; exact priorityOf_deleteJoin_other hb t ht

/-- The deleted key has no priority left: it is gone, and a sorted tree answers `none` for a key
it does not hold. -/
theorem priorityOf_delete_self (a : α) (t : Treap α) (ht : Sorted t) :
    priorityOf a (Treap.delete a t) = none :=
  priorityOf_eq_none_of_not_mem (sorted_delete ht a)
    (fun h => ((mem_delete ht a a).mp h).1 rfl)

/-- **`delete` discharges `DeleteSpec`.** Assembled from `mem_delete`, `priorityOf_delete_other`
and `valid_delete`. -/
theorem deleteSpec {t : Treap α} (ht : Valid t) (a : α) : DeleteSpec a t (Treap.delete a t) :=
  ⟨mem_delete ht.1 a, fun _ hb => priorityOf_delete_other hb t ht.1, fun hv => valid_delete hv a⟩

end Treap

end AlgoDesign.Searching
