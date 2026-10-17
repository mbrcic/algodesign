/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Spec

/-!
# Treap: structural bookkeeping

`All`, `Mem`, `AllPriority`, `HeapOrdered` and `Sorted` lemmas, `size` and `priorityList`, and
what `priorityOf` reads off a valid treap (`priorityOf_root`, `priorityOf_le_root`,
`priorityOf_eq_none_of_not_mem`). The specification they serve is in `Spec.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}

@[simp] theorem all_leaf (p : α → Prop) : All p (leaf : Treap α) ↔ True := Iff.rfl

@[simp] theorem all_node (p : α → Prop) (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    All p (node l k pr r) ↔ All p l ∧ p k ∧ All p r := Iff.rfl

@[simp] theorem mem_leaf (a : α) : Mem a (leaf : Treap α) ↔ False := Iff.rfl

@[simp] theorem mem_node (a : α) (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    Mem a (node l k pr r) ↔ Mem a l ∨ a = k ∨ Mem a r := Iff.rfl

theorem All.imp {p q : α → Prop} (h : ∀ a, p a → q a) : ∀ {t : Treap α}, All p t → All q t
  | leaf, _ => trivial
  | node _ _ _ _, ⟨hl, hk, hr⟩ => ⟨hl.imp (fun _ => h _), h _ hk, hr.imp (fun _ => h _)⟩

theorem All.of_mem {p : α → Prop} {t : Treap α} (h : All p t) {a : α} (ha : Mem a t) : p a := by
  induction t with
  | leaf => cases ha
  | node l k pr r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    rcases ha with ha | ha | ha
    · exact ihl hl ha
    · exact ha ▸ hk
    · exact ihr hr ha

/-- If every member of `t` satisfies `p`, `All p t` holds. The converse of the elimination
principle `All.of_mem`, used (as in `BST`) to rebuild an `All` fact for a *new* tree from a
membership-level argument about what's still there after some structural rearrangement. -/
theorem all_of_forall_mem {p : α → Prop} {t : Treap α} (h : ∀ b, Mem b t → p b) : All p t := by
  induction t with
  | leaf => trivial
  | node l k pr r ihl ihr =>
    exact ⟨ihl (fun b hb => h b (Or.inl hb)), h k (Or.inr (Or.inl rfl)),
      ihr (fun b hb => h b (Or.inr (Or.inr hb)))⟩

@[simp] theorem allPriority_leaf (q : ℕ → Prop) : AllPriority q (leaf : Treap α) ↔ True := Iff.rfl

@[simp] theorem allPriority_node (q : ℕ → Prop) (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    AllPriority q (node l k pr r) ↔ AllPriority q l ∧ q pr ∧ AllPriority q r := Iff.rfl

theorem AllPriority.imp {q r : ℕ → Prop} (h : ∀ n, q n → r n) :
    ∀ {t : Treap α}, AllPriority q t → AllPriority r t
  | leaf, _ => trivial
  | node _ _ _ _, ⟨hl, hp, hr⟩ => ⟨hl.imp (fun _ => h _), h _ hp, hr.imp (fun _ => h _)⟩

@[simp] theorem heapOrdered_leaf : HeapOrdered (leaf : Treap α) ↔ True := Iff.rfl

@[simp] theorem heapOrdered_node (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    HeapOrdered (node l k pr r) ↔
      AllPriority (· ≤ pr) l ∧ AllPriority (· ≤ pr) r ∧ HeapOrdered l ∧ HeapOrdered r := Iff.rfl

/-- A `HeapOrdered` node's priority bounds the whole node, root included. -/
theorem HeapOrdered.self_le {l r : Treap α} {k : α} {pr : ℕ} (h : HeapOrdered (node l k pr r)) :
    AllPriority (· ≤ pr) (node l k pr r) :=
  ⟨h.1, le_refl pr, h.2.1⟩

variable [LinearOrder α]

@[simp] theorem sorted_leaf : Sorted (leaf : Treap α) ↔ True := Iff.rfl

@[simp] theorem sorted_node (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    Sorted (node l k pr r) ↔ All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r := Iff.rfl

/-! ### Structural observations for future uniqueness and cost proofs -/

/-- Number of keys in the tree, computed recursively rather than cached. -/
def size : Treap α → ℕ
  | leaf => 0
  | node l _ _ r => l.size + r.size + 1

/-- Every priority in the tree, in key traversal order. -/
def priorityList : Treap α → List ℕ
  | leaf => []
  | node l _ p r => l.priorityList ++ [p] ++ r.priorityList

omit [LinearOrder α] in
theorem eq_leaf_of_not_mem {t : Treap α} (h : ∀ a, ¬ Mem a t) : t = leaf := by
  cases t with
  | leaf => rfl
  | node l k pr r => exact absurd (Or.inr (Or.inl rfl) : Mem k (node l k pr r)) (h k)

@[simp] theorem priorityOf_leaf (a : α) : priorityOf a (leaf : Treap α) = none := rfl

@[simp] theorem priorityOf_root (l : Treap α) (k : α) (pr : ℕ) (r : Treap α) :
    priorityOf k (node l k pr r) = some pr := by simp [priorityOf, lt_irrefl k]

theorem priorityOf_left {l : Treap α} {k : α} {pr : ℕ} {r : Treap α} {a : α} (h : a < k) :
    priorityOf a (node l k pr r) = priorityOf a l := by simp [priorityOf, h]

theorem priorityOf_right {l : Treap α} {k : α} {pr : ℕ} {r : Treap α} {a : α} (h : k < a) :
    priorityOf a (node l k pr r) = priorityOf a r := by
  simp [priorityOf, not_lt.mpr (le_of_lt h), h]

/-- A priority found along the search path is one of the tree's priorities, so any `AllPriority`
bound applies to it. -/
theorem priorityOf_allPriority {q : ℕ → Prop} {t : Treap α} (h : AllPriority q t) {a : α} {p : ℕ}
    (hp : priorityOf a t = some p) : q p := by
  induction t with
  | leaf => simp at hp
  | node l k pr r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    by_cases hak : a < k
    · exact ihl hl (by rwa [priorityOf_left hak] at hp)
    · by_cases hka : k < a
      · exact ihr hr (by rwa [priorityOf_right hka] at hp)
      · have : a = k := le_antisymm (not_lt.mp hka) (not_lt.mp hak)
        subst this
        rw [priorityOf_root] at hp
        exact Option.some.inj hp ▸ hk

/-- **The root carries the maximum priority**: anything the search path turns up is bounded by it.
This is the fact that pins a valid treap's root, and hence its whole shape. -/
theorem priorityOf_le_root {l : Treap α} {k : α} {pr : ℕ} {r : Treap α}
    (h : HeapOrdered (node l k pr r)) {a : α} {p : ℕ}
    (hp : priorityOf a (node l k pr r) = some p) : p ≤ pr :=
  priorityOf_allPriority h.self_le hp

/-- Outside the key set the search path runs out, so there is no priority to find. -/
theorem priorityOf_eq_none_of_not_mem {t : Treap α} (ht : Sorted t) {a : α} (h : ¬ Mem a t) :
    priorityOf a t = none := by
  induction t with
  | leaf => rfl
  | node l k pr r ihl ihr =>
    obtain ⟨hlt, hgt, hsl, hsr⟩ := ht
    simp only [mem_node, not_or] at h
    obtain ⟨hnl, hnk, hnr⟩ := h
    by_cases hak : a < k
    · rw [priorityOf_left hak]; exact ihl hsl hnl
    · by_cases hka : k < a
      · rw [priorityOf_right hka]; exact ihr hsr hnr
      · exact absurd (le_antisymm (not_lt.mp hka) (not_lt.mp hak)) hnk

end Treap

end AlgoDesign.Searching
