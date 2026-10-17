/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Spec

/-!
# Binary search tree: structural bookkeeping

`All`, `Mem` and `Sorted` lemmas, `toList` against `Mem` (`mem_toList`), and `size` and `height`.
The specification they serve is in `Spec.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}

/-- Is `a` a key of the tree? -/
def Mem (a : α) : BST α → Prop
  | leaf => False
  | node l k r => Mem a l ∨ a = k ∨ Mem a r

@[simp] theorem all_leaf (p : α → Prop) : All p (leaf : BST α) ↔ True := Iff.rfl

@[simp] theorem all_node (p : α → Prop) (l : BST α) (k : α) (r : BST α) :
    All p (node l k r) ↔ All p l ∧ p k ∧ All p r := Iff.rfl

@[simp] theorem mem_leaf (a : α) : Mem a (leaf : BST α) ↔ False := Iff.rfl

@[simp] theorem mem_node (a : α) (l : BST α) (k : α) (r : BST α) :
    Mem a (node l k r) ↔ Mem a l ∨ a = k ∨ Mem a r := Iff.rfl

theorem All.imp {p q : α → Prop} (h : ∀ a, p a → q a) : ∀ {t : BST α}, All p t → All q t
  | leaf, _ => trivial
  | node _ _ _, ⟨hl, hk, hr⟩ => ⟨hl.imp (fun _ => h _), h _ hk, hr.imp (fun _ => h _)⟩

theorem All.of_mem {p : α → Prop} {t : BST α} (h : All p t) {a : α} (ha : Mem a t) : p a := by
  induction t with
  | leaf => cases ha
  | node l k r ihl ihr =>
    obtain ⟨hl, hk, hr⟩ := h
    rcases ha with ha | ha | ha
    · exact ihl hl ha
    · exact ha ▸ hk
    · exact ihr hr ha

variable [LinearOrder α]

@[simp] theorem sorted_leaf : Sorted (leaf : BST α) ↔ True := Iff.rfl

@[simp] theorem sorted_node (l : BST α) (k : α) (r : BST α) :
    Sorted (node l k r) ↔ All (· < k) l ∧ All (k < ·) r ∧ Sorted l ∧ Sorted r := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem toList_leaf : toList (leaf : BST α) = [] := rfl

omit [LinearOrder α] in
@[simp] theorem toList_node (l : BST α) (k : α) (r : BST α) :
    toList (node l k r) = toList l ++ k :: toList r := rfl

omit [LinearOrder α] in
/-- **`toList` observes exactly `Mem`.** -/
theorem mem_toList {a : α} : ∀ t : BST α, a ∈ toList t ↔ Mem a t
  | leaf => by simp
  | node l k r => by
      simp only [toList_node, List.mem_append, List.mem_cons, mem_node,
        mem_toList l, mem_toList r]

/-- Number of keys in the tree. Computed, not cached in each node — a real implementation caches
this per node for O(log n) `rank`/`select?` (that's the whole point of carrying it at all), but
that's a performance trick for the *implementation*, not something the *spec* needs: correctness
of `rank`/`select?` doesn't depend on how `size` is computed, only on what it computes. -/
def size : BST α → ℕ
  | leaf => 0
  | node l _ r => l.size + r.size + 1

omit [LinearOrder α] in
@[simp] theorem size_leaf : size (leaf : BST α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem size_node (l : BST α) (k : α) (r : BST α) :
    size (node l k r) = l.size + r.size + 1 := rfl

omit [LinearOrder α] in
@[simp] theorem height_leaf : height (leaf : BST α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem height_node (l : BST α) (k : α) (r : BST α) :
    height (node l k r) = max (height l) (height r) + 1 := rfl

omit [LinearOrder α] in
/-- If every member of `s` is (pointwise) a member of `t`, and `p` holds of everything in `t`,
`p` holds of everything in `s`. The general form of the "delete only ever removes keys" argument
`delete_sorted` needs: whatever invariant held for the elements around a subtree still holds once
some of them are gone. -/
theorem all_of_forall_mem {p : α → Prop} {s : BST α} (h : ∀ b, Mem b s → p b) : All p s := by
  induction s with
  | leaf => trivial
  | node l k r ihl ihr =>
    exact ⟨ihl (fun b hb => h b (Or.inl hb)), h k (Or.inr (Or.inl rfl)),
      ihr (fun b hb => h b (Or.inr (Or.inr hb)))⟩

end BST

end AlgoDesign.Searching
