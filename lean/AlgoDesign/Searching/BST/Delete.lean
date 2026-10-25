/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Insert

/-!
# Binary search tree: deletion

Two deletions answerable to one `DeleteSpec`: `delete`, CLRS's `TRANSPLANT` (§12.3) — the
successor's *node* moves into the gap, spliced out by `spliceMin` — and `deleteHibbard`, which
copies the successor's *key* up. `deleteSpec` and `deleteHibbardSpec` discharge the obligation for
each, and `deleteHibbard_eq_delete` says that in a persistent tree they build the same tree.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}
variable [LinearOrder α]

/-- **What any deletion of `a` owes**, whichever algorithm performs it: afterwards the key set is
the old one minus exactly `a`, and a sorted tree stays sorted. A relation, not a function, so both
`delete` and `deleteHibbard` answer to it. The per-operation form the proofs discharge; the promise,
`SearchTree.Promise`, states the same for every operation at once. -/
def DeleteSpec (a : α) (before after : BST α) : Prop :=
  (∀ b, Mem b after ↔ (b ≠ a ∧ Mem b before)) ∧ (Sorted before → Sorted after)

/-- Remove the smallest key, handing back both it and the tree that remains — its own right
subtree promoted into its place in one step, which is CLRS's `TRANSPLANT(y, y.right)` applied to
the leftmost node. `none` exactly on the empty tree.

Both deletions below use it: the successor, having no left child, leaves in one step. -/
def spliceMin : BST α → Option (α × BST α)
  | leaf => none
  | node l k r =>
      match spliceMin l with
      | none => some (k, r)
      | some (m, l') => some (m, node l' k r)

omit [LinearOrder α] in
@[simp] theorem spliceMin_leaf : spliceMin (leaf : BST α) = none := rfl

omit [LinearOrder α] in
theorem spliceMin_eq_none {t : BST α} (h : spliceMin t = none) : t = leaf := by
  cases t with
  | leaf => rfl
  | node l k r =>
    unfold spliceMin at h
    split at h <;> simp at h

omit [LinearOrder α] in
/-- **`spliceMin` removes exactly one key, the one it returns.** No ordering assumption is needed
for this: it is a statement about which keys the tree holds, not about where they sit. -/
theorem mem_spliceMin {t : BST α} {m : α} {t' : BST α} (h : spliceMin t = some (m, t')) :
    Mem m t ∧ ∀ b, Mem b t ↔ (b = m ∨ Mem b t') := by
  induction t generalizing m t' with
  | leaf => simp [spliceMin] at h
  | node l k r ihl _ =>
    unfold spliceMin at h
    cases hl : spliceMin l with
    | none =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hleaf : l = leaf := spliceMin_eq_none hl
      subst hleaf
      exact ⟨Or.inr (Or.inl rfl), fun b => by simp [mem_node]⟩
    | some q =>
      obtain ⟨m0, l0⟩ := q
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hmem, hchar⟩ := ihl hl
      refine ⟨Or.inl hmem, fun b => ?_⟩
      rw [mem_node, mem_node, hchar b]
      tauto

omit [LinearOrder α] in
/-- Whatever held of every key before holds of the returned key and of every key left behind. -/
theorem all_spliceMin {p : α → Prop} {t : BST α} {m : α} {t' : BST α}
    (hp : All p t) (h : spliceMin t = some (m, t')) : p m ∧ All p t' := by
  obtain ⟨hmem, hchar⟩ := mem_spliceMin h
  exact ⟨hp.of_mem hmem,
    all_of_forall_mem (fun b hb => hp.of_mem ((hchar b).mpr (Or.inr hb)))⟩

/-- **`spliceMin` returns the minimum and leaves a sorted tree.** Both halves are what `delete`
needs to put the returned key where the deleted one stood. -/
theorem sorted_spliceMin {t : BST α} {m : α} {t' : BST α}
    (ht : Sorted t) (h : spliceMin t = some (m, t')) : Sorted t' ∧ All (m < ·) t' := by
  induction t generalizing m t' with
  | leaf => simp [spliceMin] at h
  | node l k r ihl _ =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold spliceMin at h
    cases hlm : spliceMin l with
    | none =>
      rw [hlm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hsr, hr⟩
    | some q =>
      obtain ⟨m0, l0⟩ := q
      rw [hlm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hs0, hmin0⟩ := ihl hsl hlm
      obtain ⟨hmk, hl0⟩ := all_spliceMin hl hlm
      exact ⟨⟨hl0, hr, hs0, hsr⟩,
        ⟨hmin0, hmk, hr.imp (fun b hb => lt_trans hmk hb)⟩⟩

/-- The work `delete` does at the node it found: CLRS §12.3's three cases, in CLRS's order —
no left child, promote the right subtree; no right child, promote the left; otherwise take the
right subtree's minimum out with `spliceMin` and stand it where the deleted key stood.

Pulled out of `delete` so the case analysis is proved once, against a node's two subtrees and the
`Sorted` facts that place them, rather than inside the recursion. -/
def transplantAt (l r : BST α) : BST α :=
  match l, spliceMin r with
  | leaf, _ => r
  | l, none => l
  | l, some (m, r') => node l m r'

/-- **The gap is filled with exactly the keys that were under it, minus the one that left.**
`k` is the key being deleted; the hypotheses are the two halves of `Sorted (node l k r)` that
place `l` and `r` around it. -/
theorem mem_transplantAt {l r : BST α} {k : α}
    (hl : All (· < k) l) (hr : All (k < ·) r) (b : α) :
    Mem b (transplantAt l r) ↔ b ≠ k ∧ Mem b (node l k r) := by
  unfold transplantAt
  cases l with
  | leaf =>
    simp only [mem_node, mem_leaf, false_or]
    constructor
    · exact fun hbr => ⟨(ne_of_lt (hr.of_mem hbr)).symm, Or.inr hbr⟩
    · rintro ⟨hba, rfl | hbr⟩
      · exact absurd rfl hba
      · exact hbr
  | node ll lk lr =>
    cases hrm : spliceMin r with
    | none =>
      simp only
      have hleaf : r = leaf := spliceMin_eq_none hrm
      subst hleaf
      rw [mem_node b (node ll lk lr) k leaf]
      simp only [mem_leaf, or_false]
      constructor
      · exact fun hbl => ⟨ne_of_lt (hl.of_mem hbl), Or.inl hbl⟩
      · rintro ⟨hba, hbl | rfl⟩
        · exact hbl
        · exact absurd rfl hba
    | some q =>
      obtain ⟨m, r'⟩ := q
      simp only
      obtain ⟨hmem, hchar⟩ := mem_spliceMin hrm
      have hkm : k < m := hr.of_mem hmem
      rw [mem_node b (node ll lk lr) m r', mem_node b (node ll lk lr) k r]
      constructor
      · rintro (hbl | rfl | hbr)
        · exact ⟨ne_of_lt (hl.of_mem hbl), Or.inl hbl⟩
        · exact ⟨(ne_of_lt hkm).symm, Or.inr (Or.inr ((hchar b).mpr (Or.inl rfl)))⟩
        · have hb : Mem b r := (hchar b).mpr (Or.inr hbr)
          exact ⟨(ne_of_lt (hr.of_mem hb)).symm, Or.inr (Or.inr hb)⟩
      · rintro ⟨hba, hbl | rfl | hbr⟩
        · exact Or.inl hbl
        · exact absurd rfl hba
        · rcases (hchar b).mp hbr with rfl | hbr'
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hbr')

/-- **The gap is filled with a key that belongs in it.** -/
theorem sorted_transplantAt {l r : BST α} {k : α}
    (hl : All (· < k) l) (hr : All (k < ·) r) (hsl : Sorted l) (hsr : Sorted r) :
    Sorted (transplantAt l r) := by
  unfold transplantAt
  cases l with
  | leaf => exact hsr
  | node ll lk lr =>
    cases hrm : spliceMin r with
    | none => simpa only [hrm] using hsl
    | some q =>
      obtain ⟨m, r'⟩ := q
      simp only
      obtain ⟨hs', hmin'⟩ := sorted_spliceMin hsr hrm
      obtain ⟨hmem, _⟩ := mem_spliceMin hrm
      have hkm : k < m := hr.of_mem hmem
      exact ⟨hl.imp (fun x hx => lt_trans hx hkm), hmin', hsl, hs'⟩

/-- Delete `a` by **moving the in-order successor's node** into the gap — CLRS's `TRANSPLANT`
formulation, §12.3, via `transplantAt` above. The chapter's default. -/
def delete (a : α) : BST α → BST α
  | leaf => leaf
  | node l k r =>
      if a < k then node (delete a l) k r
      else if k < a then node l k (delete a r)
      else transplantAt l r

/-- Delete `a` by **copying the in-order successor's key up** instead of moving its node: with one
child or none the child takes the node's place; with two, the successor's key is written into the
node and the successor is spliced out of the right subtree by `spliceMin`, one step, never a chain
(Weiss §4.3.4). In a persistent tree this is the same function as `delete`
(`deleteHibbard_eq_delete`); the two differ only in which node survives. -/
def deleteHibbard (a : α) : BST α → BST α
  | leaf => leaf
  | node l k r =>
      if a < k then node (deleteHibbard a l) k r
      else if k < a then node l k (deleteHibbard a r)
      else
        match l, spliceMin r with
        | leaf, _ => r
        | l, none => l
        | l, some (m, r') => node l m r'

/-- **`delete` is correct**: it removes exactly `a` and nothing else. -/
theorem mem_delete {t : BST α} (ht : Sorted t) (a b : α) :
    Mem b (delete a t) ↔ b ≠ a ∧ Mem b t := by
  induction t generalizing a with
  | leaf => simp [delete]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold delete
    split_ifs with hak hka
    · rw [mem_node, ihl hsl a, mem_node]
      constructor
      · rintro (⟨hba, hbl⟩ | rfl | hbr)
        · exact ⟨hba, Or.inl hbl⟩
        · exact ⟨(ne_of_lt hak).symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨(ne_of_lt (lt_trans hak (hr.of_mem hbr))).symm, Or.inr (Or.inr hbr)⟩
      · rintro ⟨hba, hbl | rfl | hbr⟩
        · exact Or.inl ⟨hba, hbl⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hbr)
    · rw [mem_node, ihr hsr a, mem_node]
      constructor
      · rintro (hbl | rfl | ⟨hba, hbr⟩)
        · exact ⟨ne_of_lt (lt_trans (hl.of_mem hbl) hka), Or.inl hbl⟩
        · exact ⟨ne_of_lt hka, Or.inr (Or.inl rfl)⟩
        · exact ⟨hba, Or.inr (Or.inr hbr)⟩
      · rintro ⟨hba, hbl | rfl | hbr⟩
        · exact Or.inl hbl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨hba, hbr⟩)
    · have hak' : a = k := le_antisymm (not_lt.mp hka) (not_lt.mp hak)
      subst hak'
      exact mem_transplantAt hl hr b

/-- **`delete` preserves the BST invariant**. -/
theorem sorted_delete {t : BST α} (ht : Sorted t) (a : α) : Sorted (delete a t) := by
  induction t generalizing a with
  | leaf => simp [delete]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold delete
    split_ifs with hak hka
    · have hl' : All (· < k) (delete a l) :=
        all_of_forall_mem (fun b hb => hl.of_mem ((mem_delete hsl a b).mp hb).2)
      exact ⟨hl', hr, ihl hsl a, hsr⟩
    · have hr' : All (k < ·) (delete a r) :=
        all_of_forall_mem (fun b hb => hr.of_mem ((mem_delete hsr a b).mp hb).2)
      exact ⟨hl, hr', hsl, ihr hsr a⟩
    · exact sorted_transplantAt hl hr hsl hsr

/-- **Copying the key and moving the node leave the same tree.** Without pointers the two
deletions are one function; they differ only in which node object survives, which no persistent
tree can observe. -/
theorem deleteHibbard_eq_delete (a : α) : ∀ t : BST α, deleteHibbard a t = delete a t
  | leaf => rfl
  | node l k r => by
      simp only [deleteHibbard, delete, transplantAt, deleteHibbard_eq_delete a l,
        deleteHibbard_eq_delete a r]

/-- **`deleteHibbard` is correct**: it removes exactly `a` and nothing else. -/
theorem mem_deleteHibbard {t : BST α} (ht : Sorted t) (a b : α) :
    Mem b (deleteHibbard a t) ↔ b ≠ a ∧ Mem b t := by
  rw [deleteHibbard_eq_delete]; exact mem_delete ht a b

/-- **`deleteHibbard` preserves the BST invariant**. -/
theorem sorted_deleteHibbard {t : BST α} (ht : Sorted t) (a : α) : Sorted (deleteHibbard a t) := by
  rw [deleteHibbard_eq_delete]; exact sorted_delete ht a

/-- **`delete` discharges `DeleteSpec`.** Assembled from `mem_delete` and `sorted_delete`, which
are the two halves of it. -/
theorem deleteSpec {t : BST α} (ht : Sorted t) (a : α) : DeleteSpec a t (delete a t) :=
  ⟨mem_delete ht a, fun _ => sorted_delete ht a⟩

/-- **`deleteHibbard` discharges the same `DeleteSpec`.** Two algorithms, one obligation. The shape
is outside the obligation, so it would not have to agree; here it does (`deleteHibbard_eq_delete`).
-/
theorem deleteHibbardSpec {t : BST α} (ht : Sorted t) (a : α) :
    DeleteSpec a t (deleteHibbard a t) :=
  ⟨mem_deleteHibbard ht a, fun _ => sorted_deleteHibbard ht a⟩

/-! Both deletions on the tree `DeleteSpec`'s docstring discusses, machine-checked: they build
the same tree. -/

example : delete 15 (node leaf 15 (node (node leaf 16 leaf) 30 leaf))
    = node (node leaf 16 leaf) 30 leaf := by
  rfl

example : deleteHibbard 15 (node leaf 15 (node (node leaf 16 leaf) 30 leaf))
    = node (node leaf 16 leaf) 30 leaf := by
  rfl

/-- **Argued, not proved:** a delete that counts its comparisons, answers as the delete does, and
takes at most the height in comparisons. Delete walks one path down, as search
does; Lean has no counted delete, by choice, so `Contract` does not include it. -/
def DeleteCost (o : Ops α) (deleteM : α → BST α → TimeM ℕ (BST α)) : Prop :=
  (∀ a t, (deleteM a t).ret = o.tree.delete a t) ∧ (∀ a t, (deleteM a t).time ≤ height t)

end BST

end AlgoDesign.Searching
