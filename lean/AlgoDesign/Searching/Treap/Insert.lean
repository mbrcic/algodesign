/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Split

/-!
# Treap: insertion

`insert` places the key as a leaf and rotates it up (`rotateRight`/`rotateLeft`) while its priority
beats its parent's. It keeps the key set plus `a` (`mem_insert`), both invariants (`valid_insert`),
and every other key's priority (`priorityOf_insert_other`); an absent key ends up at the priority
it was given (`priorityOf_insert_self`), and a key already present leaves the tree as it was
(`insert_of_mem`). So `insertSpec`: `insert` discharges `InsertSpec`.
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}
variable [LinearOrder α]

/-! ### `insert`

Rotate the new node up (Seidel and Aragon; Weiss §12.3). The proof is a strengthened induction
(`insert_heap_spec`): its fourth conjunct says that once the root priority has risen, everything
under the new root came from the old tree, which is what a rotation at the parent needs. -/

/-- The left subtree; a leaf's is a leaf. -/
def left : Treap α → Treap α
  | leaf => leaf
  | node l _ _ _ => l

/-- The right subtree; a leaf's is a leaf. -/
def right : Treap α → Treap α
  | leaf => leaf
  | node _ _ _ r => r

/-- The root's priority; a leaf's is `0`, below every priority. -/
def rootPriority : Treap α → ℕ
  | leaf => 0
  | node _ _ p _ => p

omit [LinearOrder α] in
@[simp] theorem rootPriority_leaf : rootPriority (leaf : Treap α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem rootPriority_node (l : Treap α) (k : α) (p : ℕ) (r : Treap α) :
    rootPriority (node l k p r) = p := rfl

omit [LinearOrder α] in
@[simp] theorem left_node (l : Treap α) (k : α) (p : ℕ) (r : Treap α) :
    left (node l k p r) = l := rfl

omit [LinearOrder α] in
@[simp] theorem right_node (l : Treap α) (k : α) (p : ℕ) (r : Treap α) :
    right (node l k p r) = r := rfl

/-- Rotate right: the left child becomes the root. A tree with no left child is left as it is. -/
def rotateRight : Treap α → Treap α
  | node (node ll lk lp lr) k p r => node ll lk lp (node lr k p r)
  | t => t

/-- Rotate left: the right child becomes the root. A tree with no right child is left as it is.
-/
def rotateLeft : Treap α → Treap α
  | node l k p (node rl rk rp rr) => node (node l k p rl) rk rp rr
  | t => t

/-- Insert as an ordinary BST insert would, then rotate the new node up while its priority is
strictly higher than its parent's; a tie leaves it below. A key already present leaves the tree
unchanged, priority included, as the textbooks do (Seidel–Aragon, Weiss §12.3). -/
def insert (a : α) (pr : ℕ) : Treap α → Treap α
  | leaf => node leaf a pr leaf
  | node l k p r =>
      if a < k then
        let l' := insert a pr l
        if p < rootPriority l' then rotateRight (node l' k p r) else node l' k p r
      else if k < a then
        let r' := insert a pr r
        if p < rootPriority r' then rotateLeft (node l k p r') else node l k p r'
      else node l k p r

omit [LinearOrder α] in
@[simp] theorem mem_rotateRight (t : Treap α) (b : α) : Mem b (rotateRight t) ↔ Mem b t := by
  rcases t with _ | ⟨l, k, p, r⟩
  · rfl
  · rcases l with _ | ⟨ll, lk, lp, lr⟩
    · rfl
    · simp [rotateRight]; tauto

omit [LinearOrder α] in
@[simp] theorem mem_rotateLeft (t : Treap α) (b : α) : Mem b (rotateLeft t) ↔ Mem b t := by
  rcases t with _ | ⟨l, k, p, r⟩
  · rfl
  · rcases r with _ | ⟨rl, rk, rp, rr⟩
    · rfl
    · simp [rotateLeft]; tauto

theorem sorted_rotateRight {t : Treap α} (ht : Sorted t) : Sorted (rotateRight t) := by
  rcases t with _ | ⟨l, k, p, r⟩
  · trivial
  · rcases l with _ | ⟨ll, lk, lp, lr⟩
    · exact ht
    · obtain ⟨hl, hr, hsl, hsr⟩ := ht
      obtain ⟨hll, hlk, hlr⟩ := hl
      obtain ⟨hllb, hlrb, hsll, hslr⟩ := hsl
      exact ⟨hllb, ⟨hlrb, hlk, hr.imp (fun _ hx => lt_trans hlk hx)⟩, hsll, ⟨hlr, hr, hslr, hsr⟩⟩

theorem sorted_rotateLeft {t : Treap α} (ht : Sorted t) : Sorted (rotateLeft t) := by
  rcases t with _ | ⟨l, k, p, r⟩
  · trivial
  · rcases r with _ | ⟨rl, rk, rp, rr⟩
    · exact ht
    · obtain ⟨hl, hr, hsl, hsr⟩ := ht
      obtain ⟨hrl, hrk, hrr⟩ := hr
      obtain ⟨hrlb, hrrb, hsrl, hsrr⟩ := hsr
      exact ⟨⟨hl.imp (fun _ hx => lt_trans hx hrk), hrk, hrlb⟩, hrrb, ⟨hl, hrl, hsl, hsrl⟩, hsrr⟩

theorem mem_insert {t : Treap α} (a : α) (pr : ℕ) (b : α) :
    Mem b (insert a pr t) ↔ b = a ∨ Mem b t := by
  induction t with
  | leaf => simp [insert]
  | node l k p r ihl ihr =>
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · rw [mem_rotateRight]; simp only [mem_node, ihl]; tauto
    · simp only [mem_node, ihl]; tauto
    · rw [mem_rotateLeft]; simp only [mem_node, ihr]; tauto
    · simp only [mem_node, ihr]; tauto
    · have hak : a = k := le_antisymm (not_lt.mp h3) (not_lt.mp h1)
      subst hak
      simp only [mem_node]
      tauto

theorem All.insert {q : α → Prop} {t : Treap α} (ht : All q t) {a : α} (ha : q a) (pr : ℕ) :
    All q (insert a pr t) :=
  all_of_forall_mem fun b hb =>
    ((mem_insert (t := t) a pr b).mp hb).elim (fun h => h ▸ ha) ht.of_mem

theorem sorted_insert (a : α) (pr : ℕ) : ∀ t : Treap α, Sorted t → Sorted (insert a pr t) := by
  intro t
  induction t with
  | leaf => intro _; exact ⟨trivial, trivial, trivial, trivial⟩
  | node l k p r ihl ihr =>
    intro ht
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · exact sorted_rotateRight ⟨hl.insert h1 pr, hr, ihl hsl, hsr⟩
    · exact ⟨hl.insert h1 pr, hr, ihl hsl, hsr⟩
    · exact sorted_rotateLeft ⟨hl, hr.insert h3 pr, hsl, ihr hsr⟩
    · exact ⟨hl, hr.insert h3 pr, hsl, ihr hsr⟩
    · exact ⟨hl, hr, hsl, hsr⟩

omit [LinearOrder α] in
theorem rootPriority_le_of_allPriority {m : ℕ} {t : Treap α} (h : AllPriority (· ≤ m) t) :
    rootPriority t ≤ m := by
  cases t with
  | leaf => exact Nat.zero_le m
  | node l k p r => exact h.2.1

omit [LinearOrder α] in
theorem allPriority_rootPriority {t : Treap α} (h : HeapOrdered t) :
    AllPriority (· ≤ rootPriority t) t := by
  cases t with
  | leaf => trivial
  | node l k p r => exact h.self_le

omit [LinearOrder α] in
theorem heapOrdered_rotateRight_step {A B r : Treap α} {x k : α} {q p : ℕ}
    (hA : AllPriority (· ≤ q) A) (hB : AllPriority (· ≤ q) B)
    (hoA : HeapOrdered A) (hoB : HeapOrdered B)
    (hBp : AllPriority (· ≤ p) B) (hr : AllPriority (· ≤ p) r) (hor : HeapOrdered r)
    (hpq : p ≤ q) :
    HeapOrdered (rotateRight (node (node A x q B) k p r)) := by
  simp only [rotateRight]
  exact ⟨hA, ⟨hB, hpq, hr.imp (fun _ h => le_trans h hpq)⟩, hoA, ⟨hBp, hr, hoB, hor⟩⟩

omit [LinearOrder α] in
theorem heapOrdered_rotateLeft_step {l C D : Treap α} {k y : α} {p q : ℕ}
    (hC : AllPriority (· ≤ q) C) (hD : AllPriority (· ≤ q) D)
    (hoC : HeapOrdered C) (hoD : HeapOrdered D)
    (hCp : AllPriority (· ≤ p) C) (hl : AllPriority (· ≤ p) l) (hol : HeapOrdered l)
    (hpq : p ≤ q) :
    HeapOrdered (rotateLeft (node l k p (node C y q D))) := by
  simp only [rotateLeft]
  exact ⟨⟨hl.imp (fun _ h => le_trans h hpq), hpq, hC⟩, hD, ⟨hl, hCp, hol, hoC⟩, hoD⟩

/-- The strengthened induction `rotate-up` insertion needs. The last conjunct is the load-bearing
one: once the root priority has actually *risen*, the new root is the freshly inserted node and
everything under it came from the old tree, so it is still bounded by the old root's priority —
which is exactly what lets the parent's rotation re-establish heap order. -/
theorem insert_heap_spec (a : α) (pr : ℕ) : ∀ t : Treap α, HeapOrdered t →
    HeapOrdered (insert a pr t) ∧
    (∀ m, AllPriority (· ≤ m) t → pr ≤ m → AllPriority (· ≤ m) (insert a pr t)) ∧
    rootPriority (insert a pr t) ≤ max (rootPriority t) pr ∧
    (rootPriority t < rootPriority (insert a pr t) →
      AllPriority (· ≤ rootPriority t) (left (insert a pr t)) ∧
      AllPriority (· ≤ rootPriority t) (right (insert a pr t))) := by
  intro t
  induction t with
  | leaf =>
    intro _
    refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun m _ hm => ⟨trivial, hm, trivial⟩, ?_, ?_⟩
    · simp [insert, rootPriority_node, rootPriority_leaf]
    · intro _; exact ⟨trivial, trivial⟩
  | node l k p r ihl ihr =>
    intro ht
    obtain ⟨hpl, hpr, hol, hor⟩ := ht
    have hrl : rootPriority l ≤ p := rootPriority_le_of_allPriority hpl
    have hrr : rootPriority r ≤ p := rootPriority_le_of_allPriority hpr
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · -- descend left, then rotate the new root up
      rcases hl' : insert a pr l with _ | ⟨A, x, q, B⟩
      · rw [hl'] at h2; simp [rootPriority_leaf] at h2
      obtain ⟨hol', hmono, hrp, hsplit⟩ := ihl hol
      rw [hl'] at hol' hmono hrp hsplit h2
      have hq2 : p < q := by simpa only [rootPriority_node] using h2
      have hrq : q ≤ max (rootPriority l) pr := by simpa only [rootPriority_node] using hrp
      simp only [rootPriority_node, left_node, right_node] at hsplit
      simp only [rotateRight, rootPriority_node, left_node, right_node]
      obtain ⟨hqA, hqB, hoA, hoB⟩ := hol'
      obtain ⟨hAp, hBp⟩ := hsplit (by omega)
      have hAp' : AllPriority (· ≤ p) A := hAp.imp (fun _ h => le_trans h hrl)
      have hBp' : AllPriority (· ≤ p) B := hBp.imp (fun _ h => le_trans h hrl)
      refine ⟨⟨hqA, ⟨hqB, le_of_lt hq2, hpr.imp (fun _ h => le_trans h (le_of_lt hq2))⟩, hoA,
          ⟨hBp', hpr, hoB, hor⟩⟩, ?_, ?_, ?_⟩
      · intro m hm hprm
        have hmm := hmono m hm.1 hprm
        exact ⟨hmm.1, hmm.2.1, ⟨hmm.2.2, hm.2.1, hm.2.2⟩⟩
      · omega
      · intro _
        exact ⟨hAp', ⟨hBp', le_refl p, hpr⟩⟩
    · -- descend left, no rotation needed
      obtain ⟨hol', hmono, hrp, -⟩ := ihl hol
      have hle : rootPriority (insert a pr l) ≤ p := by omega
      refine ⟨⟨(allPriority_rootPriority hol').imp (fun _ h => le_trans h hle), hpr, hol', hor⟩,
        ?_, ?_, ?_⟩
      · intro m hm hprm; exact ⟨hmono m hm.1 hprm, hm.2.1, hm.2.2⟩
      · simp only [rootPriority_node]; omega
      · intro hc; simp only [rootPriority_node] at hc; omega
    · -- descend right, then rotate the new root up
      rcases hr' : insert a pr r with _ | ⟨C, y, q, D⟩
      · rw [hr'] at h4; simp [rootPriority_leaf] at h4
      obtain ⟨hor', hmono, hrp, hsplit⟩ := ihr hor
      rw [hr'] at hor' hmono hrp hsplit h4
      have hq4 : p < q := by simpa only [rootPriority_node] using h4
      have hrq : q ≤ max (rootPriority r) pr := by simpa only [rootPriority_node] using hrp
      simp only [rootPriority_node, left_node, right_node] at hsplit
      simp only [rotateLeft, rootPriority_node, left_node, right_node]
      obtain ⟨hqC, hqD, hoC, hoD⟩ := hor'
      obtain ⟨hCp, hDp⟩ := hsplit (by omega)
      have hCp' : AllPriority (· ≤ p) C := hCp.imp (fun _ h => le_trans h hrr)
      have hDp' : AllPriority (· ≤ p) D := hDp.imp (fun _ h => le_trans h hrr)
      refine ⟨⟨⟨hpl.imp (fun _ h => le_trans h (le_of_lt hq4)), le_of_lt hq4, hqC⟩, hqD,
          ⟨hpl, hCp', hol, hoC⟩, hoD⟩, ?_, ?_, ?_⟩
      · intro m hm hprm
        have hmm := hmono m hm.2.2 hprm
        exact ⟨⟨hm.1, hm.2.1, hmm.1⟩, hmm.2.1, hmm.2.2⟩
      · omega
      · intro _
        exact ⟨⟨hpl, le_refl p, hCp'⟩, hDp'⟩
    · -- descend right, no rotation needed
      obtain ⟨hor', hmono, hrp, -⟩ := ihr hor
      have hle : rootPriority (insert a pr r) ≤ p := by omega
      refine ⟨⟨hpl, (allPriority_rootPriority hor').imp (fun _ h => le_trans h hle), hol, hor'⟩,
        ?_, ?_, ?_⟩
      · intro m hm hprm; exact ⟨hm.1, hm.2.1, hmono m hm.2.2 hprm⟩
      · simp only [rootPriority_node]; omega
      · intro hc; simp only [rootPriority_node] at hc; omega
    · -- the key is already here: the tree is returned unchanged, as the textbooks leave it
      refine ⟨⟨hpl, hpr, hol, hor⟩, fun _ hm _ => hm, ?_, ?_⟩
      · simp only [rootPriority_node]; exact le_max_left _ _
      · intro hc; simp only [rootPriority_node] at hc; omega

theorem heapOrdered_insert {t : Treap α} (ht : HeapOrdered t) (a : α) (pr : ℕ) :
    HeapOrdered (insert a pr t) := (insert_heap_spec a pr t ht).1

/-- **`insert` produces a legal treap from a legal one.** -/
theorem valid_insert {t : Treap α} (ht : Valid t) (a : α) (pr : ℕ) : Valid (insert a pr t) :=
  ⟨sorted_insert a pr t ht.1, heapOrdered_insert ht.2 a pr⟩

/-- Descent steps along `a`'s search path before reaching a leaf, a duplicate, or a node whose
priority `pr` beats. This is not `insert`'s cost: the rotate-up `insert` walks the whole search
path. -/
def insertSteps (a : α) (pr : ℕ) : Treap α → ℕ
  | leaf => 0
  | node l k p r =>
      if pr > p then 0
      else if a < k then insertSteps a pr l + 1
      else if k < a then insertSteps a pr r + 1
      else 0

theorem priorityOf_rotateRight {t : Treap α} (ht : Sorted t) (b : α) :
    priorityOf b (rotateRight t) = priorityOf b t := by
  rcases t with _ | ⟨l, k, p, r⟩
  · rfl
  rcases l with _ | ⟨A, x, q, B⟩
  · rfl
  have hxk : x < k := ht.1.2.1
  simp only [rotateRight]
  rcases lt_trichotomy b x with hbx | rfl | hxb
  · rw [priorityOf_left hbx, priorityOf_left (lt_trans hbx hxk), priorityOf_left hbx]
  · rw [priorityOf_root, priorityOf_left hxk, priorityOf_root]
  · rw [priorityOf_right hxb]
    rcases lt_trichotomy b k with hbk | rfl | hkb
    · rw [priorityOf_left hbk, priorityOf_left hbk, priorityOf_right hxb]
    · rw [priorityOf_root, priorityOf_root]
    · rw [priorityOf_right hkb, priorityOf_right hkb]

theorem priorityOf_rotateLeft {t : Treap α} (ht : Sorted t) (b : α) :
    priorityOf b (rotateLeft t) = priorityOf b t := by
  rcases t with _ | ⟨l, k, p, r⟩
  · rfl
  rcases r with _ | ⟨C, y, q, D⟩
  · rfl
  have hky : k < y := ht.2.1.2.1
  simp only [rotateLeft]
  rcases lt_trichotomy b y with hby | rfl | hyb
  · rw [priorityOf_left hby]
    rcases lt_trichotomy b k with hbk | rfl | hkb
    · rw [priorityOf_left hbk, priorityOf_left hbk]
    · rw [priorityOf_root, priorityOf_root]
    · rw [priorityOf_right hkb, priorityOf_right hkb, priorityOf_left hby]
  · rw [priorityOf_root, priorityOf_right hky, priorityOf_root]
  · rw [priorityOf_right hyb, priorityOf_right (lt_trans hky hyb), priorityOf_right hyb]

theorem priorityOf_insert_other {a b : α} (hb : b ≠ a) (pr : ℕ) : ∀ t : Treap α, Sorted t →
    priorityOf b (insert a pr t) = priorityOf b t := by
  intro t
  induction t with
  | leaf =>
    intro _
    simp only [insert]
    rcases lt_trichotomy b a with h | h | h
    · rw [priorityOf_left h]
    · exact absurd h hb
    · rw [priorityOf_right h]
  | node l k p r ihl ihr =>
    intro ht
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · rw [priorityOf_rotateRight (t := node (insert a pr l) k p r)
        ⟨hl.insert h1 pr, hr, sorted_insert a pr l hsl, hsr⟩ b]
      rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]; exact ihl hsl
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]
    · rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]; exact ihl hsl
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]
    · rw [priorityOf_rotateLeft (t := node l k p (insert a pr r))
        ⟨hl, hr.insert h3 pr, hsl, sorted_insert a pr r hsr⟩ b]
      rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]; exact ihr hsr
    · rcases lt_trichotomy b k with hbk | rfl | hkb
      · rw [priorityOf_left hbk, priorityOf_left hbk]
      · rw [priorityOf_root, priorityOf_root]
      · rw [priorityOf_right hkb, priorityOf_right hkb]; exact ihr hsr
    · rfl

theorem priorityOf_insert_self (a : α) (pr : ℕ) : ∀ t : Treap α, Sorted t → ¬ Mem a t →
    priorityOf a (insert a pr t) = some pr := by
  intro t
  induction t with
  | leaf => intro _ _; simp only [insert]; exact priorityOf_root _ _ _ _
  | node l k p r ihl ihr =>
    intro ht hnm
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    simp only [mem_node, not_or] at hnm
    obtain ⟨hnl, hnk, hnr⟩ := hnm
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · rw [priorityOf_rotateRight (t := node (insert a pr l) k p r)
        ⟨hl.insert h1 pr, hr, sorted_insert a pr l hsl, hsr⟩ a,
        priorityOf_left h1]
      exact ihl hsl hnl
    · rw [priorityOf_left h1]; exact ihl hsl hnl
    · rw [priorityOf_rotateLeft (t := node l k p (insert a pr r))
        ⟨hl, hr.insert h3 pr, hsl, sorted_insert a pr r hsr⟩ a,
        priorityOf_right h3]
      exact ihr hsr hnr
    · rw [priorityOf_right h3]; exact ihr hsr hnr
    · exact absurd (le_antisymm (not_lt.mp h3) (not_lt.mp h1)) hnk

/-- **A key already present leaves the tree unchanged**, priority included: the new priority is
not used. -/
theorem insert_of_mem (a : α) (pr : ℕ) :
    ∀ t : Treap α, Sorted t → HeapOrdered t → Mem a t → insert a pr t = t
  | leaf, _, _, h => h.elim
  | node l k p r, ⟨hl, hr, hsl, hsr⟩, ⟨hpl, hpr, hhl, hhr⟩, hm => by
    simp only [insert]
    split_ifs with h1 h2 h3 h4
    · have hal : Mem a l := by
        rcases hm with hm | rfl | hm
        · exact hm
        · exact absurd h1 (lt_irrefl _)
        · exact absurd (hr.of_mem hm) (not_lt.2 (le_of_lt h1))
      rw [insert_of_mem a pr l hsl hhl hal] at h2
      exact absurd h2 (not_lt.2 (rootPriority_le_of_allPriority hpl))
    · have hal : Mem a l := by
        rcases hm with hm | rfl | hm
        · exact hm
        · exact absurd h1 (lt_irrefl _)
        · exact absurd (hr.of_mem hm) (not_lt.2 (le_of_lt h1))
      rw [insert_of_mem a pr l hsl hhl hal]
    · have har : Mem a r := by
        rcases hm with hm | rfl | hm
        · exact absurd (hl.of_mem hm) (not_lt.2 (le_of_lt h3))
        · exact absurd h3 (lt_irrefl _)
        · exact hm
      rw [insert_of_mem a pr r hsr hhr har] at h4
      exact absurd h4 (not_lt.2 (rootPriority_le_of_allPriority hpr))
    · have har : Mem a r := by
        rcases hm with hm | rfl | hm
        · exact absurd (hl.of_mem hm) (not_lt.2 (le_of_lt h3))
        · exact absurd h3 (lt_irrefl _)
        · exact hm
      rw [insert_of_mem a pr r hsr hhr har]
    · rfl
/-- **`insert` discharges `InsertSpec`.** Assembled from `mem_insert`, `priorityOf_insert_other`,
`insert_of_mem`, `priorityOf_insert_self` and `valid_insert`. -/
theorem insertSpec {t : Treap α} (ht : Valid t) (a : α) (pr : ℕ) :
    InsertSpec a pr t (insert a pr t) :=
  ⟨mem_insert a pr, fun b hb => hb.elim (fun hb => priorityOf_insert_other hb pr t ht.1)
     (fun ha => by rw [insert_of_mem a pr t ht.1 ht.2 ha]),
   fun hna => priorityOf_insert_self a pr t ht.1 hna, fun hv => valid_insert hv a pr⟩

end Treap

end AlgoDesign.Searching
