/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Basic

/-!
# B-tree: search

`search`, and its specification: `search_correct_valid`, `search a t = true ↔ Mem a t` on a
`Valid` tree (`search_correct` states it for any `Bounded` subtree). `valid_iff_legal` states
`Valid` through the invariants the proofs carry, `Bounded` and `KeyCountOk`. The range query
`range` is specified by `mem_range`. Its block-transfer count is `searchM`, in `Cost.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-! ## `search`

Compare against a node's keys in turn and descend into the child where `a` would sit. -/

mutual

/-- Is `a` one of the tree's keys? -/
def search (a : α) : Node α → Bool
  | leaf ks => decide (a ∈ ks)
  | node ks cs => searchChildren a ks cs

/-- Walk `ks` and `cs` together: at key `k`, `a < k` descends into the child before `k`, `k < a`
walks on, and equality is a hit; past the last key, the last child. -/
def searchChildren (a : α) : List α → List (Node α) → Bool
  | k :: ks, c :: cs => if a < k then search a c else if k < a then searchChildren a ks cs
      else true
  | [], c :: _ => search a c
  | _, [] => false

end

@[simp] theorem search_leaf (a : α) (ks : List α) : search a (leaf ks) = decide (a ∈ ks) := rfl

@[simp] theorem search_node (a : α) (ks : List α) (cs : List (Node α)) :
    search a (node ks cs) = searchChildren a ks cs := rfl

mutual

/-- **`search` is correct** on a `Bounded` tree: it finds exactly the keys that are there — the
`BTree` analogue of `BST.search_correct` (and the ordinary BST correctness implicit in `LLRB`'s
color-blind stage). Without `Bounded`, only the easy "found ⇒ present" direction survives, same
caveat as `BST.search_correct`: an unsorted tree could hide a present key off the path followed. -/
theorem search_correct {a : α} {lo hi : Option α} :
    ∀ {t : Node α}, Bounded lo hi t → (search a t = true ↔ Mem a t)
  | leaf _, _ => by simp
  | node _ _, hb => searchChildren_correct hb.1 hb.2.2

/-- Companion to `search_correct`, walking a node's keys/children in lockstep — the same shape
`boundsList`/`BoundedChildren` (and `memChildren_bounds_of_bounded`) themselves walk. -/
theorem searchChildren_correct {a : α} {lo hi : Option α} :
    ∀ {ks : List α} {cs : List (Node α)}, BoundedKeys lo hi ks →
      BoundedChildren (boundsList lo hi ks) cs → (searchChildren a ks cs = true ↔
        a ∈ ks ∨ MemChildren a cs)
  | [], cs, _, hcs => by
      simp only [boundsList] at hcs
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => simp [BoundedChildren] at hcs
        | cons c cs' => exact ⟨c, cs', rfl⟩
      obtain ⟨hc, hcs'⟩ := hcs
      have hcs'nil : cs' = [] := by
        cases cs' with
        | nil => rfl
        | cons _ _ => simp [BoundedChildren] at hcs'
      subst hcs'nil
      change search a c = true ↔ a ∈ ([] : List α) ∨ MemChildren a [c]
      rw [search_correct hc]
      simp
  | k :: ks, cs, hbk, hcs => by
      simp only [boundsList] at hcs
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => simp [BoundedChildren] at hcs
        | cons c cs' => exact ⟨c, cs', rfl⟩
      obtain ⟨hc, hcs'⟩ := hcs
      change (if a < k then search a c else if k < a then searchChildren a ks cs' else true) =
          true ↔ a ∈ k :: ks ∨ MemChildren a (c :: cs')
      split_ifs with hak hka
      · -- `a < k`: `a` can't be `k` or in `ks` (sorted, all `> k`), and can't be in any child
        -- from `cs'` either (all flanked below by `some k`) — only `c` is left to check.
        have hnks : a ∉ k :: ks := by
          rw [List.mem_cons]
          rintro (rfl | ha)
          · exact absurd hak (lt_irrefl _)
          · exact absurd ((List.pairwise_cons.mp hbk.1).1 a ha) (not_lt.mpr (le_of_lt hak))
        have hncs' : ¬ MemChildren a cs' := fun ha =>
          absurd (memChildren_bounds_of_bounded (BoundedKeys.of_cons hbk) hcs' ha).1
            (by simpa using not_lt.mpr (le_of_lt hak))
        rw [search_correct hc]
        simp [hnks, hncs']
      · -- `k < a`: `a ≠ k`, and `a` can't be in `c` (flanked above by `some k`) — recurse right.
        have hnc : ¬ Mem a c := fun ha =>
          absurd (mem_bounds_of_bounded hc ha).2 (by simpa using not_lt.mpr (le_of_lt hka))
        rw [searchChildren_correct (BoundedKeys.of_cons hbk) hcs']
        constructor
        · rintro (ha | ha)
          · exact Or.inl (List.mem_cons_of_mem k ha)
          · exact Or.inr (Or.inr ha)
        · rintro (hk | ha)
          · rw [List.mem_cons] at hk
            rcases hk with rfl | ha
            · exact absurd hka (lt_irrefl _)
            · exact Or.inl ha
          · rcases ha with ha | ha
            · exact absurd ha hnc
            · exact Or.inr ha
      · have heq : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
        subst heq
        exact ⟨fun _ => Or.inl (List.mem_cons_self ..), fun _ => rfl⟩

end

/-- Range query: the keys between two bounds, in order, specified as `BST.range` is. -/
def range (lo hi : RangeBound α) (t : Node α) : List α :=
  keysInRange lo hi (toList t)

/-- **`range` holds exactly the keys of the tree that the bounds admit.** -/
theorem mem_range {lo hi : RangeBound α} {t : Node α} {a : α} :
    a ∈ range lo hi t ↔ Mem a t ∧ InRange lo hi a := by
  simp [range, keysInRange, List.mem_filter, mem_toList]

/-- A list below `m`, then `m`, then a list above it, all inside the bounds, is inside them. -/
private theorem boundedKeys_append_cons {lo hi : Option α} {xs ys : List α} {m : α}
    (hx : BoundedKeys lo (some m) xs) (hy : BoundedKeys (some m) hi ys)
    (hlo : ∀ l ∈ lo, l < m) (hhi : ∀ h ∈ hi, m < h) :
    BoundedKeys lo hi (xs ++ m :: ys) := by
  obtain ⟨px, lx, ux⟩ := hx
  obtain ⟨py, ly, uy⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨px, ⟨fun b hb => ly m rfl b hb, py⟩, ?_⟩
    intro a ha b hb
    have ham : a < m := ux m rfl a ha
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ham
    · exact lt_trans ham (ly m rfl b hb)
  · intro l hl k hk
    rcases List.mem_append.1 hk with hk | hk
    · exact lx l hl k hk
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hlo l hl
      · exact lt_trans (hlo l hl) (ly m rfl k hk)
  · intro h hh k hk
    rcases List.mem_append.1 hk with hk | hk
    · exact lt_trans (ux m rfl k hk) (hhi h hh)
    · rcases List.mem_cons.1 hk with rfl | hk
      · exact hhi h hh
      · exact uy h hh k hk

mutual

/-- A tree's keys, read in order, lie inside the bounds it is `Bounded` by, and increase. -/
theorem boundedKeys_toList : ∀ {lo hi : Option α} (t : Node α), Bounded lo hi t →
    BoundedKeys lo hi (toList t)
  | _, _, leaf _, h => h
  | _, _, node ks cs, h => boundedKeys_childrenToList ks cs h.1 h.2.1 h.2.2

/-- The same for a node's children and keys, read child, key, child, …, child. -/
theorem boundedKeys_childrenToList : ∀ {lo hi : Option α} (ks : List α) (cs : List (Node α)),
    BoundedKeys lo hi ks → cs.length = ks.length + 1 →
    BoundedChildren (boundsList lo hi ks) cs → BoundedKeys lo hi (childrenToList ks cs)
  | _, _, [], [c], _, _, hc => by
      simpa [childrenToList] using boundedKeys_toList c hc.1
  | _, _, [], [], _, hlen, _ => by simp at hlen
  | _, _, [], _ :: _ :: _, _, hlen, _ => by simp at hlen
  | _, _, _ :: _, [], _, hlen, _ => by simp at hlen
  | lo, hi, k :: ks, c :: cs, hk, hlen, hc => by
      obtain ⟨pk, lk, uk⟩ := hk
      rw [List.pairwise_cons] at pk
      have hks : BoundedKeys (some k) hi ks :=
        ⟨pk.2, fun l hl x hx => by cases hl; exact pk.1 x hx,
          fun h hh x hx => uk h hh x (List.mem_cons_of_mem k hx)⟩
      exact boundedKeys_append_cons (boundedKeys_toList c hc.1)
        (boundedKeys_childrenToList ks cs hks (by simpa using hlen) hc.2)
        (fun l hl => lk l hl k (List.mem_cons_self ..))
        (fun h hh => uk h hh k (List.mem_cons_self ..))

end

/-- The converse of `boundedKeys_append_cons`: a list inside the bounds, split at `m`, is a list
below `m` and a list above it, with `m` itself inside the bounds. -/
private theorem BoundedKeys.split {lo hi : Option α} {xs ys : List α} {m : α}
    (h : BoundedKeys lo hi (xs ++ m :: ys)) :
    BoundedKeys lo (some m) xs ∧ BoundedKeys (some m) hi ys ∧ (∀ l ∈ lo, l < m) ∧
      (∀ h ∈ hi, m < h) := by
  obtain ⟨p, l, u⟩ := h
  rw [List.pairwise_append, List.pairwise_cons] at p
  obtain ⟨px, ⟨pm, py⟩, pxy⟩ := p
  refine ⟨⟨px, fun a ha k hk => l a ha k (by simp [hk]), fun b hb k hk => ?_⟩,
    ⟨py, fun b hb k hk => ?_, fun b hb k hk => u b hb k (by simp [hk])⟩,
    fun a ha => l a ha m (by simp), fun b hb => u b hb m (by simp)⟩
  · cases hb
    exact pxy k hk m (List.mem_cons_self ..)
  · cases hb
    exact pm k hk

mutual

/-- A tree with one more child than keys at every node, whose keys read in order increase and lie
inside `lo` and `hi`, is `Bounded lo hi`. -/
theorem bounded_of_toList : ∀ {lo hi : Option α} (t : Node α), OneMoreChild t →
    BoundedKeys lo hi (toList t) → Bounded lo hi t
  | _, _, leaf _, _, h => h
  | _, _, node ks cs, ho, h =>
      have hkc := bounded_of_childrenToList ks cs ho.1 ho.2 h
      ⟨hkc.1, ho.1, hkc.2⟩

/-- The same for a node's keys and children, read child, key, child, …, child. -/
theorem bounded_of_childrenToList : ∀ {lo hi : Option α} (ks : List α) (cs : List (Node α)),
    cs.length = ks.length + 1 → ChildrenOneMoreChild cs →
    BoundedKeys lo hi (childrenToList ks cs) →
    BoundedKeys lo hi ks ∧ BoundedChildren (boundsList lo hi ks) cs
  | _, _, [], [c], _, ho, h =>
      ⟨⟨List.Pairwise.nil, by simp, by simp⟩,
        bounded_of_toList c ho.1 (by simpa [childrenToList] using h), trivial⟩
  | _, _, [], [], hlen, _, _ => by simp at hlen
  | _, _, [], _ :: _ :: _, hlen, _, _ => by simp at hlen
  | _, _, _ :: _, [], hlen, _, _ => by simp at hlen
  | lo, hi, k :: ks, c :: cs, hlen, ho, h => by
      have h' : BoundedKeys lo hi (toList c ++ k :: childrenToList ks cs) := h
      obtain ⟨hx, hy, hlo, hhi⟩ := BoundedKeys.split h'
      obtain ⟨⟨pk, lk, uk⟩, hcs⟩ :=
        bounded_of_childrenToList ks cs (by simpa using hlen) ho.2 hy
      refine ⟨⟨List.pairwise_cons.2 ⟨fun x hx => lk k rfl x hx, pk⟩, ?_, ?_⟩,
        bounded_of_toList c ho.1 hx, hcs⟩
      · intro l hl x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hlo l hl
        · exact lt_trans (hlo l hl) (lk k rfl x hx)
      · intro b hb x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hhi b hb
        · exact uk b hb x hx

end

section

omit [LinearOrder α]

mutual

/-- Off the root, `KeyCountOk` and `NodeHalfFull` say the same. -/
theorem keyCountOk_false_iff_halfFull {deg : ℕ} :
    ∀ t : Node α, KeyCountOk deg false t ↔ NodeHalfFull deg t
  | leaf _ => by simp [KeyCountOk, NodeHalfFull]
  | node _ cs => by
      simp only [KeyCountOk, NodeHalfFull, childrenKeyCountOk_iff_halfFull cs]
      simp

/-- The list companion to `keyCountOk_false_iff_halfFull`. -/
theorem childrenKeyCountOk_iff_halfFull {deg : ℕ} :
    ∀ cs : List (Node α), ChildrenKeyCountOk deg cs ↔ ChildrenHalfFull deg cs
  | [] => Iff.rfl
  | c :: cs => and_congr (keyCountOk_false_iff_halfFull c) (childrenKeyCountOk_iff_halfFull cs)

end

/-- `ChildrenHalfFull` is `NodeHalfFull` on every member of the list. -/
theorem childrenHalfFull_iff {deg : ℕ} :
    ∀ cs : List (Node α), ChildrenHalfFull deg cs ↔ ∀ c ∈ cs, NodeHalfFull deg c
  | [] => by simp [ChildrenHalfFull]
  | c :: cs => by simp [ChildrenHalfFull, childrenHalfFull_iff cs]

end

omit [LinearOrder α] in
/-- At the root, with one more child than keys, `KeyCountOk` is `HalfFullToFull` and
`RootBranches`. -/
theorem keyCountOk_true_iff_halfFull {deg : ℕ} {bt : Node α} (ho : OneMoreChild bt) :
    KeyCountOk deg true bt ↔ HalfFullToFull deg bt ∧ RootBranches bt := by
  cases bt with
  | leaf ks => simp [KeyCountOk, HalfFullToFull, nodeKeys, children, RootBranches]
  | node ks cs =>
      have hlen := ho.1
      simp only [KeyCountOk, HalfFullToFull, nodeKeys, children, RootBranches,
        childrenKeyCountOk_iff_halfFull cs, childrenHalfFull_iff cs, ite_true]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h2, h3⟩, by omega⟩
      · rintro ⟨⟨h2, h3⟩, h1⟩
        exact ⟨by omega, h2, h3⟩

/-- A root legal at minimum degree `deg`, in the form the proofs carry: `Bounded` with no outer
bounds, `SameDepth`, `KeyCountOk` at the root, and `2 ≤ deg`. A tree is `Valid` exactly when its
root is legal at its degree (`BTree.valid_iff_legal`). -/
def RootLegal (deg : ℕ) (bt : Node α) : Prop :=
  Bounded none none bt ∧ SameDepth bt ∧ KeyCountOk deg true bt ∧ 2 ≤ deg

/-- **`search` is correct on a legal root**: the form of `search_correct` for the whole tree,
which is `Bounded none none`. -/
theorem search_correct_valid {deg : ℕ} {bt : Node α} (h : RootLegal deg bt) (a : α) :
    search a bt = true ↔ Mem a bt := search_correct h.1

/-- Bounding neither end asks for the whole tree. -/
@[simp] theorem range_unbounded (t : Node α) :
    range .unbounded .unbounded t = toList t := by
  simp [range, keysInRange, inRange, InRange, RangeBound.Lower, RangeBound.Upper]

end BTree.Node

namespace BTree

variable {α : Type} [LinearOrder α]

/-- Is `a` one of the tree's keys? -/
def search (a : α) (t : BTree α) : Bool := t.root.search a

/-- Range query: the keys between two bounds, in order, specified as `BST.range` is. -/
def range (lo hi : RangeBound α) (t : BTree α) : List α := t.root.range lo hi

/-- **`Valid` through the induction invariants**: the box's five pieces hold exactly when the root
is `Bounded` with no outer bounds, `SameDepth`, and `KeyCountOk` at the tree's degree. -/
theorem valid_iff_legal {t : BTree α} : Valid t ↔ Node.RootLegal t.deg t.root := by
  obtain ⟨deg, hdeg, bt⟩ := t
  constructor
  · rintro ⟨hk, ho, hh, hr, hs⟩
    exact ⟨Node.bounded_of_toList bt ho ⟨hk, by simp, by simp⟩, hs,
      (Node.keyCountOk_true_iff_halfFull ho).2 ⟨hh, hr⟩, hdeg⟩
  · rintro ⟨hb, hs, hc, -⟩
    have ho := hb.arity
    have hhr := (Node.keyCountOk_true_iff_halfFull (deg := deg) ho).1 hc
    exact ⟨(Node.boundedKeys_toList bt hb).1, ho, hhr.1, hhr.2, hs⟩

/-- **`search` is correct on any `Valid` tree.** -/
theorem search_correct_valid {t : BTree α} (h : Valid t) (a : α) :
    search a t = true ↔ Mem a t := Node.search_correct_valid (valid_iff_legal.1 h) a

/-- **The keys come out in increasing order**, the search tree's promise: a legal tree's `toList`
is strictly increasing, box invariant 1. -/
theorem sorted_toList {t : BTree α} (hv : Valid t) : (toList t).Pairwise (· < ·) :=
  hv.1

/-- Bounding neither end asks for the whole tree. -/
@[simp] theorem range_unbounded (t : BTree α) :
    range .unbounded .unbounded t = toList t := Node.range_unbounded t.root

end BTree

end AlgoDesign.Searching
