/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Balance

/-!
# B-tree: insertion

CLRS §18.2's proactive split, and `insertSpec`: on a `Valid` tree, `insert` discharges
`InsertSpec` (`insertMem` for the key set, `insertValid` for the rest). The file ends with
`insertM`, its block-transfer count.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## What `insert` must do -/

/-- `insert a` adds exactly `a` to the key set. -/
def InsertMem (a : α) (before after : BTree α) : Prop :=
  ∀ b, Mem b after ↔ (b = a ∨ Mem b before)

/-- `insert` keeps a legal tree legal, at the same minimum degree. -/
def InsertValid (deg : ℕ) (before after : BTree α) : Prop :=
  Valid deg before → Valid deg after

/-- The `insert` obligation: `InsertMem` and `InsertValid`. The per-operation form the
proofs discharge; `BTree.promise` is proved from it. -/
def InsertSpec (deg : ℕ) (a : α) (before after : BTree α) : Prop :=
  InsertMem a before after ∧ InsertValid deg before after

/-! ## Sorted key lists -/

/-- Insert into a sorted, duplicate-free key list; a key already there is a no-op. -/
def insKeys (a : α) : List α → List α
  | [] => [a]
  | k :: ks => if a < k then a :: k :: ks else if k < a then k :: insKeys a ks else k :: ks

@[simp] theorem mem_insKeys (a b : α) : ∀ ks : List α, b ∈ insKeys a ks ↔ (b = a ∨ b ∈ ks)
  | [] => by simp [insKeys]
  | k :: ks => by
      simp only [insKeys]
      split_ifs with h₁ h₂
      · simp
      · simp only [List.mem_cons, mem_insKeys a b ks]
        tauto
      · have hak : a = k := le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)
        simp only [List.mem_cons]
        exact ⟨fun h => Or.inr h, fun h => h.elim (fun hb => Or.inl (hb.trans hak)) id⟩

theorem length_insKeys (a : α) : ∀ ks : List α,
    (insKeys a ks).length = ks.length ∨ (insKeys a ks).length = ks.length + 1
  | [] => by simp [insKeys]
  | k :: ks => by
      simp only [insKeys]
      split_ifs with h₁ h₂
      · simp
      · rcases length_insKeys a ks with h | h <;> simp [h]
      · simp

theorem le_length_insKeys (a : α) (ks : List α) : ks.length ≤ (insKeys a ks).length := by
  rcases length_insKeys a ks with h | h <;> omega

/-- `insKeys` respects a node's flanking bounds, provided the new key does. -/
theorem boundedKeys_insKeys {lo hi : Option α} {a : α} (hlo : ∀ l ∈ lo, l < a)
    (hhi : ∀ h ∈ hi, a < h) :
    ∀ {ks : List α}, BoundedKeys lo hi ks → BoundedKeys lo hi (insKeys a ks)
  | [], _ => by
      simp only [insKeys]
      exact ⟨by simp, by simpa using hlo, by simpa using hhi⟩
  | k :: ks, h => by
      simp only [insKeys]
      split_ifs with h₁ h₂
      · refine ⟨?_, ?_, ?_⟩
        · refine List.pairwise_cons.mpr ⟨?_, h.1⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact h₁
          · exact lt_trans h₁ ((List.pairwise_cons.mp h.1).1 b hb)
        · intro l hl b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hlo l hl
          · exact h.2.1 l hl b hb
        · intro hh hhh b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hhi hh hhh
          · exact h.2.2 hh hhh b hb
      · have hklo : ∀ l ∈ (some k : Option α), l < a := by
          intro l hl; cases hl; exact h₂
        have ih := boundedKeys_insKeys hklo hhi (BoundedKeys.of_cons h)
        refine ⟨?_, ?_, ?_⟩
        · refine List.pairwise_cons.mpr ⟨?_, ih.1⟩
          intro b hb
          exact ih.2.1 k rfl b hb
        · intro l hl b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact h.2.1 l hl b (List.mem_cons_self ..)
          · exact lt_trans (h.2.1 l hl k (List.mem_cons_self ..)) (ih.2.1 k rfl b hb)
        · intro hh hhh b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact h.2.2 hh hhh b (List.mem_cons_self ..)
          · exact ih.2.2 hh hhh b hb
      · exact h

/-- The median of an over-full, sorted key list separates the two halves it leaves behind. -/
theorem splitKeys_bounded {lo hi : Option α} {ks : List α} {m : α} {rest : List α}
    (h : BoundedKeys lo hi ks) (hsplit : ks.take (deg - 1) ++ m :: rest = ks) :
    BoundedKeys lo (some m) (ks.take (deg - 1)) ∧ (∀ l ∈ lo, l < m) ∧ (∀ hh ∈ hi, m < hh) ∧
      BoundedKeys (some m) hi rest := by
  obtain ⟨hp, hlo, hhi⟩ := h
  rw [← hsplit] at hp
  rw [List.pairwise_append] at hp
  obtain ⟨p1, p2, p3⟩ := hp
  have hmem : ∀ x ∈ ks.take (deg - 1), x ∈ ks := fun x hx => hsplit ▸ List.mem_append_left _ hx
  have hmemr : ∀ x ∈ rest, x ∈ ks := fun x hx =>
    hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  have hmm : m ∈ ks := hsplit ▸ List.mem_append_right _ (List.mem_cons_self ..)
  refine ⟨⟨p1, fun l hl x hx => hlo l hl x (hmem x hx),
      fun hh hhh x hx => ?_⟩, fun l hl => hlo l hl m hmm, fun hh hhh => hhi hh hhh m hmm,
    ⟨(List.pairwise_cons.mp p2).2, fun l hl x hx => ?_,
      fun hh hhh x hx => hhi hh hhh x (hmemr x hx)⟩⟩
  · cases hhh
    exact p3 x hx m (List.mem_cons_self ..)
  · cases hl
    exact (List.pairwise_cons.mp p2).1 x hx

/-! ## `insert`: CLRS §18.2's proactive split

Before descending into a child, split it if it is full, so the leaf at the bottom has room and no
fix-up pass goes back up: every node is read once and written at most once. -/

/-- Is this node already at the `2 * deg - 1` ceiling, so that descending into it without
splitting first could overflow it? -/
def isFull (deg : ℕ) (t : BTree α) : Bool := (nodeKeys t).length == 2 * deg - 1

/-- CLRS's `SPLIT-CHILD`, as a pure function: cut a full node at its median, giving the left
half, the median itself, and the right half. `none` only if the node has too few keys to have a
median at position `deg - 1`, which a full node never does. -/
def splitNode (deg : ℕ) : BTree α → Option (BTree α × α × BTree α)
  | leaf ks => match ks.drop (deg - 1) with
      | [] => none
      | m :: rest => some (leaf (ks.take (deg - 1)), m, leaf rest)
  | node ks cs => match ks.drop (deg - 1) with
      | [] => none
      | m :: rest => some (node (ks.take (deg - 1)) (cs.take deg), m, node rest (cs.drop deg))

/-- Where the descent goes next, with CLRS's proactive split already applied: the node's new key
list, the children to the left of the one we descend into, that child, and the children to its
right. Keeping it index-free is what lets the split be a local rearrangement (`m :: k :: ks`,
`l :: r :: cs`) instead of list surgery at a computed position. -/
structure Descent (α : Type) where
  /-- The node's key list, after the split. -/
  keys : List α
  /-- The children left of the one the descent enters. -/
  before : List (BTree α)
  /-- The child the descent enters. -/
  target : BTree α
  /-- The children right of it. -/
  after : List (BTree α)

/-- CLRS's key-scan plus the proactive split, with no recursion into any subtree: walk this
node's keys until `a`'s slot is found, split that child if it is full, and say which half to
descend into. `none` means "nothing to do here" — either `a` is already one of the keys at this
level (including a just-promoted median), or the node is malformed. -/
def prepare (deg : ℕ) (a : α) : List α → List (BTree α) → Option (Descent α)
  | k :: ks, c :: cs =>
      if a < k then
        if isFull deg c then
          match splitNode deg c with
          | none => none
          | some (l, m, r) =>
              if a < m then some ⟨m :: k :: ks, [], l, r :: cs⟩
              else if m < a then some ⟨m :: k :: ks, [l], r, cs⟩
              else none
        else some ⟨k :: ks, [], c, cs⟩
      else if k < a then
        match prepare deg a ks cs with
        | none => none
        | some d => some ⟨k :: d.keys, c :: d.before, d.target, d.after⟩
      else none
  | [], c :: cs =>
      if isFull deg c then
        match splitNode deg c with
        | none => none
        | some (l, m, r) =>
            if a < m then some ⟨[m], [], l, r :: cs⟩
            else if m < a then some ⟨[m], [l], r, cs⟩
            else none
      else some ⟨[], [], c, cs⟩
  | _, [] => none

/-! ## Why the descent terminates

The recursion is not structural: a split child is a freshly built node, not a subterm of anything.
What does decrease is height — a half of a child is no taller than the child, and a child is
shorter than its parent. -/

omit [LinearOrder α] in
theorem childrenHeight_take_le (cs : List (BTree α)) (n : ℕ) :
    childrenHeight (cs.take n) ≤ childrenHeight cs :=
  childrenHeight_le_of_mem_imp (fun _ hc => List.mem_of_mem_take hc)

omit [LinearOrder α] in
theorem childrenHeight_drop_le (cs : List (BTree α)) (n : ℕ) :
    childrenHeight (cs.drop n) ≤ childrenHeight cs :=
  childrenHeight_le_of_mem_imp (fun _ hc => List.mem_of_mem_drop hc)

omit [LinearOrder α] in
/-- Neither half of a split is taller than what it came from. -/
theorem splitNode_height_le {deg : ℕ} {t l r : BTree α} {m : α}
    (h : splitNode deg t = some (l, m, r)) : l.height ≤ t.height ∧ r.height ≤ t.height := by
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, -, hr⟩ := h
          subst hl; subst hr
          simp
  | node ks cs =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, -, hr⟩ := h
          subst hl; subst hr
          exact ⟨by simpa using childrenHeight_take_le cs deg,
                 by simpa using childrenHeight_drop_le cs deg⟩

/-- Whatever `prepare` picks to descend into is no taller than the children it came from. -/
theorem prepare_target_height {deg : ℕ} {a : α} :
    ∀ {ks : List α} {cs : List (BTree α)} {d : Descent α}, prepare deg a ks cs = some d →
      d.target.height ≤ childrenHeight cs
  | k :: ks, c :: cs, d, h => by
      simp only [prepare] at h
      split_ifs at h with h₁ h₂ h₃
      · -- a < k, child full: the target is a half of `c`
        cases hs : splitNode deg c with
        | none => rw [hs] at h; exact absurd h (by simp)
        | some p =>
            obtain ⟨l, m, r⟩ := p
            rw [hs] at h
            dsimp only at h
            obtain ⟨hlh, hrh⟩ := splitNode_height_le hs
            have hc : c.height ≤ childrenHeight (c :: cs) :=
              height_le_childrenHeight_of_mem (by simp)
            split_ifs at h with h₅ h₆ <;>
              simp only [Option.some.injEq] at h <;> subst h <;> simp <;> omega
      · -- a < k, child not full: the target is `c`
        simp only [Option.some.injEq] at h
        subst h
        exact height_le_childrenHeight_of_mem (by simp)
      · -- k < a: walk right, and the tail's children are no taller
        cases hp : prepare deg a ks cs with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some d' =>
            rw [hp] at h
            dsimp only at h
            simp only [Option.some.injEq] at h
            subst h
            exact le_trans (prepare_target_height (d := d') hp) (childrenHeight_le_cons c cs)
  | [], c :: cs, d, h => by
      simp only [prepare] at h
      split_ifs at h with h₁
      · cases hs : splitNode deg c with
        | none => rw [hs] at h; exact absurd h (by simp)
        | some p =>
            obtain ⟨l, m, r⟩ := p
            rw [hs] at h
            dsimp only at h
            obtain ⟨hlh, hrh⟩ := splitNode_height_le hs
            have hc : c.height ≤ childrenHeight (c :: cs) :=
              height_le_childrenHeight_of_mem (by simp)
            split_ifs at h with h₅ h₆ <;>
              simp only [Option.some.injEq] at h <;> subst h <;> simp <;> omega
      · simp only [Option.some.injEq] at h
        subst h
        exact height_le_childrenHeight_of_mem (by simp)
  | _, [], _, h => by simp [prepare] at h

/-! ## The descent itself -/

/-- CLRS's `B-TREE-INSERT-NONFULL`: the node is known to have room, so the descent can split the
child it is about to enter and never look back. A leaf at the bottom is guaranteed to have space,
which is the whole point of having split on the way down. -/
def insNonfull (deg : ℕ) (a : α) : BTree α → BTree α
  | leaf ks => leaf (insKeys a ks)
  | node ks cs =>
      match _hprep : prepare deg a ks cs with
      | none => node ks cs
      | some d => node d.keys (d.before ++ insNonfull deg a d.target :: d.after)
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height _hprep
    simp only [height_node]
    omega

/-- Insert into a B-tree, CLRS §18.2: one descent, a full root split first into a new root
holding the median. A duplicate is caught by the descent's key scan, after splitting any full
nodes above it, so the shape may change though the key set does not. -/
def insert (deg : ℕ) (a : α) (t : BTree α) : BTree α :=
  if isFull deg t then
    match splitNode deg t with
    | none => insNonfull deg a t
    | some (l, m, r) => insNonfull deg a (node [m] [l, r])
  else insNonfull deg a t

omit [LinearOrder α] in
theorem isFull_iff {deg : ℕ} {t : BTree α} :
    isFull deg t = true ↔ (nodeKeys t).length = 2 * deg - 1 := by
  simp [isFull]

omit [LinearOrder α] in
@[simp] theorem nodeKeys_leaf (ks : List α) : nodeKeys (leaf ks) = ks := rfl

omit [LinearOrder α] in
@[simp] theorem nodeKeys_node (ks : List α) (cs : List (BTree α)) :
    nodeKeys (node ks cs) = ks := rfl

omit [LinearOrder α] in
/-- A full node always has a median to promote: `2 * deg - 1` keys is more than `deg - 1`. -/
theorem splitNode_isSome {deg : ℕ} (hdeg : 2 ≤ deg) {t : BTree α} (hf : isFull deg t = true) :
    (splitNode deg t).isSome := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  have hdrop : (nodeKeys t).drop (deg - 1) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_drop, List.length_nil] at this
    omega
  cases t with
  | leaf ks =>
      simp only [nodeKeys_leaf] at hdrop hlen
      cases hd : ks.drop (deg - 1) with
      | nil => exact absurd hd hdrop
      | cons m rest => simp [splitNode, hd]
  | node ks cs =>
      simp only [nodeKeys_node] at hdrop hlen
      cases hd : ks.drop (deg - 1) with
      | nil => exact absurd hd hdrop
      | cons m rest => simp [splitNode, hd]

omit [LinearOrder α] in
/-- The three pieces of a split, spelled out: the key list divides as `left ++ median :: right`,
and on an internal node the children divide at `deg`. -/
theorem splitNode_parts {deg : ℕ} {t l r : BTree α} {m : α}
    (h : splitNode deg t = some (l, m, r)) :
    nodeKeys l = (nodeKeys t).take (deg - 1) ∧
    (nodeKeys t).drop (deg - 1) = m :: nodeKeys r ∧
    (nodeKeys l ++ m :: nodeKeys r = nodeKeys t) := by
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          refine ⟨rfl, by simpa using hd, ?_⟩
          simp only [nodeKeys_leaf]
          rw [← hd, List.take_append_drop]
  | node ks cs =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          refine ⟨rfl, by simpa using hd, ?_⟩
          simp only [nodeKeys_node]
          rw [← hd, List.take_append_drop]

/-- Splitting neither loses nor invents a key. -/
theorem splitNode_mem {deg : ℕ} {t l r : BTree α} {m : α}
    (h : splitNode deg t = some (l, m, r)) (b : α) :
    (Mem b l ∨ b = m ∨ Mem b r) ↔ Mem b t := by
  obtain ⟨-, -, hcat⟩ := splitNode_parts h
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          simp only [nodeKeys_leaf] at hcat
          have hkeys : b ∈ ks ↔ (b ∈ ks.take (deg - 1) ∨ b = m' ∨ b ∈ rest) := by
            conv_lhs => rw [← hcat]
            simp
          simpa only [mem_leaf] using hkeys.symm
  | node ks cs =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          have hcs : cs.take deg ++ cs.drop deg = cs := List.take_append_drop _ _
          simp only [nodeKeys_node] at hcat
          have hkeys : b ∈ ks ↔ (b ∈ ks.take (deg - 1) ∨ b = m' ∨ b ∈ rest) := by
            conv_lhs => rw [← hcat]
            simp
          have hch : MemChildren b cs ↔
              (MemChildren b (cs.take deg) ∨ MemChildren b (cs.drop deg)) := by
            conv_lhs => rw [← hcs]
            exact memChildren_append b _ _
          simp only [mem_node, hkeys, hch]
          tauto

/-- The median a split promotes was a key of the node it came from. -/
theorem splitNode_mem_median {deg : ℕ} {t l r : BTree α} {m : α}
    (h : splitNode deg t = some (l, m, r)) : Mem m t :=
  (splitNode_mem h m).mp (Or.inr (Or.inl rfl))

omit [LinearOrder α] in
/-- A full node's key list has exactly `2 * deg - 1` entries, so both halves of its split have
exactly `deg - 1` — CLRS's `t - 1` on each side — and neither is full. -/
theorem splitNode_lengths {deg : ℕ} (hdeg : 2 ≤ deg) {t l r : BTree α} {m : α}
    (hf : isFull deg t = true) (h : splitNode deg t = some (l, m, r)) :
    (nodeKeys l).length = deg - 1 ∧ (nodeKeys r).length = deg - 1 := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  obtain ⟨hl, hdrop, -⟩ := splitNode_parts h
  have hdl : ((nodeKeys t).drop (deg - 1)).length = (nodeKeys t).length - (deg - 1) := by simp
  rw [hdrop] at hdl
  simp only [List.length_cons] at hdl
  refine ⟨?_, by omega⟩
  rw [hl]
  simp only [List.length_take]
  omega

omit [LinearOrder α] in
theorem splitNode_not_full {deg : ℕ} (hdeg : 2 ≤ deg) {t l r : BTree α} {m : α}
    (hf : isFull deg t = true) (h : splitNode deg t = some (l, m, r)) :
    isFull deg l = false ∧ isFull deg r = false := by
  obtain ⟨h1, h2⟩ := splitNode_lengths hdeg hf h
  constructor <;> simp only [isFull, beq_eq_false_iff_ne, ne_eq] <;> omega

/-- Ordering survives a split: the median becomes the wall between the two halves. -/
theorem splitNode_bounded {deg : ℕ} (hdeg : 2 ≤ deg) {lo hi : Option α} {t l r : BTree α} {m : α}
    (hb : Bounded lo hi t) (hf : isFull deg t = true) (h : splitNode deg t = some (l, m, r)) :
    Bounded lo (some m) l ∧ (∀ x ∈ lo, x < m) ∧ (∀ x ∈ hi, m < x) ∧ Bounded (some m) hi r := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          have hsplit : ks.take (deg - 1) ++ m' :: rest = ks := by
            rw [← hd, List.take_append_drop]
          obtain ⟨b1, b2, b3, b4⟩ := splitKeys_bounded (deg := deg) hb hsplit
          exact ⟨b1, b2, b3, b4⟩
  | node ks cs =>
      obtain ⟨hk, harity, hbc⟩ := hb
      simp only [nodeKeys_node] at hlen
      simp only [splitNode] at h
      cases hd : ks.drop (deg - 1) with
      | nil => rw [hd] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hd] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          have hsplit : ks.take (deg - 1) ++ m' :: rest = ks := by
            rw [← hd, List.take_append_drop]
          have hrest : rest.length + 1 = ks.length - (deg - 1) := by
            have := congrArg List.length hd
            simpa using this.symm
          obtain ⟨b1, b2, b3, b4⟩ := splitKeys_bounded (deg := deg) hk hsplit
          have hbc' : BoundedChildren
              (boundsList lo (some m') (ks.take (deg - 1)) ++ boundsList (some m') hi rest) cs := by
            rw [← boundsList_append, hsplit]; exact hbc
          rw [← List.take_append_drop deg cs] at hbc'
          have hlenmatch : (boundsList lo (some m') (ks.take (deg - 1))).length =
              (cs.take deg).length := by
            rw [boundsList_length]
            simp only [List.length_take]
            omega
          obtain ⟨c1, c2⟩ := (boundedChildren_append hlenmatch).mp hbc'
          refine ⟨⟨b1, ?_, c1⟩, b2, b3, ⟨b4, ?_, c2⟩⟩ <;>
            simp only [List.length_take, List.length_drop] <;> omega

omit [LinearOrder α] in
/-- Balance survives a split: both halves keep every leaf at the depth the original had. -/
theorem splitNode_depth {deg : ℕ} (hdeg : 2 ≤ deg) {t l r : BTree α} {m : α} {d : ℕ}
    (harity : OneMoreChild t) (hd : depth? t = some d) (hf : isFull deg t = true)
    (h : splitNode deg t = some (l, m, r)) :
    depth? l = some d ∧ depth? r = some d := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hdr : ks.drop (deg - 1) with
      | nil => rw [hdr] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hdr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          have : d = 0 := by simpa [depth?] using hd.symm
          subst this
          exact ⟨rfl, rfl⟩
  | node ks cs =>
      simp only [nodeKeys_node] at hlen
      obtain ⟨hlenc, -⟩ := harity
      simp only [splitNode] at h
      cases hdr : ks.drop (deg - 1) with
      | nil => rw [hdr] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hdr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          obtain ⟨d', hd', rfl⟩ : ∃ d', childrenDepth? cs = some d' ∧ d = d' + 1 := by
            simp only [depth?, Option.map_eq_some_iff] at hd
            obtain ⟨d', h₁, h₂⟩ := hd
            exact ⟨d', h₁, h₂.symm⟩
          have hcsne : cs ≠ [] := by
            intro hnil; rw [hnil] at hlenc; simp at hlenc
          have htake : childrenDepth? (cs.take deg) = some d' :=
            childrenDepth?_take hd' (by omega) hcsne
          have hdrop : childrenDepth? (cs.drop deg) = some d' :=
            childrenDepth?_drop hd' (by omega)
          exact ⟨by simp [depth?, htake], by simp [depth?, hdrop]⟩

omit [LinearOrder α] in
/-- Occupancy survives a split, and neither half is full. -/
theorem splitNode_keyCount {deg : ℕ} (hdeg : 2 ≤ deg) {t l r : BTree α} {m : α}
    (harity : OneMoreChild t) (hk : KeyCountOk deg false t) (hf : isFull deg t = true)
    (h : splitNode deg t = some (l, m, r)) :
    KeyCountOk deg false l ∧ KeyCountOk deg false r ∧ OneMoreChild l ∧ OneMoreChild r := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  obtain ⟨hll, hrl⟩ := splitNode_lengths hdeg hf h
  cases t with
  | leaf ks =>
      simp only [splitNode] at h
      cases hdr : ks.drop (deg - 1) with
      | nil => rw [hdr] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hdr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          simp only [nodeKeys_leaf] at hll hrl
          exact ⟨⟨Or.inr (by omega), by omega⟩, ⟨Or.inr (by omega), by omega⟩, trivial, trivial⟩
  | node ks cs =>
      simp only [nodeKeys_node] at hlen
      obtain ⟨hlenc, harc⟩ := harity
      obtain ⟨-, -, hck⟩ := hk
      simp only [splitNode] at h
      cases hdr : ks.drop (deg - 1) with
      | nil => rw [hdr] at h; exact absurd h (by simp)
      | cons m' rest =>
          rw [hdr] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hm, hr⟩ := h
          subst hl; subst hm; subst hr
          simp only [nodeKeys_node] at hll hrl
          refine ⟨⟨?_, by omega, childrenKeyCountOk_take hck _⟩,
                  ⟨?_, by omega, childrenKeyCountOk_drop hck _⟩,
                  ⟨?_, arityChildren_take harc _⟩, ⟨?_, arityChildren_drop harc _⟩⟩ <;>
            simp only [List.length_take, List.length_drop, Bool.false_eq_true, ite_false] <;>
            omega

omit [LinearOrder α] in
theorem childrenDepth?_tail {c : BTree α} {cs : List (BTree α)} {dep : ℕ}
    (h : childrenDepth? (c :: cs) = some dep) (hne : cs ≠ []) : childrenDepth? cs = some dep :=
  childrenDepth?_of_forall hne (fun x hx => childrenDepth?_uniform h (by simp [hx]))

omit [LinearOrder α] in
theorem childrenDepth?_cons2 {x y : BTree α} {cs : List (BTree α)} {d : ℕ}
    (hx : depth? x = some d) (hy : depth? y = some d)
    (hcs : ∀ z ∈ cs, depth? z = some d) : childrenDepth? (x :: y :: cs) = some d :=
  childrenDepth?_of_forall (by simp) (by
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · exact hx
    · exact hy
    · exact hcs z hz)

omit [LinearOrder α] in
theorem childrenDepth?_cons1 {x : BTree α} {cs : List (BTree α)} {d : ℕ}
    (hx : depth? x = some d) (hcs : ∀ z ∈ cs, depth? z = some d) :
    childrenDepth? (x :: cs) = some d :=
  childrenDepth?_of_forall (by simp) (by
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact hcs z hz)

set_option maxHeartbeats 800000 in
-- One induction for ordering, balance, occupancy and membership: `prepare`'s split couples them.
/-- What `prepare` guarantees: a subtree that is legal where it sits, not full, with `a` strictly
between its flanking keys, and a context that turns any legal replacement for it back into a legal
node, the key set changed by exactly `a`. Stated over key and child lists, since the recursion
walks a suffix of a node. -/
theorem prepare_spec (deg : ℕ) (hdeg : 2 ≤ deg) (a : α) :
    ∀ {lo hi : Option α} {dep : ℕ} {ks : List α} {cs : List (BTree α)} {D : Descent α},
      BoundedKeys lo hi ks → BoundedChildren (boundsList lo hi ks) cs →
      cs.length = ks.length + 1 → childrenDepth? cs = some dep → ChildrenKeyCountOk deg cs →
      (∀ l ∈ lo, l < a) → (∀ h ∈ hi, a < h) →
      prepare deg a ks cs = some D →
      ∃ lo' hi',
        Legal deg lo' hi' dep D.target ∧ isFull deg D.target = false ∧
        (∀ l ∈ lo', l < a) ∧ (∀ h ∈ hi', a < h) ∧
        (D.keys.length = ks.length ∨ D.keys.length = ks.length + 1) ∧
        ∀ x : BTree α, Legal deg lo' hi' dep x →
          (∀ b, Mem b x ↔ (b = a ∨ Mem b D.target)) →
          BoundedKeys lo hi D.keys ∧
          BoundedChildren (boundsList lo hi D.keys) (D.before ++ x :: D.after) ∧
          (D.before ++ x :: D.after).length = D.keys.length + 1 ∧
          childrenDepth? (D.before ++ x :: D.after) = some dep ∧
          ChildrenKeyCountOk deg (D.before ++ x :: D.after) ∧
          (∀ b, (b ∈ D.keys ∨ MemChildren b (D.before ++ x :: D.after)) ↔
                (b = a ∨ (b ∈ ks ∨ MemChildren b cs))) := by
  intro lo hi dep ks
  induction ks generalizing lo with
  | nil =>
      intro cs D hk hbc hlen hdep hck hlo hhi hp
      -- exactly one child
      obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
        cases cs with
        | nil => simp at hlen
        | cons c cs' =>
            cases cs' with
            | nil => exact ⟨c, rfl⟩
            | cons _ _ => simp at hlen
      simp only [boundsList, BoundedChildren] at hbc
      obtain ⟨hbcc, -⟩ := hbc
      have hdc : depth? c = some dep := childrenDepth?_uniform hdep (by simp)
      have hkc : KeyCountOk deg false c := hck.1
      simp only [prepare] at hp
      split_ifs at hp with hfull
      · -- the child is full: split it, then pick the half `a` belongs in
        obtain ⟨p, hs⟩ : ∃ p, splitNode deg c = some p :=
          Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
        obtain ⟨l, m, r⟩ := p
        rw [hs] at hp
        dsimp only at hp
        obtain ⟨sb1, sb2, sb3, sb4⟩ := splitNode_bounded hdeg hbcc hfull hs
        obtain ⟨sd1, sd2⟩ := splitNode_depth hdeg (Bounded.arity hbcc) hdc hfull hs
        obtain ⟨sk1, sk2, -, -⟩ :=
          splitNode_keyCount hdeg (Bounded.arity hbcc) hkc hfull hs
        obtain ⟨snf1, snf2⟩ := splitNode_not_full hdeg hfull hs
        have hmem := splitNode_mem hs
        split_ifs at hp with h₁ h₂
        · -- descend left
          simp only [Option.some.injEq] at hp
          subst hp
          refine ⟨lo, some m, ⟨sb1, sd1, sk1⟩, snf1, hlo, by simpa using h₁, Or.inr rfl, ?_⟩
          intro x ⟨xb, xd, xk⟩ xm
          refine ⟨⟨by simp, ?_, ?_⟩, ?_, by simp, ?_, ⟨xk, sk2, trivial⟩, ?_⟩
          · intro l' hl' y hy; simp only [List.mem_singleton] at hy; subst hy; exact sb2 l' hl'
          · intro h' hh' y hy; simp only [List.mem_singleton] at hy; subst hy; exact sb3 h' hh'
          · simp only [boundsList, BoundedChildren, List.nil_append]
            exact ⟨xb, sb4, trivial⟩
          · simp only [List.nil_append]
            exact childrenDepth?_cons2 xd sd2 (by simp)
          · intro b
            simp only [List.mem_singleton, memChildren_cons, memChildren_nil, List.not_mem_nil,
              or_false, false_or, List.nil_append, xm]
            rw [← hmem b]
            tauto
        · -- descend right
          simp only [Option.some.injEq] at hp
          subst hp
          refine ⟨some m, hi, ⟨sb4, sd2, sk2⟩, snf2, by simpa using h₂, hhi, Or.inr rfl, ?_⟩
          intro x ⟨xb, xd, xk⟩ xm
          refine ⟨⟨by simp, ?_, ?_⟩, ?_, by simp, ?_, ⟨sk1, xk, trivial⟩, ?_⟩
          · intro l' hl' y hy; simp only [List.mem_singleton] at hy; subst hy; exact sb2 l' hl'
          · intro h' hh' y hy; simp only [List.mem_singleton] at hy; subst hy; exact sb3 h' hh'
          · simp only [boundsList, BoundedChildren, List.singleton_append]
            exact ⟨sb1, xb, trivial⟩
          · simp only [List.singleton_append]
            exact childrenDepth?_cons2 sd1 xd (by simp)
          · intro b
            simp only [List.mem_singleton, memChildren_cons, memChildren_nil, List.not_mem_nil,
              or_false, false_or, List.singleton_append, xm]
            rw [← hmem b]
            tauto
      · -- the child has room already
        simp only [Option.some.injEq] at hp
        subst hp
        refine ⟨lo, hi, ⟨hbcc, hdc, hkc⟩, by simpa using hfull, hlo, hhi, Or.inl rfl, ?_⟩
        intro x ⟨xb, xd, xk⟩ xm
        refine ⟨hk, ?_, by simp, ?_, ⟨xk, trivial⟩, ?_⟩
        · simp only [boundsList, BoundedChildren, List.nil_append]
          exact ⟨xb, trivial⟩
        · simp only [List.nil_append]
          exact childrenDepth?_cons1 xd (by simp)
        · intro b
          simp only [List.not_mem_nil, false_or, memChildren_cons, memChildren_nil, or_false,
            List.nil_append, xm]
  | cons k ks ih =>
      intro cs D hk hbc hlen hdep hck hlo hhi hp
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => simp at hlen
        | cons c cs' => exact ⟨c, cs', rfl⟩
      simp only [boundsList, BoundedChildren] at hbc
      obtain ⟨hbcc, hbcs⟩ := hbc
      have hdc : depth? c = some dep := childrenDepth?_uniform hdep (by simp)
      have hcs'ne : cs' ≠ [] := by
        intro hnil; rw [hnil] at hlen; simp at hlen
      have hdcs : childrenDepth? cs' = some dep := childrenDepth?_tail hdep hcs'ne
      have hkc : KeyCountOk deg false c := hck.1
      have hkall : ∀ y ∈ ks, k < y := (List.pairwise_cons.mp hk.1).1
      simp only [prepare] at hp
      split_ifs at hp with h₁ hfull h₂
      · -- `a` belongs before `k`, and the child is full
        obtain ⟨p, hs⟩ : ∃ p, splitNode deg c = some p :=
          Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
        obtain ⟨l, m, r⟩ := p
        rw [hs] at hp
        dsimp only at hp
        obtain ⟨sb1, sb2, sb3, sb4⟩ := splitNode_bounded hdeg hbcc hfull hs
        obtain ⟨sd1, sd2⟩ := splitNode_depth hdeg (Bounded.arity hbcc) hdc hfull hs
        obtain ⟨sk1, sk2, -, -⟩ := splitNode_keyCount hdeg (Bounded.arity hbcc) hkc hfull hs
        obtain ⟨snf1, snf2⟩ := splitNode_not_full hdeg hfull hs
        have hmem := splitNode_mem hs
        have hmk : m < k := sb3 k rfl
        have hkeys : BoundedKeys lo hi (m :: k :: ks) := by
          refine ⟨?_, ?_, ?_⟩
          · refine List.pairwise_cons.mpr ⟨?_, hk.1⟩
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hmk
            · exact lt_trans hmk (hkall y hy)
          · intro l' hl' y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact sb2 l' hl'
            · exact hk.2.1 l' hl' y hy
          · intro h' hh' y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact lt_trans hmk (hk.2.2 h' hh' k (List.mem_cons_self ..))
            · exact hk.2.2 h' hh' y hy
        split_ifs at hp with h₃ h₄
        · simp only [Option.some.injEq] at hp
          subst hp
          refine ⟨lo, some m, ⟨sb1, sd1, sk1⟩, snf1, hlo, by simpa using h₃, Or.inr (by simp), ?_⟩
          intro x ⟨xb, xd, xk⟩ xm
          refine ⟨hkeys, ?_, by simp at hlen ⊢; omega, ?_, ⟨xk, sk2, hck.2⟩, ?_⟩
          · simp only [boundsList, BoundedChildren, List.nil_append]
            exact ⟨xb, sb4, hbcs⟩
          · simp only [List.nil_append]
            exact childrenDepth?_cons2 xd sd2
              (fun z hz => childrenDepth?_uniform hdep (by simp [hz]))
          · intro b
            simp only [List.mem_cons, memChildren_cons, List.nil_append, xm]
            rw [← hmem b]
            tauto
        · simp only [Option.some.injEq] at hp
          subst hp
          refine ⟨some m, some k, ⟨sb4, sd2, sk2⟩, snf2, by simpa using h₄,
            by simpa using h₁, Or.inr (by simp), ?_⟩
          intro x ⟨xb, xd, xk⟩ xm
          refine ⟨hkeys, ?_, by simp at hlen ⊢; omega, ?_, ⟨sk1, xk, hck.2⟩, ?_⟩
          · simp only [boundsList, BoundedChildren, List.singleton_append]
            exact ⟨sb1, xb, hbcs⟩
          · simp only [List.singleton_append]
            exact childrenDepth?_cons2 sd1 xd
              (fun z hz => childrenDepth?_uniform hdep (by simp [hz]))
          · intro b
            simp only [List.mem_cons, memChildren_cons, List.singleton_append, xm]
            rw [← hmem b]
            tauto
      · -- `a` belongs before `k`, and the child has room
        simp only [Option.some.injEq] at hp
        subst hp
        refine ⟨lo, some k, ⟨hbcc, hdc, hkc⟩, by simpa using hfull, hlo,
          by simpa using h₁, Or.inl rfl, ?_⟩
        intro x ⟨xb, xd, xk⟩ xm
        refine ⟨hk, ?_, by simp at hlen ⊢; omega, ?_, ⟨xk, hck.2⟩, ?_⟩
        · simp only [boundsList, BoundedChildren, List.nil_append]
          exact ⟨xb, hbcs⟩
        · simp only [List.nil_append]
          exact childrenDepth?_cons1 xd
            (fun z hz => childrenDepth?_uniform hdep (by simp [hz]))
        · intro b
          simp only [List.mem_cons, memChildren_cons, List.nil_append, xm]
          tauto
      · -- `a` belongs strictly to the right of `k`: walk on
        cases hrec : prepare deg a ks cs' with
        | none => rw [hrec] at hp; exact absurd hp (by simp)
        | some D' =>
            rw [hrec] at hp
            dsimp only at hp
            have hklo : ∀ l' ∈ (some k : Option α), l' < a := by
              intro y hy; cases hy; exact h₂
            obtain ⟨lo', hi', hleg, hnf, hlo', hhi', hgrow, hsub⟩ :=
              ih (BoundedKeys.of_cons hk) hbcs (by simpa using hlen) hdcs hck.2 hklo hhi hrec
            simp only [Option.some.injEq] at hp
            subst hp
            refine ⟨lo', hi', hleg, hnf, hlo', hhi', ?_, ?_⟩
            · simp only [List.length_cons]
              rcases hgrow with h | h <;> simp [h]
            · intro x hx xm
              obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hsub x hx xm
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
              · refine ⟨List.pairwise_cons.mpr ⟨fun y hy => q1.2.1 k rfl y hy, q1.1⟩, ?_, ?_⟩
                · intro l' hl' y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact hk.2.1 l' hl' y (List.mem_cons_self ..)
                  · exact lt_trans (hk.2.1 l' hl' k (List.mem_cons_self ..)) (q1.2.1 k rfl y hy)
                · intro h' hh' y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact hk.2.2 h' hh' y (List.mem_cons_self ..)
                  · exact q1.2.2 h' hh' y hy
              · simp only [boundsList, BoundedChildren, List.cons_append]
                exact ⟨hbcc, q2⟩
              · simp only [List.cons_append, List.length_cons] at q3 ⊢
                omega
              · simp only [List.cons_append]
                exact childrenDepth?_cons1 hdc (fun z hz => childrenDepth?_uniform q4 hz)
              · simp only [List.cons_append, childrenKeyCountOk_cons]
                exact ⟨hkc, q5⟩
              · intro b
                simp only [List.cons_append, List.mem_cons, memChildren_cons]
                have := q6 b
                tauto

/-- `prepare` only declines when there is nothing to do: `a` is already a key of this node, or of
the child it would have descended into (as a just-promoted median). -/
theorem prepare_none_mem (deg : ℕ) (hdeg : 2 ≤ deg) (a : α) :
    ∀ {ks : List α} {cs : List (BTree α)}, cs.length = ks.length + 1 →
      prepare deg a ks cs = none → (a ∈ ks ∨ MemChildren a cs) := by
  intro ks
  induction ks with
  | nil =>
      intro cs hlen hp
      obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
        cases cs with
        | nil => simp at hlen
        | cons c cs' =>
            cases cs' with
            | nil => exact ⟨c, rfl⟩
            | cons _ _ => simp at hlen
      simp only [prepare] at hp
      -- only the "child is full, and `a` is the promoted median" branch survives; the others
      -- return `some`, which `split_ifs` discharges against `hp`.
      split_ifs at hp with hfull
      obtain ⟨q, hs⟩ : ∃ q, splitNode deg c = some q :=
        Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
      obtain ⟨l, m, r⟩ := q
      rw [hs] at hp
      dsimp only at hp
      split_ifs at hp with h₁ h₂
      have hax : a = m := le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)
      subst hax
      exact Or.inr (Or.inl (splitNode_mem_median hs))
  | cons k ks ih =>
      intro cs hlen hp
      obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
        cases cs with
        | nil => simp at hlen
        | cons c cs' => exact ⟨c, cs', rfl⟩
      simp only [prepare] at hp
      split_ifs at hp with h₁ hfull h₂
      · obtain ⟨q, hs⟩ : ∃ q, splitNode deg c = some q :=
          Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
        obtain ⟨l, m, r⟩ := q
        rw [hs] at hp
        dsimp only at hp
        split_ifs at hp with h₃ h₄
        have hax : a = m := le_antisymm (not_lt.mp h₄) (not_lt.mp h₃)
        subst hax
        exact Or.inr (Or.inl (splitNode_mem_median hs))
      · cases hrec : prepare deg a ks cs' with
        | none =>
            have hih := ih (by simpa using hlen) hrec
            simp only [List.mem_cons, memChildren_cons]
            tauto
        | some D' => rw [hrec] at hp; exact absurd hp (by simp)
      · have hax : a = k := le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)
        subst hax
        exact Or.inl (List.mem_cons_self ..)

/-- **`insNonfull` keeps the node legal and adds exactly `a`.** The `isFull deg t = false`
hypothesis is CLRS's descent invariant, and `prepare` is what re-establishes it one level down:
whatever it hands back to descend into has just been split if it needed it. -/
theorem insNonfull_spec (deg : ℕ) (hdeg : 2 ≤ deg) (a : α) :
    ∀ (t : BTree α) (lo hi : Option α) (isRoot : Bool) (dep : ℕ),
      Bounded lo hi t → depth? t = some dep → KeyCountOk deg isRoot t →
      isFull deg t = false → (∀ l ∈ lo, l < a) → (∀ h ∈ hi, a < h) →
      Bounded lo hi (insNonfull deg a t) ∧ depth? (insNonfull deg a t) = some dep ∧
        KeyCountOk deg isRoot (insNonfull deg a t) ∧
        (∀ b, Mem b (insNonfull deg a t) ↔ (b = a ∨ Mem b t))
  | leaf ks, lo, hi, isRoot, dep, hb, hd, hk, hnf, hlo, hhi => by
      have hdep : dep = 0 := by simpa [depth?] using hd.symm
      subst hdep
      have hlen : ks.length ≠ 2 * deg - 1 := by
        simpa [isFull] using hnf
      have hub : ks.length ≤ 2 * deg - 1 := hk.2
      rw [insNonfull]
      refine ⟨boundedKeys_insKeys hlo hhi hb, rfl, ⟨?_, ?_⟩, ?_⟩
      · rcases hk.1 with hr | hlow
        · exact Or.inl hr
        · exact Or.inr (le_trans hlow (le_length_insKeys a ks))
      · rcases length_insKeys a ks with h | h <;> omega
      · intro b; simp [mem_insKeys]
  | node ks cs, lo, hi, isRoot, dep, hb, hd, hk, hnf, hlo, hhi => by
      obtain ⟨hbk, hlen, hbc⟩ := hb
      obtain ⟨dep', hdep', rfl⟩ : ∃ d, childrenDepth? cs = some d ∧ dep = d + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨d, h₁, h₂⟩ := hd
        exact ⟨d, h₁, h₂.symm⟩
      have hkslen : ks.length ≠ 2 * deg - 1 := by simpa [isFull] using hnf
      have hub : ks.length ≤ 2 * deg - 1 := hk.2.1
      rw [insNonfull]
      cases hp : prepare deg a ks cs with
      | none =>
          have hmem : Mem a (node ks cs) := by
            simpa [mem_node] using prepare_none_mem deg hdeg a hlen hp
          refine ⟨⟨hbk, hlen, hbc⟩, by simp [depth?, hdep'], hk, ?_⟩
          intro b
          constructor
          · exact fun h => Or.inr h
          · rintro (rfl | h)
            · exact hmem
            · exact h
      | some D =>
          obtain ⟨lo', hi', hleg, hnf', hlo', hhi', hgrow, hsub⟩ :=
            prepare_spec deg hdeg a hbk hbc hlen hdep' hk.2.2 hlo hhi hp
          obtain ⟨tb, td, tk⟩ := hleg
          have ih := insNonfull_spec deg hdeg a D.target lo' hi' false dep' tb td tk hnf' hlo' hhi'
          obtain ⟨ib, id, ik, im⟩ := ih
          obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hsub _ ⟨ib, id, ik⟩ im
          refine ⟨⟨q1, q3, q2⟩, by simp [depth?, q4], ⟨?_, ?_, q5⟩, ?_⟩
          · cases isRoot with
            | true =>
                change 1 ≤ D.keys.length
                have h0 : 1 ≤ ks.length := hk.1
                rcases hgrow with h | h <;> omega
            | false =>
                change deg - 1 ≤ D.keys.length
                have h0 : deg - 1 ≤ ks.length := hk.1
                rcases hgrow with h | h <;> omega
          · rcases hgrow with h | h <;> omega
          · intro b
            simpa [mem_node] using q6 b
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hp
    simp only [height_node]
    omega

omit [LinearOrder α] in
/-- A full node meets the *non-root* occupancy floor automatically: `2 * deg - 1` keys is more
than `deg - 1`. This is what lets a full root be split into two ordinary nodes. -/
theorem keyCountOk_false_of_full {deg : ℕ} (hdeg : 2 ≤ deg) {t : BTree α}
    (h : KeyCountOk deg true t) (hf : isFull deg t = true) : KeyCountOk deg false t := by
  have hlen : (nodeKeys t).length = 2 * deg - 1 := isFull_iff.mp hf
  cases t with
  | leaf ks =>
      simp only [nodeKeys_leaf] at hlen
      exact ⟨Or.inr (by omega), h.2⟩
  | node ks cs =>
      simp only [nodeKeys_node] at hlen
      exact ⟨by change deg - 1 ≤ ks.length; omega, h.2.1, h.2.2⟩

/-- On a legal tree, `insert` adds exactly `a` to the key set. -/
theorem insertMem {deg : ℕ} {bt : BTree α} (h : Valid deg bt) (a : α) :
    InsertMem a bt (insert deg a bt) := by
  obtain ⟨hb, hsd, hk, hdeg⟩ := valid_iff_legal.1 h
  have hd : depth? bt = some bt.height := depth?_eq_some_height hsd
  intro b
  rw [insert]
  split_ifs with hfull
  · obtain ⟨q, hs⟩ : ∃ q, splitNode deg bt = some q :=
      Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
    obtain ⟨l, m, r⟩ := q
    rw [hs]
    obtain ⟨sb1, sb2, sb3, sb4⟩ := splitNode_bounded hdeg hb hfull hs
    obtain ⟨sd1, sd2⟩ := splitNode_depth hdeg (Bounded.arity hb) hd hfull hs
    obtain ⟨sk1, sk2, -, -⟩ :=
      splitNode_keyCount hdeg (Bounded.arity hb) (keyCountOk_false_of_full hdeg hk hfull) hfull hs
    have hroot : Bounded none none (node [m] [l, r]) := by
      refine ⟨⟨by simp, by simp, by simp⟩, by simp, ?_⟩
      simp only [boundsList, BoundedChildren]
      exact ⟨sb1, sb4, trivial⟩
    have hrootd : depth? (node [m] [l, r]) = some (bt.height + 1) := by
      simp [depth?, childrenDepth?, sd1, sd2]
    have hrootk : KeyCountOk deg true (node [m] [l, r]) :=
      ⟨by change 1 ≤ [m].length; simp, by simp; omega, sk1, sk2, trivial⟩
    have hrootnf : isFull deg (node [m] [l, r]) = false := by
      simp only [isFull, nodeKeys_node, beq_eq_false_iff_ne, ne_eq, List.length_singleton]
      omega
    obtain ⟨-, -, -, hm⟩ :=
      insNonfull_spec deg hdeg a (node [m] [l, r]) none none true (bt.height + 1)
        hroot hrootd hrootk hrootnf (by simp) (by simp)
    rw [hm b]
    simp only [mem_node, memChildren_cons, memChildren_nil, List.mem_singleton, or_false]
    rw [← splitNode_mem hs b]
    tauto
  · obtain ⟨-, -, -, hm⟩ :=
      insNonfull_spec deg hdeg a bt none none true bt.height hb hd hk
        (by simpa using hfull) (by simp) (by simp)
    exact hm b

/-- **`insert` keeps the tree legal**, at the same minimum degree. A full root is split first,
which is the one place the tree gets taller — and it gets taller on every path at once. -/
theorem insertValid {deg : ℕ} {bt : BTree α} (h : Valid deg bt) (a : α) :
    Valid deg (insert deg a bt) := by
  obtain ⟨hb, hsd, hk, hdeg⟩ := valid_iff_legal.1 h
  have hd : depth? bt = some bt.height := depth?_eq_some_height hsd
  rw [insert]
  split_ifs with hfull
  · obtain ⟨q, hs⟩ : ∃ q, splitNode deg bt = some q :=
      Option.isSome_iff_exists.mp (splitNode_isSome hdeg hfull)
    obtain ⟨l, m, r⟩ := q
    rw [hs]
    obtain ⟨sb1, sb2, sb3, sb4⟩ := splitNode_bounded hdeg hb hfull hs
    obtain ⟨sd1, sd2⟩ := splitNode_depth hdeg (Bounded.arity hb) hd hfull hs
    obtain ⟨sk1, sk2, -, -⟩ :=
      splitNode_keyCount hdeg (Bounded.arity hb) (keyCountOk_false_of_full hdeg hk hfull) hfull hs
    have hroot : Bounded none none (node [m] [l, r]) := by
      refine ⟨⟨by simp, by simp, by simp⟩, by simp, ?_⟩
      simp only [boundsList, BoundedChildren]
      exact ⟨sb1, sb4, trivial⟩
    have hrootd : depth? (node [m] [l, r]) = some (bt.height + 1) := by
      simp [depth?, childrenDepth?, sd1, sd2]
    have hrootk : KeyCountOk deg true (node [m] [l, r]) :=
      ⟨by change 1 ≤ [m].length; simp, by simp; omega, sk1, sk2, trivial⟩
    have hrootnf : isFull deg (node [m] [l, r]) = false := by
      simp only [isFull, nodeKeys_node, beq_eq_false_iff_ne, ne_eq, List.length_singleton]
      omega
    obtain ⟨rb, rd, rk, -⟩ :=
      insNonfull_spec deg hdeg a (node [m] [l, r]) none none true (bt.height + 1)
        hroot hrootd hrootk hrootnf (by simp) (by simp)
    exact valid_iff_legal.2 ⟨rb, Option.ne_none_iff_exists'.mpr ⟨_, rd⟩, rk, hdeg⟩
  · obtain ⟨rb, rd, rk, -⟩ :=
      insNonfull_spec deg hdeg a bt none none true bt.height hb hd hk
        (by simpa using hfull) (by simp) (by simp)
    exact valid_iff_legal.2 ⟨rb, Option.ne_none_iff_exists'.mpr ⟨_, rd⟩, rk, hdeg⟩

/-- `insert` discharges `InsertSpec`. -/
theorem insertSpec {deg : ℕ} {bt : BTree α} (h : Valid deg bt) (a : α) :
    InsertSpec deg a bt (insert deg a bt) :=
  ⟨insertMem h a, fun _ => insertValid h a⟩

/-! ## What an insertion costs

One block transfer per node entered, as `searchM` (`Cost.lean`). -/

/-- `insNonfull`, charged one block transfer per node entered. The split a full child needs on
the way down is a write to a block already fetched, so it costs nothing extra here. -/
def insNonfullM (deg : ℕ) (a : α) : BTree α → TimeM ℕ (BTree α)
  | leaf ks => do
      tick 1
      pure (leaf (insKeys a ks))
  | node ks cs =>
      match _hprep : prepare deg a ks cs with
      | none => do
          tick 1
          pure (node ks cs)
      | some d => do
          tick 1
          let t ← insNonfullM deg a d.target
          pure (node d.keys (d.before ++ t :: d.after))
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height _hprep
    simp only [height_node]
    omega

/-- **Erasing the cost gives ordinary `insNonfull`.** -/
theorem ret_insNonfullM (deg : ℕ) (a : α) :
    ∀ t : BTree α, (insNonfullM deg a t).ret = insNonfull deg a t
  | leaf ks => by simp [insNonfullM, insNonfull]
  | node ks cs => by
      -- the recursive call is taken once, outside the case split, so that the termination
      -- goal sees exactly one descent
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullM deg a d.target).ret = insNonfull deg a d.target := by
        intro d hd
        exact ret_insNonfullM deg a d.target
      rw [insNonfullM, insNonfull]
      split
      · simp
      · rename_i d hd
        simp only [ret_bind]
        rw [ih d hd]
        rfl
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- **One block transfer per level.** -/
theorem time_insNonfullM_le (deg : ℕ) (a : α) :
    ∀ t : BTree α, (insNonfullM deg a t).time ≤ t.height + 1
  | leaf ks => by simp [insNonfullM, height]
  | node ks cs => by
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullM deg a d.target).time ≤ d.target.height + 1 := by
        intro d hd
        exact time_insNonfullM_le deg a d.target
      rw [insNonfullM]
      split
      · simp [height_node]
      · rename_i d hd
        simp only [time_bind, time_tick, time_pure, height_node]
        have hle := prepare_target_height hd
        have := ih d hd
        omega
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- `insert`, charged one block transfer per node entered. One descent, so the charge is the
descent's — the same shape as `searchM`'s and as `delRecCost`'s. -/
def insertM (deg : ℕ) (a : α) (t : BTree α) : TimeM ℕ (BTree α) := do
  if isFull deg t then
    match splitNode deg t with
    | none => insNonfullM deg a t
    | some (l, m, r) => insNonfullM deg a (node [m] [l, r])
  else insNonfullM deg a t

/-- **Erasing the cost gives ordinary `insert`.** -/
theorem ret_insertM (deg : ℕ) (a : α) (t : BTree α) :
    (insertM deg a t).ret = insert deg a t := by
  rw [insertM, insert]
  split
  · split
    · exact ret_insNonfullM deg a t
    · exact ret_insNonfullM deg a _
  · exact ret_insNonfullM deg a t

/-- **An insertion costs one descent.** The `+ 2` over the height is the leaf the descent ends
on and the extra level a root split adds. -/
theorem time_insertM_le (deg : ℕ) (a : α) (t : BTree α) :
    (insertM deg a t).time ≤ t.height + 2 := by
  rw [insertM]
  split
  · split
    · have := time_insNonfullM_le deg a t
      omega
    · rename_i l m r hsp
      have hlr := splitNode_height_le hsp
      have := time_insNonfullM_le deg a (node [m] [l, r])
      simp only [height_node, childrenHeight] at this
      omega
  · have := time_insNonfullM_le deg a t
    omega

/-- **The trips an insertion costs, in the same unit as `time_searchM_le_log`.** -/
theorem time_insertM_le_log {deg : ℕ} {bt : BTree α} (hv : Valid deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (insertM deg a bt).time ≤ Nat.log deg ((bt.size + 1) / 2) + 2 := by
  have hdeg : 2 ≤ deg := (valid_iff_legal.1 hv).2.2.2
  have hstruct : 2 * deg ^ bt.height ≤ bt.size + 1 := two_mul_pow_height_le_size_succ hv hsz
  have hdiv : deg ^ bt.height ≤ (bt.size + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hlog : bt.height ≤ Nat.log deg ((bt.size + 1) / 2) :=
    Nat.le_log_of_pow_le (by omega) hdiv
  have := time_insertM_le deg a bt
  omega

end BTree

end AlgoDesign.Searching
