/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Spec

/-!
# B-tree: structural bookkeeping

The definitions and lemmas that search, insertion and deletion share: the induction invariants
`Bounded` and `KeyCountOk`, `All`, `size`, `height`, the `depth?` facts behind `SameDepth`, the
bridge from `Bounded` to membership, `toList` against `Mem`, and the arity, depth, occupancy and
ordering facts about lists of children that both updates use. The specification they serve is in
`Spec.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

section

variable {α : Type}

mutual

/-- `a` is one of the tree's keys. -/
def Mem (a : α) : BTree α → Prop
  | leaf ks => a ∈ ks
  | node ks cs => a ∈ ks ∨ MemChildren a cs

/-- `Mem a` holds of some child in the list. -/
def MemChildren (a : α) : List (BTree α) → Prop
  | [] => False
  | c :: cs => Mem a c ∨ MemChildren a cs

end

mutual

/-- Number of keys in the tree. The box's bounds are in `SearchTree.size`, the number of keys held;
on a valid tree the two agree (`tree_size`). Like `Mem`, split into a `List` companion
(`sizeChildren`). -/
def size : BTree α → ℕ
  | leaf ks => ks.length
  | node ks cs => ks.length + sizeChildren cs

/-- Total `size` across a list of children. -/
def sizeChildren : List (BTree α) → ℕ
  | [] => 0
  | c :: cs => c.size + sizeChildren cs

end

end

variable {α : Type} [LinearOrder α]

/-! ## The induction invariants

`Bounded` and `KeyCountOk` are the invariants the proofs carry down the tree: `Bounded lo hi`
threads a subtree's flanking keys and child count, `KeyCountOk deg isRoot` its occupancy with the
root rule. `valid_iff_legal` (`Search.lean`) states `Valid` through them. -/

/-- `ks` is sorted and lies strictly between `lo` and `hi`; `none` means no bound on that side. -/
def BoundedKeys (lo hi : Option α) (ks : List α) : Prop :=
  ks.Pairwise (· < ·) ∧ (∀ l ∈ lo, ∀ k ∈ ks, l < k) ∧ (∀ h ∈ hi, ∀ k ∈ ks, k < h)

/-- For `n` keys, the `n + 1` `(lo, hi)` bound pairs flanking each of a node's `n + 1` children:
before the first key, between each consecutive pair, and after the last. -/
def boundsList (lo hi : Option α) : List α → List (Option α × Option α)
  | [] => [(lo, hi)]
  | k :: ks => (lo, some k) :: boundsList (some k) hi ks

mutual

/-- The keys of a subtree lie strictly between `lo` and `hi` and increase, every child's keys lie
strictly between the two keys flanking it, and a node has one more child than keys. -/
def Bounded (lo hi : Option α) : BTree α → Prop
  | leaf ks => BoundedKeys lo hi ks
  | node ks cs => BoundedKeys lo hi ks ∧ cs.length = ks.length + 1 ∧
      BoundedChildren (boundsList lo hi ks) cs

/-- `Bounded` on every child, each against its flanking pair from `boundsList`; false on a length
mismatch. -/
def BoundedChildren : List (Option α × Option α) → List (BTree α) → Prop
  | [], [] => True
  | (lo, hi) :: bs, c :: cs => Bounded lo hi c ∧ BoundedChildren bs cs
  | _, _ => False

end

mutual

/-- Occupancy with the root rule: at most `2 * t - 1` keys, at least `t - 1` off the root, at least
one in an internal root. -/
def KeyCountOk (t : ℕ) (isRoot : Bool) : BTree α → Prop
  | leaf ks => (isRoot ∨ ks.length ≥ t - 1) ∧ ks.length ≤ 2 * t - 1
  | node ks cs => (if isRoot then 1 ≤ ks.length else t - 1 ≤ ks.length) ∧
      ks.length ≤ 2 * t - 1 ∧ ChildrenKeyCountOk t cs

/-- `KeyCountOk t false` on every child — children are never the root. -/
def ChildrenKeyCountOk (t : ℕ) : List (BTree α) → Prop
  | [] => True
  | c :: cs => KeyCountOk t false c ∧ ChildrenKeyCountOk t cs

end

instance decidableBoundedKeys (lo hi : Option α) (ks : List α) :
    Decidable (BoundedKeys lo hi ks) :=
  inferInstanceAs (Decidable (ks.Pairwise (· < ·) ∧ (∀ l ∈ lo, ∀ k ∈ ks, l < k) ∧
    (∀ h ∈ hi, ∀ k ∈ ks, k < h)))

mutual

/-- `Bounded` decides on a concrete tree. -/
def decidableBounded : (lo hi : Option α) → (bt : BTree α) → Decidable (Bounded lo hi bt)
  | lo, hi, leaf ks => inferInstanceAs (Decidable (BoundedKeys lo hi ks))
  | lo, hi, node ks cs =>
      haveI := decidableBoundedChildren (boundsList lo hi ks) cs
      inferInstanceAs (Decidable (BoundedKeys lo hi ks ∧ cs.length = ks.length + 1 ∧
        BoundedChildren (boundsList lo hi ks) cs))

/-- `BoundedChildren` decides on a concrete child list. -/
def decidableBoundedChildren :
    (bs : List (Option α × Option α)) → (cs : List (BTree α)) →
      Decidable (BoundedChildren bs cs)
  | [], [] => inferInstanceAs (Decidable True)
  | (lo, hi) :: bs, c :: cs =>
      haveI := decidableBounded lo hi c
      haveI := decidableBoundedChildren bs cs
      inferInstanceAs (Decidable (Bounded lo hi c ∧ BoundedChildren bs cs))
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)

end

instance (lo hi : Option α) (bt : BTree α) : Decidable (Bounded lo hi bt) :=
  decidableBounded lo hi bt

mutual

/-- `KeyCountOk` decides on a concrete tree. -/
def decidableKeyCountOk (t : ℕ) : (isRoot : Bool) → (bt : BTree α) →
    Decidable (KeyCountOk t isRoot bt)
  | isRoot, leaf ks =>
      inferInstanceAs (Decidable ((isRoot ∨ ks.length ≥ t - 1) ∧ ks.length ≤ 2 * t - 1))
  | isRoot, node ks cs =>
      haveI := decidableChildrenKeyCountOk t cs
      inferInstanceAs (Decidable ((if isRoot then 1 ≤ ks.length else t - 1 ≤ ks.length) ∧
        ks.length ≤ 2 * t - 1 ∧ ChildrenKeyCountOk t cs))

/-- `ChildrenKeyCountOk` decides on a concrete child list. -/
def decidableChildrenKeyCountOk (t : ℕ) : (cs : List (BTree α)) →
    Decidable (ChildrenKeyCountOk t cs)
  | [] => inferInstanceAs (Decidable True)
  | c :: cs =>
      haveI := decidableKeyCountOk t false c
      haveI := decidableChildrenKeyCountOk t cs
      inferInstanceAs (Decidable (KeyCountOk t false c ∧ ChildrenKeyCountOk t cs))

end

instance (t : ℕ) (isRoot : Bool) (bt : BTree α) : Decidable (KeyCountOk t isRoot bt) :=
  decidableKeyCountOk t isRoot bt

/-! ## `Mem`/`All`, and other structural bookkeeping -/

omit [LinearOrder α] in
@[simp] theorem mem_leaf (a : α) (ks : List α) : Mem a (leaf ks) ↔ a ∈ ks := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem mem_node (a : α) (ks : List α) (cs : List (BTree α)) :
    Mem a (node ks cs) ↔ a ∈ ks ∨ MemChildren a cs := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem memChildren_nil (a : α) : MemChildren a ([] : List (BTree α)) ↔ False := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem memChildren_cons (a : α) (c : BTree α) (cs : List (BTree α)) :
    MemChildren a (c :: cs) ↔ Mem a c ∨ MemChildren a cs := Iff.rfl

omit [LinearOrder α] in
theorem memChildren_append (a : α) (cs₁ cs₂ : List (BTree α)) :
    MemChildren a (cs₁ ++ cs₂) ↔ MemChildren a cs₁ ∨ MemChildren a cs₂ := by
  induction cs₁ with
  | nil => simp
  | cons c cs ih => simp [ih, or_assoc]

omit [LinearOrder α] in
theorem memChildren_of_mem {a : α} {c : BTree α} {cs : List (BTree α)} (hc : c ∈ cs)
    (ha : Mem a c) : MemChildren a cs := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Or.inl ha
    · exact Or.inr (ih hc)

mutual

/-- Every key in the tree satisfies `p` — the `BTree` analogue of `BST.All`/`LLRB.All`. -/
def All (p : α → Prop) : BTree α → Prop
  | leaf ks => ∀ k ∈ ks, p k
  | node ks cs => (∀ k ∈ ks, p k) ∧ AllChildren p cs

/-- `All p` holds of every child in the list. -/
def AllChildren (p : α → Prop) : List (BTree α) → Prop
  | [] => True
  | c :: cs => All p c ∧ AllChildren p cs

end

omit [LinearOrder α] in
@[simp] theorem all_leaf (p : α → Prop) (ks : List α) : All p (leaf ks) ↔ ∀ k ∈ ks, p k := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem all_node (p : α → Prop) (ks : List α) (cs : List (BTree α)) :
    All p (node ks cs) ↔ (∀ k ∈ ks, p k) ∧ AllChildren p cs := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem allChildren_nil (p : α → Prop) : AllChildren p ([] : List (BTree α)) ↔ True :=
  Iff.rfl

omit [LinearOrder α] in
@[simp] theorem allChildren_cons (p : α → Prop) (c : BTree α) (cs : List (BTree α)) :
    AllChildren p (c :: cs) ↔ All p c ∧ AllChildren p cs := Iff.rfl

omit [LinearOrder α] in
theorem AllChildren.of_mem {p : α → Prop} {cs : List (BTree α)} (h : AllChildren p cs)
    {c : BTree α} (hc : c ∈ cs) : All p c := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    obtain ⟨hc', h⟩ := h
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hc'
    · exact ih h hc

-- `All.of_mem` needs simultaneous structural recursion over `t : BTree α` and
-- `cs : List (BTree α)` (the same shape as `Mem`/`MemChildren` themselves): the plain
-- `induction` tactic rejects `BTree` because it's a *nested* inductive (its `node` case embeds
-- `List (BTree α)`), so this is proved as a `mutual` pair of equation-compiled theorems instead,
-- matching how `Mem`/`MemChildren` are themselves defined.
omit [LinearOrder α] in
mutual

theorem All.of_mem {p : α → Prop} : ∀ {t : BTree α}, All p t → ∀ {a : α}, Mem a t → p a
  | leaf _, h, a, ha => h a ha
  | node _ _, h, a, ha => by
      rcases ha with ha | ha
      · exact h.1 a ha
      · exact AllChildren.of_mem' h.2 ha

theorem AllChildren.of_mem' {p : α → Prop} : ∀ {cs : List (BTree α)}, AllChildren p cs →
    ∀ {a : α}, MemChildren a cs → p a
  | [], _, _, ha => by cases ha
  | c :: cs, h, a, ha => by
      rcases ha with ha | ha
      · exact All.of_mem h.1 ha
      · exact AllChildren.of_mem' h.2 ha

end

omit [LinearOrder α] in
@[simp] theorem size_leaf (ks : List α) : size (leaf ks) = ks.length := rfl

omit [LinearOrder α] in
@[simp] theorem size_node (ks : List α) (cs : List (BTree α)) :
    size (node ks cs) = ks.length + sizeChildren cs := rfl

omit [LinearOrder α] in
@[simp] theorem sizeChildren_nil : sizeChildren ([] : List (BTree α)) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem sizeChildren_cons (c : BTree α) (cs : List (BTree α)) :
    sizeChildren (c :: cs) = c.size + sizeChildren cs := rfl

omit [LinearOrder α] in
theorem sizeChildren_le_of_mem {c : BTree α} {cs : List (BTree α)} (hc : c ∈ cs) :
    c.size ≤ sizeChildren cs := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · have := ih hc; simp; omega

mutual

/-- The tree's height: a *total* stand-in for `depth?`'s partial `Option ℕ` (defined only when
every leaf agrees), used as a termination measure for `insert` and as a proof device the same way
`LLRB.bheight` stands in for `blackHeight` — see `depth?_eq_some_height` below for the bridge back
to the committed `SameDepth`/`depth?` spec. `leaf` has height `0`; an internal node's height is one
more than the *tallest* of its children (so this is meaningful even off a `SameDepth` tree, unlike
`depth?`). -/
def height : BTree α → ℕ
  | leaf _ => 0
  | node _ cs => childrenHeight cs + 1

/-- The tallest `height` across a list of children (`0` for the empty list). -/
def childrenHeight : List (BTree α) → ℕ
  | [] => 0
  | [c] => c.height
  | c :: cs => max c.height (childrenHeight cs)

end

omit [LinearOrder α] in
@[simp] theorem height_leaf (ks : List α) : height (leaf ks) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem height_node (ks : List α) (cs : List (BTree α)) :
    height (node ks cs) = childrenHeight cs + 1 := rfl

omit [LinearOrder α] in
theorem height_le_childrenHeight_of_mem {c : BTree α} {cs : List (BTree α)} (hc : c ∈ cs) :
    c.height ≤ childrenHeight cs := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · rcases cs with _ | ⟨c'', cs⟩
      · simp [childrenHeight]
      · simp only [childrenHeight]; exact Nat.le_max_left _ _
    · rcases cs with _ | ⟨c'', cs⟩
      · cases hc
      · have := ih hc
        simp only [childrenHeight]
        omega

omit [LinearOrder α] in
mutual

/-- Under `SameDepth`, the total `height` recovers exactly what `depth?` witnesses — the `BTree`
counterpart to `LLRB.blackHeight_of_balanced`, bridging the proof device back to the committed
`Option`-based spec. -/
theorem depth?_eq_some_height {t : BTree α} (h : SameDepth t) : depth? t = some (height t) := by
  match t, h with
  | leaf _, _ => rfl
  | node _ cs, h =>
    have h' : (childrenDepth? cs).isSome := by
      simpa [SameDepth, depth?, ← Option.isSome_iff_ne_none] using h
    simp [depth?, height, childrenDepth?_isSome h']

/-- Companion to `depth?_eq_some_height` for the `List`-valued `childrenDepth?`/`childrenHeight`
pair. -/
theorem childrenDepth?_isSome {cs : List (BTree α)} (h : (childrenDepth? cs).isSome) :
    childrenDepth? cs = some (childrenHeight cs) := by
  match cs, h with
  | [c], h =>
    have hc : SameDepth c := by
      simpa [childrenDepth?, SameDepth, ← Option.isSome_iff_ne_none] using h
    simp [childrenDepth?, childrenHeight, depth?_eq_some_height hc]
  | c :: c2 :: cs, h =>
    simp only [childrenDepth?] at h ⊢
    rcases hd1 : c.depth? with _ | d
    · simp [hd1] at h
    rcases hd2 : childrenDepth? (c2 :: cs) with _ | d'
    · simp [hd1, hd2] at h
    by_cases hdd : d = d'
    · subst hdd
      have hsd : SameDepth c := Option.ne_none_iff_exists'.mpr ⟨d, hd1⟩
      have h1 := depth?_eq_some_height hsd
      rw [hd1] at h1
      have h2 := childrenDepth?_isSome (Option.isSome_iff_exists.mpr ⟨d, hd2⟩)
      rw [hd2] at h2
      have e1 : c.height = d := (Option.some.inj h1).symm
      have e2 : childrenHeight (c2 :: cs) = d := (Option.some.inj h2).symm
      simp [childrenHeight, e1, e2]
    · simp [hd1, hd2, hdd] at h

end

omit [LinearOrder α] in
/-- Companion to `childrenDepth?_isSome`: if a children list's depths agree at all (on `d`), then
*every* element individually has `depth? = some d`, not just the one element `childrenDepth?`'s
own recursion happens to inspect last. `size_ge_of_keyCountOk` below needs this to apply the same
height bound to *every* child of a `SameDepth` node, not only a single one of them. -/
theorem childrenDepth?_uniform :
    ∀ {cs : List (BTree α)} {d : ℕ}, childrenDepth? cs = some d →
      ∀ {c : BTree α}, c ∈ cs → c.depth? = some d
  | [c], d, h, c', hc' => by
      simp only [childrenDepth?] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      subst hc'
      exact h
  | c :: c2 :: cs, d, h, c', hc' => by
      simp only [childrenDepth?] at h
      rcases he1 : c.depth? with _ | e1
      · simp [he1] at h
      rcases he2 : childrenDepth? (c2 :: cs) with _ | e2
      · simp [he1, he2] at h
      by_cases hee : e1 = e2
      · subst hee
        simp only [he1, he2] at h
        have hed : e1 = d := Option.some.inj h
        subst hed
        rw [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact he1
        · exact childrenDepth?_uniform he2 hc'
      · simp [he1, he2, hee] at h

/-! ## The bounds/membership bridge

The one lemma every `search`/`insert`-correctness argument below leans on: if `a` is a member of
a `Bounded` tree, it satisfies that tree's own flanking bounds. This is what justifies "if
`a < k`, don't bother looking right of `k`" — the wrong subtree is *provably* empty of `a`, not
just conventionally skipped. -/

/-- Peeling the first key off `BoundedKeys lo hi (k :: ks)` tightens the lower bound to `some k`
for the rest — the key fact `boundsList`'s recursive `(some k)` argument is chasing. Needed
wherever a proof walks past one key of a node and must re-derive `BoundedKeys` for the tail. -/
theorem BoundedKeys.of_cons {lo hi : Option α} {k : α} {ks : List α}
    (h : BoundedKeys lo hi (k :: ks)) : BoundedKeys (some k) hi ks := by
  obtain ⟨hp, _, hhi⟩ := h
  rw [List.pairwise_cons] at hp
  refine ⟨hp.2, fun l hl x hx => ?_, fun h hh x hx => hhi h hh x (List.mem_cons_of_mem _ hx)⟩
  rw [Option.mem_some_iff] at hl
  exact hl ▸ hp.1 x hx

mutual

/-- If `a` is a member of a `Bounded` tree, it obeys the tree's own flanking bounds — the
ordering invariant, read as a statement about where a member key can and can't be. -/
theorem mem_bounds_of_bounded {a : α} : ∀ {lo hi : Option α} {t : BTree α}, Bounded lo hi t →
    Mem a t → (∀ l ∈ lo, l < a) ∧ (∀ h ∈ hi, a < h)
  | lo, hi, leaf _, hb, ha => by
      obtain ⟨_, hlo, hhi⟩ := hb
      exact ⟨fun l hl => hlo l hl a ha, fun h hh => hhi h hh a ha⟩
  | lo, hi, node _ _, hb, ha => by
      obtain ⟨hbk, _, hcs⟩ := hb
      rcases ha with ha | ha
      · obtain ⟨_, hlo, hhi⟩ := hbk
        exact ⟨fun l hl => hlo l hl a ha, fun h hh => hhi h hh a ha⟩
      · exact memChildren_bounds_of_bounded hbk hcs ha

/-- Companion to `mem_bounds_of_bounded`, descending along a node's keys/children in lockstep —
the same shape `boundsList`/`BoundedChildren` themselves walk. Carries `BoundedKeys lo hi ks`
(not just the `BoundedChildren` part) because relating a deeply-nested child's own flanking bound
back to the outer `(lo, hi)` needs the key `k` in between to be related to both. -/
theorem memChildren_bounds_of_bounded {a lo hi} :
    ∀ {ks : List α} {cs : List (BTree α)}, BoundedKeys lo hi ks →
      BoundedChildren (boundsList lo hi ks) cs → MemChildren a cs →
      (∀ l ∈ lo, l < a) ∧ (∀ h ∈ hi, a < h)
  | [], cs, _, hcs, ha => by
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
      exact mem_bounds_of_bounded hc (by simpa using ha)
  | k :: ks, cs, hbk, hcs, ha => by
      simp only [boundsList] at hcs
      match cs, hcs with
      | c :: cs, ⟨hc, hcs'⟩ =>
        rw [memChildren_cons] at ha
        rcases ha with ha | ha
        · obtain ⟨_, _, hhi⟩ := hbk
          obtain ⟨hla, hah⟩ := mem_bounds_of_bounded hc ha
          exact ⟨hla, fun h hh => lt_trans (hah k rfl) (hhi h hh k (List.mem_cons_self ..))⟩
        · have hlo := hbk.2.1
          obtain ⟨hla, hah⟩ :=
            memChildren_bounds_of_bounded (BoundedKeys.of_cons hbk) hcs' ha
          exact ⟨fun l hl => lt_trans (hlo l hl k (List.mem_cons_self ..)) (hla k rfl), hah⟩

end

omit [LinearOrder α] in
/-- Dropping a child cannot raise the tallest height among them. -/
theorem childrenHeight_le_cons (c : BTree α) :
    ∀ cs : List (BTree α), childrenHeight cs ≤ childrenHeight (c :: cs)
  | [] => by simp [childrenHeight]
  | c' :: cs' => by
      simp only [childrenHeight]
      exact Nat.le_max_right _ _

/-! ## `toList`: the tree's contents, independent of its shape

`toList` (in `Spec.lean`) is the observation a cross-implementation check compares, since two
correct implementations may build differently shaped trees; `mem_toList` is what makes agreement
on it evidence about `Mem`, and `length_toList` evidence about `size`. -/

omit [LinearOrder α] in
@[simp] theorem toList_leaf (ks : List α) : toList (leaf ks) = ks := rfl

omit [LinearOrder α] in
@[simp] theorem toList_node (ks : List α) (cs : List (BTree α)) :
    toList (node ks cs) = childrenToList ks cs := rfl

omit [LinearOrder α] in
mutual

/-- **`toList` observes exactly `Mem`.** Without this, agreement between two implementations'
in-order traversals would be evidence about a lookalike; with it, it is evidence about the
predicate `search_correct` and `InsertMem` are stated with. -/
theorem mem_toList (a : α) : ∀ t : BTree α, a ∈ toList t ↔ Mem a t
  | leaf _ => Iff.rfl
  | node ks cs => mem_childrenToList a ks cs

/-- The lockstep companion to `mem_toList`. -/
theorem mem_childrenToList (a : α) :
    ∀ (ks : List α) (cs : List (BTree α)),
      a ∈ childrenToList ks cs ↔ (a ∈ ks ∨ MemChildren a cs)
  | k :: ks, c :: cs => by
      simp only [childrenToList, List.mem_append, List.mem_cons, memChildren_cons,
        mem_toList a c, mem_childrenToList a ks cs]
      tauto
  | [], c :: cs => by
      simp only [childrenToList, List.mem_append, memChildren_cons,
        mem_toList a c, mem_childrenToList a [] cs]
      tauto
  | ks, [] => by simp [childrenToList]

end

omit [LinearOrder α] in
mutual

/-- `toList` loses nothing: its length is the tree's `size`, so a cross-implementation `len()`
comparison is evidence about `size`, which the occupancy bounds are stated with. -/
theorem length_toList : ∀ t : BTree α, (toList t).length = size t
  | leaf _ => rfl
  | node ks cs => length_childrenToList ks cs

/-- The lockstep companion to `length_toList`. -/
theorem length_childrenToList :
    ∀ (ks : List α) (cs : List (BTree α)),
      (childrenToList ks cs).length = ks.length + sizeChildren cs
  | k :: ks, c :: cs => by
      simp only [childrenToList, List.length_append, List.length_cons,
        length_toList c, length_childrenToList ks cs, sizeChildren_cons]
      omega
  | [], c :: cs => by
      simp only [childrenToList, List.length_append,
        length_toList c, length_childrenToList [] cs, sizeChildren_cons]
      simp
  | ks, [] => by simp [childrenToList]

end

/-! ## One more child than keys

`OneMoreChild`, box invariant 2. `Bounded` carries it too (`Bounded.arity`), but the depth and
occupancy proofs need it on its own, without dragging the ordering bounds through every step. -/

omit [LinearOrder α] in
@[simp] theorem arity_leaf (ks : List α) : OneMoreChild (leaf ks) := trivial

omit [LinearOrder α] in
@[simp] theorem arity_node (ks : List α) (cs : List (BTree α)) :
    OneMoreChild (node ks cs) ↔ (cs.length = ks.length + 1 ∧ ChildrenOneMoreChild cs) :=
  Iff.rfl

omit [LinearOrder α] in
@[simp] theorem arityChildren_nil : ChildrenOneMoreChild ([] : List (BTree α)) := trivial

omit [LinearOrder α] in
@[simp] theorem arityChildren_cons (c : BTree α) (cs : List (BTree α)) :
    ChildrenOneMoreChild (c :: cs) ↔ (OneMoreChild c ∧ ChildrenOneMoreChild cs) := Iff.rfl

omit [LinearOrder α] in
theorem arityChildren_take : ∀ {cs : List (BTree α)}, ChildrenOneMoreChild cs →
    ∀ n, ChildrenOneMoreChild (cs.take n)
  | [], _, n => by simp
  | c :: cs, h, n => by
      cases n with
      | zero => simp
      | succ n => exact ⟨h.1, arityChildren_take h.2 n⟩

omit [LinearOrder α] in
theorem arityChildren_drop : ∀ {cs : List (BTree α)}, ChildrenOneMoreChild cs →
    ∀ n, ChildrenOneMoreChild (cs.drop n)
  | [], _, n => by simp
  | c :: cs, h, n => by
      cases n with
      | zero => exact h
      | succ n => exact arityChildren_drop h.2 n

mutual

/-- `Bounded` already says it; this is the projection. -/
theorem Bounded.arity :
    ∀ {lo hi : Option α} {t : BTree α}, Bounded lo hi t → OneMoreChild t
  | _, _, leaf _, _ => trivial
  | _, _, node _ _, h => ⟨h.2.1, BoundedChildren.arity h.2.2⟩

/-- The list companion to `Bounded.arity`. -/
theorem BoundedChildren.arity :
    ∀ {bs : List (Option α × Option α)} {cs : List (BTree α)}, BoundedChildren bs cs →
      ChildrenOneMoreChild cs
  | [], [], _ => trivial
  | (lo, hi) :: bs, c :: cs, h => ⟨Bounded.arity h.1, BoundedChildren.arity h.2⟩
  | [], _ :: _, h => absurd h (by simp [BoundedChildren])
  | _ :: _, [], h => absurd h (by simp [BoundedChildren])

end

/-! ## Depth: every leaf stays at the same level

A split is the only operation here that changes a path length, and it changes *every* path by the
same amount — which is the whole reason a B-tree is balanced without a rebalancing step. -/

omit [LinearOrder α] in
theorem childrenDepth?_of_forall : ∀ {cs : List (BTree α)} {d : ℕ}, cs ≠ [] →
    (∀ c ∈ cs, c.depth? = some d) → childrenDepth? cs = some d
  | [c], d, _, h => by simpa [childrenDepth?] using h c (by simp)
  | c :: c2 :: cs, d, _, h => by
      simp only [childrenDepth?]
      rw [h c (by simp), childrenDepth?_of_forall (by simp) (fun x hx => h x (by simp [hx]))]
      simp

omit [LinearOrder α] in
theorem childrenDepth?_take {cs : List (BTree α)} {d n : ℕ} (h : childrenDepth? cs = some d)
    (hn : 0 < n) (hcs : cs ≠ []) : childrenDepth? (cs.take n) = some d :=
  childrenDepth?_of_forall
    (by cases cs with
        | nil => exact absurd rfl hcs
        | cons c cs => cases n with
          | zero => omega
          | succ n => simp)
    (fun c hc => childrenDepth?_uniform h (List.mem_of_mem_take hc))

omit [LinearOrder α] in
theorem childrenDepth?_drop {cs : List (BTree α)} {d n : ℕ} (h : childrenDepth? cs = some d)
    (hn : n < cs.length) : childrenDepth? (cs.drop n) = some d :=
  childrenDepth?_of_forall
    (by intro hnil; rw [← List.length_eq_zero_iff, List.length_drop] at hnil; omega)
    (fun c hc => childrenDepth?_uniform h (List.mem_of_mem_drop hc))

/-! ## Occupancy: how full every node stays

The bound that makes the idle-space argument work. A node overflows at exactly `2 * deg` keys,
and the split hands `deg - 1` keys left, `deg` keys right, and one key up — so both halves land
inside `[deg - 1, 2 * deg - 1]` with nothing to spare on the low side. -/

omit [LinearOrder α] in
@[simp] theorem childrenKeyCountOk_nil (deg : ℕ) :
    ChildrenKeyCountOk deg ([] : List (BTree α)) := trivial

omit [LinearOrder α] in
@[simp] theorem childrenKeyCountOk_cons (deg : ℕ) (c : BTree α) (cs : List (BTree α)) :
    ChildrenKeyCountOk deg (c :: cs) ↔ (KeyCountOk deg false c ∧ ChildrenKeyCountOk deg cs) :=
  Iff.rfl

omit [LinearOrder α] in
theorem childrenKeyCountOk_take {deg : ℕ} : ∀ {cs : List (BTree α)}, ChildrenKeyCountOk deg cs →
    ∀ n, ChildrenKeyCountOk deg (cs.take n)
  | [], _, n => by simp
  | c :: cs, h, n => by
      cases n with
      | zero => simp
      | succ n => exact ⟨h.1, childrenKeyCountOk_take h.2 n⟩

omit [LinearOrder α] in
theorem childrenKeyCountOk_drop {deg : ℕ} : ∀ {cs : List (BTree α)}, ChildrenKeyCountOk deg cs →
    ∀ n, ChildrenKeyCountOk deg (cs.drop n)
  | [], _, n => by simp
  | c :: cs, h, n => by
      cases n with
      | zero => exact h
      | succ n => exact childrenKeyCountOk_drop h.2 n

/-! ## Ordering: the bounds a split hands to its two halves

The promoted median is what separates them: everything left of it keeps the old lower bound and
gains `m` as its upper bound, everything right of it gains `m` as its lower bound and keeps the
old upper one. `boundsList_append` is the statement that `boundsList` already agrees. -/

omit [LinearOrder α] in
theorem boundsList_length (lo hi : Option α) :
    ∀ ks : List α, (boundsList lo hi ks).length = ks.length + 1
  | [] => rfl
  | k :: ks => by simp [boundsList, boundsList_length (some k) hi ks]

omit [LinearOrder α] in
theorem boundsList_append (lo hi : Option α) (m : α) :
    ∀ (ks₁ ks₂ : List α), boundsList lo hi (ks₁ ++ m :: ks₂) =
      boundsList lo (some m) ks₁ ++ boundsList (some m) hi ks₂
  | [], ks₂ => by simp [boundsList]
  | k :: ks₁, ks₂ => by
      simp [boundsList, boundsList_append (some k) hi m ks₁ ks₂]

theorem boundedChildren_append :
    ∀ {bs₁ : List (Option α × Option α)} {cs₁ : List (BTree α)}, bs₁.length = cs₁.length →
      ∀ {bs₂ : List (Option α × Option α)} {cs₂ : List (BTree α)},
        (BoundedChildren (bs₁ ++ bs₂) (cs₁ ++ cs₂) ↔
          BoundedChildren bs₁ cs₁ ∧ BoundedChildren bs₂ cs₂)
  | [], [], _, bs₂, cs₂ => by
      simp only [List.nil_append]
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | b :: bs₁, c :: cs₁, h, bs₂, cs₂ => by
      obtain ⟨lo, hi⟩ := b
      simp only [List.cons_append, BoundedChildren,
        boundedChildren_append (by simpa using h) (bs₂ := bs₂) (cs₂ := cs₂)]
      tauto
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-! ## Shared by insertion and deletion

A subtree sitting legally where it sits (`Legal`), and two small facts both updates' proofs use;
the keys a node holds itself are `keys` (`Spec.lean`). -/

/-- A `Valid` tree's keys are distinct, because its ordering invariant is a strict `Pairwise`. -/
theorem nodup_of_boundedKeys {lo hi : Option α} {ks : List α} (h : BoundedKeys lo hi ks) :
    ks.Nodup := h.1.imp (fun hlt => ne_of_lt hlt)

omit [LinearOrder α] in
theorem childrenHeight_le_of_mem_imp :
    ∀ {cs₁ cs₂ : List (BTree α)}, (∀ c ∈ cs₁, c ∈ cs₂) → childrenHeight cs₁ ≤ childrenHeight cs₂
  | [], _, _ => by simp [childrenHeight]
  | [c], _, h => by
      simpa [childrenHeight] using height_le_childrenHeight_of_mem (h c (by simp))
  | c :: c' :: cs, _, h => by
      simp only [childrenHeight]
      refine max_le (height_le_childrenHeight_of_mem (h c (by simp))) ?_
      exact childrenHeight_le_of_mem_imp (fun x hx => h x (by simp [hx]))

/-- A subtree sitting legally where it sits: correctly ordered between its flanking keys, every
leaf at depth `dep`, and inside the non-root occupancy bounds. -/
def Legal (deg : ℕ) (lo hi : Option α) (dep : ℕ) (t : BTree α) : Prop :=
  Bounded lo hi t ∧ depth? t = some dep ∧ KeyCountOk deg false t

end BTree

end AlgoDesign.Searching
