/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Insert

/-!
# B-tree: the deletion algorithm

CLRS §18.3's borrow-and-merge: `ensureSpare` tops up a
thin child by borrowing (`borrowLeft`/`borrowRight`) or merging (`mergeNodes`) before the descent
enters it, `takeMax`/`takeMin` lift out a predecessor or successor, `delRec` is the descent, and
`delete` finishes with `collapseRoot`. The height lemmas are here because `delRec`'s termination
needs them. That `delete` discharges `DeleteSpec` is `deleteSpec`, in `Delete.lean`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-! ## `delete`: CLRS §18.3's borrow-and-merge

Never descend into a node holding only `deg - 1` keys without first giving it a spare one, by
borrowing through the separator from a sibling that can afford it, or else merging the two
siblings around the separator. A key found in an internal node is replaced by its predecessor or
successor, whichever side can spare it. The descent runs on height
(`ensureSpare_target_height`). -/

/-- Can this node give a key away without dropping below the `deg - 1` floor? -/
def hasSpare (deg : ℕ) (t : Node α) : Bool := decide (deg ≤ (nodeKeys t).length)

/-- Rotate the left sibling's last key up into the separator slot and the old separator down into
the target — CLRS's borrow-from-left. The sibling's last child comes with it. -/
def borrowLeft : Node α → α → Node α → Option (Node α × α × Node α)
  | leaf lk, s, leaf ck =>
      match lk.getLast? with
      | none => none
      | some b => some (leaf lk.dropLast, b, leaf (s :: ck))
  | node lk lc, s, node ck cc =>
      match lk.getLast?, lc.getLast? with
      | some b, some bc =>
          some (node lk.dropLast lc.dropLast, b, node (s :: ck) (bc :: cc))
      | _, _ => none
  | _, _, _ => none

/-- The mirror image: the right sibling's first key rotates up, the separator comes down. -/
def borrowRight : Node α → α → Node α → Option (Node α × α × Node α)
  | leaf ck, s, leaf (b :: rk) => some (leaf (ck ++ [s]), b, leaf rk)
  | node ck cc, s, node (b :: rk) (bc :: rc) =>
      some (node (ck ++ [s]) (cc ++ [bc]), b, node rk rc)
  | _, _, _ => none

/-- Merge two siblings around the separator that divided them. Two minimal nodes give
`(deg - 1) + 1 + (deg - 1) = 2 * deg - 1` keys, exactly the ceiling, so this never overflows. -/
def mergeNodes : Node α → α → Node α → Node α
  | leaf lk, s, leaf rk => leaf (lk ++ s :: rk)
  | node lk lc, s, node rk rc => node (lk ++ s :: rk) (lc ++ rc)
  | l, _, _ => l

/-- A node opened up at the child the descent is about to enter: the node is
`node (keysL ++ keysR) (childrenL ++ target :: childrenR)`. Keeping both sides explicit is what
lets the fix-up reach the target's left sibling, which a left-to-right walk has already passed. -/
structure Spot (α : Type) where
  /-- The keys left of the target. -/
  keysL : List α
  /-- The children left of the target. -/
  childrenL : List (Node α)
  /-- The child the descent enters. -/
  target : Node α
  /-- The keys right of the target. -/
  keysR : List α
  /-- The children right of the target. -/
  childrenR : List (Node α)

/-- Put a `Spot` back together. -/
def Spot.node (sp : Spot α) : Node α :=
  Node.node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)

/-- Borrow from the left sibling: its last key rises into the separator slot, the old separator
drops into the target. -/
def borrowLeftSpot (sp : Spot α) : Option (Spot α) :=
  match sp.childrenL.getLast?, sp.keysL.getLast? with
  | some l, some s =>
      match borrowLeft l s sp.target with
      | some (l', s', t') =>
          some { sp with keysL := sp.keysL.dropLast ++ [s'],
                         childrenL := sp.childrenL.dropLast ++ [l'], target := t' }
      | none => none
  | _, _ => none

/-- The mirror image, borrowing from the right sibling. -/
def borrowRightSpot (sp : Spot α) : Option (Spot α) :=
  match sp.keysR, sp.childrenR with
  | s :: kr, r :: cr =>
      match borrowRight sp.target s r with
      | some (t', s', r') => some { sp with target := t', keysR := s' :: kr, childrenR := r' :: cr }
      | none => none
  | _, _ => none

/-- Absorb the target into its left sibling, pulling the separator down between them. -/
def mergeLeftSpot (sp : Spot α) : Option (Spot α) :=
  match sp.childrenL.getLast?, sp.keysL.getLast? with
  | some l, some s =>
      some { sp with keysL := sp.keysL.dropLast, childrenL := sp.childrenL.dropLast,
                     target := mergeNodes l s sp.target }
  | _, _ => none

/-- Absorb the right sibling into the target, pulling the separator down between them. -/
def mergeRightSpot (sp : Spot α) : Option (Spot α) :=
  match sp.keysR, sp.childrenR with
  | s :: kr, r :: cr =>
      some { sp with target := mergeNodes sp.target s r, keysR := kr, childrenR := cr }
  | _, _ => none

/-- Give the target a spare key if it has none: borrow from the left sibling, else from the
right, else merge, with the left if there is one, otherwise the right. Rust:
`top_up`. -/
def ensureSpare (deg : ℕ) (sp : Spot α) : Spot α :=
  if hasSpare deg sp.target then sp
  else
    match sp.childrenL.getLast? with
    | some l =>
        if hasSpare deg l then (borrowLeftSpot sp).getD sp
        else
          match sp.childrenR with
          | r :: _ =>
              if hasSpare deg r then (borrowRightSpot sp).getD sp
              else (mergeLeftSpot sp).getD sp
          | [] => (mergeLeftSpot sp).getD sp
    | none =>
        match sp.childrenR with
        | r :: _ =>
            if hasSpare deg r then (borrowRightSpot sp).getD sp
            else (mergeRightSpot sp).getD sp
        | [] => sp

/-! ## Heights: nothing the fix-up does makes a subtree taller

The descent is not structurally recursive — a merged node is freshly built — so it runs on
height, the same way `insNonfull` does. These are the lemmas that make that go through. -/

omit [LinearOrder α] in
theorem childrenHeight_append_le : ∀ (xs ys : List (Node α)),
    childrenHeight (xs ++ ys) ≤ max (childrenHeight xs) (childrenHeight ys)
  | [], ys => by simp [childrenHeight]
  | [x], ys => by
      cases ys with
      | nil => simp [childrenHeight]
      | cons y ys => simp only [List.cons_append, List.nil_append, childrenHeight]; omega
  | x :: x' :: xs, ys => by
      have ih := childrenHeight_append_le (x' :: xs) ys
      simp only [List.cons_append, childrenHeight] at ih ⊢
      omega

omit [LinearOrder α] in
theorem childrenHeight_dropLast_le (cs : List (Node α)) :
    childrenHeight cs.dropLast ≤ childrenHeight cs :=
  childrenHeight_le_of_mem_imp (fun _ hc => List.dropLast_subset _ hc)

omit [LinearOrder α] in
theorem mergeNodes_height (l : Node α) (s : α) (r : Node α) :
    (mergeNodes l s r).height ≤ max l.height r.height := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => simp [mergeNodes]
      | node rk rc => simp [mergeNodes]
  | node lk lc =>
      cases r with
      | leaf rk => simp [mergeNodes]
      | node rk rc =>
          simp only [mergeNodes, height_node]
          have := childrenHeight_append_le lc rc
          omega

omit [LinearOrder α] in
theorem borrowLeft_height {l : Node α} {s : α} {c l' t' : Node α} {s' : α}
    (h : borrowLeft l s c = some (l', s', t')) :
    l'.height ≤ l.height ∧ t'.height ≤ max l.height c.height := by
  cases l with
  | leaf lk =>
      cases c with
      | leaf ck =>
          simp only [borrowLeft] at h
          cases hg : lk.getLast? with
          | none => rw [hg] at h; exact absurd h (by simp)
          | some b =>
              rw [hg] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hl, -, ht⟩ := h
              subst hl; subst ht; simp
      | node ck cc => simp only [borrowLeft] at h; exact absurd h (by simp)
  | node lk lc =>
      cases c with
      | leaf ck => simp only [borrowLeft] at h; exact absurd h (by simp)
      | node ck cc =>
          simp only [borrowLeft] at h
          cases hk : lk.getLast? with
          | none => rw [hk] at h; simp at h
          | some b =>
              cases hc : lc.getLast? with
              | none => rw [hk, hc] at h; simp at h
              | some bc =>
                  rw [hk, hc] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hl, -, ht⟩ := h
                  subst hl; subst ht
                  have hbc : bc ∈ lc := List.mem_of_getLast? hc
                  have h1 : bc.height ≤ childrenHeight lc :=
                    height_le_childrenHeight_of_mem hbc
                  refine ⟨?_, ?_⟩
                  · simp only [height_node]
                    have := childrenHeight_dropLast_le lc
                    omega
                  · simp only [height_node]
                    cases cc with
                    | nil => simp only [childrenHeight]; omega
                    | cons c₁ cc' => simp only [childrenHeight]; omega

omit [LinearOrder α] in
theorem borrowRight_height {c : Node α} {s : α} {r t' r' : Node α} {s' : α}
    (h : borrowRight c s r = some (t', s', r')) :
    t'.height ≤ max c.height r.height ∧ r'.height ≤ r.height := by
  cases c with
  | leaf ck =>
      cases r with
      | leaf rk =>
          cases rk with
          | nil => simp only [borrowRight] at h; exact absurd h (by simp)
          | cons b rk' =>
              simp only [borrowRight, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨ht, -, hr⟩ := h
              subst ht; subst hr; simp
      | node rk rc => simp only [borrowRight] at h; exact absurd h (by simp)
  | node ck cc =>
      cases r with
      | leaf rk => simp only [borrowRight] at h; exact absurd h (by simp)
      | node rk rc =>
          cases rk with
          | nil => simp only [borrowRight] at h; exact absurd h (by simp)
          | cons b rk' =>
              cases rc with
              | nil => simp only [borrowRight] at h; exact absurd h (by simp)
              | cons bc rc' =>
                  simp only [borrowRight, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨ht, -, hr⟩ := h
                  subst ht; subst hr
                  refine ⟨?_, ?_⟩
                  · simp only [height_node]
                    have h1 := childrenHeight_append_le cc [bc]
                    simp only [childrenHeight] at h1
                    have h2 : bc.height ≤ childrenHeight (bc :: rc') := by
                      exact height_le_childrenHeight_of_mem (by simp)
                    omega
                  · simp only [height_node]
                    have : childrenHeight rc' ≤ childrenHeight (bc :: rc') :=
                      childrenHeight_le_cons bc rc'
                    omega

/-- The children a `Spot` holds, as one list. -/
def Spot.children (sp : Spot α) : List (Node α) := sp.childrenL ++ sp.target :: sp.childrenR

omit [LinearOrder α] in
theorem Spot.target_height_le (sp : Spot α) :
    sp.target.height ≤ childrenHeight sp.children :=
  height_le_childrenHeight_of_mem (by simp [Spot.children])

omit [LinearOrder α] in
theorem Spot.left_height_le {sp : Spot α} {l : Node α} (h : sp.childrenL.getLast? = some l) :
    l.height ≤ childrenHeight sp.children :=
  height_le_childrenHeight_of_mem (by
    simp only [Spot.children, List.mem_append]
    exact Or.inl (List.mem_of_getLast? h))

omit [LinearOrder α] in
theorem Spot.right_height_le {sp : Spot α} {r : Node α} {cr : List (Node α)}
    (h : sp.childrenR = r :: cr) : r.height ≤ childrenHeight sp.children :=
  height_le_childrenHeight_of_mem (by simp [Spot.children, h])

omit [LinearOrder α] in
theorem borrowLeftSpot_height {sp sp' : Spot α} (h : borrowLeftSpot sp = some sp') :
    sp'.target.height ≤ childrenHeight sp.children := by
  simp only [borrowLeftSpot] at h
  cases hl : sp.childrenL.getLast? with
  | none => rw [hl] at h; simp at h
  | some l =>
      cases hs : sp.keysL.getLast? with
      | none => rw [hl, hs] at h; simp at h
      | some s =>
          rw [hl, hs] at h
          dsimp only at h
          cases hb : borrowLeft l s sp.target with
          | none => rw [hb] at h; exact absurd h (by simp)
          | some q =>
              obtain ⟨l', s', t'⟩ := q
              rw [hb] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨-, ht⟩ := borrowLeft_height hb
              have h1 := Spot.left_height_le (sp := sp) hl
              have h2 := Spot.target_height_le sp
              simp only []
              omega

omit [LinearOrder α] in
theorem borrowRightSpot_height {sp sp' : Spot α} (h : borrowRightSpot sp = some sp') :
    sp'.target.height ≤ childrenHeight sp.children := by
  simp only [borrowRightSpot] at h
  cases hk : sp.keysR with
  | nil => rw [hk] at h; simp at h
  | cons s kr =>
      cases hc : sp.childrenR with
      | nil => rw [hk, hc] at h; simp at h
      | cons r cr =>
          rw [hk, hc] at h
          dsimp only at h
          cases hb : borrowRight sp.target s r with
          | none => rw [hb] at h; exact absurd h (by simp)
          | some q =>
              obtain ⟨t', s', r'⟩ := q
              rw [hb] at h
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨ht, -⟩ := borrowRight_height hb
              have h1 := Spot.right_height_le (sp := sp) hc
              have h2 := Spot.target_height_le sp
              simp only []
              omega

omit [LinearOrder α] in
theorem mergeLeftSpot_height {sp sp' : Spot α} (h : mergeLeftSpot sp = some sp') :
    sp'.target.height ≤ childrenHeight sp.children := by
  simp only [mergeLeftSpot] at h
  cases hl : sp.childrenL.getLast? with
  | none => rw [hl] at h; simp at h
  | some l =>
      cases hs : sp.keysL.getLast? with
      | none => rw [hl, hs] at h; simp at h
      | some s =>
          rw [hl, hs] at h
          simp only [Option.some.injEq] at h
          subst h
          have h1 := Spot.left_height_le (sp := sp) hl
          have h2 := Spot.target_height_le sp
          have h3 := mergeNodes_height l s sp.target
          simp only []
          omega

omit [LinearOrder α] in
theorem mergeRightSpot_height {sp sp' : Spot α} (h : mergeRightSpot sp = some sp') :
    sp'.target.height ≤ childrenHeight sp.children := by
  simp only [mergeRightSpot] at h
  cases hk : sp.keysR with
  | nil => rw [hk] at h; simp at h
  | cons s kr =>
      cases hc : sp.childrenR with
      | nil => rw [hk, hc] at h; simp at h
      | cons r cr =>
          rw [hk, hc] at h
          simp only [Option.some.injEq] at h
          subst h
          have h1 := Spot.right_height_le (sp := sp) hc
          have h2 := Spot.target_height_le sp
          have h3 := mergeNodes_height sp.target s r
          simp only []
          omega

omit [LinearOrder α] in
/-- **The fix-up never makes the target taller than the children it came from.** This is what
lets the descent recurse on height. -/
theorem ensureSpare_target_height (deg : ℕ) (sp : Spot α) :
    (ensureSpare deg sp).target.height ≤ childrenHeight sp.children := by
  have hT := Spot.target_height_le sp
  unfold ensureSpare
  split_ifs with h1
  · exact hT
  · cases hl : sp.childrenL.getLast? with
    | none =>
        dsimp only
        cases hc : sp.childrenR with
        | nil => exact hT
        | cons r cr =>
            dsimp only
            split_ifs with h2
            · cases hb : borrowRightSpot sp with
              | none => simpa [hb] using hT
              | some sp' => simpa [hb] using borrowRightSpot_height hb
            · cases hm : mergeRightSpot sp with
              | none => simpa [hm] using hT
              | some sp' => simpa [hm] using mergeRightSpot_height hm
    | some l =>
        dsimp only
        split_ifs with h2
        · cases hb : borrowLeftSpot sp with
          | none => simpa [hb] using hT
          | some sp' => simpa [hb] using borrowLeftSpot_height hb
        · cases hc : sp.childrenR with
          | nil =>
              dsimp only
              cases hm : mergeLeftSpot sp with
              | none => simpa [hm] using hT
              | some sp' => simpa [hm] using mergeLeftSpot_height hm
          | cons r cr =>
              dsimp only
              split_ifs with h3
              · cases hb : borrowRightSpot sp with
                | none => simpa [hb] using hT
                | some sp' => simpa [hb] using borrowRightSpot_height hb
              · cases hm : mergeLeftSpot sp with
                | none => simpa [hm] using hT
                | some sp' => simpa [hm] using mergeLeftSpot_height hm

/-! ## Taking the extreme key out of a subtree -/

omit [LinearOrder α] in
theorem dropLast_append_getLast : ∀ {l : List (Node α)} {a : Node α}, l.getLast? = some a →
    l.dropLast ++ [a] = l
  | [], a, h => by simp at h
  | [x], a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h; simp
  | x :: y :: l, a, h => by
      simp only [List.getLast?_cons_cons] at h
      have ih := dropLast_append_getLast h
      simp only [List.dropLast_cons_cons, List.cons_append, ih]

/-- Remove and return the largest key — the in-order predecessor of a key sitting just above it.
Every node on the way down is given a spare key first, by the same discipline `delRec` follows,
so the result is legal by the same argument. -/
def takeMax (deg : ℕ) : Node α → Node α × Option α
  | leaf ks =>
      match ks.getLast? with
      | none => (leaf ks, none)
      | some m => (leaf ks.dropLast, some m)
  | node ks cs =>
      match _hc : cs.getLast? with
      | none => (node ks cs, none)
      | some c =>
          let sp := ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩
          let res := takeMax deg sp.target
          (({ sp with target := res.1 } : Spot α).node, res.2)
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast _hc
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The mirror image: remove and return the smallest key, a deleted key's in-order successor. -/
def takeMin (deg : ℕ) : Node α → Node α × Option α
  | leaf ks =>
      match ks with
      | [] => (leaf ks, none)
      | m :: ks' => (leaf ks', some m)
  | node ks cs =>
      match _hc : cs with
      | [] => (node ks cs, none)
      | c :: cs' =>
          let sp := ensureSpare deg ⟨[], [], c, ks, cs'⟩
          let res := takeMin deg sp.target
          (({ sp with target := res.1 } : Spot α).node, res.2)
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

/-! ## `delete` -/

/-- Where `a` belongs among a node's keys: the number of keys strictly below it. -/
def slot (a : α) (ks : List α) : ℕ := (ks.takeWhile (· < a)).length

/-- The descent. The node is the root or already holds a spare key, so no key is ever taken from
a node that cannot afford it. Returns the rebuilt subtree and whether `a` was found. Rust:
`delete_rec`. -/
def delRec (deg : ℕ) (a : α) : Node α → Node α × Bool
  | leaf ks => (leaf (ks.erase a), decide (a ∈ ks))
  | node ks cs =>
      match _hkr : ks.drop (slot a ks), _hcr : cs.drop (slot a ks) with
      | k :: kr, c :: r :: rest =>
          if a < k then
            -- `a` is not here; descend into the child before `k`, after giving it a spare key.
            let sp := ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr,
                                       r :: rest⟩
            let res := delRec deg a sp.target
            (({ sp with target := res.1 } : Spot α).node, res.2)
          else
            -- `k = a`: the key is in this node. Replace it by a neighbour that can be spared, or
            -- merge its two children around it and delete from the merge.
            if hasSpare deg c then
              match takeMax deg c with
              | (c', some pred) =>
                  (node (ks.take (slot a ks) ++ pred :: kr)
                        (cs.take (slot a ks) ++ c' :: r :: rest), true)
              | (_, none) => (node ks cs, true)
            else if hasSpare deg r then
              match takeMin deg r with
              | (r', some succ) =>
                  (node (ks.take (slot a ks) ++ succ :: kr)
                        (cs.take (slot a ks) ++ c :: r' :: rest), true)
              | (_, none) => (node ks cs, true)
            else
              let res := delRec deg a (mergeNodes c k r)
              (node (ks.take (slot a ks) ++ kr)
                    (cs.take (slot a ks) ++ res.1 :: rest), res.2)
      | [], [c] =>
          -- every key is below `a`: the last child is where it would be.
          let sp := ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩
          let res := delRec deg a sp.target
          (({ sp with target := res.1 } : Spot α).node, res.2)
      | _, _ => (node ks cs, false)
  termination_by t => t.height
  decreasing_by
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
    · have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      simp only [height_node]
      omega
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega

/-- An internal root with no keys has exactly one child, and the tree has lost a level: the child
becomes the root. The only place a B-tree's height ever decreases, mirroring the root split that
is the only place it increases. -/
def collapseRoot : Node α → Node α
  | node [] [c] => c
  | t => t

/-- **Delete a key from a B-tree, CLRS §18.3.** -/
def delete (deg : ℕ) (a : α) (bt : Node α) : Node α × Bool :=
  let res := delRec deg a bt
  (collapseRoot res.1, res.2)

end BTree.Node

end AlgoDesign.Searching
