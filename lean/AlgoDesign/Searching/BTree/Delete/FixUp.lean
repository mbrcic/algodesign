/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete.Borrow

/-!
# B-tree deletion: the fix-up

`ensureSpare_spec`: topping up a thin child before the descent enters it — by a borrow from either
side or a merge with either neighbour — keeps all five invariants, and leaves the child with a key
to spare.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## The fix-up, against all five invariants

`ensureSpare` is the whole of CLRS's delete discipline: never descend into a node with only
`deg - 1` keys without first giving it a spare. It has four moves and they are proved one at a
time, each against ordering, balance, occupancy, arity and the key set, and then composed. The
parent pays at most one key, and only on a merge — which is safe exactly because the descent
never reaches a node without a spare of its own. -/

omit [LinearOrder α] in
/-- Every non-root node carries at least the occupancy floor. -/
theorem keyCount_floor {deg : ℕ} {t : BTree α} (h : KeyCountOk deg false t) :
    deg - 1 ≤ (nodeKeys t).length := by
  cases t with
  | leaf ks => exact h.1.resolve_left (by simp)
  | node ks cs => exact h.1

omit [LinearOrder α] in
/-- Merging two minimal siblings around their separator leaves a node that can spare a key. -/
theorem hasSpare_mergeNodes {deg d : ℕ} {l r : BTree α} {s : α} (hdeg : 2 ≤ deg)
    (hdl : depth? l = some d) (hdr : depth? r = some d)
    (hl : KeyCountOk deg false l) (hr : KeyCountOk deg false r) :
    hasSpare deg (mergeNodes l s r) = true := by
  have hfl := keyCount_floor hl
  have hfr := keyCount_floor hr
  have hkeys := nodeKeys_mergeNodes (s := s) hdl hdr
  simp only [hasSpare, decide_eq_true_eq, hkeys, List.length_append, List.length_cons]
  omega

omit [LinearOrder α] in
/-- A sibling with a key to spare, at the target's depth, can always be borrowed from. -/
theorem borrowLeft_isSome {deg d : ℕ} {l c : BTree α} {s : α} (hdeg : 2 ≤ deg)
    (hdl : depth? l = some d) (hdc : depth? c = some d) (hal : OneMoreChild l)
    (hsl : hasSpare deg l = true) :
    ∃ l' s' t', borrowLeft l s c = some (l', s', t') := by
  have hlk : deg ≤ (nodeKeys l).length := by simpa [hasSpare] using hsl
  cases l with
  | leaf lk =>
      cases c with
      | leaf ck =>
          simp only [nodeKeys_leaf] at hlk
          cases hg : lk.getLast? with
          | none =>
              exfalso
              rw [List.getLast?_eq_none_iff] at hg
              subst hg; simp at hlk; omega
          | some b => exact ⟨leaf lk.dropLast, b, leaf (s :: ck), by simp [borrowLeft, hg]⟩
      | node ck cc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdl.symm
          subst this; simp [depth?] at hdc
  | node lk lc =>
      cases c with
      | leaf ck =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdc.symm
          subst this; simp [depth?] at hdl
      | node ck cc =>
          simp only [nodeKeys_node] at hlk
          obtain ⟨hlen, -⟩ := hal
          cases hg : lk.getLast? with
          | none =>
              exfalso
              rw [List.getLast?_eq_none_iff] at hg
              subst hg; simp at hlk; omega
          | some b =>
              cases hgc : lc.getLast? with
              | none =>
                  exfalso
                  rw [List.getLast?_eq_none_iff] at hgc
                  subst hgc; simp at hlen
              | some bc =>
                  exact ⟨node lk.dropLast lc.dropLast, b, node (s :: ck) (bc :: cc), by
                    simp [borrowLeft, hg, hgc]⟩

omit [LinearOrder α] in
/-- The mirror image, for the right sibling. -/
theorem borrowRight_isSome {deg d : ℕ} {c r : BTree α} {s : α} (hdeg : 2 ≤ deg)
    (hdc : depth? c = some d) (hdr : depth? r = some d) (har : OneMoreChild r)
    (hsr : hasSpare deg r = true) :
    ∃ t' s' r', borrowRight c s r = some (t', s', r') := by
  have hrk : deg ≤ (nodeKeys r).length := by simpa [hasSpare] using hsr
  cases c with
  | leaf ck =>
      cases r with
      | leaf rk =>
          cases rk with
          | nil => exfalso; simp at hrk; omega
          | cons b rk' => exact ⟨_, _, _, rfl⟩
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdc.symm
          subst this; simp [depth?] at hdr
  | node ck cc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdr.symm
          subst this; simp [depth?] at hdc
      | node rk rc =>
          simp only [nodeKeys_node] at hrk
          obtain ⟨hlen, -⟩ := har
          cases rk with
          | nil => exfalso; simp at hrk; omega
          | cons b rk' =>
              cases rc with
              | nil => exfalso; simp at hlen
              | cons bc rc' => exact ⟨_, _, _, rfl⟩

omit [LinearOrder α] in
/-- Borrowing only adds to the target: every key it held, it still holds. -/
theorem borrowLeft_target_mono {l c l' t' : BTree α} {s s' : α}
    (h : borrowLeft l s c = some (l', s', t')) (b : α) : Mem b c → Mem b t' := by
  rcases borrowLeft_cases h with ⟨lk, ck, rfl, rfl, hg, rfl, rfl⟩ |
    ⟨lk, lc, ck, cc, bc, rfl, rfl, hg, hgc, rfl, rfl⟩
  · intro hb
    simp only [mem_leaf, List.mem_cons] at hb ⊢
    exact Or.inr hb
  · intro hb
    simp only [mem_node, memChildren_cons] at hb ⊢
    tauto

omit [LinearOrder α] in
/-- The mirror image. -/
theorem borrowRight_target_mono {c r t' r' : BTree α} {s s' : α}
    (h : borrowRight c s r = some (t', s', r')) (b : α) : Mem b c → Mem b t' := by
  rcases borrowRight_cases h with ⟨ck, rk, rfl, rfl, rfl, rfl⟩ |
    ⟨ck, cc, rk, rc, bc, rfl, rfl, rfl, rfl⟩
  · intro hb
    simp only [mem_leaf, List.mem_append] at hb ⊢
    exact Or.inl hb
  · intro hb
    simp only [mem_node, memChildren_append, List.mem_append] at hb ⊢
    tauto

omit [LinearOrder α] in
/-- A node's membership, regrouped so that the three parts a borrow rearranges — the sibling, the
separator and the target — sit together and the untouched parts sit together. -/
private theorem or_regroup {X S Y C1 L T C2 : Prop} :
    ((X ∨ S ∨ Y) ∨ (C1 ∨ L ∨ T ∨ C2)) ↔ ((X ∨ Y ∨ C1 ∨ C2) ∨ (L ∨ S ∨ T)) := by
  tauto

omit [LinearOrder α] in
/-- The same regrouping after a merge, which leaves one child and no separator where a borrow
leaves two children and one. -/
private theorem or_regroup_merge {X Y C1 M C2 : Prop} :
    ((X ∨ Y) ∨ (C1 ∨ M ∨ C2)) ↔ ((X ∨ Y ∨ C1 ∨ C2) ∨ M) := by
  tauto

/-- A node opened at the child the descent is about to enter, with everything the fix-up has to
preserve: ordered between its flanking bounds, every child rooted at depth `d`, every child
inside the non-root occupancy bounds — so the opened node itself sits at depth `d + 1`, unlike
`Legal`, whose `dep` is the depth of the tree it is about — and the hole located, `childrenL` as
long as `keysL`. -/
def SpotLegal (deg : ℕ) (lo hi : Option α) (d : ℕ) (sp : Spot α) : Prop :=
  Bounded lo hi sp.node ∧ childrenDepth? sp.children = some d ∧
    ChildrenKeyCountOk deg sp.children ∧ sp.childrenL.length = sp.keysL.length

/-- Borrowing from the left sibling preserves all five invariants, gives the target a spare key,
and leaves the parent's key count alone. -/
theorem borrowLeftSpot_spec {deg d : ℕ} {lo hi : Option α} {sp : Spot α} {l : BTree α}
    (hdeg : 2 ≤ deg) (h : SpotLegal deg lo hi d sp)
    (hgl : sp.childrenL.getLast? = some l)
    (hsl : hasSpare deg l = true) (hst : hasSpare deg sp.target = false) :
    ∃ sp', borrowLeftSpot sp = some sp' ∧ SpotLegal deg lo hi d sp' ∧
      (∀ b, Mem b sp'.node ↔ Mem b sp.node) ∧
      (∀ b, Mem b sp.target → Mem b sp'.target) ∧
      hasSpare deg sp'.target = true ∧
      (nodeKeys sp'.node).length = (nodeKeys sp.node).length := by
  obtain ⟨hb, hd, hk, hlen⟩ := h
  obtain ⟨cl, hcl⟩ : ∃ cl, sp.childrenL = cl ++ [l] :=
    ⟨sp.childrenL.dropLast, (dropLast_getLast_eq hgl).symm⟩
  cases hgk : sp.keysL.getLast? with
  | none =>
      exfalso
      rw [List.getLast?_eq_none_iff] at hgk
      rw [hgk, hcl] at hlen; simp at hlen
  | some s =>
      obtain ⟨kl, hkl⟩ : ∃ kl, sp.keysL = kl ++ [s] :=
        ⟨sp.keysL.dropLast, (dropLast_getLast_eq hgk).symm⟩
      have hlen' : cl.length = kl.length := by
        rw [hcl, hkl] at hlen; simpa using hlen
      have hchild : sp.children = cl ++ l :: sp.target :: sp.childrenR := by
        simp [Spot.children, hcl]
      have hnode : sp.node = node (kl ++ s :: sp.keysR) (cl ++ l :: sp.target :: sp.childrenR) := by
        simp [Spot.node, hcl, hkl]
      have hne : sp.children ≠ [] := by rw [hchild]; simp
      have hdall : ∀ c ∈ sp.children, depth? c = some d := (childrenDepth?_iff hne).mp hd
      have hkall : ∀ c ∈ sp.children, KeyCountOk deg false c := (childrenKeyCountOk_iff _).mp hk
      have hml : l ∈ sp.children := by rw [hchild]; simp
      have hmt : sp.target ∈ sp.children := by rw [hchild]; simp
      have hdl : depth? l = some d := hdall l hml
      have hdt : depth? sp.target = some d := hdall sp.target hmt
      have hcl' : KeyCountOk deg false l := hkall l hml
      have hct : KeyCountOk deg false sp.target := hkall sp.target hmt
      rw [hnode] at hb
      obtain ⟨⟨hbl, hbt, hlos, hshi⟩, hput, -⟩ :=
        bounded_pair kl cl hlen' lo hi s sp.keysR l sp.target sp.childrenR hb
      have hal : OneMoreChild l := hbl.arity
      have hat : OneMoreChild sp.target := hbt.arity
      have hlspare : 1 ≤ (nodeKeys l).length := by
        have : deg ≤ (nodeKeys l).length := by simpa [hasSpare] using hsl
        omega
      obtain ⟨l', s', t', hbor⟩ := borrowLeft_isSome (s := s) hdeg hdl hdt hal hsl
      obtain ⟨hbl', hbt', hlos', hshi'⟩ := borrowLeft_bounded hbor hbl hbt hlos hshi
      obtain ⟨hdl', hdt'⟩ := borrowLeft_depth hbor hdl hdt hal hlspare
      obtain ⟨-, -, hcl'', hct'', hspare'⟩ :=
        borrowLeft_shape hdeg hbor hal hat hcl' hct hsl hst
      have hdkl : sp.keysL.dropLast = kl := by rw [hkl]; simp
      have hdcl : sp.childrenL.dropLast = cl := by rw [hcl]; simp
      set sp' : Spot α := { sp with keysL := sp.keysL.dropLast ++ [s'],
                                    childrenL := sp.childrenL.dropLast ++ [l'],
                                    target := t' } with hsp'
      have hnode' : sp'.node = node (kl ++ s' :: sp.keysR) (cl ++ l' :: t' :: sp.childrenR) := by
        simp [hsp', Spot.node, hdkl, hdcl]
      have hch' : sp'.children = cl ++ l' :: t' :: sp.childrenR := by
        simp [hsp', Spot.children, hdcl]
      refine ⟨sp', by simp [hsp', borrowLeftSpot, hgl, hgk, hbor], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_,
        hspare', ?_⟩
      · simpa [hnode'] using hput l' s' t' hbl' hbt' hlos' hshi'
      · rw [hch']
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | rfl | hc
        · exact hdall c (by rw [hchild]; simp [hc])
        · exact hdl'
        · exact hdt'
        · exact hdall c (by rw [hchild]; simp [hc])
      · rw [hch']
        refine (childrenKeyCountOk_iff _).mpr ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | rfl | hc
        · exact hkall c (by rw [hchild]; simp [hc])
        · exact hcl''
        · exact hct''
        · exact hkall c (by rw [hchild]; simp [hc])
      · simp [hsp', hdkl, hdcl, hlen']
      · intro b
        rw [hnode', hnode]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append,
          List.mem_cons]
        rw [or_regroup, or_regroup]
        exact or_congr Iff.rfl (borrowLeft_mem hbor b)
      · intro b hbm
        exact borrowLeft_target_mono hbor b hbm
      · rw [hnode', hnode]
        simp

/-- Borrowing from the right sibling, the mirror image. -/
theorem borrowRightSpot_spec {deg d : ℕ} {lo hi : Option α} {sp : Spot α} {r : BTree α}
    {cr : List (BTree α)} (hdeg : 2 ≤ deg) (h : SpotLegal deg lo hi d sp)
    (hcr : sp.childrenR = r :: cr)
    (hsr : hasSpare deg r = true) (hst : hasSpare deg sp.target = false) :
    ∃ sp', borrowRightSpot sp = some sp' ∧ SpotLegal deg lo hi d sp' ∧
      (∀ b, Mem b sp'.node ↔ Mem b sp.node) ∧
      (∀ b, Mem b sp.target → Mem b sp'.target) ∧
      hasSpare deg sp'.target = true ∧
      (nodeKeys sp'.node).length = (nodeKeys sp.node).length := by
  obtain ⟨hb, hd, hk, hlen⟩ := h
  have hb0 : Bounded lo hi
      (node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)) := hb
  have harity := hb0.2.1
  simp only [List.length_append, List.length_cons] at harity
  have hlenR : sp.keysR.length = sp.childrenR.length := by omega
  obtain ⟨s, kr, hkr⟩ : ∃ s kr, sp.keysR = s :: kr := by
    cases hk2 : sp.keysR with
    | nil => rw [hk2, hcr] at hlenR; simp at hlenR
    | cons s kr => exact ⟨s, kr, rfl⟩
  have hchild : sp.children = sp.childrenL ++ sp.target :: r :: cr := by
    simp [Spot.children, hcr]
  have hnode : sp.node
      = node (sp.keysL ++ s :: kr) (sp.childrenL ++ sp.target :: r :: cr) := by
    simp [Spot.node, hcr, hkr]
  have hne : sp.children ≠ [] := by rw [hchild]; simp
  have hdall : ∀ c ∈ sp.children, depth? c = some d := (childrenDepth?_iff hne).mp hd
  have hkall : ∀ c ∈ sp.children, KeyCountOk deg false c := (childrenKeyCountOk_iff _).mp hk
  have hmt : sp.target ∈ sp.children := by rw [hchild]; simp
  have hmr : r ∈ sp.children := by rw [hchild]; simp
  have hdt : depth? sp.target = some d := hdall sp.target hmt
  have hdr : depth? r = some d := hdall r hmr
  have hct : KeyCountOk deg false sp.target := hkall sp.target hmt
  have hcrk : KeyCountOk deg false r := hkall r hmr
  rw [hnode] at hb
  obtain ⟨⟨hbt, hbr, hlos, hshi⟩, hput, -⟩ :=
    bounded_pair sp.keysL sp.childrenL hlen lo hi s kr sp.target r cr hb
  have hat : OneMoreChild sp.target := hbt.arity
  have har : OneMoreChild r := hbr.arity
  obtain ⟨t', s', r', hbor⟩ := borrowRight_isSome (s := s) hdeg hdt hdr har hsr
  obtain ⟨hbt', hbr', hlos', hshi'⟩ := borrowRight_bounded hbor hbt hbr hlos hshi
  obtain ⟨hdt', hdr'⟩ := borrowRight_depth hbor hdt hdr har
  obtain ⟨-, -, hct'', hcr'', hspare'⟩ :=
    borrowRight_shape hdeg hbor hat har hct hcrk hsr hst
  set sp' : Spot α := { sp with target := t', keysR := s' :: kr,
                                childrenR := r' :: cr } with hsp'
  have hnode' : sp'.node
      = node (sp.keysL ++ s' :: kr) (sp.childrenL ++ t' :: r' :: cr) := by
    simp [hsp', Spot.node]
  have hch' : sp'.children = sp.childrenL ++ t' :: r' :: cr := by
    simp [hsp', Spot.children]
  refine ⟨sp', by simp [hsp', borrowRightSpot, hkr, hcr, hbor], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_,
    hspare', ?_⟩
  · simpa [hnode'] using hput t' s' r' hbt' hbr' hlos' hshi'
  · rw [hch']
    refine (childrenDepth?_iff (by simp)).mpr ?_
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | rfl | hc
    · exact hdall c (by rw [hchild]; simp [hc])
    · exact hdt'
    · exact hdr'
    · exact hdall c (by rw [hchild]; simp [hc])
  · rw [hch']
    refine (childrenKeyCountOk_iff _).mpr ?_
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | rfl | hc
    · exact hkall c (by rw [hchild]; simp [hc])
    · exact hct''
    · exact hcr''
    · exact hkall c (by rw [hchild]; simp [hc])
  · simpa [hsp'] using hlen
  · intro b
    rw [hnode', hnode]
    simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append, List.mem_cons]
    rw [or_regroup, or_regroup]
    exact or_congr Iff.rfl (borrowRight_mem hbor b)
  · intro b hbm
    exact borrowRight_target_mono hbor b hbm
  · rw [hnode', hnode]
    simp

/-- Merging with the left sibling preserves all five invariants and gives the target a spare key,
at the cost of one key from the parent. -/
theorem mergeLeftSpot_spec {deg d : ℕ} {lo hi : Option α} {sp : Spot α} {l : BTree α}
    (hdeg : 2 ≤ deg) (h : SpotLegal deg lo hi d sp)
    (hgl : sp.childrenL.getLast? = some l)
    (hsl : hasSpare deg l = false) (hst : hasSpare deg sp.target = false) :
    ∃ sp', mergeLeftSpot sp = some sp' ∧ SpotLegal deg lo hi d sp' ∧
      (∀ b, Mem b sp'.node ↔ Mem b sp.node) ∧
      (∀ b, Mem b sp.target → Mem b sp'.target) ∧
      hasSpare deg sp'.target = true ∧
      (nodeKeys sp'.node).length + 1 = (nodeKeys sp.node).length := by
  obtain ⟨hb, hd, hk, hlen⟩ := h
  obtain ⟨cl, hcl⟩ : ∃ cl, sp.childrenL = cl ++ [l] :=
    ⟨sp.childrenL.dropLast, (dropLast_getLast_eq hgl).symm⟩
  cases hgk : sp.keysL.getLast? with
  | none =>
      exfalso
      rw [List.getLast?_eq_none_iff] at hgk
      rw [hgk, hcl] at hlen; simp at hlen
  | some s =>
      obtain ⟨kl, hkl⟩ : ∃ kl, sp.keysL = kl ++ [s] :=
        ⟨sp.keysL.dropLast, (dropLast_getLast_eq hgk).symm⟩
      have hlen' : cl.length = kl.length := by
        rw [hcl, hkl] at hlen; simpa using hlen
      have hchild : sp.children = cl ++ l :: sp.target :: sp.childrenR := by
        simp [Spot.children, hcl]
      have hnode : sp.node
          = node (kl ++ s :: sp.keysR) (cl ++ l :: sp.target :: sp.childrenR) := by
        simp [Spot.node, hcl, hkl]
      have hne : sp.children ≠ [] := by rw [hchild]; simp
      have hdall : ∀ c ∈ sp.children, depth? c = some d := (childrenDepth?_iff hne).mp hd
      have hkall : ∀ c ∈ sp.children, KeyCountOk deg false c := (childrenKeyCountOk_iff _).mp hk
      have hml : l ∈ sp.children := by rw [hchild]; simp
      have hmt : sp.target ∈ sp.children := by rw [hchild]; simp
      have hdl : depth? l = some d := hdall l hml
      have hdt : depth? sp.target = some d := hdall sp.target hmt
      have hcl' : KeyCountOk deg false l := hkall l hml
      have hct : KeyCountOk deg false sp.target := hkall sp.target hmt
      rw [hnode] at hb
      obtain ⟨⟨hbl, hbt, hlos, hshi⟩, -, hmerge⟩ :=
        bounded_pair kl cl hlen' lo hi s sp.keysR l sp.target sp.childrenR hb
      have hdkl : sp.keysL.dropLast = kl := by rw [hkl]; simp
      have hdcl : sp.childrenL.dropLast = cl := by rw [hcl]; simp
      set sp' : Spot α := { sp with keysL := sp.keysL.dropLast,
                                    childrenL := sp.childrenL.dropLast,
                                    target := mergeNodes l s sp.target } with hsp'
      have hnode' : sp'.node = node (kl ++ sp.keysR) (cl ++ mergeNodes l s sp.target
          :: sp.childrenR) := by
        simp [hsp', Spot.node, hdkl, hdcl]
      have hch' : sp'.children = cl ++ mergeNodes l s sp.target :: sp.childrenR := by
        simp [hsp', Spot.children, hdcl]
      refine ⟨sp', by simp [hsp', mergeLeftSpot, hgl, hgk], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa [hnode'] using hmerge _ (bounded_mergeNodes hdl hdt hbl hbt hlos hshi)
      · rw [hch']
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | hc
        · exact hdall c (by rw [hchild]; simp [hc])
        · exact depth_mergeNodes hdl hdt
        · exact hdall c (by rw [hchild]; simp [hc])
      · rw [hch']
        refine (childrenKeyCountOk_iff _).mpr ?_
        intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | rfl | hc
        · exact hkall c (by rw [hchild]; simp [hc])
        · exact keyCount_mergeNodes hdeg hdl hdt hcl' hct hsl hst
        · exact hkall c (by rw [hchild]; simp [hc])
      · simp [hsp', hdkl, hdcl, hlen']
      · intro b
        rw [hnode', hnode]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append,
          List.mem_cons]
        rw [or_regroup_merge, or_regroup]
        exact or_congr Iff.rfl (mem_mergeNodes hdl hdt)
      · intro b hbm
        exact (mem_mergeNodes (s := s) hdl hdt).mpr (Or.inr (Or.inr hbm))
      · simpa [hsp'] using hasSpare_mergeNodes (s := s) hdeg hdl hdt hcl' hct
      · rw [hnode', hnode]
        simp only [nodeKeys_node, List.length_append, List.length_cons]
        omega

/-- Merging with the right sibling, the case the leftmost child falls into. -/
theorem mergeRightSpot_spec {deg d : ℕ} {lo hi : Option α} {sp : Spot α} {r : BTree α}
    {cr : List (BTree α)} (hdeg : 2 ≤ deg) (h : SpotLegal deg lo hi d sp)
    (hcr : sp.childrenR = r :: cr)
    (hsr : hasSpare deg r = false) (hst : hasSpare deg sp.target = false) :
    ∃ sp', mergeRightSpot sp = some sp' ∧ SpotLegal deg lo hi d sp' ∧
      (∀ b, Mem b sp'.node ↔ Mem b sp.node) ∧
      (∀ b, Mem b sp.target → Mem b sp'.target) ∧
      hasSpare deg sp'.target = true ∧
      (nodeKeys sp'.node).length + 1 = (nodeKeys sp.node).length := by
  obtain ⟨hb, hd, hk, hlen⟩ := h
  have hb0 : Bounded lo hi
      (node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)) := hb
  have harity := hb0.2.1
  simp only [List.length_append, List.length_cons] at harity
  have hlenR : sp.keysR.length = sp.childrenR.length := by omega
  obtain ⟨s, kr, hkr⟩ : ∃ s kr, sp.keysR = s :: kr := by
    cases hk2 : sp.keysR with
    | nil => rw [hk2, hcr] at hlenR; simp at hlenR
    | cons s kr => exact ⟨s, kr, rfl⟩
  have hchild : sp.children = sp.childrenL ++ sp.target :: r :: cr := by
    simp [Spot.children, hcr]
  have hnode : sp.node
      = node (sp.keysL ++ s :: kr) (sp.childrenL ++ sp.target :: r :: cr) := by
    simp [Spot.node, hcr, hkr]
  have hne : sp.children ≠ [] := by rw [hchild]; simp
  have hdall : ∀ c ∈ sp.children, depth? c = some d := (childrenDepth?_iff hne).mp hd
  have hkall : ∀ c ∈ sp.children, KeyCountOk deg false c := (childrenKeyCountOk_iff _).mp hk
  have hmt : sp.target ∈ sp.children := by rw [hchild]; simp
  have hmr : r ∈ sp.children := by rw [hchild]; simp
  have hdt : depth? sp.target = some d := hdall sp.target hmt
  have hdr : depth? r = some d := hdall r hmr
  have hct : KeyCountOk deg false sp.target := hkall sp.target hmt
  have hcrk : KeyCountOk deg false r := hkall r hmr
  rw [hnode] at hb
  obtain ⟨⟨hbt, hbr, hlos, hshi⟩, -, hmerge⟩ :=
    bounded_pair sp.keysL sp.childrenL hlen lo hi s kr sp.target r cr hb
  set sp' : Spot α := { sp with target := mergeNodes sp.target s r, keysR := kr,
                                childrenR := cr } with hsp'
  have hnode' : sp'.node
      = node (sp.keysL ++ kr) (sp.childrenL ++ mergeNodes sp.target s r :: cr) := by
    simp [hsp', Spot.node]
  have hch' : sp'.children = sp.childrenL ++ mergeNodes sp.target s r :: cr := by
    simp [hsp', Spot.children]
  refine ⟨sp', by simp [hsp', mergeRightSpot, hkr, hcr], ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [hnode'] using hmerge _ (bounded_mergeNodes hdt hdr hbt hbr hlos hshi)
  · rw [hch']
    refine (childrenDepth?_iff (by simp)).mpr ?_
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact hdall c (by rw [hchild]; simp [hc])
    · exact depth_mergeNodes hdt hdr
    · exact hdall c (by rw [hchild]; simp [hc])
  · rw [hch']
    refine (childrenKeyCountOk_iff _).mpr ?_
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact hkall c (by rw [hchild]; simp [hc])
    · exact keyCount_mergeNodes hdeg hdt hdr hct hcrk hst hsr
    · exact hkall c (by rw [hchild]; simp [hc])
  · simpa [hsp'] using hlen
  · intro b
    rw [hnode', hnode]
    simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append, List.mem_cons]
    rw [or_regroup_merge, or_regroup]
    exact or_congr Iff.rfl (mem_mergeNodes hdt hdr)
  · intro b hbm
    exact (mem_mergeNodes (s := s) hdt hdr).mpr (Or.inl hbm)
  · simpa [hsp'] using hasSpare_mergeNodes (s := s) hdeg hdt hdr hct hcrk
  · rw [hnode', hnode]
    simp only [nodeKeys_node, List.length_append, List.length_cons]
    omega

/-- A node with a key of its own has at least two children, so opening it anywhere leaves a
sibling on one side or the other — which is the one hypothesis `ensureSpare_spec` cannot supply
for itself. An internal root always qualifies: `KeyCountOk deg true` gives it `1 ≤ keys`. -/
theorem Spot.sibling_of_keys {sp : Spot α} {lo hi : Option α}
    (hb : Bounded lo hi sp.node) (hk : 1 ≤ (nodeKeys sp.node).length) :
    sp.childrenL ≠ [] ∨ sp.childrenR ≠ [] := by
  -- Inside this declaration's namespace a bare `node` would mean `Spot.node`, so the node is
  -- opened by unfolding rather than by writing the constructor.
  simp only [Spot.node, nodeKeys_node, List.length_append] at hk
  simp only [Spot.node] at hb
  have harity := hb.2.1
  simp only [List.length_append, List.length_cons] at harity
  by_cases hl : sp.childrenL = []
  · refine Or.inr fun hr => ?_
    rw [hl, hr] at harity
    simp only [List.length_nil] at harity
    omega
  · exact Or.inl hl

/-- **CLRS's delete discipline, discharged.** The fix-up preserves ordering, balance, occupancy
and the key set, and the child the descent is about to enter comes out with a key to spare. The
parent pays at most one key for it — which is safe exactly because CLRS never reaches a node
without a spare of its own, and `collapseRoot` absorbs the one case that has none. -/
theorem ensureSpare_spec {deg d : ℕ} {lo hi : Option α} {sp : Spot α} (hdeg : 2 ≤ deg)
    (h : SpotLegal deg lo hi d sp) (hsib : sp.childrenL ≠ [] ∨ sp.childrenR ≠ []) :
    SpotLegal deg lo hi d (ensureSpare deg sp) ∧
    (∀ b, Mem b (ensureSpare deg sp).node ↔ Mem b sp.node) ∧
    (∀ b, Mem b sp.target → Mem b (ensureSpare deg sp).target) ∧
    hasSpare deg (ensureSpare deg sp).target = true ∧
    (nodeKeys (ensureSpare deg sp).node).length ≤ (nodeKeys sp.node).length ∧
    (nodeKeys sp.node).length ≤ (nodeKeys (ensureSpare deg sp).node).length + 1 := by
  cases hsp : hasSpare deg sp.target with
  | true =>
      have heq : ensureSpare deg sp = sp := by simp [ensureSpare, hsp]
      rw [heq]
      exact ⟨h, fun _ => Iff.rfl, fun _ hb => hb, hsp, le_refl _, by omega⟩
  | false =>
      cases hgl : sp.childrenL.getLast? with
      | some l =>
          cases hsl : hasSpare deg l with
          | true =>
              obtain ⟨sp', hspot, hleg, hmem, hmono, hspare, hcount⟩ :=
                borrowLeftSpot_spec hdeg h hgl hsl hsp
              have heq : ensureSpare deg sp = sp' := by
                simp [ensureSpare, hsp, hgl, hsl, hspot]
              rw [heq]
              exact ⟨hleg, hmem, hmono, hspare, le_of_eq hcount, by omega⟩
          | false =>
              obtain ⟨sp', hspot, hleg, hmem, hmono, hspare, hcount⟩ :=
                mergeLeftSpot_spec hdeg h hgl hsl hsp
              cases hcr : sp.childrenR with
              | nil =>
                  have heq : ensureSpare deg sp = sp' := by
                    simp [ensureSpare, hsp, hgl, hsl, hcr, hspot]
                  rw [heq]
                  exact ⟨hleg, hmem, hmono, hspare, by omega, by omega⟩
              | cons r cr =>
                  cases hsr : hasSpare deg r with
                  | true =>
                      obtain ⟨sp'', hspot', hleg', hmem', hmono', hspare', hcount'⟩ :=
                        borrowRightSpot_spec hdeg h hcr hsr hsp
                      have heq : ensureSpare deg sp = sp'' := by
                        simp [ensureSpare, hsp, hgl, hsl, hcr, hsr, hspot']
                      rw [heq]
                      exact ⟨hleg', hmem', hmono', hspare', le_of_eq hcount', by omega⟩
                  | false =>
                      have heq : ensureSpare deg sp = sp' := by
                        simp [ensureSpare, hsp, hgl, hsl, hcr, hsr, hspot]
                      rw [heq]
                      exact ⟨hleg, hmem, hmono, hspare, by omega, by omega⟩
      | none =>
          have hnil : sp.childrenL = [] := List.getLast?_eq_none_iff.mp hgl
          cases hcr : sp.childrenR with
          | nil =>
              exact absurd hsib (by simp [hnil, hcr])
          | cons r cr =>
              cases hsr : hasSpare deg r with
              | true =>
                  obtain ⟨sp', hspot, hleg, hmem, hmono, hspare, hcount⟩ :=
                    borrowRightSpot_spec hdeg h hcr hsr hsp
                  have heq : ensureSpare deg sp = sp' := by
                    simp [ensureSpare, hsp, hgl, hcr, hsr, hspot]
                  rw [heq]
                  exact ⟨hleg, hmem, hmono, hspare, le_of_eq hcount, by omega⟩
              | false =>
                  obtain ⟨sp', hspot, hleg, hmem, hmono, hspare, hcount⟩ :=
                    mergeRightSpot_spec hdeg h hcr hsr hsp
                  have heq : ensureSpare deg sp = sp' := by
                    simp [ensureSpare, hsp, hgl, hcr, hsr, hspot]
                  rw [heq]
                  exact ⟨hleg, hmem, hmono, hspare, by omega, by omega⟩

end BTree

end AlgoDesign.Searching
