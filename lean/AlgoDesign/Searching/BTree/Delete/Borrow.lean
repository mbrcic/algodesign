/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete.Merge

/-!
# B-tree deletion: borrowing

What `borrowLeft` and `borrowRight` preserve — depth, membership, shape and ordering — when a key
rotates through the separator between two siblings.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-! ## Borrowing across a separator -/

theorem dropLast_getLast_eq {β : Type} : ∀ {l : List β} {a : β}, l.getLast? = some a →
    l.dropLast ++ [a] = l
  | [], a, h => by simp at h
  | [x], a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h; simp
  | x :: y :: l, a, h => by
      simp only [List.getLast?_cons_cons] at h
      have ih := dropLast_getLast_eq h
      simp only [List.dropLast_cons_cons, List.cons_append, ih]

omit [LinearOrder α] in
/-- The two shapes `borrowLeft` can return, spelled out. Siblings under a `SameDepth` tree are
both leaves or both internal, so the mixed case never arises and `none` is never returned when
the left sibling has a key to give. -/
theorem borrowLeft_cases {l c l' t' : Node α} {s s' : α}
    (h : borrowLeft l s c = some (l', s', t')) :
    (∃ lk ck, l = leaf lk ∧ c = leaf ck ∧ lk.getLast? = some s' ∧
       l' = leaf lk.dropLast ∧ t' = leaf (s :: ck)) ∨
    (∃ lk lc ck cc bc, l = node lk lc ∧ c = node ck cc ∧ lk.getLast? = some s' ∧
       lc.getLast? = some bc ∧ l' = node lk.dropLast lc.dropLast ∧
       t' = node (s :: ck) (bc :: cc)) := by
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
              obtain ⟨h1, h2, h3⟩ := h
              exact Or.inl ⟨lk, ck, rfl, rfl, by rw [hg, h2], h1.symm ▸ rfl, h3.symm ▸ rfl⟩
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
                  obtain ⟨h1, h2, h3⟩ := h
                  exact Or.inr ⟨lk, lc, ck, cc, bc, rfl, rfl, by rw [hk, h2], hc,
                    h1.symm ▸ rfl, h3.symm ▸ rfl⟩

omit [LinearOrder α] in
/-- The mirror image for `borrowRight`. -/
theorem borrowRight_cases {c r t' r' : Node α} {s s' : α}
    (h : borrowRight c s r = some (t', s', r')) :
    (∃ ck rk, c = leaf ck ∧ r = leaf (s' :: rk) ∧
       t' = leaf (ck ++ [s]) ∧ r' = leaf rk) ∨
    (∃ ck cc rk rc bc, c = node ck cc ∧ r = node (s' :: rk) (bc :: rc) ∧
       t' = node (ck ++ [s]) (cc ++ [bc]) ∧ r' = node rk rc) := by
  cases c with
  | leaf ck =>
      cases r with
      | leaf rk =>
          cases rk with
          | nil => simp only [borrowRight] at h; exact absurd h (by simp)
          | cons b rk' =>
              simp only [borrowRight, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2, h3⟩ := h
              exact Or.inl ⟨ck, rk', rfl, by rw [h2], h1.symm ▸ rfl, h3.symm ▸ rfl⟩
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
                  obtain ⟨h1, h2, h3⟩ := h
                  exact Or.inr ⟨ck, cc, rk', rc', bc, rfl, by rw [h2], h1.symm ▸ rfl,
                    h3.symm ▸ rfl⟩

omit [LinearOrder α] in
theorem borrowLeft_depth {d : ℕ} {l c l' t' : Node α} {s s' : α}
    (h : borrowLeft l s c = some (l', s', t'))
    (hdl : depth? l = some d) (hdc : depth? c = some d) (hal : OneMoreChild l)
    (hspare : 1 ≤ (nodeKeys l).length) :
    depth? l' = some d ∧ depth? t' = some d := by
  rcases borrowLeft_cases h with ⟨lk, ck, rfl, rfl, hg, rfl, rfl⟩ |
    ⟨lk, lc, ck, cc, bc, rfl, rfl, hg, hgc, rfl, rfl⟩
  · have : d = 0 := by simpa [depth?] using hdl.symm
    subst this; exact ⟨rfl, rfl⟩
  · obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? lc = some e ∧ d = e + 1 := by
      simp only [depth?, Option.map_eq_some_iff] at hdl
      obtain ⟨e, h₁, h₂⟩ := hdl; exact ⟨e, h₁, h₂.symm⟩
    have hec : childrenDepth? cc = some e := by
      simp only [depth?, Option.map_eq_some_iff] at hdc
      obtain ⟨e', h₁, h₂⟩ := hdc
      have : e' = e := by omega
      exact this ▸ h₁
    have hbc : bc ∈ lc := List.mem_of_getLast? hgc
    have hlclen : 2 ≤ lc.length := by
      have := hal.1
      simp only [nodeKeys_node] at hspare
      omega
    have hne : lc.dropLast ≠ [] := by
      intro hnil
      have := congrArg List.length hnil
      simp only [List.length_dropLast, List.length_nil] at this
      omega
    have hccne : cc ≠ [] := by
      intro hnil; rw [hnil] at hec; simp [childrenDepth?] at hec
    refine ⟨?_, ?_⟩
    · simp only [depth?, childrenDepth?_of_forall hne
        (fun x hx => childrenDepth?_uniform he (List.dropLast_subset _ hx))]
      rfl
    · have : childrenDepth? (bc :: cc) = some e :=
        childrenDepth?_of_forall (by simp) (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact childrenDepth?_uniform he hbc
          · exact childrenDepth?_uniform hec hx)
      simp only [depth?, this]
      rfl

theorem borrowLeft_mem {l c l' t' : Node α} {s s' : α}
    (h : borrowLeft l s c = some (l', s', t')) (b : α) :
    (Mem b l' ∨ b = s' ∨ Mem b t') ↔ (Mem b l ∨ b = s ∨ Mem b c) := by
  rcases borrowLeft_cases h with ⟨lk, ck, rfl, rfl, hg, rfl, rfl⟩ |
    ⟨lk, lc, ck, cc, bc, rfl, rfl, hg, hgc, rfl, rfl⟩
  · have hk : lk.dropLast ++ [s'] = lk := dropLast_getLast_eq hg
    constructor
    · rintro (hb | rfl | hb)
      · exact Or.inl (by rw [← hk]; simp only [mem_leaf, List.mem_append]; exact Or.inl hb)
      · exact Or.inl (by rw [← hk]; simp)
      · simp only [mem_leaf, List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hb)
    · rintro (hb | rfl | hb)
      · simp only [mem_leaf] at hb
        rw [← hk] at hb
        rcases List.mem_append.mp hb with hb | hb
        · exact Or.inl hb
        · simp only [List.mem_singleton] at hb; exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (by simp))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hb))
  · have hk : lk.dropLast ++ [s'] = lk := dropLast_getLast_eq hg
    have hc : lc.dropLast ++ [bc] = lc := dropLast_getLast_eq hgc
    have e1 : b ∈ lk ↔ (b ∈ lk.dropLast ∨ b = s') := by
      conv_lhs => rw [← hk]
      simp
    have e2 : MemChildren b lc ↔ (MemChildren b lc.dropLast ∨ Mem b bc) := by
      conv_lhs => rw [← hc]
      simp only [memChildren_iff b, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨x, hx | rfl, hb⟩
        · exact Or.inl ⟨x, hx, hb⟩
        · exact Or.inr hb
      · rintro (⟨x, hx, hb⟩ | hb)
        · exact ⟨x, Or.inl hx, hb⟩
        · exact ⟨bc, Or.inr rfl, hb⟩
    simp only [mem_node, memChildren_cons, List.mem_cons, e1, e2]
    tauto

omit [LinearOrder α] in
/-- Borrowing moves exactly one key each way: the sibling drops to `|keys| - 1`, which it could
afford, and the target rises to `deg`, which is what the descent needed. -/
theorem borrowLeft_shape {deg : ℕ} {l c l' t' : Node α} {s s' : α} (hdeg : 2 ≤ deg)
    (h : borrowLeft l s c = some (l', s', t'))
    (hal : OneMoreChild l) (hac : OneMoreChild c)
    (hkl : KeyCountOk deg false l) (hkc : KeyCountOk deg false c)
    (hsl : hasSpare deg l = true) (hsc : hasSpare deg c = false) :
    OneMoreChild l' ∧ OneMoreChild t' ∧ KeyCountOk deg false l' ∧ KeyCountOk deg false t' ∧
      hasSpare deg t' = true := by
  have hlspare : deg ≤ (nodeKeys l).length := by simpa [hasSpare] using hsl
  have hcshort : (nodeKeys c).length < deg := by simpa [hasSpare] using hsc
  rcases borrowLeft_cases h with ⟨lk, ck, rfl, rfl, hg, rfl, rfl⟩ |
    ⟨lk, lc, ck, cc, bc, rfl, rfl, hg, hgc, rfl, rfl⟩
  · simp only [nodeKeys_leaf] at hlspare hcshort
    have hlub : lk.length ≤ 2 * deg - 1 := hkl.2
    have hcmin : deg - 1 ≤ ck.length := hkc.1.resolve_left (by simp)
    refine ⟨trivial, trivial, ⟨Or.inr ?_, ?_⟩, ⟨Or.inr ?_, ?_⟩, ?_⟩
    · simp only [List.length_dropLast]; omega
    · simp only [List.length_dropLast]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · exact decide_eq_true (by simp only [nodeKeys_leaf, List.length_cons]; omega)
  · simp only [nodeKeys_node] at hlspare hcshort
    have hlub : lk.length ≤ 2 * deg - 1 := hkl.2.1
    have hcmin : deg - 1 ≤ ck.length := hkc.1
    have hlarity : lc.length = lk.length + 1 := hal.1
    have hcarity : cc.length = ck.length + 1 := hac.1
    have hbcmem : bc ∈ lc := List.mem_of_getLast? hgc
    have hlcsub : ∀ x ∈ lc.dropLast, x ∈ lc := fun x hx => List.dropLast_subset _ hx
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [List.length_dropLast]; omega
    · rw [arityChildren_iff]
      exact fun x hx => (arityChildren_iff _).mp hal.2 x (hlcsub x hx)
    · simp only [List.length_cons]; omega
    · rw [arityChildren_iff]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (arityChildren_iff _).mp hal.2 x hbcmem
      · exact (arityChildren_iff _).mp hac.2 x hx
    · change deg - 1 ≤ lk.dropLast.length
      simp only [List.length_dropLast]; omega
    · simp only [List.length_dropLast]; omega
    · rw [childrenKeyCountOk_iff]
      exact fun x hx => (childrenKeyCountOk_iff _).mp hkl.2.2 x (hlcsub x hx)
    · change deg - 1 ≤ (s :: ck).length
      simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · rw [childrenKeyCountOk_iff]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (childrenKeyCountOk_iff _).mp hkl.2.2 x hbcmem
      · exact (childrenKeyCountOk_iff _).mp hkc.2.2 x hx
    · exact decide_eq_true (by simp only [nodeKeys_node, List.length_cons]; omega)

/-- **Ordering through a borrow.** The sibling's last key becomes the new separator, so the wall
between the two children moves left by one key — and everything on either side of it was already
on the correct side. -/
theorem borrowLeft_bounded {lo hi : Option α} {l c l' t' : Node α} {s s' : α}
    (h : borrowLeft l s c = some (l', s', t'))
    (hbl : Bounded lo (some s) l) (hbc : Bounded (some s) hi c)
    (hlo : ∀ x ∈ lo, x < s) (hhi : ∀ y ∈ hi, s < y) :
    Bounded lo (some s') l' ∧ Bounded (some s') hi t' ∧
      (∀ x ∈ lo, x < s') ∧ (∀ y ∈ hi, s' < y) := by
  rcases borrowLeft_cases h with ⟨lk, ck, rfl, rfl, hg, rfl, rfl⟩ |
    ⟨lk, lc, ck, cc, bc, rfl, rfl, hg, hgc, rfl, rfl⟩
  · obtain ⟨lk', hk⟩ : ∃ lk', lk = lk' ++ [s'] := ⟨lk.dropLast, (dropLast_getLast_eq hg).symm⟩
    subst hk
    simp only [List.dropLast_concat]
    have hmem : s' ∈ lk' ++ [s'] := by simp
    have hlos' : ∀ x ∈ lo, x < s' := fun x hx => hbl.2.1 x hx s' hmem
    have hs's : s' < s := hbl.2.2 s rfl s' hmem
    have hpre : ∀ x ∈ lk', x < s' := by
      have := List.pairwise_append.mp hbl.1
      exact fun x hx => this.2.2 x hx s' (by simp)
    refine ⟨⟨(List.pairwise_append.mp hbl.1).1, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hlos', ?_⟩
    · exact fun x hx y hy => hbl.2.1 x hx y (by simp [hy])
    · intro y hy z hz
      cases hy
      exact hpre z hz
    · refine List.pairwise_cons.mpr ⟨fun y hy => hbc.2.1 s rfl y hy, hbc.1⟩
    · intro x hx y hy
      cases hx
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hs's
      · exact lt_trans hs's (hbc.2.1 s rfl y hy)
    · intro y hy z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hhi y hy
      · exact hbc.2.2 y hy z hz
    · intro y hy; exact lt_trans hs's (hhi y hy)
  · obtain ⟨hlk, hllen, hlbc⟩ := hbl
    obtain ⟨hck, hclen, hcbc⟩ := hbc
    obtain ⟨lk', hk⟩ : ∃ lk', lk = lk' ++ [s'] := ⟨lk.dropLast, (dropLast_getLast_eq hg).symm⟩
    obtain ⟨lc', hc⟩ : ∃ lc', lc = lc' ++ [bc] := ⟨lc.dropLast, (dropLast_getLast_eq hgc).symm⟩
    subst hk; subst hc
    simp only [List.dropLast_concat]
    have hmem : s' ∈ lk' ++ [s'] := by simp
    have hlos' : ∀ x ∈ lo, x < s' := fun x hx => hlk.2.1 x hx s' hmem
    have hs's : s' < s := hlk.2.2 s rfl s' hmem
    have hpre : ∀ x ∈ lk', x < s' := by
      have := List.pairwise_append.mp hlk.1
      exact fun x hx => this.2.2 x hx s' (by simp)
    have hkeysl : BoundedKeys lo (some s') lk' := by
      refine ⟨(List.pairwise_append.mp hlk.1).1, ?_, ?_⟩
      · exact fun x hx y hy => hlk.2.1 x hx y (by simp [hy])
      · intro y hy z hz
        cases hy
        exact hpre z hz
    have hsplit : BoundedChildren (boundsList lo (some s') lk' ++ [(some s', some s)])
        (lc' ++ [bc]) := by
      have : boundsList lo (some s) (lk' ++ s' :: []) =
          boundsList lo (some s') lk' ++ boundsList (some s') (some s) [] :=
        boundsList_append lo (some s) s' lk' []
      simpa [boundsList] using this ▸ hlbc
    have hlenmatch : (boundsList lo (some s') lk').length = lc'.length := by
      rw [boundsList_length]
      simp only [List.length_append, List.length_cons, List.length_nil] at hllen
      omega
    obtain ⟨hc1, hc2⟩ := (boundedChildren_append hlenmatch).mp hsplit
    have hbcb : Bounded (some s') (some s) bc := by
      simp only [BoundedChildren] at hc2
      exact hc2.1
    refine ⟨⟨hkeysl, ?_, hc1⟩, ⟨?_, ?_, ?_⟩, hlos', fun y hy => lt_trans hs's (hhi y hy)⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hllen ⊢
      omega
    · refine ⟨List.pairwise_cons.mpr ⟨fun y hy => hck.2.1 s rfl y hy, hck.1⟩, ?_, ?_⟩
      · intro x hx y hy
        cases hx
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hs's
        · exact lt_trans hs's (hck.2.1 s rfl y hy)
      · intro y hy z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hhi y hy
        · exact hck.2.2 y hy z hz
    · simp only [List.length_cons]; omega
    · simp only [boundsList, BoundedChildren]
      exact ⟨hbcb, hcbc⟩

omit [LinearOrder α] in
theorem borrowRight_depth {d : ℕ} {c r t' r' : Node α} {s s' : α}
    (h : borrowRight c s r = some (t', s', r'))
    (hdc : depth? c = some d) (hdr : depth? r = some d) (har : OneMoreChild r) :
    depth? t' = some d ∧ depth? r' = some d := by
  rcases borrowRight_cases h with ⟨ck, rk, rfl, rfl, rfl, rfl⟩ |
    ⟨ck, cc, rk, rc, bc, rfl, rfl, rfl, rfl⟩
  · have : d = 0 := by simpa [depth?] using hdc.symm
    subst this; exact ⟨rfl, rfl⟩
  · obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cc = some e ∧ d = e + 1 := by
      simp only [depth?, Option.map_eq_some_iff] at hdc
      obtain ⟨e, h₁, h₂⟩ := hdc; exact ⟨e, h₁, h₂.symm⟩
    have her : childrenDepth? (bc :: rc) = some e := by
      simp only [depth?, Option.map_eq_some_iff] at hdr
      obtain ⟨e', h₁, h₂⟩ := hdr
      have : e' = e := by omega
      exact this ▸ h₁
    have hrcne : rc ≠ [] := by
      intro hnil
      have := har.1
      simp only [hnil, List.length_cons, List.length_nil] at this
      omega
    have hccne : cc ≠ [] := by
      intro hnil; rw [hnil] at he; simp [childrenDepth?] at he
    refine ⟨?_, ?_⟩
    · have : childrenDepth? (cc ++ [bc]) = some e :=
        childrenDepth?_of_forall (by simp [hccne]) (by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact childrenDepth?_uniform he hx
          · simp only [List.mem_singleton] at hx
            subst hx
            exact childrenDepth?_uniform her (by simp))
      simp only [depth?, this]; rfl
    · have : childrenDepth? rc = some e :=
        childrenDepth?_of_forall hrcne
          (fun x hx => childrenDepth?_uniform her (List.mem_cons_of_mem _ hx))
      simp only [depth?, this]; rfl

omit [LinearOrder α] in
theorem borrowRight_mem {c r t' r' : Node α} {s s' : α}
    (h : borrowRight c s r = some (t', s', r')) (b : α) :
    (Mem b t' ∨ b = s' ∨ Mem b r') ↔ (Mem b c ∨ b = s ∨ Mem b r) := by
  rcases borrowRight_cases h with ⟨ck, rk, rfl, rfl, rfl, rfl⟩ |
    ⟨ck, cc, rk, rc, bc, rfl, rfl, rfl, rfl⟩
  · simp only [mem_leaf, List.mem_append, List.mem_cons]
    tauto
  · simp only [mem_node, memChildren_append, memChildren_cons, memChildren_nil,
      List.mem_append, List.mem_cons, or_false]
    tauto

omit [LinearOrder α] in
theorem borrowRight_shape {deg : ℕ} {c r t' r' : Node α} {s s' : α} (hdeg : 2 ≤ deg)
    (h : borrowRight c s r = some (t', s', r'))
    (hac : OneMoreChild c) (har : OneMoreChild r)
    (hkc : KeyCountOk deg false c) (hkr : KeyCountOk deg false r)
    (hsr : hasSpare deg r = true) (hsc : hasSpare deg c = false) :
    OneMoreChild t' ∧ OneMoreChild r' ∧ KeyCountOk deg false t' ∧ KeyCountOk deg false r' ∧
      hasSpare deg t' = true := by
  have hrspare : deg ≤ (nodeKeys r).length := by simpa [hasSpare] using hsr
  have hcshort : (nodeKeys c).length < deg := by simpa [hasSpare] using hsc
  rcases borrowRight_cases h with ⟨ck, rk, rfl, rfl, rfl, rfl⟩ |
    ⟨ck, cc, rk, rc, bc, rfl, rfl, rfl, rfl⟩
  · simp only [nodeKeys_leaf, List.length_cons] at hrspare hcshort
    have hrub : (s' :: rk).length ≤ 2 * deg - 1 := hkr.2
    simp only [List.length_cons] at hrub
    have hcmin : deg - 1 ≤ ck.length := hkc.1.resolve_left (by simp)
    refine ⟨trivial, trivial, ⟨Or.inr ?_, ?_⟩, ⟨Or.inr ?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · omega
    · omega
    · exact decide_eq_true (by
        simp only [nodeKeys_leaf, List.length_append, List.length_cons, List.length_nil]; omega)
  · simp only [nodeKeys_node, List.length_cons] at hrspare hcshort
    have hrub : (s' :: rk).length ≤ 2 * deg - 1 := hkr.2.1
    simp only [List.length_cons] at hrub
    have hcmin : deg - 1 ≤ ck.length := hkc.1
    have hcarity : cc.length = ck.length + 1 := hac.1
    have hrarity : (bc :: rc).length = (s' :: rk).length + 1 := har.1
    simp only [List.length_cons] at hrarity
    have hbcmem : bc ∈ bc :: rc := by simp
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · rw [arityChildren_iff]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (arityChildren_iff _).mp hac.2 x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        exact (arityChildren_iff _).mp har.2 x hbcmem
    · omega
    · rw [arityChildren_iff]
      exact fun x hx => (arityChildren_iff _).mp har.2 x (List.mem_cons_of_mem _ hx)
    · change deg - 1 ≤ (ck ++ [s]).length
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · rw [childrenKeyCountOk_iff]
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (childrenKeyCountOk_iff _).mp hkc.2.2 x hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx
        exact (childrenKeyCountOk_iff _).mp hkr.2.2 x hbcmem
    · change deg - 1 ≤ rk.length; omega
    · omega
    · rw [childrenKeyCountOk_iff]
      exact fun x hx => (childrenKeyCountOk_iff _).mp hkr.2.2 x (List.mem_cons_of_mem _ hx)
    · exact decide_eq_true (by
        simp only [nodeKeys_node, List.length_append, List.length_cons, List.length_nil]; omega)

theorem borrowRight_bounded {lo hi : Option α} {c r t' r' : Node α} {s s' : α}
    (h : borrowRight c s r = some (t', s', r'))
    (hbc : Bounded lo (some s) c) (hbr : Bounded (some s) hi r)
    (hlo : ∀ x ∈ lo, x < s) (hhi : ∀ y ∈ hi, s < y) :
    Bounded lo (some s') t' ∧ Bounded (some s') hi r' ∧
      (∀ x ∈ lo, x < s') ∧ (∀ y ∈ hi, s' < y) := by
  rcases borrowRight_cases h with ⟨ck, rk, rfl, rfl, rfl, rfl⟩ |
    ⟨ck, cc, rk, rc, bc, rfl, rfl, rfl, rfl⟩
  · have hss' : s < s' := hbr.2.1 s rfl s' (by simp)
    have hs'hi : ∀ y ∈ hi, s' < y := fun y hy => hbr.2.2 y hy s' (by simp)
    have hcks : ∀ x ∈ ck, x < s := fun x hx => hbc.2.2 s rfl x hx
    refine ⟨?_, ?_, fun x hx => lt_trans (hlo x hx) hss', hs'hi⟩
    · refine ⟨?_, ?_, ?_⟩
      · refine List.pairwise_append.mpr ⟨hbc.1, by simp, ?_⟩
        intro x hx y hy
        simp only [List.mem_singleton] at hy; subst hy
        exact hcks x hx
      · intro x hx y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hbc.2.1 x hx y hy
        · simp only [List.mem_singleton] at hy; subst hy; exact hlo x hx
      · intro y hy z hz
        cases hy
        rcases List.mem_append.mp hz with hz | hz
        · exact lt_trans (hcks z hz) hss'
        · simp only [List.mem_singleton] at hz; subst hz; exact hss'
    · exact ⟨(List.pairwise_cons.mp hbr.1).2,
        fun x hx y hy => by cases hx; exact (List.pairwise_cons.mp hbr.1).1 y hy,
        fun y hy z hz => hbr.2.2 y hy z (List.mem_cons_of_mem _ hz)⟩
  · obtain ⟨hck, hclen, hcbc⟩ := hbc
    obtain ⟨hrk, hrlen, hrbc⟩ := hbr
    have hss' : s < s' := hrk.2.1 s rfl s' (by simp)
    have hs'hi : ∀ y ∈ hi, s' < y := fun y hy => hrk.2.2 y hy s' (by simp)
    have hcks : ∀ x ∈ ck, x < s := fun x hx => hck.2.2 s rfl x hx
    simp only [boundsList, BoundedChildren] at hrbc
    obtain ⟨hbcb, hrcb⟩ := hrbc
    refine ⟨?_, ?_, fun x hx => lt_trans (hlo x hx) hss', hs'hi⟩
    · refine ⟨?_, ?_, ?_⟩
      · refine ⟨List.pairwise_append.mpr ⟨hck.1, by simp, ?_⟩, ?_, ?_⟩
        · intro x hx y hy
          simp only [List.mem_singleton] at hy; subst hy
          exact hcks x hx
        · intro x hx y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact hck.2.1 x hx y hy
          · simp only [List.mem_singleton] at hy; subst hy; exact hlo x hx
        · intro y hy z hz
          cases hy
          rcases List.mem_append.mp hz with hz | hz
          · exact lt_trans (hcks z hz) hss'
          · simp only [List.mem_singleton] at hz; subst hz; exact hss'
      · simp only [List.length_append, List.length_cons] at hclen ⊢
        omega
      · have hb : boundsList lo (some s') (ck ++ s :: []) =
            boundsList lo (some s) ck ++ boundsList (some s) (some s') [] :=
          boundsList_append lo (some s') s ck []
        have hlenmatch : (boundsList lo (some s) ck).length = cc.length := by
          rw [boundsList_length]; omega
        simp only [hb, boundsList]
        exact (boundedChildren_append hlenmatch).mpr ⟨hcbc, by
          simp only [BoundedChildren]; exact ⟨hbcb, trivial⟩⟩
    · refine ⟨⟨(List.pairwise_cons.mp hrk.1).2,
        fun x hx y hy => by cases hx; exact (List.pairwise_cons.mp hrk.1).1 y hy,
        fun y hy z hz => hrk.2.2 y hy z (List.mem_cons_of_mem _ hz)⟩, ?_, hrcb⟩
      simp only [List.length_cons] at hrlen ⊢
      omega

end BTree.Node

end AlgoDesign.Searching
