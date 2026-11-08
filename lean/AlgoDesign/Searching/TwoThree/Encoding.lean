/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.TwoThree.Spec
public import AlgoDesign.Searching.LLRB

/-!
# 2-3 trees: the encoding is a bijection

Decoding the encoding gives the 2-3 tree back (`ofLlrb_toLlrb`, so `toLlrb_injective`); the
encoding of a balanced 2-3 tree meets the LLRB color conditions (`llrbColors_toLlrb`), and every
tree meeting them is one's encoding (`exists_twoThree_of_llrbColors`). Black height is 2-3 height
plus one (`bheight_toLlrb`). Keys are carried along unchanged (`mem_toLlrb`, `sorted_toLlrb_iff`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace T23

variable {α : Type}

/-- Decoding: a black node with a red left child is a 3-node, any other black node a 2-node. A red
root, or a red link anywhere the encoding never puts one, has no 2-3 reading. -/
def ofLlrb : LLRB α → Option (T23 α)
  | .leaf => some leaf
  | .node .black (.node .red ll a lr) b r =>
      match ofLlrb ll, ofLlrb lr, ofLlrb r with
      | some l, some m, some r' => some (three l a m b r')
      | _, _, _ => none
  | .node .black l k r =>
      match ofLlrb l, ofLlrb r with
      | some l', some r' => some (two l' k r')
      | _, _ => none
  | .node .red _ _ _ => none

/-- **Decoding the encoding gives the tree back**, so no two 2-3 trees share an encoding. -/
theorem ofLlrb_toLlrb : ∀ t : T23 α, ofLlrb (toLlrb t) = some t
  | leaf => rfl
  | two l k r => by
      have hl := ofLlrb_toLlrb l
      have hr := ofLlrb_toLlrb r
      cases l with
      | leaf => simp [toLlrb, ofLlrb, hr]
      | two l1 k1 r1 =>
          simp only [toLlrb] at hl ⊢
          rw [ofLlrb, hl, hr]
          intro _ _ _ h; cases h
      | three l1 a1 m1 b1 r1 =>
          simp only [toLlrb] at hl ⊢
          rw [ofLlrb, hl, hr]
          intro _ _ _ h; cases h
  | three l a m b r => by simp [toLlrb, ofLlrb, ofLlrb_toLlrb l, ofLlrb_toLlrb m, ofLlrb_toLlrb r]

theorem toLlrb_injective : Function.Injective (toLlrb : T23 α → LLRB α) := by
  intro s t h
  have := ofLlrb_toLlrb s
  rw [h, ofLlrb_toLlrb t] at this
  exact (Option.some.inj this).symm

/-- The encoding's black-height, counted down the left spine, is the 2-3 tree's height plus one:
red links, which stand inside 3-nodes, count nothing. -/
theorem bheight_toLlrb : ∀ t : T23 α, LLRB.bheight (toLlrb t) = height t + 1
  | leaf => rfl
  | two l _ _ => by simp [toLlrb, LLRB.bheight, height, bheight_toLlrb l]
  | three l _ _ _ _ => by simp [toLlrb, LLRB.bheight, height, bheight_toLlrb l]

/-- The encoding is black-balanced exactly when the 2-3 tree is balanced. -/
theorem balanced_toLlrb_iff : ∀ t : T23 α, LLRB.Balanced (toLlrb t) ↔ SameDepth t
  | leaf => by simp [toLlrb, LLRB.Balanced, SameDepth]
  | two l _ r => by
      simp [toLlrb, LLRB.Balanced, SameDepth, bheight_toLlrb, balanced_toLlrb_iff l,
        balanced_toLlrb_iff r]
  | three l _ m _ r => by
      simp only [toLlrb, LLRB.Balanced, LLRB.bheight, bheight_toLlrb, reduceCtorEq, ↓reduceIte,
        add_zero, Nat.add_right_cancel_iff, balanced_toLlrb_iff l, balanced_toLlrb_iff m,
        balanced_toLlrb_iff r, SameDepth]
      constructor
      · rintro ⟨h1, ⟨h2, hl, hm⟩, hr⟩; exact ⟨h2, h2 ▸ h1, hl, hm, hr⟩
      · rintro ⟨h1, h2, hl, hm, hr⟩; exact ⟨h1.trans h2, ⟨h1, hl, hm⟩, hr⟩

/-- **All leaves at one depth is the encoding's black balance**: a 2-3 tree has `SameDepth`
exactly when its encoding has `LLRB.BlackHeightOk`, box invariant 5 of the LLRB. -/
theorem sameDepth_iff_blackHeightOk (t : T23 α) :
    SameDepth t ↔ LLRB.BlackHeightOk (toLlrb t) :=
  (balanced_toLlrb_iff t).symm.trans LLRB.blackHeightOk_iff_balanced.symm

/-- Every encoding has a black root, leans left and has no red link under a red one. -/
theorem shape_toLlrb : ∀ t : T23 α,
    ¬ (toLlrb t).IsRed ∧ LLRB.LeftLeaning (toLlrb t) ∧ LLRB.NoRedRed (toLlrb t)
  | leaf => by simp [toLlrb, LLRB.IsRed, LLRB.LeftLeaning, LLRB.NoRedRed]
  | two l _ r => by
      obtain ⟨_, hl2, hl3⟩ := shape_toLlrb l
      obtain ⟨hr1, hr2, hr3⟩ := shape_toLlrb r
      simp only [toLlrb, LLRB.LeftLeaning, LLRB.NoRedRed]
      exact ⟨by simp [LLRB.IsRed], ⟨hr1, hl2, hr2⟩, ⟨by simp, hl3, hr3⟩⟩
  | three l _ m _ r => by
      obtain ⟨hl1, hl2, hl3⟩ := shape_toLlrb l
      obtain ⟨hm1, hm2, hm3⟩ := shape_toLlrb m
      obtain ⟨hr1, hr2, hr3⟩ := shape_toLlrb r
      simp only [toLlrb, LLRB.LeftLeaning, LLRB.NoRedRed]
      exact ⟨by simp [LLRB.IsRed], ⟨hr1, ⟨hm1, hl2, hm2⟩, hr2⟩,
        ⟨by simp, ⟨fun _ => ⟨hl1, hm1⟩, hl3, hm3⟩, hr3⟩⟩

/-- **The encoding of a balanced 2-3 tree is a legal LLRB shape.** -/
theorem llrbColors_toLlrb {t : T23 α} (ht : SameDepth t) : LLRBColors (toLlrb t) := by
  obtain ⟨h1, h2, h3⟩ := shape_toLlrb t
  refine ⟨?_, h2, h3, (sameDepth_iff_blackHeightOk t).mp ht⟩
  cases t <;> simp_all [toLlrb, LLRB.RootBlack, LLRB.IsRed]

/-- A black-rooted tree that leans left and has no red-red link decodes. -/
theorem ofLlrb_isSome : ∀ u : LLRB α,
    ¬ u.IsRed → LLRB.LeftLeaning u → LLRB.NoRedRed u → ∃ t, ofLlrb u = some t
  | .leaf, _, _, _ => ⟨.leaf, rfl⟩
  | .node .red _ _ _, h, _, _ => absurd rfl h
  | .node .black (.node .red ll a lr) b r, _, hL, hN => by
      obtain ⟨hr, ⟨hlr, hll, hlrL⟩, hrL⟩ := hL
      obtain ⟨-, ⟨hred, hllN, hlrN⟩, hrN⟩ := hN
      obtain ⟨hllR, hlrR⟩ := hred rfl
      obtain ⟨l, hl⟩ := ofLlrb_isSome ll hllR hll hllN
      obtain ⟨m, hm⟩ := ofLlrb_isSome lr hlrR hlrL hlrN
      obtain ⟨r', hr'⟩ := ofLlrb_isSome r hr hrL hrN
      exact ⟨three l a m b r', by simp [ofLlrb, hl, hm, hr']⟩
  | .node .black .leaf k r, _, hL, hN => by
      obtain ⟨hr, -, hrL⟩ := hL
      obtain ⟨-, -, hrN⟩ := hN
      obtain ⟨r', hr'⟩ := ofLlrb_isSome r hr hrL hrN
      exact ⟨two .leaf k r', by simp [ofLlrb, hr']⟩
  | .node .black (.node .black ll a lr) k r, _, hL, hN => by
      obtain ⟨hr, hlL, hrL⟩ := hL
      obtain ⟨-, hlN, hrN⟩ := hN
      obtain ⟨l', hl'⟩ := ofLlrb_isSome (.node .black ll a lr) (by simp [LLRB.IsRed]) hlL hlN
      obtain ⟨r', hr'⟩ := ofLlrb_isSome r hr hrL hrN
      exact ⟨two l' k r', by simp [ofLlrb, hl', hr']⟩

/-- Decoding only ever returns a tree whose encoding is what was decoded. -/
theorem toLlrb_of_ofLlrb : ∀ {u : LLRB α} {t : T23 α}, ofLlrb u = some t → toLlrb t = u
  | .leaf, t, h => by simp only [ofLlrb, Option.some.injEq] at h; subst h; rfl
  | .node .red _ _ _, _, h => by simp [ofLlrb] at h
  | .node .black (.node .red ll a lr) b r, t, h => by
      cases hl : ofLlrb ll <;> cases hm : ofLlrb lr <;> cases hr : ofLlrb r <;>
        simp only [ofLlrb, hl, hm, hr, reduceCtorEq, Option.some.injEq] at h
      subst h
      simp [toLlrb, toLlrb_of_ofLlrb hl, toLlrb_of_ofLlrb hm, toLlrb_of_ofLlrb hr]
  | .node .black .leaf k r, t, h => by
      cases hr : ofLlrb r <;> simp only [ofLlrb, hr, reduceCtorEq, Option.some.injEq] at h
      subst h
      simp [toLlrb, toLlrb_of_ofLlrb hr]
  | .node .black (.node .black ll a lr) k r, t, h => by
      cases hl : ofLlrb (.node .black ll a lr) <;> cases hr : ofLlrb r <;>
        simp only [ofLlrb, hl, hr] at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      simp [toLlrb, toLlrb_of_ofLlrb hl, toLlrb_of_ofLlrb hr]

/-- **Every legal LLRB shape is the encoding of a balanced 2-3 tree.** With `toLlrb_injective`,
the one each: the left-leaning convention makes the translation a bijection. -/
theorem exists_twoThree_of_llrbColors {u : LLRB α} (hu : LLRBColors u) :
    ∃ t, SameDepth t ∧ toLlrb t = u := by
  obtain ⟨hB, hL, hN, hBal⟩ := hu
  have hnr : ¬ u.IsRed := by cases u <;> simp_all [LLRB.RootBlack, LLRB.IsRed]
  obtain ⟨t, ht⟩ := ofLlrb_isSome u hnr hL hN
  have he := toLlrb_of_ofLlrb ht
  refine ⟨t, (balanced_toLlrb_iff t).mp (he ▸ LLRB.blackHeightOk_iff_balanced.mp hBal), he⟩

/-! ### Keys: membership and order -/

theorem All.imp {p q : α → Prop} (h : ∀ x, p x → q x) : ∀ {t : T23 α}, All p t → All q t
  | leaf, _ => trivial
  | two _ _ _, ⟨hl, hk, hr⟩ => ⟨hl.imp h, h _ hk, hr.imp h⟩
  | three _ _ _ _ _, ⟨hl, ha, hm, hb, hr⟩ => ⟨hl.imp h, h _ ha, hm.imp h, h _ hb, hr.imp h⟩

theorem all_and {p q : α → Prop} : ∀ {t : T23 α}, All (fun x => p x ∧ q x) t ↔ All p t ∧ All q t
  | leaf => by simp [All]
  | two l _ r => by simp only [All, all_and (t := l), all_and (t := r)]; tauto
  | three l _ m _ r => by
      simp only [All, all_and (t := l), all_and (t := m), all_and (t := r)]; tauto

/-- The encoding keeps every key: a property of all keys holds on one side exactly when it holds on
the other. -/
theorem all_toLlrb {p : α → Prop} : ∀ t : T23 α, LLRB.All p (toLlrb t) ↔ All p t
  | leaf => by simp [toLlrb, LLRB.All, All]
  | two l _ r => by simp only [toLlrb, LLRB.All, All, all_toLlrb l, all_toLlrb r]
  | three l _ m _ r => by
      simp only [toLlrb, LLRB.All, All, all_toLlrb l, all_toLlrb m, all_toLlrb r]; tauto

/-- The encoding has exactly the 2-3 tree's keys. -/
theorem mem_toLlrb (x : α) : ∀ t : T23 α, LLRB.Mem x (toLlrb t) ↔ Mem x t
  | leaf => by simp [toLlrb, Mem]
  | two l _ r => by simp only [toLlrb, LLRB.Mem, Mem, mem_toLlrb x l, mem_toLlrb x r]
  | three l _ m _ r => by
      simp only [toLlrb, LLRB.Mem, Mem, mem_toLlrb x l, mem_toLlrb x m, mem_toLlrb x r]; tauto

variable [LinearOrder α]

/-- **The encoding carries key order unchanged**: a 2-3 tree is sorted exactly when its encoding
is. -/
theorem sorted_toLlrb_iff : ∀ t : T23 α, LLRB.Sorted (toLlrb t) ↔ Sorted t
  | leaf => by simp [toLlrb, LLRB.Sorted, Sorted]
  | two l _ r => by
      simp only [toLlrb, LLRB.Sorted, Sorted, all_toLlrb, sorted_toLlrb_iff l,
        sorted_toLlrb_iff r]
  | three l a m b r => by
      simp only [toLlrb, LLRB.Sorted, LLRB.All, Sorted, all_toLlrb, sorted_toLlrb_iff l,
        sorted_toLlrb_iff m, sorted_toLlrb_iff r, all_and]
      constructor
      · rintro ⟨⟨-, hab, hmb⟩, hr, ⟨hla, ham, hsl, hsm⟩, hsr⟩
        exact ⟨hab, hla, ⟨ham, hmb⟩, hr, hsl, hsm, hsr⟩
      · rintro ⟨hab, hla, ⟨ham, hmb⟩, hr, hsl, hsm, hsr⟩
        exact ⟨⟨hla.imp fun _ h => lt_trans h hab, hab, hmb⟩, hr, ⟨hla, ham, hsl, hsm⟩, hsr⟩

omit [LinearOrder α] in
theorem mem_iff_mem_toList (x : α) : ∀ t : T23 α, Mem x t ↔ x ∈ toList t
  | leaf => by simp [Mem, toList]
  | two l _ r => by simp [Mem, toList, mem_iff_mem_toList x l, mem_iff_mem_toList x r]
  | three l _ m _ r => by
      simp [Mem, toList, mem_iff_mem_toList x l, mem_iff_mem_toList x m,
        mem_iff_mem_toList x r]

omit [LinearOrder α] in
theorem all_iff_forall (p : α → Prop) : ∀ t : T23 α, All p t ↔ ∀ x ∈ toList t, p x
  | leaf => by simp [All, toList]
  | two l _ r => by
      simp [All, toList, all_iff_forall p l, all_iff_forall p r, or_imp, forall_and]
  | three l _ m _ r => by
      simp [All, toList, all_iff_forall p l, all_iff_forall p m, all_iff_forall p r, or_imp,
        forall_and]

/-- A 2-3 tree is sorted exactly when its keys, read in order, strictly increase. -/
theorem sorted_iff_pairwise : ∀ t : T23 α, Sorted t ↔ (toList t).Pairwise (· < ·)
  | leaf => by simp [Sorted, toList]
  | two l k r => by
      rw [Sorted, toList, all_iff_forall, all_iff_forall, sorted_iff_pairwise l,
        sorted_iff_pairwise r]
      simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons]
      constructor
      · rintro ⟨hl, hr, pl, pr⟩
        exact ⟨pl, ⟨hr, pr⟩, fun a ha b hb => hb.elim (fun h => h ▸ hl a ha)
          (fun h => lt_trans (hl a ha) (hr b h))⟩
      · rintro ⟨pl, ⟨hr, pr⟩, hx⟩
        exact ⟨fun a ha => hx a ha k (Or.inl rfl), hr, pl, pr⟩
  | three l a m b r => by
      rw [Sorted, toList, all_iff_forall, all_iff_forall, all_iff_forall, sorted_iff_pairwise l,
        sorted_iff_pairwise m, sorted_iff_pairwise r]
      simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro ⟨hab, hl, hm, hr, pl, pm, pr⟩
        refine ⟨pl, ⟨fun y hy => ?_, pm, ⟨hr, pr⟩, fun y hy z hz => ?_⟩, fun x hx y hy => ?_⟩
        · rcases hy with hy | hy | hy
          · exact (hm y hy).1
          · exact hy ▸ hab
          · exact lt_trans hab (hr y hy)
        · rcases hz with hz | hz
          · exact hz ▸ (hm y hy).2
          · exact lt_trans (hm y hy).2 (hr z hz)
        · have hxa := hl x hx
          rcases hy with hy | hy | hy | hy
          · exact hy ▸ hxa
          · exact lt_trans hxa (hm y hy).1
          · exact hy ▸ lt_trans hxa hab
          · exact lt_trans (lt_trans hxa hab) (hr y hy)
      · rintro ⟨pl, ⟨ha, pm, ⟨hr, pr⟩, hmr⟩, hlx⟩
        refine ⟨ha b (Or.inr (Or.inl rfl)), fun x hx => hlx x hx a (Or.inl rfl),
          fun x hx => ⟨ha x (Or.inl hx), hmr x hx b (Or.inl rfl)⟩, hr, pl, pm, pr⟩

end T23

end AlgoDesign.Searching
