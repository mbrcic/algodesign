/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete.FixUp

/-!
# B-tree deletion: `takeMax` and `takeMin`

`takeMax_spec` and `takeMin_spec`: lifting the largest or smallest key out of a legal subtree —
topping up each child on the way down — returns that key and a legal subtree holding the rest.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-! ## `takeMax` and `takeMin`

A key deleted from an internal node is replaced by its predecessor or successor. These two walk
to the extreme leaf, giving every node on the way a spare first, as `delRec` does. The extreme key
occurs nowhere else in the tree (`lt_of_mem_before_last`, `lt_of_mem_after_first`). -/

/-- Everything a node holds before its last child is strictly below everything the last child
holds. The one fact `takeMax` needs that the per-node ordering invariant does not state: the
maximum it lifts out of the last child occurs nowhere else in the node. -/
theorem lt_of_mem_before_last : ∀ (kl : List α) (cl : List (Node α)), cl.length = kl.length →
    ∀ (lo hi : Option α) (t : Node α) (m b : α),
      Bounded lo hi (node kl (cl ++ [t])) → Mem m t →
      (b ∈ kl ∨ MemChildren b cl) → b < m := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi t m b _ _ hmem
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp at hmem
  | cons k kl' ih =>
      intro cl hlen lo hi t m b hb hmt hmem
      obtain ⟨c, cl', rfl⟩ : ∃ c cl', cl = c :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c cl' => exact ⟨c, cl', rfl⟩
      have hlen' : cl'.length = kl'.length := by simpa using hlen
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [boundsList, BoundedChildren, List.cons_append] at hbc
      obtain ⟨hbcc, hbrest⟩ := hbc
      -- the node made of everything after the first key
      have hsub : Bounded (some k) hi (node kl' (cl' ++ [t])) := by
        refine ⟨hbk.of_cons, ?_, hbrest⟩
        simp only [List.length_append, List.length_cons] at hlenb ⊢
        omega
      have hkm : k < m := by
        have hmnode : Mem m (node kl' (cl' ++ [t])) := by
          refine Or.inr ?_
          exact (memChildren_iff m _).mpr ⟨t, by simp, hmt⟩
        exact (mem_bounds_of_bounded hsub hmnode).1 k rfl
      rcases hmem with hmem | hmem
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hkm
        · exact ih cl' hlen' (some k) hi t m b hsub hmt (Or.inl hmem)
      · rcases (memChildren_cons ..).mp hmem with hmem | hmem
        · exact lt_trans ((mem_bounds_of_bounded hbcc hmem).2 k rfl) hkm
        · exact ih cl' hlen' (some k) hi t m b hsub hmt (Or.inr hmem)

omit [LinearOrder α] in
/-- Both left-hand moves rebuild only the left of the hole. -/
theorem borrowLeftSpot_right {sp sp' : Spot α} (h : borrowLeftSpot sp = some sp') :
    sp'.keysR = sp.keysR ∧ sp'.childrenR = sp.childrenR := by
  simp only [borrowLeftSpot] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [LinearOrder α] in
/-- The same for the merge. -/
theorem mergeLeftSpot_right {sp sp' : Spot α} (h : mergeLeftSpot sp = some sp') :
    sp'.keysR = sp.keysR ∧ sp'.childrenR = sp.childrenR := by
  simp only [mergeLeftSpot] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

omit [LinearOrder α] in
/-- With no right sibling there is nothing to borrow from or merge with on that side, so the
fix-up leaves the right of the hole exactly as it found it. `takeMax` opens a node at its last
child, so this is what keeps the result in the `node kl (cl ++ [t])` shape that
`lt_of_mem_before_last` reads. -/
theorem ensureSpare_right_nil {deg : ℕ} {sp : Spot α} (h : sp.childrenR = []) :
    (ensureSpare deg sp).keysR = sp.keysR ∧ (ensureSpare deg sp).childrenR = sp.childrenR := by
  cases hsp : hasSpare deg sp.target with
  | true => simp [ensureSpare, hsp]
  | false =>
      cases hgl : sp.childrenL.getLast? with
      | some l =>
          cases hsl : hasSpare deg l with
          | true =>
              have heq : ensureSpare deg sp = (borrowLeftSpot sp).getD sp := by
                simp [ensureSpare, hsp, hgl, hsl]
              rw [heq]
              cases hbor : borrowLeftSpot sp with
              | none => simp
              | some sp' => simpa using borrowLeftSpot_right hbor
          | false =>
              have heq : ensureSpare deg sp = (mergeLeftSpot sp).getD sp := by
                simp [ensureSpare, hsp, hgl, hsl, h]
              rw [heq]
              cases hmrg : mergeLeftSpot sp with
              | none => simp
              | some sp' => simpa using mergeLeftSpot_right hmrg
      | none => simp [ensureSpare, hsp, hgl, h]

omit [LinearOrder α] in
/-- Both right-hand moves rebuild only the right of the hole. -/
theorem borrowRightSpot_left {sp sp' : Spot α} (h : borrowRightSpot sp = some sp') :
    sp'.keysL = sp.keysL ∧ sp'.childrenL = sp.childrenL := by
  simp only [borrowRightSpot] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [LinearOrder α] in
/-- The same for the merge. -/
theorem mergeRightSpot_left {sp sp' : Spot α} (h : mergeRightSpot sp = some sp') :
    sp'.keysL = sp.keysL ∧ sp'.childrenL = sp.childrenL := by
  simp only [mergeRightSpot] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

omit [LinearOrder α] in
/-- The mirror of `ensureSpare_right_nil`, for the first child, which is where `takeMin` opens. -/
theorem ensureSpare_left_nil {deg : ℕ} {sp : Spot α} (h : sp.childrenL = []) :
    (ensureSpare deg sp).keysL = sp.keysL ∧ (ensureSpare deg sp).childrenL = sp.childrenL := by
  have hgl : sp.childrenL.getLast? = none := by rw [h]; simp
  cases hsp : hasSpare deg sp.target with
  | true => simp [ensureSpare, hsp]
  | false =>
      cases hcr : sp.childrenR with
      | nil => simp [ensureSpare, hsp, hgl, hcr]
      | cons r cr =>
          cases hsr : hasSpare deg r with
          | true =>
              have heq : ensureSpare deg sp = (borrowRightSpot sp).getD sp := by
                simp [ensureSpare, hsp, hgl, hcr, hsr]
              rw [heq]
              cases hbor : borrowRightSpot sp with
              | none => simp
              | some sp' => simpa using borrowRightSpot_left hbor
          | false =>
              have heq : ensureSpare deg sp = (mergeRightSpot sp).getD sp := by
                simp [ensureSpare, hsp, hgl, hcr, hsr]
              rw [heq]
              cases hmrg : mergeRightSpot sp with
              | none => simp
              | some sp' => simpa using mergeRightSpot_left hmrg

/-- The mirror of `lt_of_mem_before_last`. Everything a node holds after its first child is
strictly above everything the first child holds — and this direction needs no induction, because
the node's own first key already separates the first child from all the rest. -/
theorem lt_of_mem_after_first (kr : List α) (cr : List (Node α)) (hlen : cr.length = kr.length)
    (lo hi : Option α) (t : Node α) (m b : α)
    (hb : Bounded lo hi (node kr (t :: cr))) (hmt : Mem m t)
    (hmem : b ∈ kr ∨ MemChildren b cr) : m < b := by
  cases kr with
  | nil =>
      obtain rfl : cr = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp at hmem
  | cons k kr' =>
      obtain ⟨c, cr', rfl⟩ : ∃ c cr', cr = c :: cr' := by
        cases cr with
        | nil => simp at hlen
        | cons c cr' => exact ⟨c, cr', rfl⟩
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [boundsList, BoundedChildren] at hbc
      obtain ⟨hbt, hbrest⟩ := hbc
      have hmk : m < k := (mem_bounds_of_bounded hbt hmt).2 k rfl
      have hsub : Bounded (some k) hi (node kr' (c :: cr')) := by
        refine ⟨hbk.of_cons, ?_, hbrest⟩
        simp only [List.length_cons] at hlenb ⊢
        omega
      have hkb : ∀ x, Mem x (node kr' (c :: cr')) → k < x :=
        fun x hx => (mem_bounds_of_bounded hsub hx).1 k rfl
      rcases hmem with hmem | hmem
      · rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hmk
        · exact lt_trans hmk (hkb b (Or.inl hmem))
      · exact lt_trans hmk (hkb b (Or.inr hmem))

/-- **`takeMax` removes and returns the largest key.** -/
theorem takeMax_spec {deg : ℕ} (hdeg : 2 ≤ deg) :
    ∀ (t : Node α) (d : ℕ) (lo hi : Option α), Legal deg lo hi d t → hasSpare deg t = true →
      ∃ t' m, takeMax deg t = (t', some m) ∧
        Mem m t ∧ (∀ b, Mem b t → b ≤ m) ∧
        (∀ b, Mem b t' ↔ (Mem b t ∧ b ≠ m)) ∧
        (∀ b, Mem b t' → b < m) ∧
        Legal deg lo hi d t' := by
  intro t
  induction t using takeMax.induct (deg := deg) with
  | case1 ks hg =>
      -- No last key: the leaf is empty, so it had nothing to spare.
      intro d lo hi _ hspare
      exfalso
      rw [List.getLast?_eq_none_iff] at hg
      subst hg
      have hz : deg ≤ 0 := by simpa [hasSpare] using hspare
      omega
  | case2 ks m hg =>
      intro d lo hi hleg hspare
      obtain ⟨hb, hd, hk⟩ := hleg
      obtain ⟨ks', hks⟩ : ∃ ks', ks = ks' ++ [m] :=
        ⟨ks.dropLast, (dropLast_getLast_eq hg).symm⟩
      subst hks
      have hkeys : deg ≤ (ks' ++ [m]).length := by simpa [hasSpare] using hspare
      simp only [List.length_append, List.length_cons, List.length_nil] at hkeys
      have hub : (ks' ++ [m]).length ≤ 2 * deg - 1 := hk.2
      simp only [List.length_append, List.length_cons, List.length_nil] at hub
      have hlt : ∀ b ∈ ks', b < m :=
        fun b hbm => (List.pairwise_append.mp hb.1).2.2 b hbm m (by simp)
      refine ⟨leaf ks', m, by simp [takeMax, hg], by simp, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
      · intro b hbm
        simp only [mem_leaf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hbm
        rcases hbm with hbm | rfl
        · exact le_of_lt (hlt b hbm)
        · exact le_refl _
      · intro b
        simp only [mem_leaf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨fun h => ⟨Or.inl h, ne_of_lt (hlt b h)⟩, fun h => h.1.resolve_right h.2⟩
      · intro b hbm
        exact hlt b (by simpa using hbm)
      · exact ⟨(List.pairwise_append.mp hb.1).1,
              fun l hl x hx => hb.2.1 l hl x (by simp [hx]),
              fun y hy x hx => hb.2.2 y hy x (by simp [hx])⟩
      · have : d = 0 := by simpa [depth?] using hd.symm
        subst this; rfl
      · exact ⟨Or.inr (by omega), by omega⟩
  | case3 ks cs hg =>
      -- No last child: the node has no children at all, which `Bounded` rules out.
      intro d lo hi hleg _
      exfalso
      rw [List.getLast?_eq_none_iff] at hg
      subst hg
      have := hleg.1.2.1
      simp at this
  | case4 ks cs c hg sp ih =>
      intro d lo hi hleg hspare
      obtain ⟨hb, hd, hk⟩ := hleg
      have hcs : cs.dropLast ++ [c] = cs := dropLast_getLast_eq hg
      have hkeys : deg ≤ ks.length := by
        simp only [hasSpare, nodeKeys_node] at hspare
        exact of_decide_eq_true hspare
      have harity : cs.length = ks.length + 1 := hb.2.1
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      set sp0 : Spot α := ⟨ks, cs.dropLast, c, [], []⟩ with hsp0
      have hsp0n : sp0.node = node ks cs := by
        simp only [hsp0, Spot.node, List.append_nil]
        rw [show cs.dropLast ++ [c] = cs from hcs]
      have hsp0c : sp0.children = cs := by
        simp only [hsp0, Spot.children]
        rw [show cs.dropLast ++ [c] = cs from hcs]
      have hlen0 : sp0.childrenL.length = sp0.keysL.length := by
        simp only [hsp0]
        have : cs.dropLast.length + 1 = cs.length := by
          conv_rhs => rw [← hcs]
          simp
        omega
      have hleg0 : SpotLegal deg lo hi e sp0 :=
        ⟨by rw [hsp0n]; exact hb, by rw [hsp0c]; exact he, by rw [hsp0c]; exact hk.2.2, hlen0⟩
      have hsib : sp0.childrenL ≠ [] ∨ sp0.childrenR ≠ [] :=
        Spot.sibling_of_keys hleg0.1 (by rw [hsp0n]; simp only [nodeKeys_node]; omega)
      obtain ⟨hleg', hmemiff, hmono, hspare', hcnt1, hcnt2⟩ := ensureSpare_spec hdeg hleg0 hsib
      obtain ⟨hkR, hcR⟩ := ensureSpare_right_nil (deg := deg) (sp := sp0) rfl
      have hspdef : ensureSpare deg sp0 = sp := rfl
      rw [hspdef] at hleg' hmemiff hmono hspare' hcnt1 hcnt2 hkR hcR
      have hkR0 : sp.keysR = [] := by rw [hkR, hsp0]
      have hcR0 : sp.childrenR = [] := by rw [hcR, hsp0]
      obtain ⟨hb', hd', hk', hlen'⟩ := hleg'
      have hspn : sp.node = node sp.keysL (sp.childrenL ++ [sp.target]) := by
        simp [Spot.node, hkR0, hcR0]
      have hspc : sp.children = sp.childrenL ++ [sp.target] := by
        simp [Spot.children, hcR0]
      have hbn : Bounded lo hi (node (sp.keysL ++ []) (sp.childrenL ++ sp.target :: [])) := by
        simpa [hspn] using hb'
      obtain ⟨hbt0, hput⟩ := bounded_hole sp.keysL sp.childrenL hlen' lo hi [] [] sp.target hbn
      simp only [hiAt, List.head?_nil, Option.none_or] at hbt0 hput
      have hcne : sp.children ≠ [] := by rw [hspc]; simp
      have hdall : ∀ x ∈ sp.children, depth? x = some e := (childrenDepth?_iff hcne).mp hd'
      have hkall : ∀ x ∈ sp.children, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk'
      have hmt : sp.target ∈ sp.children := by rw [hspc]; simp
      obtain ⟨t'', m, heq, hmemm, hmax, hiff, hltm, hlegt⟩ :=
        ih e (loAt lo sp.keysL) hi ⟨hbt0, hdall sp.target hmt, hkall sp.target hmt⟩ hspare'
      -- everything left of the last child is below the maximum the last child gave up
      have hbefore : ∀ b, (b ∈ sp.keysL ∨ MemChildren b sp.childrenL) → b < m :=
        fun b hbm => lt_of_mem_before_last sp.keysL sp.childrenL hlen' lo hi sp.target m b
          (by rw [← hspn]; exact hb') hmemm hbm
      -- the node's membership, read through the fix-up
      have hnodemem : ∀ b, Mem b (node ks cs) ↔
          (b ∈ sp.keysL ∨ MemChildren b sp.childrenL ∨ Mem b sp.target) := by
        intro b
        rw [← hsp0n, ← hmemiff b, hspn, mem_node, memChildren_append, memChildren_cons,
          memChildren_nil, or_false]
      have hresn : ({ sp with target := t'' } : Spot α).node
          = node sp.keysL (sp.childrenL ++ [t'']) := by
        simp [Spot.node, hkR0, hcR0]
      have hresmem : ∀ b, Mem b ({ sp with target := t'' } : Spot α).node ↔
          (b ∈ sp.keysL ∨ MemChildren b sp.childrenL ∨ Mem b t'') := by
        intro b
        rw [hresn, mem_node, memChildren_append, memChildren_cons, memChildren_nil, or_false]
      refine ⟨({ sp with target := t'' } : Spot α).node, m, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
      · simp only [takeMax]
        split
        · rename_i hnone
          rw [hg] at hnone
          exact absurd hnone (by simp)
        · rename_i c' hsome
          rw [hg] at hsome
          simp only [Option.some.injEq] at hsome
          subst hsome
          exact congrArg
            (fun r : Node α × Option α => (({ sp with target := r.1 } : Spot α).node, r.2)) heq
      · exact (hnodemem m).mpr (Or.inr (Or.inr hmemm))
      · intro b hbm
        rcases (hnodemem b).mp hbm with h | h | h
        · exact le_of_lt (hbefore b (Or.inl h))
        · exact le_of_lt (hbefore b (Or.inr h))
        · exact hmax b h
      · intro b
        rw [hresmem b, hnodemem b]
        constructor
        · rintro (h | h | h)
          · exact ⟨Or.inl h, ne_of_lt (hbefore b (Or.inl h))⟩
          · exact ⟨Or.inr (Or.inl h), ne_of_lt (hbefore b (Or.inr h))⟩
          · exact ⟨Or.inr (Or.inr ((hiff b).mp h).1), ((hiff b).mp h).2⟩
        · rintro ⟨h | h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ((hiff b).mpr ⟨h, hne⟩))
      · intro b hbm
        rcases (hresmem b).mp hbm with h | h | h
        · exact hbefore b (Or.inl h)
        · exact hbefore b (Or.inr h)
        · exact hltm b h
      · have := hput t'' hlegt.1
        simpa [hresn] using this
      · rw [hresn]
        simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hdall x (by rw [hspc]; simp [hx])
        · simp only [List.mem_singleton] at hx
          subst hx
          exact hlegt.2.1
      · rw [hresn]
        have hkl : (nodeKeys sp.node).length = sp.keysL.length := by simp [hspn]
        have hk0 : (nodeKeys sp0.node).length = ks.length := by simp [hsp0n]
        rw [hkl, hk0] at hcnt1 hcnt2
        have hub : ks.length ≤ 2 * deg - 1 := hk.2.1
        refine ⟨show deg - 1 ≤ sp.keysL.length by omega, by omega, ?_⟩
        refine (childrenKeyCountOk_iff _).mpr ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hkall x (by rw [hspc]; simp [hx])
        · simp only [List.mem_singleton] at hx
          subst hx
          exact hlegt.2.2

/-- **`takeMin` removes and returns the smallest key** — a deleted key's in-order successor, and
the mirror of `takeMax_spec`. -/
theorem takeMin_spec {deg : ℕ} (hdeg : 2 ≤ deg) :
    ∀ (t : Node α) (d : ℕ) (lo hi : Option α), Legal deg lo hi d t → hasSpare deg t = true →
      ∃ t' m, takeMin deg t = (t', some m) ∧
        Mem m t ∧ (∀ b, Mem b t → m ≤ b) ∧
        (∀ b, Mem b t' ↔ (Mem b t ∧ b ≠ m)) ∧
        (∀ b, Mem b t' → m < b) ∧
        Legal deg lo hi d t' := by
  intro t
  induction t using takeMin.induct (deg := deg) with
  | case1 =>
      intro d lo hi _ hspare
      exfalso
      have hz : deg ≤ 0 := by simpa [hasSpare] using hspare
      omega
  | case2 k ks =>
      intro d lo hi hleg hspare
      obtain ⟨hb, hd, hk⟩ := hleg
      have hkeys : deg ≤ (k :: ks).length := by
        simp only [hasSpare, nodeKeys_leaf] at hspare
        exact of_decide_eq_true hspare
      simp only [List.length_cons] at hkeys
      have hub : (k :: ks).length ≤ 2 * deg - 1 := hk.2
      simp only [List.length_cons] at hub
      have hlt : ∀ b ∈ ks, k < b := (List.pairwise_cons.mp hb.1).1
      refine ⟨leaf ks, k, by simp [takeMin], by simp, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
      · intro b hbm
        simp only [mem_leaf, List.mem_cons] at hbm
        rcases hbm with rfl | hbm
        · exact le_refl _
        · exact le_of_lt (hlt b hbm)
      · intro b
        simp only [mem_leaf, List.mem_cons]
        exact ⟨fun h => ⟨Or.inr h, (ne_of_lt (hlt b h)).symm⟩,
               fun h => h.1.resolve_left (fun hx => h.2 hx)⟩
      · intro b hbm
        exact hlt b (by simpa using hbm)
      · exact boundedKeys_tail hb
      · have : d = 0 := by simpa [depth?] using hd.symm
        subst this; rfl
      · exact ⟨Or.inr (by omega), by omega⟩
  | case3 ks =>
      intro d lo hi hleg _
      exfalso
      have := hleg.1.2.1
      simp at this
  | case4 ks c cs' sp ih =>
      intro d lo hi hleg hspare
      obtain ⟨hb, hd, hk⟩ := hleg
      have hkeys : deg ≤ ks.length := by
        simp only [hasSpare, nodeKeys_node] at hspare
        exact of_decide_eq_true hspare
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? (c :: cs') = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      set sp0 : Spot α := ⟨[], [], c, ks, cs'⟩ with hsp0
      have hsp0n : sp0.node = node ks (c :: cs') := by simp [hsp0, Spot.node]
      have hsp0c : sp0.children = c :: cs' := by simp [hsp0, Spot.children]
      have hlen0 : sp0.childrenL.length = sp0.keysL.length := by simp [hsp0]
      have hleg0 : SpotLegal deg lo hi e sp0 :=
        ⟨by rw [hsp0n]; exact hb, by rw [hsp0c]; exact he, by rw [hsp0c]; exact hk.2.2, hlen0⟩
      have hsib : sp0.childrenL ≠ [] ∨ sp0.childrenR ≠ [] :=
        Spot.sibling_of_keys hleg0.1 (by rw [hsp0n]; simp only [nodeKeys_node]; omega)
      obtain ⟨hleg', hmemiff, hmono, hspare', hcnt1, hcnt2⟩ := ensureSpare_spec hdeg hleg0 hsib
      obtain ⟨hkL, hcL⟩ := ensureSpare_left_nil (deg := deg) (sp := sp0) rfl
      have hspdef : ensureSpare deg sp0 = sp := rfl
      rw [hspdef] at hleg' hmemiff hmono hspare' hcnt1 hcnt2 hkL hcL
      have hkL0 : sp.keysL = [] := by rw [hkL, hsp0]
      have hcL0 : sp.childrenL = [] := by rw [hcL, hsp0]
      obtain ⟨hb', hd', hk', hlen'⟩ := hleg'
      have hspn : sp.node = node sp.keysR (sp.target :: sp.childrenR) := by
        simp [Spot.node, hkL0, hcL0]
      have hspc : sp.children = sp.target :: sp.childrenR := by
        simp [Spot.children, hcL0]
      have hbn : Bounded lo hi (node ([] ++ sp.keysR) ([] ++ sp.target :: sp.childrenR)) := by
        simpa [hspn] using hb'
      obtain ⟨hbt0, hput⟩ :=
        bounded_hole [] [] rfl lo hi sp.keysR sp.childrenR sp.target hbn
      simp only [loAt, List.getLast?_nil, Option.none_or] at hbt0 hput
      have hlenR : sp.childrenR.length = sp.keysR.length := by
        have h2 := hb'.2.1
        rw [hkL0, hcL0] at h2
        simp only [List.nil_append, List.length_cons] at h2
        omega
      have hcne : sp.children ≠ [] := by rw [hspc]; simp
      have hdall : ∀ x ∈ sp.children, depth? x = some e := (childrenDepth?_iff hcne).mp hd'
      have hkall : ∀ x ∈ sp.children, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk'
      have hmt : sp.target ∈ sp.children := by rw [hspc]; simp
      obtain ⟨t'', m, heq, hmemm, hmin, hiff, hgtm, hlegt⟩ :=
        ih e lo (hiAt hi sp.keysR) ⟨hbt0, hdall sp.target hmt, hkall sp.target hmt⟩ hspare'
      have hafter : ∀ b, (b ∈ sp.keysR ∨ MemChildren b sp.childrenR) → m < b :=
        fun b hbm => lt_of_mem_after_first sp.keysR sp.childrenR hlenR lo hi sp.target m b
          (by rw [← hspn]; exact hb') hmemm hbm
      have hnodemem : ∀ b, Mem b (node ks (c :: cs')) ↔
          (b ∈ sp.keysR ∨ Mem b sp.target ∨ MemChildren b sp.childrenR) := by
        intro b
        rw [← hsp0n, ← hmemiff b, hspn, mem_node, memChildren_cons]
      have hresn : ({ sp with target := t'' } : Spot α).node
          = node sp.keysR (t'' :: sp.childrenR) := by
        simp [Spot.node, hkL0, hcL0]
      have hresmem : ∀ b, Mem b ({ sp with target := t'' } : Spot α).node ↔
          (b ∈ sp.keysR ∨ Mem b t'' ∨ MemChildren b sp.childrenR) := by
        intro b
        rw [hresn, mem_node, memChildren_cons]
      refine ⟨({ sp with target := t'' } : Spot α).node, m, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
      · simp only [takeMin]
        exact congrArg
          (fun r : Node α × Option α => (({ sp with target := r.1 } : Spot α).node, r.2)) heq
      · exact (hnodemem m).mpr (Or.inr (Or.inl hmemm))
      · intro b hbm
        rcases (hnodemem b).mp hbm with h | h | h
        · exact le_of_lt (hafter b (Or.inl h))
        · exact hmin b h
        · exact le_of_lt (hafter b (Or.inr h))
      · intro b
        rw [hresmem b, hnodemem b]
        constructor
        · rintro (h | h | h)
          · exact ⟨Or.inl h, (ne_of_lt (hafter b (Or.inl h))).symm⟩
          · exact ⟨Or.inr (Or.inl ((hiff b).mp h).1), ((hiff b).mp h).2⟩
          · exact ⟨Or.inr (Or.inr h), (ne_of_lt (hafter b (Or.inr h))).symm⟩
        · rintro ⟨h | h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ((hiff b).mpr ⟨h, hne⟩))
          · exact Or.inr (Or.inr h)
      · intro b hbm
        rcases (hresmem b).mp hbm with h | h | h
        · exact hafter b (Or.inl h)
        · exact hgtm b h
        · exact hafter b (Or.inr h)
      · have := hput t'' hlegt.1
        simpa [hresn] using this
      · rw [hresn]
        simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlegt.2.1
        · exact hdall x (by rw [hspc]; simp [hx])
      · rw [hresn]
        have hkl : (nodeKeys sp.node).length = sp.keysR.length := by simp [hspn]
        have hk0 : (nodeKeys sp0.node).length = ks.length := by simp [hsp0n]
        rw [hkl, hk0] at hcnt1 hcnt2
        have hub : ks.length ≤ 2 * deg - 1 := hk.2.1
        refine ⟨show deg - 1 ≤ sp.keysR.length by omega, by omega, ?_⟩
        refine (childrenKeyCountOk_iff _).mpr ?_
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hlegt.2.2
        · exact hkall x (by rw [hspc]; simp [hx])

end BTree.Node

end AlgoDesign.Searching
