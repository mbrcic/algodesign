/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Knapsack.Decide
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Knapsack as a longest path: paths and packings

The facts the walk's proofs share: the graph has no cycle, since every move decides one more item
(`follow_fst`, with the other move facts the decisions need, in `Knapsack/Decide.lean`); the paths
to the last layer and the packings that fit are the same thing; and the largest gain into a vertex
is the better of its two moves in. -/

@[expose] public section

namespace AlgoDesign.Paths.Knapsack

variable {items : List Item} {C : ℕ}

/-! ## Moves -/

theorem follow_append_singleton {v v'' : ℕ × ℕ} {p : List Move} {m : Move} :
    follow items C v (p ++ [m]) = some v'' ↔
      ∃ v', follow items C v p = some v' ∧ next items C v' m = some v'' := by
  induction p generalizing v with
  | nil =>
    simp only [List.nil_append, follow, Option.some.injEq, exists_eq_left']
    cases next items C v m <;> simp
  | cons m' p ih =>
    simp only [List.cons_append, follow]
    cases next items C v m' with
    | none => simp
    | some v₁ => simpa using ih

theorem pathGain_append_singleton (i : ℕ) (p : List Move) (m : Move) :
    pathGain items i (p ++ [m]) = pathGain items i p + gain items (i + p.length) m := by
  induction p generalizing i with
  | nil => simp [pathGain]
  | cons m' p ih =>
    simp only [List.cons_append, pathGain, ih, List.length_cons]
    rw [show i + 1 + p.length = i + (p.length + 1) by omega]
    omega

/-- A path keeps the weight used within the capacity. -/
theorem follow_snd_le {v v' : ℕ × ℕ} {p : List Move} (hv : v.2 ≤ C)
    (h : follow items C v p = some v') : v'.2 ≤ C := by
  induction p generalizing v with
  | nil => simp only [follow, Option.some.injEq] at h; subst h; exact hv
  | cons m p ih =>
    simp only [follow] at h
    cases hm : next items C v m with
    | none => rw [hm] at h; cases h
    | some v₁ =>
      rw [hm, Option.bind_some] at h
      refine ih ?_ h
      cases m
      · rw [(next_skip.1 hm).2]; exact hv
      · rw [(next_take.1 hm).2.2]; exact (next_take.1 hm).2.1

/-- **The graph has no cycle.** -/
theorem no_cycle (items : List Item) (C : ℕ) : NoCycle items C := by
  intro v p hp h
  have := follow_fst h
  have : p.length ≠ 0 := by simpa using hp
  omega

/-- **A path comes apart at its last move**: a path into layer `i + 1` is a path into layer `i`,
then a skip or a take. -/
theorem IsPath.eq_snoc {p : List Move} {i w : ℕ} (h : IsPath items C p (i + 1, w)) :
    ∃ q m v, p = q ++ [m] ∧ IsPath items C q v ∧ v.1 = i ∧ next items C v m = some (i + 1, w) := by
  have hl := length_of_isPath h
  obtain ⟨q, m, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left (by rintro rfl; simp at hl)
  rw [List.concat_eq_append] at h hl ⊢
  obtain ⟨v, hv, hm⟩ := follow_append_singleton.1 h
  have := length_of_isPath (C := C) hv
  simp only [List.length_append, List.length_singleton] at hl
  exact ⟨q, m, v, rfl, hv, by omega, hm⟩

/-! ## Paths and packings -/

theorem packingOf_sublist (i : ℕ) (p : List Move) :
    (packingOf i p).Sublist (List.range' i p.length) := by
  induction p generalizing i with
  | nil => simp [packingOf]
  | cons m p ih =>
    rw [List.length_cons, List.range'_succ]
    cases m
    · exact (ih (i + 1)).cons i
    · exact (ih (i + 1)).cons_cons i

theorem not_mem_packingOf {i k : ℕ} {p : List Move} (hk : k < i) : k ∉ packingOf i p := fun h =>
  by have := List.mem_range'.1 ((packingOf_sublist i p).subset h); omega

theorem pathGain_eq_valueOf (i : ℕ) (p : List Move) :
    pathGain items i p = valueOf items (packingOf i p) := by
  induction p generalizing i with
  | nil => simp [pathGain, packingOf, valueOf]
  | cons m p ih =>
    cases m <;> simp [pathGain, packingOf, gain, ih, valueOf]

/-- The path that takes exactly the items a path takes is that path. -/
theorem map_range'_packingOf (i : ℕ) (p : List Move) :
    (List.range' i p.length).map (fun k => if k ∈ packingOf i p then Move.take else .skip) = p := by
  induction p generalizing i with
  | nil => simp
  | cons m p ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons]
    have htail : (List.range' (i + 1) p.length).map
        (fun k => if k ∈ packingOf i (m :: p) then Move.take else .skip) =
        (List.range' (i + 1) p.length).map
          (fun k => if k ∈ packingOf (i + 1) p then Move.take else .skip) := by
      refine List.map_congr_left fun k hk => ?_
      have hki : k ≠ i := by have := List.mem_range'.1 hk; omega
      have hmem : k ∈ packingOf i (m :: p) ↔ k ∈ packingOf (i + 1) p := by
        cases m <;> simp [packingOf, hki]
      by_cases h : k ∈ packingOf (i + 1) p <;> simp [h, hmem]
    rw [htail, ih]
    cases m
    · simp [packingOf, not_mem_packingOf (Nat.lt_succ_self i)]
    · simp [packingOf]

theorem follow_packingOf {i w : ℕ} {p : List Move} {v : ℕ × ℕ}
    (h : follow items C (i, w) p = some v) : v.2 = w + weightOf items (packingOf i p) := by
  induction p generalizing i w with
  | nil => simp only [follow, Option.some.injEq] at h; subst h; simp [packingOf, weightOf]
  | cons m p ih =>
    simp only [follow] at h
    cases hm : next items C (i, w) m with
    | none => rw [hm] at h; cases h
    | some v₁ =>
      rw [hm, Option.bind_some] at h
      cases m
      · obtain ⟨-, rfl⟩ := next_skip.1 hm
        rw [ih h]; simp [packingOf]
      · obtain ⟨-, -, rfl⟩ := next_take.1 hm
        rw [ih h]; simp [packingOf, weightOf]; omega

/-- The path that takes the items `S` among `i, …, i + k - 1` arrives at their weight, takes
exactly them, and gains their value. -/
theorem pathOf_spec (k : ℕ) :
    ∀ {i w : ℕ} {S : List ℕ}, S.Sublist (List.range' i k) → i + k ≤ items.length →
      w + weightOf items S ≤ C →
      let P := (List.range' i k).map fun k => if k ∈ S then Move.take else .skip
      follow items C (i, w) P = some (i + k, w + weightOf items S) ∧ packingOf i P = S ∧
        pathGain items i P = valueOf items S := by
  induction k with
  | zero =>
    intro i w S hS _ _
    simp only [List.range'_zero, List.sublist_nil] at hS
    subst hS
    simp [follow, packingOf, pathGain, weightOf, valueOf]
  | succ k ih =>
    intro i w S hS hn hw
    rw [List.range'_succ] at hS ⊢
    have hfar : ∀ T : List ℕ, T.Sublist (List.range' (i + 1) k) → i ∉ T := fun T hT hi => by
      have := List.mem_range'.1 (hT.subset hi); omega
    rcases List.sublist_cons_iff.1 hS with hS' | ⟨S', rfl, hS'⟩
    · have hiS := hfar S hS'
      obtain ⟨h1, h2, h3⟩ := ih (w := w) hS' (by omega) hw
      simp only [List.map_cons, hiS, ite_false, follow, next, show i < items.length by omega,
        ite_true, Option.bind_some, packingOf, pathGain, gain, zero_add]
      refine ⟨by rw [h1]; congr 2; omega, h2, h3⟩
    · have hiS := hfar S' hS'
      have hcongr : (List.range' (i + 1) k).map
          (fun k => if k ∈ i :: S' then Move.take else .skip) =
          (List.range' (i + 1) k).map (fun k => if k ∈ S' then Move.take else .skip) := by
        refine List.map_congr_left fun x hx => ?_
        have hxi : x ≠ i := by have := List.mem_range'.1 hx; omega
        simp [hxi]
      have hw' : w + (item items i).weight + weightOf items S' ≤ C := by
        simp only [weightOf, List.map_cons, List.sum_cons] at hw ⊢; omega
      obtain ⟨h1, h2, h3⟩ := ih (w := w + (item items i).weight) hS' (by omega) hw'
      simp only [List.map_cons, List.mem_cons_self, ite_true, hcongr, follow, next,
        show i < items.length by omega, show w + (item items i).weight ≤ C by omega, and_self,
        Option.bind_some, packingOf, pathGain, gain]
      refine ⟨by rw [h1]; simp only [weightOf, List.map_cons, List.sum_cons]; congr 2 <;> omega,
        by rw [h2], by rw [h3]; simp [valueOf]⟩

/-- **Paths are packings**, the chapter's argument: each path from `(0, 0)` to the last layer is
one packing that fits, and each packing that fits is one path, with the same value. -/
theorem paths_are_packings (items : List Item) (C : ℕ) : PathsArePackings items C := by
  refine ⟨fun p w hp => ?_, fun S hS => ?_⟩
  · have hl := length_of_isPath hp
    have hw := follow_packingOf hp
    simp only [zero_add] at hw
    have hsub := packingOf_sublist 0 p
    rw [hl, ← List.range_eq_range'] at hsub
    refine ⟨⟨hsub, ?_⟩, ?_, hw.symm, (pathGain_eq_valueOf 0 p).symm⟩
    · rw [← hw]; exact follow_snd_le (le_refl 0 |>.trans (Nat.zero_le C)) hp
    · have := map_range'_packingOf 0 p
      rw [hl, ← List.range_eq_range'] at this
      exact this
  · have hsub : S.Sublist (List.range' 0 items.length) := by
      rw [← List.range_eq_range']; exact hS.1
    obtain ⟨h1, h2, h3⟩ := pathOf_spec (items := items) (C := C) (w := 0) items.length hsub
      (by omega) (by simpa using hS.2)
    simp only [← List.range_eq_range', zero_add] at h1 h2 h3
    exact ⟨h1, h2, h3⟩

/-! ## The largest gain into a vertex -/

theorem atLeast_max_left {a : Option ℤ} (b : Option ℤ) {g : ℤ} (h : AtLeast a g) :
    AtLeast (max a b) g := by
  cases a with
  | none => exact absurd h id
  | some d =>
    cases b with
    | none => exact h
    | some e => exact le_trans (α := ℤ) h (le_max_left d e)

theorem atLeast_max_right (a : Option ℤ) {b : Option ℤ} {g : ℤ} (h : AtLeast b g) :
    AtLeast (max a b) g := by
  cases b with
  | none => exact absurd h id
  | some e =>
    cases a with
    | none => exact h
    | some d => exact le_trans (α := ℤ) h (le_max_right d e)

theorem mem_max {a b : Option ℤ} {d : ℤ} (h : d ∈ max a b) : d ∈ a ∨ d ∈ b := by
  cases a <;> cases b <;> simp_all [max_def]
  split_ifs at h <;> simp_all

/-- **The largest gain into `(i + 1, w)` is the better of its two moves in**: the skip from
`(i, w)`, and the take from `(i, w - weight i)` when it fits. -/
theorem longestTo_succ {i w : ℕ} (hi : i < items.length) {b₁ b₂ : Option ℤ}
    (h₁ : LongestTo items C (i, w) b₁)
    (h₂ : LongestTo items C (i, w - (item items i).weight) b₂) :
    LongestTo items C (i + 1, w) (max b₁
      (if (item items i).weight ≤ w ∧ w ≤ C then b₂.map (· + (item items i).value) else none)) := by
  refine ⟨fun p hp => ?_, fun d hd => ?_⟩
  · obtain ⟨q, m, v, rfl, hq, hv1, hm⟩ := hp.eq_snoc
    have hql : q.length = i := (length_of_isPath hq).trans hv1
    rw [pathGain_append_singleton, zero_add, hql]
    obtain ⟨v1, v2⟩ := v
    simp only at hv1
    subst hv1
    cases m
    · obtain ⟨-, he⟩ := next_skip.1 hm
      simp only [Prod.mk.injEq, true_and] at he
      subst he
      simp only [gain, add_zero]
      exact atLeast_max_left _ (h₁.1 q hq)
    · obtain ⟨-, hC, he⟩ := next_take.1 hm
      simp only [Prod.mk.injEq, true_and] at he
      subst he
      have hq' : IsPath items C q (v1, v2 + (item items v1).weight - (item items v1).weight) := by
        simpa using hq
      have hat := h₂.1 q hq'
      refine atLeast_max_right _ ?_
      split_ifs with hc
      swap
      · exact absurd ⟨by omega, hC⟩ hc
      cases hb : b₂ with
      | none => rw [hb] at hat; exact absurd hat id
      | some e =>
        rw [hb] at hat
        simp only [Option.map_some, gain, AtLeast] at hat ⊢
        omega
  · rcases mem_max hd with hd | hd
    · obtain ⟨q, hq, hg⟩ := h₁.2 d hd
      refine ⟨q ++ [.skip], follow_append_singleton.2 ⟨_, hq, next_skip.2 ⟨hi, rfl⟩⟩, ?_⟩
      rw [pathGain_append_singleton, hg]
      simp [gain]
    · split_ifs at hd with hc
      · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hd
        obtain ⟨q, hq, hg⟩ := h₂.2 e he
        refine ⟨q ++ [.take], follow_append_singleton.2 ⟨_, hq, next_take.2 ⟨hi, ?_, ?_⟩⟩, ?_⟩
        · simp only; omega
        · simp only [Prod.mk.injEq, true_and]; omega
        · rw [pathGain_append_singleton, hg, zero_add, (length_of_isPath hq)]
          simp [gain]
      · simp at hd

/-- A vertex has one largest gain. -/
theorem LongestTo.unique {v : ℕ × ℕ} {b b' : Option ℤ} (h : LongestTo items C v b)
    (h' : LongestTo items C v b') : b = b' := by
  cases b with
  | none =>
    cases b' with
    | none => rfl
    | some d' =>
      obtain ⟨p, hp, -⟩ := h'.2 d' rfl
      exact absurd (h.1 p hp) id
  | some d =>
    obtain ⟨p, hp, hg⟩ := h.2 d rfl
    cases b' with
    | none => exact absurd (h'.1 p hp) id
    | some d' =>
      obtain ⟨p', hp', hg'⟩ := h'.2 d' rfl
      have h1 := h'.1 p hp
      have h2 := h.1 p' hp'
      simp only [AtLeast] at h1 h2
      rw [Option.some.injEq]
      omega

/-- In layer 0 only `(0, 0)` is reached, with gain 0. -/
theorem longestTo_zero (w : ℕ) :
    LongestTo items C (0, w) (if w = 0 then some 0 else none) := by
  have hnil : ∀ p, IsPath items C p (0, w) → p = [] ∧ w = 0 := by
    intro p hp
    have := length_of_isPath hp
    simp only [List.length_eq_zero_iff] at this
    subst this
    simp only [IsPath, follow, Option.some.injEq, Prod.mk.injEq, true_and] at hp
    exact ⟨rfl, hp.symm⟩
  refine ⟨fun p hp => ?_, fun d hd => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hnil p hp
    simp [pathGain, AtLeast]
  · split_ifs at hd with hw
    · subst hw
      simp only [Option.mem_def, Option.some.injEq] at hd
      exact ⟨[], rfl, by simp [pathGain, hd]⟩
    · simp at hd

end AlgoDesign.Paths.Knapsack
