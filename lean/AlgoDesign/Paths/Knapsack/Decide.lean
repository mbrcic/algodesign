/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Knapsack.Spec

/-! # Knapsack as a longest path: deciding the definitions

Each piece of `Valid`, `Valid` itself, `Fits` and `IsBest` decide on concrete items, so `decide`
checks small cases. A question about every path into layer `i` decides through the `2 ^ i` lists
of `i` moves; a question about every packing, through the sublists of the item indices. -/

@[expose] public section

namespace AlgoDesign.Paths.Knapsack

variable {items : List Item} {C : ℕ}

instance (b : Option ℤ) (g : ℤ) : Decidable (AtLeast b g) := by
  cases b <;> unfold AtLeast <;> infer_instance

/-! ## Moves: every path into layer `i` has `i` moves -/

theorem next_skip {v v' : ℕ × ℕ} :
    next items C v .skip = some v' ↔ v.1 < items.length ∧ v' = (v.1 + 1, v.2) := by
  obtain ⟨i, w⟩ := v
  simp only [next]
  split_ifs with h <;> simp [h, eq_comm]

theorem next_take {v v' : ℕ × ℕ} :
    next items C v .take = some v' ↔ v.1 < items.length ∧ v.2 + (item items v.1).weight ≤ C ∧
      v' = (v.1 + 1, v.2 + (item items v.1).weight) := by
  obtain ⟨i, w⟩ := v
  simp only [next]
  split_ifs with h <;> simp [h, eq_comm]
  omega

/-- **Every move decides one more item**: a path of `k` moves from `(i, w)` arrives in layer
`i + k`. -/
theorem follow_fst {v v' : ℕ × ℕ} {p : List Move} (h : follow items C v p = some v') :
    v'.1 = v.1 + p.length := by
  induction p generalizing v with
  | nil => simp only [follow, Option.some.injEq] at h; subst h; simp
  | cons m p ih =>
    simp only [follow] at h
    cases hm : next items C v m with
    | none => rw [hm] at h; cases h
    | some v₁ =>
      rw [hm, Option.bind_some] at h
      have h₁ : v₁.1 = v.1 + 1 := by
        cases m
        · exact ((next_skip.1 hm).2 ▸ rfl)
        · exact ((next_take.1 hm).2.2 ▸ rfl)
      rw [ih h, h₁, List.length_cons]
      omega

theorem length_of_isPath {p : List Move} {v : ℕ × ℕ} (h : IsPath items C p v) : p.length = v.1 := by
  have := follow_fst h
  simp at this
  omega

/-! ## The definitions decided -/

/-- Every list of `k` moves. -/
def movesOfLength : ℕ → List (List Move)
  | 0 => [[]]
  | k + 1 => (movesOfLength k).flatMap fun p => [.skip :: p, .take :: p]

theorem mem_movesOfLength {k : ℕ} {p : List Move} : p ∈ movesOfLength k ↔ p.length = k := by
  induction k generalizing p with
  | zero => simp [movesOfLength]
  | succ k ih =>
    simp only [movesOfLength, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨q, hq, rfl | rfl⟩ <;> simp [ih.1 hq]
    · intro h
      cases p with
      | nil => simp at h
      | cons m q =>
        refine ⟨q, ih.2 (by simpa using h), ?_⟩
        cases m <;> simp

instance (items : List Item) (C : ℕ) (p : List Move) (v : ℕ × ℕ) :
    Decidable (IsPath items C p v) := by
  unfold IsPath; infer_instance

theorem longestTo_iff {items : List Item} {C : ℕ} {v : ℕ × ℕ} {b : Option ℤ} :
    LongestTo items C v b ↔
      (∀ p ∈ movesOfLength v.1, IsPath items C p v → AtLeast b (pathGain items 0 p)) ∧
        ∀ d ∈ b, ∃ p ∈ movesOfLength v.1, IsPath items C p v ∧ pathGain items 0 p = d := by
  unfold LongestTo
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p _ hp => h1 p hp, fun d hd => ?_⟩
    obtain ⟨p, hp, hg⟩ := h2 d hd
    exact ⟨p, mem_movesOfLength.2 (length_of_isPath hp), hp, hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => h1 p (mem_movesOfLength.2 (length_of_isPath hp)) hp, fun d hd => ?_⟩
    obtain ⟨p, -, hp, hg⟩ := h2 d hd
    exact ⟨p, hp, hg⟩

instance decidableLongestTo (items : List Item) (C : ℕ) (v : ℕ × ℕ) (b : Option ℤ) :
    Decidable (LongestTo items C v b) :=
  decidable_of_iff' _ longestTo_iff

instance decidableFits (items : List Item) (C : ℕ) (S : List ℕ) : Decidable (Fits items C S) := by
  unfold Fits; infer_instance

theorem isBest_iff {items : List Item} {C : ℕ} {b : ℤ} :
    IsBest items C b ↔
      (∃ S ∈ (List.range items.length).sublists, Fits items C S ∧ valueOf items S = b) ∧
        ∀ S ∈ (List.range items.length).sublists, Fits items C S → valueOf items S ≤ b := by
  unfold IsBest
  constructor
  · rintro ⟨⟨S, hS, hv⟩, h⟩
    exact ⟨⟨S, List.mem_sublists.2 hS.1, hS, hv⟩, fun S _ hS => h S hS⟩
  · rintro ⟨⟨S, -, hS, hv⟩, h⟩
    exact ⟨⟨S, hS, hv⟩, fun S hS => h S (List.mem_sublists.2 hS.1) hS⟩

instance decidableIsBest (items : List Item) (C : ℕ) (b : ℤ) : Decidable (IsBest items C b) :=
  decidable_of_iff' _ isBest_iff

instance decidableLayersHoldLongest (items : List Item) (C : ℕ) (st : State) :
    Decidable (LayersHoldLongest items C st) := by
  unfold LayersHoldLongest; infer_instance

instance decidableDecidedAtMostItems (items : List Item) (st : State) :
    Decidable (DecidedAtMostItems items st) := by
  unfold DecidedAtMostItems; infer_instance

instance decidableValid (items : List Item) (C : ℕ) (st : State) :
    Decidable (Valid items C st) := by
  unfold Valid; infer_instance

end AlgoDesign.Paths.Knapsack
