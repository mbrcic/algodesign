/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RankSelect.Spec

/-!
# Rank and select: the counting laws

`select` is a right inverse of `rank` (`rank_select`, `select_eq_some_iff`, `select_rank`), and
over two symbols `occ` is `rank` (`occ_eq_rank`). `rank` saturates past the end, as `List.take`
does.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- `rank` never runs backwards. -/
theorem rank_mono (b : List Bool) {i j : Nat} (h : i ≤ j) : rank b i ≤ rank b j := by
  have hs : List.Sublist (b.take i) (b.take j) := by
    have := List.take_sublist i (b.take j)
    rwa [List.take_take, Nat.min_eq_left h] at this
  exact (hs.filter id).length_le

/-- `rank b i` is at most `i`. -/
theorem rank_le (b : List Bool) (i : Nat) : rank b i ≤ i :=
  Nat.le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

/-- One step of `rank`, for every `k`: past the end `b[k]!` reads `false`. -/
theorem rank_succ (b : List Bool) (k : Nat) :
    rank b (k + 1) = rank b k + (if b[k]! = true then 1 else 0) := by
  have hk : b[k]! = (b[k]?).getD false := by
    cases h : b[k]? with
    | none => simp [getElem!_def, h]
    | some x => simp [getElem!_def, h]
  simp only [rank, List.take_add_one, List.filter_append, List.length_append, hk]
  cases h : b[k]? with
  | none => simp
  | some x => cases x <;> simp

/-- `select` is a right inverse of `rank`: its answer is a set bit of rank `j`. -/
theorem rank_select (b : List Bool) (j i : Nat) (h : select b j = some i) :
    b[i]! = true ∧ rank b i = j := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

/-- `select b j = some i` exactly when `i` is a set bit of rank `j` inside the vector. Backward:
an earlier set bit has rank below `j`, so the scan does not stop there. -/
theorem select_eq_some_iff (b : List Bool) (j i : Nat) :
    select b j = some i ↔ i < b.length ∧ b[i]! = true ∧ rank b i = j := by
  unfold select
  rw [List.find?_range_eq_some]
  simp only [Bool.and_eq_true, beq_iff_eq, List.mem_range, Bool.not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, -⟩; exact ⟨h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩
    refine ⟨⟨h1, h2⟩, h3, fun k hk => ?_⟩
    cases hb : b[k]!
    · rfl
    · have hne : rank b k ≠ j := by
        intro hrk
        have hstep := rank_succ b k
        simp only [hb, ite_true] at hstep
        have hmono := rank_mono b (show k + 1 ≤ i by omega)
        omega
      simpa using hne

/-- At a set bit inside the vector, `select` of its rank finds it again. -/
theorem select_rank (b : List Bool) (i : Nat) (hi : i < b.length) (hb : b[i]! = true) :
    select b (rank b i) = some i :=
  (select_eq_some_iff b (rank b i) i).mpr ⟨hi, hb, rfl⟩

/-- Over two symbols, `occ` is `rank`. -/
theorem occ_eq_rank (b : List Bool) (i : Nat) :
    occ (b.map fun x => if x then 1 else 0) 1 i = rank b i := by
  have hp : ((fun x : Nat => x == 1) ∘ fun x : Bool => if x then 1 else 0) = id := by
    funext x; cases x <;> rfl
  simp only [occ, rank, ← List.map_take, List.filter_map, List.length_map, hp]

end AlgoDesign.Strings
