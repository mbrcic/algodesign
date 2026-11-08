/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sequential search

Sources: the Search chapter, "Checking one place at a time"; Sedgewick and Wayne, *Algorithms*
(4th ed.), §3.1, Algorithm 3.1, except that a new key is appended, as in the chapter's trace.

The stored list has no duplicate keys: building keeps it (`nodup_buildM`, `mem_buildM`). The scan
returns list membership (`ret_containsM_tickEq`) and costs at most `xs.length` comparisons,
exactly that on a miss (`time_containsM_tickEq_le`, `time_containsM_tickEq_eq_length_of_not_mem`);
building `n` keys costs `n * (n - 1) / 2` (`time_buildM_eq`). The scan's running state is
`SequentialSearch.Scan`, and `SequentialSearch.Valid` what it keeps.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

-- `Type`, not `Type*`: `Bool` and `List α` share one monadic `>>=` chain, so one universe.
variable {α : Type} {m} [Monad m]

/-- A monadic linear scan: does `a` occur in `xs`, comparing elements via `eq`? -/
def containsM (eq : α → α → m Bool) (a : α) : List α → m Bool
  | [] => pure false
  | b :: l => eq a b >>= fun found => if found then pure true else containsM eq a l

@[simp]
theorem containsM_nil (eq : α → α → m Bool) (a : α) : containsM eq a [] = pure false := rfl

@[simp]
theorem containsM_cons (eq : α → α → m Bool) (a b : α) (l : List α) :
    containsM eq a (b :: l) =
      eq a b >>= fun found => if found then pure true else containsM eq a l := rfl

/-- `containsM` instantiated with `Cslib.Algorithms.Lean.TimeM ℕ`: charges one tick per
comparison, via `DecidableEq`. -/
def tickEq [DecidableEq α] (a b : α) : TimeM ℕ Bool := do
  tick 1
  pure (decide (a = b))

@[simp]
theorem ret_tickEq [DecidableEq α] (a b : α) : (tickEq a b).ret = decide (a = b) := rfl

@[simp]
theorem time_tickEq [DecidableEq α] (a b : α) : (tickEq a b).time = 1 := rfl

/-- **Proposition A, upper bound**: a scan costs at most `xs.length` comparisons. -/
theorem time_containsM_tickEq_le [DecidableEq α] (a : α) (xs : List α) :
    (containsM tickEq a xs).time ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons b l ih =>
    simp only [containsM_cons, time_bind, time_tickEq, ret_tickEq, List.length_cons]
    by_cases hab : a = b <;> simp [hab]
    omega

/-- **Proposition A**: on a search miss, every element gets compared: the cost equals
`xs.length`. -/
theorem time_containsM_tickEq_eq_length_of_not_mem [DecidableEq α] {a : α} {xs : List α}
    (h : a ∉ xs) : (containsM tickEq a xs).time = xs.length := by
  induction xs with
  | nil => simp
  | cons b l ih =>
    rw [List.mem_cons, not_or] at h
    simp only [containsM_cons, time_bind, time_tickEq, ret_tickEq, List.length_cons]
    simp [h.1, ih h.2]
    omega

/-- A search miss also never *returns* found. -/
theorem ret_containsM_tickEq_of_not_mem [DecidableEq α] {a : α} {xs : List α} (h : a ∉ xs) :
    (containsM tickEq a xs).ret = false := by
  induction xs with
  | nil => simp
  | cons b l ih =>
    rw [List.mem_cons, not_or] at h
    simp only [containsM_cons, ret_bind, ret_tickEq]
    simp [h.1, ih h.2]

/-- The instrumented scan returns exactly the ordinary list membership decision. -/
theorem ret_containsM_tickEq [DecidableEq α] (a : α) (xs : List α) :
    (containsM tickEq a xs).ret = decide (a ∈ xs) := by
  induction xs with
  | nil => simp [containsM_nil]
  | cons b xs ih =>
    by_cases hab : a = b <;>
      simp [containsM_cons, ret_bind, ret_tickEq, hab, ih]

/-- Insert the keys of `ks` one at a time onto the **end** of an accumulator, skipping any already
present (checked via `containsM tickEq`). The order decides which probe finds a repeated key. -/
def buildAux [DecidableEq α] : List α → List α → TimeM ℕ (List α)
  | acc, [] => pure acc
  | acc, k :: ks => do
      let dup : Bool ← containsM tickEq k acc
      buildAux (if dup then acc else acc ++ [k]) ks

@[simp]
theorem buildAux_nil [DecidableEq α] (acc : List α) : buildAux acc [] = pure acc := rfl

@[simp]
theorem buildAux_cons [DecidableEq α] (acc : List α) (k : α) (ks : List α) :
    buildAux acc (k :: ks) =
      containsM tickEq k acc >>= fun dup => buildAux (if dup then acc else acc ++ [k]) ks := rfl

/-- Building a `Nodup` list onto a disjoint accumulator costs exactly
`∑ i ∈ range ks.length, (acc.length + i)`: every scan is a full miss. -/
theorem time_buildAux_eq [DecidableEq α] {ks : List α} (h : ks.Nodup) :
    ∀ {acc : List α}, (∀ k ∈ ks, k ∉ acc) →
      (buildAux acc ks).time = ∑ i ∈ Finset.range ks.length, (acc.length + i) := by
  induction ks with
  | nil => intro acc _; simp
  | cons k ks ih =>
    intro acc hacc
    rw [List.nodup_cons] at h
    have hk_acc : k ∉ acc := hacc k (List.mem_cons_self ..)
    have hks_acc : ∀ j ∈ ks, j ∉ (acc ++ [k]) := by
      intro j hj
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hacc j (List.mem_cons_of_mem _ hj), fun he => h.1 (he ▸ hj)⟩
    simp [buildAux_cons, time_bind, ret_containsM_tickEq_of_not_mem hk_acc,
      time_containsM_tickEq_eq_length_of_not_mem hk_acc, ih h.2 hks_acc,
      Finset.sum_range_succ', add_comm, add_left_comm]

/-- Build a `Nodup` list of keys one insert at a time, from scratch. -/
def buildM [DecidableEq α] (ks : List α) : TimeM ℕ (List α) := buildAux [] ks

/-- Building extends the accumulator's key set by exactly the input keys. -/
theorem mem_buildAux [DecidableEq α] (ks : List α) :
    ∀ (acc : List α) (a : α), a ∈ (buildAux acc ks).ret ↔ a ∈ acc ∨ a ∈ ks := by
  induction ks with
  | nil => intro acc a; simp [buildAux_nil]
  | cons k ks ih =>
    intro acc a
    by_cases hk : k ∈ acc
    · simp [buildAux_cons, ret_bind, ret_containsM_tickEq, hk, ih]
      aesop
    · simp [buildAux_cons, ret_bind, ret_containsM_tickEq, hk, ih]
      aesop

/-- Building from an empty accumulator preserves exactly the input key set. -/
theorem mem_buildM [DecidableEq α] (ks : List α) (a : α) :
    a ∈ (buildM ks).ret ↔ a ∈ ks := by
  simpa [buildM] using mem_buildAux ks [] a

/-- Building preserves uniqueness of an initially duplicate-free accumulator. -/
theorem nodup_buildAux [DecidableEq α] (ks : List α) :
    ∀ (acc : List α), acc.Nodup → (buildAux acc ks).ret.Nodup := by
  induction ks with
  | nil => intro acc hacc; simpa [buildAux_nil] using hacc
  | cons k ks ih =>
    intro acc hacc
    by_cases hk : k ∈ acc
    · simpa [buildAux_cons, ret_bind, ret_containsM_tickEq, hk] using ih acc hacc
    · have hnd : (acc ++ [k]).Nodup := by
        simp only [List.nodup_append, List.nodup_singleton, true_and]
        refine ⟨hacc, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        exact fun he => hk (he ▸ ha)
      simpa [buildAux_cons, ret_bind, ret_containsM_tickEq, hk] using ih (acc ++ [k]) hnd

/-- Building removes duplicates from any input list. -/
theorem nodup_buildM [DecidableEq α] (ks : List α) : (buildM ks).ret.Nodup := by
  simpa [buildM] using nodup_buildAux ks [] (by simp)

/-- **Corollary**: building `n` distinct keys one insert at a time costs exactly
`n * (n - 1) / 2` comparisons. -/
theorem time_buildM_eq [DecidableEq α] {ks : List α} (h : ks.Nodup) :
    (buildM ks).time = ks.length * (ks.length - 1) / 2 := by
  have := time_buildAux_eq h (acc := []) (by simp)
  simpa [buildM, Finset.sum_range_id] using this

/-! ## The scan's running state -/

namespace SequentialSearch

/-- **The scan's running state**: the key looked for, the list scanned, and how many of its
positions have been compared so far. -/
structure Scan (α : Type) where
  /-- The key looked for. -/
  key : α
  /-- The list scanned. -/
  list : List α
  /-- How many positions, from the front, have been compared. -/
  checked : ℕ
  /-- The scan never passes the end of the list. -/
  checked_le : checked ≤ list.length

/-- The scan's first state: nothing compared yet. -/
def Scan.first (a : α) (xs : List α) : Scan α := ⟨a, xs, 0, Nat.zero_le _⟩

/-- The scan one position further on, past a position of the list. -/
def Scan.next (s : Scan α) (h : s.checked < s.list.length) : Scan α :=
  ⟨s.key, s.list, s.checked + 1, h⟩

/-- After each comparison: none of the positions compared holds the key. -/
def NoMatchBefore (s : Scan α) : Prop := s.key ∉ s.list.take s.checked

/-- **The scan's running state is valid**: no match among the positions compared. `valid_first`
starts it, `valid_next` keeps it past a position that is not the key, and `not_mem_of_valid` reads
a miss off it at the end of the list; together, a scan that answers "not found" is right
(`not_mem_of_containsM_tickEq`). -/
def Valid (s : Scan α) : Prop := NoMatchBefore s

instance [DecidableEq α] (s : Scan α) : Decidable (NoMatchBefore s) :=
  by unfold NoMatchBefore; infer_instance

instance [DecidableEq α] (s : Scan α) : Decidable (Valid s) :=
  by unfold Valid; infer_instance

/-- Before any comparison, no position has been checked. -/
theorem valid_first (a : α) (xs : List α) : Valid (Scan.first a xs) := by
  simp [Valid, NoMatchBefore, Scan.first]

/-- **One comparison keeps `Valid`**: a position that does not hold the key extends the stretch
without a match. -/
theorem valid_next {s : Scan α} (hv : Valid s) (h : s.checked < s.list.length)
    (hne : s.list[s.checked] ≠ s.key) : Valid (s.next h) := by
  unfold Valid NoMatchBefore Scan.next at *
  simp only
  rw [List.take_succ_eq_append_getElem h]
  simp only [List.mem_append, List.mem_singleton, not_or]
  exact ⟨hv, fun h' => hne h'.symm⟩

/-- **At the end of the list, `Valid` is a miss.** -/
theorem not_mem_of_valid {s : Scan α} (hv : Valid s) (hend : s.checked = s.list.length) :
    s.key ∉ s.list := by
  unfold Valid NoMatchBefore at hv
  rwa [hend, List.take_length] at hv

/-- **The scan reports a miss only on a miss.** From a valid state, if the comparisons left, over
the positions not yet compared, report no match, the key is not in the list: each comparison that
misses keeps `Valid` (`valid_next`), and at the end `Valid` is a miss (`not_mem_of_valid`). -/
theorem not_mem_of_scan [DecidableEq α] :
    ∀ (n : ℕ) (s : Scan α), s.list.length - s.checked = n → Valid s →
      (containsM tickEq s.key (s.list.drop s.checked)).ret = false → s.key ∉ s.list
  | 0, s, hn, hv, _ => not_mem_of_valid hv (by have := s.checked_le; omega)
  | n + 1, s, hn, hv, hret => by
      have h : s.checked < s.list.length := by omega
      rw [List.drop_eq_getElem_cons h] at hret
      simp only [containsM_cons, ret_bind, ret_tickEq] at hret
      by_cases hk : s.key = s.list[s.checked]
      · simp [hk] at hret
      · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte] at hret
        exact not_mem_of_scan n (s.next h) (by simp only [Scan.next]; omega)
          (valid_next hv h (Ne.symm hk)) hret

/-- **A scan that answers "not found" is right**, read through the scan's running state from its
first state (`valid_first`, `not_mem_of_scan`). -/
theorem not_mem_of_containsM_tickEq [DecidableEq α] {a : α} {xs : List α}
    (h : (containsM tickEq a xs).ret = false) : a ∉ xs :=
  not_mem_of_scan _ (Scan.first a xs) rfl (valid_first a xs) (by simpa [Scan.first] using h)

end SequentialSearch

end AlgoDesign.Searching
