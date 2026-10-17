/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Spec
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Pairwise

/-!
# The 1D range tree: the build

From sorted keys, repeats allowed: a single key is a leaf; otherwise the first `⌈n/2⌉` keys go
left, so the left part ends with the **lower median**, and that key is the split. The Rust and
the Python build the same way. The build stores exactly its keys (`leaves_build`) and keeps both
box invariants (`keysSeparate_build`, `splitsHalve_build`, `valid_build`); its split is the
largest key on its left (`build_split_mem` with `keysSeparate_build`).

`ofList` is the build the contract names, as the Rust's `RangeTree1D::new` runs it: keys in any
order are sorted first, and no keys build no tree (`ofList_eq_none`). It stores the keys sorted
(`leaves_ofList`) and keeps both invariants (`valid_ofList`).
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace RangeTree1D

variable {α : Type}

/-- How many keys go left: `⌈n/2⌉`, so the left part ends with the lower median. -/
def half (xs : List α) : ℕ := (xs.length + 1) / 2

theorem take_half_ne_nil {xs : List α} (h : xs ≠ []) : xs.take (half xs) ≠ [] := by
  have : 0 < xs.length := List.length_pos_iff.mpr h
  simp only [ne_eq, List.take_eq_nil_iff, half, not_or]
  exact ⟨by omega, h⟩

theorem drop_half_ne_nil {xs : List α} (hlen : ¬ xs.length ≤ 1) : xs.drop (half xs) ≠ [] := by
  simp only [ne_eq, List.drop_eq_nil_iff, half]
  omega

/-- Build from a sorted list (repeats allowed). A single key is a leaf; otherwise the first
`⌈n/2⌉` keys go left, and the last of them, the **lower median**, is the split. -/
def build (xs : List α) (h : xs ≠ []) : RangeTree1D α :=
  if hlen : xs.length ≤ 1 then leaf (xs.head h)
  else
    node ((xs.take (half xs)).getLast (take_half_ne_nil h))
      (build (xs.take (half xs)) (take_half_ne_nil h))
      (build (xs.drop (half xs)) (drop_half_ne_nil hlen))
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- The build stores exactly the keys it was given, in order. -/
theorem leaves_build (xs : List α) (h : xs ≠ []) : leaves (build xs h) = xs := by
  rw [build]
  split_ifs with hlen
  · match xs, h, hlen with
    | [a], _, _ => rfl
    | _ :: _ :: _, _, hlen => simp at hlen
  · simp only [leaves]
    rw [leaves_build, leaves_build, List.take_append_drop]
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- **The build keeps box invariant 2**, for any keys: every node sends `⌈n/2⌉` left. -/
theorem splitsHalve_build (xs : List α) (h : xs ≠ []) : SplitsHalve (build xs h) := by
  rw [build]
  split_ifs with hlen
  · trivial
  · refine ⟨?_, ?_, splitsHalve_build _ _, splitsHalve_build _ _⟩ <;>
      simp only [leaves_build, List.length_take, List.length_drop, half] <;> omega
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- The split key `build` chooses is one of the keys on its left. With `keysSeparate_build` (it
is `≥` every key on the left), it is **the largest key on its left**: the lower median. -/
theorem build_split_mem {xs : List α} {h : xs ≠ []} {s : α} {l r : RangeTree1D α}
    (hb : build xs h = node s l r) : s ∈ leaves l := by
  rw [build] at hb
  split_ifs at hb with hlen
  obtain ⟨rfl, rfl, rfl⟩ := RangeTree1D.node.inj hb
  rw [leaves_build]
  exact List.getLast_mem _

variable [LinearOrder α]

/-- In a sorted list, every element is at most the last. -/
theorem le_getLast_of_pairwise {xs : List α} (hs : xs.Pairwise (· ≤ ·)) (h : xs ≠ [])
    {x : α} (hx : x ∈ xs) : x ≤ xs.getLast h := by
  rw [← List.dropLast_append_getLast h] at hs hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (List.pairwise_append.mp hs).2.2 x hx _ (List.mem_singleton_self _)
  · rw [List.mem_singleton.mp hx]

/-- **The build keeps box invariant 1**, for any sorted keys, repeats included. -/
theorem keysSeparate_build (xs : List α) (h : xs ≠ []) (hs : xs.Pairwise (· ≤ ·)) :
    KeysSeparate (build xs h) := by
  rw [build]
  split_ifs with hlen
  · trivial
  · have hsplit := hs
    rw [← List.take_append_drop (half xs) xs] at hsplit
    refine ⟨fun x hx => ?_, fun x hx => ?_,
      keysSeparate_build _ _ (hs.sublist (List.take_sublist _ _)),
      keysSeparate_build _ _ (hs.sublist (List.drop_sublist _ _))⟩
    · rw [leaves_build] at hx
      exact le_getLast_of_pairwise (hs.sublist (List.take_sublist _ _)) _ hx
    · rw [leaves_build] at hx
      exact (List.pairwise_append.mp hsplit).2.2 _ (List.getLast_mem _) x hx
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- **The build of sorted keys is valid.** -/
theorem valid_build (xs : List α) (h : xs ≠ []) (hs : xs.Pairwise (· ≤ ·)) :
    Valid (build xs h) :=
  ⟨keysSeparate_build xs h hs, splitsHalve_build xs h⟩

/-- The keys sorted, least first, repeats kept. -/
def sortKeys (xs : List α) : List α := xs.insertionSort (· ≤ ·)

theorem sortKeys_perm (xs : List α) : (sortKeys xs).Perm xs := List.perm_insertionSort _ _

theorem sortKeys_sorted (xs : List α) : (sortKeys xs).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ _

theorem sortKeys_ne_nil {xs : List α} (h : xs ≠ []) : sortKeys xs ≠ [] :=
  fun h' => h (List.Perm.nil_eq (h' ▸ sortKeys_perm xs)).symm

/-- **The build from keys in any order**: sort them, then build; `none` for no keys. -/
def ofList (xs : List α) : Option (RangeTree1D α) :=
  if h : xs = [] then none else some (build (sortKeys xs) (sortKeys_ne_nil h))

theorem ofList_eq_none {xs : List α} : ofList xs = none ↔ xs = [] := by
  unfold ofList; split_ifs with h <;> simp [h]

theorem ofList_eq_some {xs : List α} {t : RangeTree1D α} (h : ofList xs = some t) :
    ∃ hne : xs ≠ [], build (sortKeys xs) (sortKeys_ne_nil hne) = t := by
  unfold ofList at h
  split_ifs at h with hne
  exact ⟨hne, Option.some.inj h⟩

/-- **The build stores exactly the keys it was given, sorted.** -/
theorem leaves_ofList {xs : List α} {t : RangeTree1D α} (h : ofList xs = some t) :
    (leaves t).Perm xs ∧ (leaves t).Pairwise (· ≤ ·) := by
  obtain ⟨hne, rfl⟩ := ofList_eq_some h
  rw [leaves_build]
  exact ⟨sortKeys_perm xs, sortKeys_sorted xs⟩

/-- **Every tree the build makes is valid.** -/
theorem valid_ofList {xs : List α} {t : RangeTree1D α} (h : ofList xs = some t) : Valid t := by
  obtain ⟨hne, rfl⟩ := ofList_eq_some h
  exact valid_build _ _ (sortKeys_sorted xs)

end RangeTree1D
end AlgoDesign.Geometry
