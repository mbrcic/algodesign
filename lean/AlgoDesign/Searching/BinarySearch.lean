/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Defs.LinearOrder

/-!
# Binary search on a sorted array

Sources: the Search chapter, "Binary search"; Sedgewick and Wayne, *Algorithms* (4th ed.), §3.1,
Algorithm 3.2, Proposition B.

On a sorted array (`BinarySearch.Sorted`) a present key stays in the closed stretch `[lo, hi]`
of the search's running state (`BinarySearch.Stretch`, `BinarySearch.Valid`). `search` returns an
index exactly when the key is present (`search_isSome_iff`), and a returned index holds it
(`searchM_sound`). Every probe halves the stretch, so at most `Nat.log2 n + 1` compares
(`searchProbes_le`), the exact cost of the recurrence `searchCost` (`time_searchCost_eq`).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- The assumption every theorem about the search makes: the array is in order, each element no
larger than the next. -/
def BinarySearch.Sorted {α : Type} [LinearOrder α] (xs : Array α) : Prop :=
  xs.toList.Pairwise (· ≤ ·)

instance {α : Type} [LinearOrder α] (xs : Array α) : Decidable (BinarySearch.Sorted xs) :=
  by unfold BinarySearch.Sorted; infer_instance

/-- The cost, in compares, of binary-searching `n` candidates: Sedgewick's recurrence
`C(N) = C(⌊N/2⌋) + 1`, always taking the never-found branch. -/
def searchCost : ℕ → TimeM ℕ Unit
  | 0 => pure ()
  | n + 1 => tick 1 *> searchCost ((n + 1) / 2)

@[simp] theorem searchCost_zero : searchCost 0 = pure () := by simp [searchCost]

theorem searchCost_succ (n : ℕ) :
    searchCost (n + 1) = tick 1 *> searchCost ((n + 1) / 2) := by simp [searchCost]

/-- **Proposition B**, exact form: `searchCost` on `n ≥ 1` candidates costs exactly
`Nat.log2 n + 1` compares. -/
theorem time_searchCost_eq {n : ℕ} (hn : 1 ≤ n) : (searchCost n).time = Nat.log2 n + 1 := by
  induction n using searchCost.induct with
  | case1 => omega
  | case2 n ih =>
    simp only [Nat.succ_eq_add_one] at *
    rw [searchCost_succ, Nat.log2_def]
    simp only [time_seqRight, time_tick]
    split
    · rename_i h2
      have hpos : 1 ≤ (n + 1) / 2 := by omega
      rw [ih hpos]
      omega
    · rename_i h2
      have h0 : (n + 1) / 2 = 0 := by omega
      simp [h0]

/-! ### The search itself -/

/-- Sedgewick's Algorithm 3.2: closed stretch `[lo, hi]` from `[0, N - 1]`, midpoint
`lo + (hi - lo) / 2`. A step left of `mid = 0` ends the search, since indices are unsigned. One
tick per probe, one three-way comparison of the key with `xs[mid]` (one or two `<` tests). -/
def searchM {α : Type} [LinearOrder α] (a : α) (xs : Array α) : ℕ → ℕ → TimeM ℕ (Option ℕ)
  | lo, hi =>
    if _h : lo ≤ hi then
      let mid := lo + (hi - lo) / 2
      match xs[mid]? with
      | none => ⟨none, 0⟩
      | some k =>
          if k < a then
            let r := searchM a xs (mid + 1) hi
            ⟨r.ret, r.time + 1⟩
          else if a < k then
            if _h0 : mid = 0 then ⟨none, 1⟩
            else
              let r := searchM a xs lo (mid - 1)
              ⟨r.ret, r.time + 1⟩
          else ⟨some mid, 1⟩
    else ⟨none, 0⟩
termination_by lo hi => hi + 1 - lo
decreasing_by
  · omega
  · omega

/-- The whole array's search, stretch `[0, xs.size - 1]`; an empty array costs nothing. -/
def searchTimed {α : Type} [LinearOrder α] (a : α) (xs : Array α) : TimeM ℕ (Option ℕ) :=
  if xs.size = 0 then ⟨none, 0⟩ else searchM a xs 0 (xs.size - 1)

/-- The index of `a` in a sorted array, or `none`. Cost erased. -/
def search {α : Type} [LinearOrder α] (a : α) (xs : Array α) : Option ℕ :=
  (searchTimed a xs).ret

/-- The three-way comparisons (probes) `search` makes; see `searchM` for the unit. -/
def searchProbes {α : Type} [LinearOrder α] (a : α) (xs : Array α) : ℕ :=
  (searchTimed a xs).time

/-- **What the search finds is really there.** Needs no sortedness: an index only comes back from
the branch that compared equal. -/
theorem searchM_sound {α : Type} [LinearOrder α] (a : α) (xs : Array α) (lo hi i : ℕ)
    (h : (searchM a xs lo hi).ret = some i) : xs[i]? = some a := by
  fun_induction searchM a xs lo hi with
  | case1 lo hi hle mid hmid => simp at h
  | case2 lo hi hle mid k hmid hlt r ih =>
      exact ih (by simpa [hle, hmid, hlt] using h)
  | case3 lo hi hle mid k hmid hge hlt h0 => simp at h
  | case4 lo hi hle mid k hmid hge hlt h0 r ih =>
      exact ih (by simpa [hle, hmid, hge, hlt, h0] using h)
  | case5 lo hi hle mid k hmid hge hge2 =>
      have hi' : i = mid := by simpa [hle, hmid, hge, hge2] using h.symm
      subst hi'
      have hk : k = a := le_antisymm (not_lt.mp hge2) (not_lt.mp hge)
      simpa [hk] using hmid
  | case6 lo hi hle => simp at h

theorem searchTimed_sound {α : Type} [LinearOrder α] (a : α) (xs : Array α) (i : ℕ)
    (h : (searchTimed a xs).ret = some i) : xs[i]? = some a := by
  unfold searchTimed at h
  split_ifs at h
  exact searchM_sound a xs _ _ i h

/-- The sortedness `isSome_of_valid` asks for, in index form: `xs[i] ≤ xs[j]` whenever `i ≤ j`. -/
theorem getElem_le_of_pairwise {α : Type} [LinearOrder α] {xs : Array α}
    (hs : BinarySearch.Sorted xs) {i j : ℕ} (hij : i ≤ j) (hj : j < xs.size) :
    xs[i]'(Nat.lt_of_le_of_lt hij hj) ≤ xs[j] := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · have := List.pairwise_iff_getElem.mp hs i j (by simp; omega) (by simpa using hj) h
    simpa using this
  · subst h; exact le_refl _

/-! ## The search's running state -/

namespace BinarySearch

variable {α : Type} [LinearOrder α]

/-- **Binary search's running state**: the key looked for, the array searched, and the closed
stretch `[lo, hi]` of indices still in play. -/
structure Stretch (α : Type) where
  /-- The key looked for. -/
  key : α
  /-- The array searched. -/
  array : Array α
  /-- The stretch's first index. -/
  lo : ℕ
  /-- The stretch's last index. -/
  hi : ℕ

/-- The search's first stretch: the whole array, `[0, xs.size - 1]`. -/
def Stretch.first (a : α) (xs : Array α) : Stretch α := ⟨a, xs, 0, xs.size - 1⟩

/-- After each probe: the stretch ends inside the array. -/
def StretchInArray (w : Stretch α) : Prop := w.hi < w.array.size

/-- After each probe: every index holding the key lies in the stretch — the bracket. -/
def KeyInStretch (w : Stretch α) : Prop :=
  ∀ j, j < w.array.size → w.array[j]? = some w.key → w.lo ≤ j ∧ j ≤ w.hi

/-- **Binary search's running state is valid**: the stretch ends inside the array and brackets
every index holding the key. `valid_first` starts it; on a sorted array `valid_right` and
`valid_left` keep it through a probe that misses, and `isSome_of_valid` says a key that is there
is then found. -/
def Valid (w : Stretch α) : Prop := StretchInArray w ∧ KeyInStretch w

instance (w : Stretch α) : Decidable (StretchInArray w) :=
  by unfold StretchInArray; infer_instance

instance (w : Stretch α) : Decidable (KeyInStretch w) :=
  inferInstanceAs (Decidable
    (∀ j, j < w.array.size → w.array[j]? = some w.key → w.lo ≤ j ∧ j ≤ w.hi))

instance (w : Stretch α) : Decidable (Valid w) :=
  by unfold Valid; infer_instance

omit [LinearOrder α] in
/-- **The first stretch is valid**, on a non-empty array: it is the whole array. -/
theorem valid_first (a : α) {xs : Array α} (h : 0 < xs.size) : Valid (Stretch.first a xs) :=
  ⟨by simp only [StretchInArray, Stretch.first]; omega,
    fun j hj _ => by simp only [Stretch.first] at hj ⊢; omega⟩

/-- **A probe below the key keeps `Valid`**: on a sorted array, every index holding the key is
past `mid`. -/
theorem valid_right {w : Stretch α} (hs : Sorted w.array) (hv : Valid w) {mid : ℕ}
    (hmid : mid < w.array.size) (hlt : w.array[mid] < w.key) :
    Valid { w with lo := mid + 1 } := by
  obtain ⟨hhi, hkey⟩ := hv
  refine ⟨hhi, fun j hj hxj => ⟨?_, (hkey j hj hxj).2⟩⟩
  by_contra hle'
  have hxj' : w.array[j] = w.key := by simpa [hj] using hxj
  have := getElem_le_of_pairwise hs (i := j) (j := mid) (by simp at hle'; omega) hmid
  rw [hxj'] at this
  exact absurd hlt (not_lt.mpr this)

/-- **A probe above the key keeps `Valid`**: on a sorted array, every index holding the key is
before `mid`. -/
theorem valid_left {w : Stretch α} (hs : Sorted w.array) (hv : Valid w) {mid : ℕ}
    (hmid : mid < w.array.size) (hlt : w.key < w.array[mid]) :
    Valid { w with hi := mid - 1 } := by
  obtain ⟨-, hkey⟩ := hv
  refine ⟨by simp only [StretchInArray]; omega, fun j hj hxj => ⟨(hkey j hj hxj).1, ?_⟩⟩
  by_contra hle'
  have hxj' : w.array[j] = w.key := by simpa [hj] using hxj
  have := getElem_le_of_pairwise hs (i := mid) (j := j) (by simp at hle'; omega) hj
  rw [hxj'] at this
  exact absurd hlt (not_lt.mpr this)

/-- **`Valid` gives the answer**: on a sorted array, searching a stretch that brackets the key
finds it, when it is there. Each probe that misses keeps `Valid` (`valid_right`, `valid_left`),
so the stretch never loses the key; a probe left of index `0` cannot miss it, and `hi` inside the
array means `xs[mid]?` never misses. -/
theorem isSome_of_valid {w : Stretch α} (hs : Sorted w.array) (hv : Valid w) {j : ℕ}
    (hj : j < w.array.size) (hxj : w.array[j]? = some w.key) :
    ((searchM w.key w.array w.lo w.hi).ret).isSome := by
  obtain ⟨a, xs, lo, hi⟩ := w
  simp only at hs hj hxj ⊢
  fun_induction searchM a xs lo hi with
  | case1 lo hi hle mid hmid =>
      exfalso
      have : mid < xs.size := by have := hv.1; simp only [StretchInArray] at this; omega
      simp [this] at hmid
  | case2 lo hi hle mid k hmid hlt r ih =>
      have hmid' : mid < xs.size := by have := hv.1; simp only [StretchInArray] at this; omega
      have hk : xs[mid] = k := by simpa [hmid'] using hmid
      exact ih (valid_right (w := ⟨a, xs, lo, hi⟩) hs hv hmid' (by simpa [hk] using hlt))
  | case3 lo hi hle mid k hmid hge hlt h0 =>
      exfalso
      have hmid' : mid < xs.size := by have := hv.1; simp only [StretchInArray] at this; omega
      have hk : xs[mid] = k := by simpa [hmid'] using hmid
      have hxj' : xs[j] = a := by simpa [hj] using hxj
      have := getElem_le_of_pairwise hs (i := mid) (j := j) (by omega) hj
      rw [hk, hxj'] at this
      exact absurd hlt (not_lt.mpr this)
  | case4 lo hi hle mid k hmid hge hlt h0 r ih =>
      have hmid' : mid < xs.size := by have := hv.1; simp only [StretchInArray] at this; omega
      have hk : xs[mid] = k := by simpa [hmid'] using hmid
      exact ih (valid_left (w := ⟨a, xs, lo, hi⟩) hs hv hmid' (by simpa [hk] using hlt))
  | case5 lo hi hle mid k hmid hge hge2 => simp
  | case6 lo hi hle =>
      have := hv.2 j hj hxj
      simp only at this
      omega

end BinarySearch

/-- **Completeness**: in a sorted array, a key that is there is found: the first stretch is valid
(`valid_first`), and `Valid` gives the answer (`isSome_of_valid`). -/
theorem search_complete {α : Type} [LinearOrder α] {a : α} {xs : Array α}
    (hs : BinarySearch.Sorted xs) (ha : a ∈ xs) : ∃ i, search a xs = some i := by
  obtain ⟨j, hj, hxj⟩ := Array.mem_iff_getElem.mp ha
  have hne : xs.size ≠ 0 := by omega
  have := BinarySearch.isSome_of_valid (w := BinarySearch.Stretch.first a xs) hs
    (BinarySearch.valid_first a (by omega)) (j := j) hj
    (by simp [BinarySearch.Stretch.first, hj, hxj])
  simp only [search, searchTimed, hne, ↓reduceIte]
  exact Option.isSome_iff_exists.mp this

/-- Soundness and completeness together: on a sorted array, `search` returns an index exactly
when the key is present. -/
theorem search_isSome_iff {α : Type} [LinearOrder α] {a : α} {xs : Array α}
    (hs : BinarySearch.Sorted xs) : (∃ i, search a xs = some i) ↔ a ∈ xs := by
  constructor
  · rintro ⟨i, hi⟩
    have h := searchTimed_sound a xs i hi
    rw [Array.getElem?_eq_some_iff] at h
    obtain ⟨hi', rfl⟩ := h
    exact Array.getElem_mem hi'
  · exact search_complete hs

/-! ### What the routine costs

Each probe leaves at most `n / 2` of `n` candidates, `searchCost`'s own step. The bound is stated
against `searchCost`, not `Nat.log2 n + 1`, because the two differ at `n = 0`. -/

/-- `searchCost`'s time, as a function of `n`: nothing for no candidates, `Nat.log2 n + 1`
otherwise. -/
theorem time_searchCost_le {n : ℕ} : (searchCost n).time ≤ Nat.log2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Nat.le_of_eq (time_searchCost_eq hn)

/-- One more compare than a search of at most half the stretch is no more than the recurrence
charges for the whole stretch. -/
theorem time_searchCost_half_succ_le {m n : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n / 2) :
    (searchCost m).time + 1 ≤ (searchCost n).time := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [time_searchCost_eq hn]; simp
  · rw [time_searchCost_eq hm, time_searchCost_eq hn]
    have hle : Nat.log2 m + 1 ≤ Nat.log2 n := by
      rw [Nat.le_log2 (by omega), Nat.pow_succ]
      have := Nat.log2_self_le (n := m) (by omega)
      omega
    omega

/-- **The routine's cost is bounded by the recurrence's**, for any stretch `[lo, hi]`. -/
theorem time_searchM_le {α : Type} [LinearOrder α] (a : α) (xs : Array α) (lo hi : ℕ) :
    (searchM a xs lo hi).time ≤ (searchCost (hi + 1 - lo)).time := by
  fun_induction searchM a xs lo hi with
  | case1 lo hi hle mid hmid => simp
  | case2 lo hi hle mid k hmid hlt r ih =>
      have hm : hi + 1 - (mid + 1) ≤ (hi + 1 - lo) / 2 := by simp only [mid]; omega
      exact Nat.le_trans (Nat.add_le_add_right ih 1)
        (time_searchCost_half_succ_le (by omega) hm)
  | case3 lo hi hle mid k hmid hge hlt h0 =>
      have := time_searchCost_half_succ_le (m := 0) (n := hi + 1 - lo) (by omega) (Nat.zero_le _)
      simpa using this
  | case4 lo hi hle mid k hmid hge hlt h0 r ih =>
      have hm : mid - 1 + 1 - lo ≤ (hi + 1 - lo) / 2 := by simp only [mid] at h0 ⊢; omega
      exact Nat.le_trans (Nat.add_le_add_right ih 1)
        (time_searchCost_half_succ_le (by omega) hm)
  | case5 lo hi hle mid k hmid hge hge2 =>
      have := time_searchCost_half_succ_le (m := 0) (n := hi + 1 - lo) (by omega) (Nat.zero_le _)
      simpa using this
  | case6 lo hi hle => simp

/-- `search` makes no more comparisons than `searchCost` charges for the array's length —
the routine and Sedgewick's recurrence, in the same unit. -/
theorem searchProbes_le_searchCost {α : Type} [LinearOrder α] (a : α) (xs : Array α) :
    searchProbes a xs ≤ (searchCost xs.size).time := by
  unfold searchProbes searchTimed
  split_ifs with h0
  · simp
  · have := time_searchM_le a xs 0 (xs.size - 1)
    rwa [show xs.size - 1 + 1 - 0 = xs.size by omega] at this

/-- **Proposition B for the routine**: `search` on `N` keys makes at most `Nat.log2 N + 1`
three-way comparisons (probes; each may take up to two `<` tests), found or not, sorted or
not. -/
theorem searchProbes_le {α : Type} [LinearOrder α] (a : α) (xs : Array α) :
    searchProbes a xs ≤ Nat.log2 xs.size + 1 :=
  Nat.le_trans (searchProbes_le_searchCost a xs) time_searchCost_le


end AlgoDesign.Searching
