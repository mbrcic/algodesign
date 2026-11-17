/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.SuffixArray.Build
public import AlgoDesign.Searching.BinarySearch

/-!
# Suffix arrays: the search

The chapter's `search(text, sa, pattern)`: cut every suffix to the pattern's length, find the top
edge (first row not below the pattern) and the bottom edge (first row above it) by two binary
searches, and return the rows between. The empty pattern answers `n` and then all of `sa`.
`search_eq_filter` needs `SuffixArray.Valid`: on an unsorted permutation the halving can miss
occurrences.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-! ## A binary search's running state -/

namespace Bisect

/-- After each probe: the stretch `[lo, hi)` lies inside the array. -/
def StretchInsideArray (sa : List Nat) (lo hi : Nat) : Prop := lo ≤ hi ∧ hi ≤ sa.length

/-- After each probe: every row before `lo` satisfies `below`. -/
def LeftOfStretchBelow (below : Nat → Prop) (sa : List Nat) (lo : Nat) : Prop :=
  ∀ i (h : i < sa.length), i < lo → below sa[i]

/-- After each probe: every row from `hi` on fails `below`. -/
def RightOfStretchNotBelow (below : Nat → Prop) (sa : List Nat) (hi : Nat) : Prop :=
  ∀ i (h : i < sa.length), hi ≤ i → ¬ below sa[i]

/-- **A binary search's running state**, the stretch `[lo, hi)` of rows still undecided. -/
def Valid (below : Nat → Prop) (sa : List Nat) (lo hi : Nat) : Prop :=
  StretchInsideArray sa lo hi ∧ LeftOfStretchBelow below sa lo ∧ RightOfStretchNotBelow below sa hi

instance (sa : List Nat) (lo hi : Nat) : Decidable (StretchInsideArray sa lo hi) :=
  by unfold StretchInsideArray; infer_instance

instance (below : Nat → Prop) [DecidablePred below] (sa : List Nat) (lo : Nat) :
    Decidable (LeftOfStretchBelow below sa lo) :=
  inferInstanceAs (Decidable (∀ i (h : i < sa.length), i < lo → below sa[i]))

instance (below : Nat → Prop) [DecidablePred below] (sa : List Nat) (hi : Nat) :
    Decidable (RightOfStretchNotBelow below sa hi) :=
  inferInstanceAs (Decidable (∀ i (h : i < sa.length), hi ≤ i → ¬ below sa[i]))

instance (below : Nat → Prop) [DecidablePred below] (sa : List Nat) (lo hi : Nat) :
    Decidable (Valid below sa lo hi) :=
  inferInstanceAs (Decidable
    (StretchInsideArray sa lo hi ∧ LeftOfStretchBelow below sa lo ∧
      RightOfStretchNotBelow below sa hi))

end Bisect

/-- **Binary search for an edge** over rows `[lo, hi)` of `sa`, as Python's `bisect`: probe the
middle row; if `below` holds there the edge is after it, otherwise at it or before. `fuel` never
runs out from `search`. -/
def bisect (below : Nat → Bool) (sa : List Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        if below sa[(lo + hi) / 2]! then bisect below sa fuel ((lo + hi) / 2 + 1) hi
        else bisect below sa fuel lo ((lo + hi) / 2)
      else lo

/-- **The chapter's suffix-array search.** The empty pattern answers `t.length` and then every
row; otherwise the rows between the two edges, in row order. -/
def search (t sa p : List Nat) : List Nat :=
  if p = [] then t.length :: sa
  else
    let lo := bisect (fun i => decide ((suffix t i).take p.length < p)) sa sa.length 0 sa.length
    let hi := bisect (fun i => decide ((suffix t i).take p.length ≤ p)) sa sa.length 0 sa.length
    (sa.drop lo).take (hi - lo)

/-- Cutting two lists to the same length keeps their order. -/
theorem take_le_take_of_le {l l' : List Nat} (h : l ≤ l') (m : Nat) : l.take m ≤ l'.take m :=
  fun hlt => h (lt_of_take_lt_take hlt)

/-- **One probe keeps `Bisect.Valid`.** If the middle row is below, the edge is past it;
otherwise it is at it or before — the two branches of `bisect`, whose probe reads the middle row. -/
theorem Bisect.valid_probe (below : Nat → Prop) [DecidablePred below] (sa : List Nat)
    (hmono : ∀ i j (hij : i ≤ j) (hj : j < sa.length),
      below sa[j] → below (sa[i]'(Nat.lt_of_le_of_lt hij hj)))
    {lo hi : Nat} (hv : Bisect.Valid below sa lo hi) (hlt : lo < hi) :
    if below sa[(lo + hi) / 2]! then Bisect.Valid below sa ((lo + hi) / 2 + 1) hi
    else Bisect.Valid below sa lo ((lo + hi) / 2) := by
  obtain ⟨⟨hlh, hhn⟩, hlo, hhi⟩ := hv
  have hmid : (lo + hi) / 2 < sa.length := by omega
  rw [getElem!_pos sa _ hmid]
  by_cases hb : below sa[(lo + hi) / 2]
  · simp only [hb, ↓reduceIte]
    refine ⟨⟨by omega, hhn⟩, fun i hi' hil => ?_, hhi⟩
    by_cases hil' : i < lo
    · exact hlo i hi' hil'
    · exact hmono i _ (by omega) hmid hb
  · simp only [hb, ↓reduceIte]
    refine ⟨⟨by omega, by omega⟩, hlo, fun i hin hi' hbi => ?_⟩
    by_cases hih : hi ≤ i
    · exact hhi i hin hih hbi
    · exact hb (hmono _ i (by omega) hin hbi)

/-- **An empty stretch is the edge.** With `lo = hi`, `Bisect.Valid` says every row before `lo`
is below and every row from it on is not. -/
theorem Bisect.edge_of_valid {below : Nat → Prop} {sa : List Nat} {r : Nat}
    (hv : Bisect.Valid below sa r r) :
    r ≤ sa.length ∧ (∀ i (h : i < sa.length), i < r → below sa[i]) ∧
      (∀ i (h : i < sa.length), r ≤ i → ¬ below sa[i]) :=
  ⟨hv.1.2, hv.2.1, hv.2.2⟩

/-- **The search keeps `Bisect.Valid` to the end.** From a valid stretch, every probe keeps it
(`Bisect.valid_probe`), so `bisect` ends at an empty stretch that is still valid: the edge
(`Bisect.edge_of_valid`). -/
theorem Bisect.valid_bisect (below : Nat → Bool) (sa : List Nat)
    (hmono : ∀ i j (hij : i ≤ j) (hj : j < sa.length),
      below sa[j] = true → below (sa[i]'(Nat.lt_of_le_of_lt hij hj)) = true) :
    ∀ fuel lo hi, hi - lo ≤ fuel → Bisect.Valid (below · = true) sa lo hi →
      Bisect.Valid (below · = true) sa (bisect below sa fuel lo hi) (bisect below sa fuel lo hi)
  | 0, lo, hi, hf, hv => by
      have : lo = hi := by have := hv.1.1; omega
      subst this
      exact hv
  | fuel + 1, lo, hi, hf, hv => by
      simp only [bisect]
      by_cases hlt : lo < hi
      · have hp := Bisect.valid_probe (below · = true) sa hmono hv hlt
        simp only [hlt, ↓reduceIte]
        by_cases hb : below sa[(lo + hi) / 2]! = true
        · simp only [hb, ↓reduceIte] at hp ⊢
          exact Bisect.valid_bisect below sa hmono fuel _ hi (by omega) hp
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hp ⊢
          exact Bisect.valid_bisect below sa hmono fuel lo _ (by omega) hp
      · simp only [hlt, ↓reduceIte]
        have : lo = hi := by have := hv.1.1; omega
        subst this
        exact hv

/-- **The edge `bisect` finds**, from the whole array. If `below` is monotone over the rows, the
search returns the row `r` where `below` turns: every row before it is below, and no row from it
on (`Bisect.valid_bisect`, `Bisect.edge_of_valid`). -/
theorem bisect_full (below : Nat → Bool) (sa : List Nat)
    (hmono : ∀ i j, i ≤ j → j < sa.length → below sa[j]! = true → below sa[i]! = true) :
    let r := bisect below sa sa.length 0 sa.length
    r ≤ sa.length ∧ (∀ i, i < r → below sa[i]! = true) ∧
      (∀ i, r ≤ i → i < sa.length → below sa[i]! = false) := by
  have hmono' : ∀ i j (hij : i ≤ j) (hj : j < sa.length),
      below sa[j] = true → below (sa[i]'(Nat.lt_of_le_of_lt hij hj)) = true := by
    intro i j hij hj hb
    have := hmono i j hij hj (by rwa [getElem!_pos sa j hj])
    rwa [getElem!_pos sa i (Nat.lt_of_le_of_lt hij hj)] at this
  have hv : Bisect.Valid (below · = true) sa 0 sa.length :=
    ⟨⟨Nat.zero_le _, le_refl _⟩, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ h h' => (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h h')).elim⟩
  obtain ⟨hn, hl, hh⟩ :=
    Bisect.edge_of_valid (Bisect.valid_bisect below sa hmono' sa.length 0 sa.length (by omega) hv)
  refine ⟨hn, fun i hi => ?_, fun i hi hin => ?_⟩
  · have hin : i < sa.length := by omega
    rw [getElem!_pos sa i hin]
    exact hl i hin hi
  · rw [getElem!_pos sa i hin]
    simpa using hh i hin hi

/-- On a suffix array, the suffixes in row order are sorted: row `i` at or before row `j` holds
the smaller suffix. -/
theorem suffix_le_of_le {t sa : List Nat} (h : SuffixArray.Valid ⟨t, sa⟩) {i j : Nat} (hij : i ≤ j)
    (hj : j < sa.length) : suffix t sa[i]! ≤ suffix t sa[j]! := by
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have hp := List.pairwise_iff_getElem.mp h.2 i j (by simp; omega) (by simpa using hj) hlt
    simpa [getElem!_pos sa i (by omega), getElem!_pos sa j hj] using hp
  · exact List.le_refl _

/-- A pattern begins a list exactly when the list cut to the pattern's length is the pattern. -/
theorem isPrefixOf_iff_take (p s : List Nat) : p.isPrefixOf s = true ↔ s.take p.length = p := by
  rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **What `search` returns.** On a suffix array, the rows of `t.length :: sa` whose suffix begins
with `p`, in that order. -/
theorem search_eq_filter {t sa : List Nat} (h : SuffixArray.Valid ⟨t, sa⟩) (p : List Nat) :
    search t sa p = (t.length :: sa).filter (fun i => p.isPrefixOf (suffix t i)) := by
  unfold search
  by_cases hp : p = []
  · subst hp
    simp
  simp only [hp, ↓reduceIte]
  have hlast : (p.isPrefixOf (suffix t t.length)) = false := by
    cases p with
    | nil => exact absurd rfl hp
    | cons a q => simp [suffix]
  rw [List.filter_cons, hlast]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the two edges
  set m := p.length
  set lo := bisect (fun i => decide ((suffix t i).take m < p)) sa sa.length 0 sa.length
  set hi := bisect (fun i => decide ((suffix t i).take m ≤ p)) sa sa.length 0 sa.length
  have hmlo : ∀ i j, i ≤ j → j < sa.length →
      decide ((suffix t sa[j]!).take m < p) = true → decide ((suffix t sa[i]!).take m < p) = true :=
    by
    intro i j hij hj hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact List.lt_of_le_of_lt (take_le_take_of_le (suffix_le_of_le h hij hj) m) hb
  have hmhi : ∀ i j, i ≤ j → j < sa.length →
      decide ((suffix t sa[j]!).take m ≤ p) = true → decide ((suffix t sa[i]!).take m ≤ p) = true :=
    by
    intro i j hij hj hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact List.le_trans (take_le_take_of_le (suffix_le_of_le h hij hj) m) hb
  obtain ⟨hlo_n, hlo_b, hlo_a⟩ := bisect_full (fun i => decide ((suffix t i).take m < p)) sa hmlo
  obtain ⟨hhi_n, hhi_b, hhi_a⟩ := bisect_full (fun i => decide ((suffix t i).take m ≤ p)) sa hmhi
  -- row `i` begins with `p` exactly when it lies in `[lo, hi)`
  have hrow : ∀ i, i < sa.length → (p.isPrefixOf (suffix t sa[i]!) = true ↔ lo ≤ i ∧ i < hi) := by
    intro i hi'
    rw [isPrefixOf_iff_take]
    change (suffix t sa[i]!).take m = p ↔ _
    constructor
    · intro he
      refine ⟨?_, ?_⟩
      · by_contra hc
        have := hlo_b i (by omega)
        simp only [decide_eq_true_eq] at this
        rw [he] at this
        exact List.lt_irrefl _ this
      · by_contra hc
        have := hhi_a i (by omega) hi'
        simp only [decide_eq_false_iff_not] at this
        rw [he] at this
        exact this (List.le_refl _)
    · rintro ⟨h1, h2⟩
      have a := hlo_a i h1 hi'
      have b := hhi_b i h2
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at a b
      exact List.le_antisymm b (List.not_lt.mp a)
  -- so the filter keeps exactly the slice
  have hlohi : lo ≤ hi := by
    by_contra hc
    have := hlo_b hi (by omega)
    have h2 := hhi_a hi (le_refl _) (by omega)
    simp only [decide_eq_true_eq] at this
    simp only [decide_eq_false_iff_not] at h2
    exact h2 (List.le_of_lt this)
  have hP : ∀ i (hi' : i < sa.length),
      (p.isPrefixOf (suffix t sa[i]) = true ↔ lo ≤ i ∧ i < hi) := by
    intro i hi'
    have := hrow i hi'
    rwa [getElem!_pos sa i hi'] at this
  have hsplit : sa = sa.take lo ++ ((sa.drop lo).take (hi - lo) ++ sa.drop hi) := by
    conv_lhs => rw [← List.take_append_drop lo sa]
    congr 1
    conv_lhs => rw [← List.take_append_drop (hi - lo) (sa.drop lo)]
    rw [List.drop_drop]
    congr 2
    omega
  conv_rhs => rw [hsplit]
  rw [List.filter_append, List.filter_append]
  have hA : (sa.take lo).filter (fun i => p.isPrefixOf (suffix t i)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take] at hi'
    rw [List.getElem_take]
    have := hP i (by omega)
    intro hc
    have := this.mp hc
    omega
  have hC : (sa.drop hi).filter (fun i => p.isPrefixOf (suffix t i)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_drop] at hi'
    rw [List.getElem_drop]
    have := hP (hi + i) (by omega)
    intro hc
    have := this.mp hc
    omega
  have hB : ((sa.drop lo).take (hi - lo)).filter (fun i => p.isPrefixOf (suffix t i)) =
      (sa.drop lo).take (hi - lo) := by
    rw [List.filter_eq_self]
    intro x hx
    obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_take, List.length_drop] at hi'
    rw [List.getElem_take, List.getElem_drop]
    exact (hP (lo + i) (by omega)).mpr ⟨by omega, by omega⟩
  rw [hA, hB, hC]
  simp

/-- **`search` as occurrences in the text.** On a suffix array, `i` is in the answer exactly when
`i` is a position of `t`, the end included, at which `p` begins. -/
theorem mem_search_iff {t sa : List Nat} (h : SuffixArray.Valid ⟨t, sa⟩) (p : List Nat) (i : Nat) :
    i ∈ search t sa p ↔ i ≤ t.length ∧ p <+: t.drop i := by
  rw [search_eq_filter h, List.mem_filter, List.mem_cons, h.1.mem_iff, List.mem_range,
    List.isPrefixOf_iff_prefix, suffix]
  dsimp only
  constructor
  · rintro ⟨hi | hi, hp⟩ <;> exact ⟨by omega, hp⟩
  · rintro ⟨hi, hp⟩
    exact ⟨by omega, hp⟩

/-! ## What the search costs

A probe compares the pattern with one suffix, cut to the pattern's length: at most `|p|` letter
comparisons. Each probe leaves at most half the rows still undecided, the step of the Searching
chapter's recurrence `Searching.searchCost`, so each binary search over `n` rows probes at most
`⌊log₂ n⌋ + 1` rows (`Searching.time_searchCost_le`). -/

open Cslib.Algorithms.Lean

/-- `bisect`, counting `cost` steps per probe. -/
def bisectM (below : Nat → Bool) (sa : List Nat) (cost : Nat) : Nat → Nat → Nat → TimeM ℕ Nat
  | 0, lo, _ => ⟨lo, 0⟩
  | fuel + 1, lo, hi =>
      if lo < hi then
        let r := if below sa[(lo + hi) / 2]! then bisectM below sa cost fuel ((lo + hi) / 2 + 1) hi
          else bisectM below sa cost fuel lo ((lo + hi) / 2)
        ⟨r.ret, r.time + cost⟩
      else ⟨lo, 0⟩

/-- The counted `bisect` finds the edge `bisect` finds. -/
theorem ret_bisectM (below : Nat → Bool) (sa : List Nat) (cost : Nat) :
    ∀ fuel lo hi, (bisectM below sa cost fuel lo hi).ret = bisect below sa fuel lo hi
  | 0, _, _ => rfl
  | fuel + 1, lo, hi => by
      simp only [bisectM, bisect]
      split_ifs <;> simp [ret_bisectM below sa cost fuel]

/-- **A binary search over `n` rows costs at most `cost` per probe of the recurrence's**: each
probe leaves at most half the rows. -/
theorem time_bisectM_le (below : Nat → Bool) (sa : List Nat) (cost : Nat) :
    ∀ fuel lo hi, (bisectM below sa cost fuel lo hi).time ≤
      cost * (Searching.searchCost (hi - lo)).time
  | 0, _, _ => by simp [bisectM]
  | fuel + 1, lo, hi => by
      simp only [bisectM]
      split_ifs with hlt hb
      · have ih := time_bisectM_le below sa cost fuel ((lo + hi) / 2 + 1) hi
        have hs := Searching.time_searchCost_half_succ_le (m := hi - ((lo + hi) / 2 + 1))
          (n := hi - lo) (by omega) (by omega)
        calc _ ≤ cost * (Searching.searchCost (hi - ((lo + hi) / 2 + 1))).time + cost :=
              Nat.add_le_add_right ih cost
          _ = cost * ((Searching.searchCost (hi - ((lo + hi) / 2 + 1))).time + 1) :=
            (Nat.mul_succ _ _).symm
          _ ≤ cost * (Searching.searchCost (hi - lo)).time := Nat.mul_le_mul_left cost hs
      · have ih := time_bisectM_le below sa cost fuel lo ((lo + hi) / 2)
        have hs := Searching.time_searchCost_half_succ_le (m := (lo + hi) / 2 - lo)
          (n := hi - lo) (by omega) (by omega)
        calc _ ≤ cost * (Searching.searchCost ((lo + hi) / 2 - lo)).time + cost :=
              Nat.add_le_add_right ih cost
          _ = cost * ((Searching.searchCost ((lo + hi) / 2 - lo)).time + 1) :=
            (Nat.mul_succ _ _).symm
          _ ≤ cost * (Searching.searchCost (hi - lo)).time := Nat.mul_le_mul_left cost hs
      · simp

/-- **The chapter's search, counted**: each probe of the two binary searches costs the pattern's
length in letter comparisons, and each place found one step. -/
def searchM (t sa p : List Nat) : TimeM ℕ (List Nat) :=
  if p = [] then ⟨t.length :: sa, sa.length + 1⟩
  else
    let lo := bisectM (fun i => decide ((suffix t i).take p.length < p)) sa p.length sa.length 0
      sa.length
    let hi := bisectM (fun i => decide ((suffix t i).take p.length ≤ p)) sa p.length sa.length 0
      sa.length
    let out := (sa.drop lo.ret).take (hi.ret - lo.ret)
    ⟨out, lo.time + hi.time + out.length⟩

/-- The counted search answers as `search` does. -/
theorem ret_searchM (t sa p : List Nat) : (searchM t sa p).ret = search t sa p := by
  unfold searchM search
  split_ifs <;> simp [ret_bisectM]

/-- **The search's cost**: at most `|p|` letter comparisons per probe of two binary searches of at
most `⌊log₂ n⌋ + 1` probes each, plus one step per place found. -/
theorem time_searchM_le (t sa p : List Nat) :
    (searchM t sa p).time ≤
      2 * (p.length * (Nat.log2 sa.length + 1)) + (search t sa p).length := by
  have hlog := Searching.time_searchCost_le (n := sa.length)
  unfold searchM
  split_ifs with hp
  · simp [search, hp]
  · rw [← ret_searchM]
    simp only [searchM, hp, ↓reduceIte]
    have h1 := time_bisectM_le (fun i => decide ((suffix t i).take p.length < p)) sa p.length
      sa.length 0 sa.length
    have h2 := time_bisectM_le (fun i => decide ((suffix t i).take p.length ≤ p)) sa p.length
      sa.length 0 sa.length
    simp only [Nat.sub_zero] at h1 h2
    have h3 := Nat.mul_le_mul_left p.length hlog
    omega

end AlgoDesign.Strings
