/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.FMIndex.Search

/-!
# FM-index: locating a row without storing the suffix array

Sources: Ferragina and Manzini (FOCS 2000); Navarro, *Compact Data Structures*, §11.1.4.

A marker bit per row, set when the row's text position is a multiple of `k`, and the marked rows'
values in row order. `positionOf` walks `lf` to a marked row and adds the steps taken; its fuel is
`min k n`, and `none` means the fuel ran out. `locateSampled_eq`: the walk returns `sa[r]` within
that fuel. The row `extractSampledM` starts from is a hypothesis.

One tick is one LF step: a hit costs `sa[r] mod k` steps, at most `k - 1`; all hits at most
`occ · (k - 1)`; extraction at most `len + (k - 1)`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-! ## The sampled walk's running state -/

namespace SampledLocate

/-- **The sampled walk's running state**: the suffix array whose rows it walks, the start position
being located, the row it stands at, and the LF steps taken. -/
structure Walk where
  /-- The text and its suffix array. -/
  index : SuffixArray
  /-- The start position being located. -/
  position : Nat
  /-- The row the walk stands at. -/
  row : Nat
  /-- The LF steps taken so far. -/
  steps : Nat

/-- The walk's row position plus the steps taken is the start position. -/
def StepsAccounted (w : Walk) : Prop :=
  ∀ h : w.row < w.index.positions.length, w.index.positions[w.row] + w.steps = w.position

/-- The sampled walk's running state after `steps` LF steps from the row of `position`. -/
def Valid (w : Walk) : Prop := RowInTable w.index w.row ∧ StepsAccounted w

instance (w : Walk) : Decidable (StepsAccounted w) :=
  inferInstanceAs (Decidable
    (∀ h : w.row < w.index.positions.length, w.index.positions[w.row] + w.steps = w.position))

instance (w : Walk) : Decidable (Valid w) :=
  by unfold Valid; infer_instance

end SampledLocate

/-- `marks`: row `r` is marked exactly when its text position is a multiple of `k`. -/
def saMarks (sa : List Nat) (k : Nat) : List Bool := sa.map fun p => p % k == 0

/-- `sa_samples`: the marked rows' positions, in row order. -/
def saValues (sa : List Nat) (k : Nat) : List Nat := sa.filter fun p => p % k == 0

/-- `isa_samples`: for each kept position `0, k, 2k, …` below `n`, the row that holds it. -/
def saKeptRows (sa : List Nat) (k : Nat) : List Nat :=
  (List.range ((sa.length + k - 1) / k)).map fun j => sa.idxOf (j * k)

/-- Models `FmIndex::position_of`: walk `lf` from row `r` to a marked row, read its sample, add
the steps taken; `none` when the fuel runs out. -/
def positionOf (bwt : List Nat) (marks : List Bool) (values : List Nat) :
    Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, r, steps =>
    if marks[r]! then some (values[rank marks r]! + steps)
    else positionOf bwt marks values fuel (lf bwt r) (steps + 1)

/-- The sampled `locate` of one row, with fuel `min k n`. -/
def locateSampled (t sa : List Nat) (k r : Nat) : Option Nat :=
  positionOf (bwtOfSa t sa) (saMarks sa k) (saValues sa k) (min k t.length) r 0

/-- The rank of a marked row indexes its own value. -/
theorem getElem!_filter_rank (P : Nat → Bool) :
    ∀ (l : List Nat) (r : Nat), r < l.length → P l[r]! = true →
      (l.filter P)[rank (l.map P) r]! = l[r]! := by
  intro l
  induction l with
  | nil => intro r hr; simp at hr
  | cons x xs ih =>
    intro r hr hP
    cases r with
    | zero =>
      have hx : P x = true := by simpa using hP
      simp [rank, hx]
    | succ r =>
      have hr' : r < xs.length := by simpa using hr
      have hP' : P xs[r]! = true := by simpa using hP
      have hrank : rank (P x :: xs.map P) (r + 1)
          = (if P x = true then 1 else 0) + rank (xs.map P) r := by
        simp only [rank, List.take_succ_cons, List.filter_cons, id]
        split <;> simp [Nat.add_comm]
      simp only [List.map_cons, hrank, List.getElem!_cons_succ]
      cases hx : P x
      · rw [List.filter_cons_of_neg (by simp [hx])]
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        exact ih r hr' hP'
      · rw [List.filter_cons_of_pos hx]
        simp only [↓reduceIte, Nat.add_comm 1, List.getElem!_cons_succ]
        exact ih r hr' hP'

/-- From a row whose position is `d` past a multiple of `k`, with more than `d` fuel, the walk
answers that position plus the steps already taken, for any marks and values that flag the rows
whose position is a multiple of `k` and hold those positions in row order. -/
theorem positionOf_walk (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k)
    (marks : List Bool) (values : List Nat)
    (hmark : ∀ r, r < sa.length → marks[r]! = (sa[r]! % k == 0))
    (hval : ∀ r, r < sa.length → sa[r]! % k = 0 → values[rank marks r]! = sa[r]!) :
    ∀ d r steps fuel, r < sa.length → sa[r]! % k = d → d < fuel →
      positionOf (bwtOfSa t sa) marks values fuel r steps = some (sa[r]! + steps) := by
  have hmem : ∀ r, r < sa.length → sa[r]! < t.length := by
    intro r hr
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  intro d
  induction d with
  | zero =>
    intro r steps fuel hr hd hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hm : marks[r]! = true := by rw [hmark r hr]; simpa using hd
    simp only [positionOf, hm, ↓reduceIte]
    rw [hval r hr hd]
  | succ d ih =>
    intro r steps fuel hr hd hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hm : marks[r]! = false := by
      rw [hmark r hr, hd]; simp
    have hpos : 0 < sa[r]! := by
      rcases Nat.eq_zero_or_pos sa[r]! with h0 | h0
      · rw [h0, Nat.zero_mod] at hd; omega
      · exact h0
    have hlt := hmem r hr
    have hlf : sa[lf (bwtOfSa t sa) r]! = sa[r]! - 1 := by
      rw [lf_spec t s h sa hsa r hr, show sa[r]! + t.length - 1 = (sa[r]! - 1) + t.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hdk : d + 1 < k := by rw [← hd]; exact Nat.mod_lt _ hk
    have hmod : (sa[r]! - 1) % k = d := by
      have hsplit := Nat.mod_add_div' (sa[r]!) k
      rw [hd] at hsplit
      rw [show sa[r]! - 1 = d + sa[r]! / k * k by omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
    simp only [positionOf, hm, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ _ f (lf_lt_length t s h sa hsa r hr) (by rw [hlf, hmod]) (by omega), hlf]
    congr 1
    omega

/-- One LF step from an unkept row keeps `SampledLocate.Valid`. -/
theorem SampledLocate.valid_lf {w : SampledLocate.Walk} {z : Nat} (h : Terminated w.index.text z)
    (hsa : SuffixArray.Valid w.index) (k : Nat) (hv : SampledLocate.Valid w)
    (hm : w.index.positions[w.row]! % k ≠ 0) :
    SampledLocate.Valid ⟨w.index, w.position,
      lf (bwtOfSa w.index.text w.index.positions) w.row, w.steps + 1⟩ := by
  obtain ⟨⟨t, sa⟩, p, r, steps⟩ := w
  obtain ⟨hr, hp⟩ := hv
  unfold RowInTable at hr
  unfold SampledLocate.StepsAccounted at hp
  dsimp only at hr hp hm h hsa ⊢
  have hp' : sa[r]! + steps = p := by rw [getElem!_pos sa r hr]; exact hp hr
  have hlt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have hpos : 0 < sa[r]! := by
    rcases Nat.eq_zero_or_pos sa[r]! with h0 | h0
    · rw [h0, Nat.zero_mod] at hm; exact absurd rfl hm
    · exact h0
  have hlf : sa[lf (bwtOfSa t sa) r]! = sa[r]! - 1 := by
    rw [lf_spec t z h sa hsa r hr, show sa[r]! + t.length - 1 = (sa[r]! - 1) + t.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine ⟨lf_lt_length t z h sa hsa r hr, fun hl => ?_⟩
  dsimp only
  rw [← getElem!_pos sa _ hl, hlf]
  omega

/-- Sampled locate is `sa[r]`, within the fuel `min k n`. -/
theorem locateSampled_eq (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (r : Nat)
    (hr : r < sa.length) : locateSampled t sa k r = some sa[r]! := by
  have hlt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have hmodk : sa[r]! % k < k := Nat.mod_lt _ hk
  have hmodle : sa[r]! % k ≤ sa[r]! := Nat.mod_le _ _
  have := positionOf_walk t s h sa hsa k hk (saMarks sa k) (saValues sa k)
    (fun r hr => by
      rw [getElem!_pos _ r (by simpa [saMarks] using hr), getElem!_pos sa r hr]
      simp [saMarks])
    (fun r hr hm => by
      rw [saMarks, saValues,
        getElem!_filter_rank (fun p => p % k == 0) sa r hr (by simpa using hm)])
    (sa[r]! % k) r 0 (min k t.length) hr rfl (by omega)
  simpa [locateSampled] using this

/-! ### Costs, in LF steps -/

/-- `positionOf` with one tick per LF step. -/
def positionOfM (bwt : List Nat) (marks : List Bool) (values : List Nat) :
    Nat → Nat → Nat → Cslib.Algorithms.Lean.TimeM ℕ (Option Nat)
  | 0, _, _ => ⟨none, 0⟩
  | fuel + 1, r, steps =>
    if marks[r]! then ⟨some (values[rank marks r]! + steps), 0⟩
    else
      let x := positionOfM bwt marks values fuel (lf bwt r) (steps + 1)
      ⟨x.ret, x.time + 1⟩

theorem ret_positionOfM (bwt : List Nat) (marks : List Bool) (values : List Nat) :
    ∀ fuel r steps, (positionOfM bwt marks values fuel r steps).ret
      = positionOf bwt marks values fuel r steps
  | 0, _, _ => rfl
  | fuel + 1, r, steps => by
    simp only [positionOfM, positionOf]
    split
    · rfl
    · exact ret_positionOfM bwt marks values fuel _ _

/-- Marks that flag exactly the rows whose position is a multiple of `k`: from a row whose position
is `d` past a multiple of `k`, the walk takes exactly `d` steps. -/
theorem time_positionOfM_walk (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k)
    (marks : List Bool) (values : List Nat)
    (hmark : ∀ r, r < sa.length → marks[r]! = (sa[r]! % k == 0)) :
    ∀ d r steps fuel, r < sa.length → sa[r]! % k = d → d < fuel →
      (positionOfM (bwtOfSa t sa) marks values fuel r steps).time = d := by
  have hmem : ∀ r, r < sa.length → sa[r]! < t.length := by
    intro r hr
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  intro d
  induction d with
  | zero =>
    intro r steps fuel hr hd hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hm : marks[r]! = true := by rw [hmark r hr]; simpa using hd
    simp [positionOfM, hm]
  | succ d ih =>
    intro r steps fuel hr hd hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hm : marks[r]! = false := by
      rw [hmark r hr, hd]; simp
    have hpos : 0 < sa[r]! := by
      rcases Nat.eq_zero_or_pos sa[r]! with h0 | h0
      · rw [h0, Nat.zero_mod] at hd; omega
      · exact h0
    have hlt := hmem r hr
    have hlf : sa[lf (bwtOfSa t sa) r]! = sa[r]! - 1 := by
      rw [lf_spec t s h sa hsa r hr, show sa[r]! + t.length - 1 = (sa[r]! - 1) + t.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hdk : d + 1 < k := by rw [← hd]; exact Nat.mod_lt _ hk
    have hmod : (sa[r]! - 1) % k = d := by
      have hsplit := Nat.mod_add_div' (sa[r]!) k
      rw [hd] at hsplit
      rw [show sa[r]! - 1 = d + sa[r]! / k * k by omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
    simp only [positionOfM, hm, Bool.false_eq_true, ↓reduceIte]
    rw [ih _ _ f (lf_lt_length t s h sa hsa r hr) (by rw [hlf, hmod]) (by omega)]

/-- The sampled `locate` of one row, timed: `locateSampled` with one tick per LF step. -/
def locateSampledM (t sa : List Nat) (k r : Nat) : Cslib.Algorithms.Lean.TimeM ℕ (Option Nat) :=
  positionOfM (bwtOfSa t sa) (saMarks sa k) (saValues sa k) (min k t.length) r 0

theorem ret_locateSampledM (t sa : List Nat) (k r : Nat) :
    (locateSampledM t sa k r).ret = locateSampled t sa k r :=
  ret_positionOfM _ _ _ _ _ _

/-- One hit costs exactly `sa[r] mod k` LF steps. -/
theorem time_locateSampledM (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (r : Nat)
    (hr : r < sa.length) : (locateSampledM t sa k r).time = sa[r]! % k := by
  have hlt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have hmodk : sa[r]! % k < k := Nat.mod_lt _ hk
  have hmodle : sa[r]! % k ≤ sa[r]! := Nat.mod_le _ _
  refine time_positionOfM_walk t s h sa hsa k hk _ _ (fun x hx => ?_) _ r 0 _ hr rfl (by omega)
  rw [getElem!_pos _ x (by simpa [saMarks] using hx), getElem!_pos sa x hx]
  simp [saMarks]

/-- At most `k - 1` LF steps per hit. -/
theorem time_locateSampledM_le (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (r : Nat)
    (hr : r < sa.length) : (locateSampledM t sa k r).time ≤ k - 1 := by
  rw [time_locateSampledM t s h sa hsa k hk r hr]
  have := Nat.mod_lt sa[r]! hk
  omega

/-- At most `n - 1` LF steps per hit: position `0` is sampled at every rate. -/
theorem time_locateSampledM_le_length (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (r : Nat)
    (hr : r < sa.length) : (locateSampledM t sa k r).time ≤ t.length - 1 := by
  rw [time_locateSampledM t s h sa hsa k hk r hr]
  have hlt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  have := Nat.mod_le sa[r]! k
  omega

/-- Locate a list of rows, one walk each, the costs added up. -/
def locateRowsM (t sa : List Nat) (k : Nat) :
    List Nat → Cslib.Algorithms.Lean.TimeM ℕ (List (Option Nat))
  | [] => ⟨[], 0⟩
  | r :: rs =>
      let x := locateSampledM t sa k r
      let y := locateRowsM t sa k rs
      ⟨x.ret :: y.ret, x.time + y.time⟩

theorem ret_locateRowsM (t sa : List Nat) (k : Nat) (rows : List Nat) :
    (locateRowsM t sa k rows).ret = rows.map (locateSampled t sa k) := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp [locateRowsM, ih, ret_locateSampledM]

/-- Locating `occ` rows costs at most `occ · (k - 1)` LF steps. -/
theorem time_locateRowsM_le (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (rows : List Nat)
    (hrows : ∀ r ∈ rows, r < sa.length) :
    (locateRowsM t sa k rows).time ≤ rows.length * (k - 1) := by
  induction rows with
  | nil => simp [locateRowsM]
  | cons r rs ih =>
      have h1 := time_locateSampledM_le t s h sa hsa k hk r (hrows r (by simp))
      have h2 := ih (fun x hx => hrows x (by simp [hx]))
      simp only [locateRowsM, List.length_cons, Nat.succ_mul]
      omega

/-- The sampled `locate` of a pattern: walk from every row of its interval. -/
def locateIntervalM (t sa : List Nat) (k : Nat) (p : List Nat) :
    Cslib.Algorithms.Lean.TimeM ℕ (List (Option Nat)) :=
  let (lo, hi) := backwardSearch (bwtOfSa t sa) (cLess t) p
  locateRowsM t sa k (List.range' lo (hi - lo))

/-- Locating every occurrence of `p` costs at most `occ · (k - 1)` LF steps. -/
theorem time_locateIntervalM_le (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (p : List Nat)
    (hp : s ∉ p.dropLast) :
    (locateIntervalM t sa k p).time ≤ matchCount t p * (k - 1) := by
  have hin : ∀ r, lexBelow t p ≤ r → r < lexBelow t p + matchCount t p → r < sa.length := by
    intro r h1 h2
    exact ((backwardSearch_spec t s h sa hsa p hp r).mp
      (by rw [backwardSearch_eq t s h sa hsa p hp]; exact ⟨h1, h2⟩)).1
  unfold locateIntervalM
  rw [backwardSearch_eq t s h sa hsa p hp]
  simp only
  have := time_locateRowsM_le t s h sa hsa k hk
    (List.range' (lexBelow t p) (lexBelow t p + matchCount t p - lexBelow t p))
    (fun r hr => by
      rw [List.mem_range'_1] at hr
      exact hin r hr.1 (by omega))
  simpa using this

/-- `lfWalk` with one tick per LF step. -/
def lfWalkM (bwt : List Nat) : Nat → Nat → Cslib.Algorithms.Lean.TimeM ℕ (List Nat)
  | 0, _ => ⟨[], 0⟩
  | j + 1, r =>
      let x := lfWalkM bwt j (lf bwt r)
      ⟨bwt[r]! :: x.ret, x.time + 1⟩

theorem ret_lfWalkM (bwt : List Nat) : ∀ j r, (lfWalkM bwt j r).ret = lfWalk bwt j r
  | 0, _ => rfl
  | j + 1, r => by simp [lfWalkM, lfWalk, ret_lfWalkM bwt j]

theorem time_lfWalkM (bwt : List Nat) : ∀ j r, (lfWalkM bwt j r).time = j
  | 0, _ => rfl
  | j + 1, r => by simp [lfWalkM, time_lfWalkM bwt j]

/-- Where `extract(from, len)` starts walking: the first multiple of `k` at or past `from + len`,
or `n` when that is `n` or more. -/
def extractStart (n k f len : Nat) : Nat :=
  if n ≤ (f + len + k - 1) / k * k then n else (f + len + k - 1) / k * k

/-- The start is past the range's end, within `k - 1` of it, and not past the text's end. -/
theorem extractStart_bounds (n k f len : Nat) (hk : 0 < k) (hfl : f + len ≤ n) :
    f + len ≤ extractStart n k f len ∧ extractStart n k f len ≤ n
      ∧ extractStart n k f len ≤ f + len + (k - 1) := by
  have hdm := Nat.div_add_mod (f + len + k - 1) k
  have hml := Nat.mod_lt (f + len + k - 1) hk
  have hq : (f + len + k - 1) / k * k = k * ((f + len + k - 1) / k) := Nat.mul_comm _ _
  unfold extractStart
  split <;> omega

/-- Models `FmIndex::extract`, timed: walk `start - from` LF steps from `row`, reverse, and drop
the letters past the range. -/
def extractSampledM (bwt : List Nat) (n k f len row : Nat) :
    Cslib.Algorithms.Lean.TimeM ℕ (List Nat) :=
  if len = 0 then ⟨[], 0⟩
  else
    let w := lfWalkM bwt (extractStart n k f len - f) row
    ⟨(w.ret.reverse).take len, w.time⟩

/-- Extraction returns the slice, given the row of the start position. -/
theorem ret_extractSampledM (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (k : Nat) (hk : 0 < k) (f len : Nat)
    (hfl : f + len ≤ t.length) (row : Nat) (hr : row < sa.length)
    (hrow : sa[row]! = extractStart t.length k f len % t.length) :
    (extractSampledM (bwtOfSa t sa) t.length k f len row).ret = (t.drop f).take len := by
  unfold extractSampledM
  split
  · simp_all
  · obtain ⟨h1, h2, _⟩ := extractStart_bounds t.length k f len hk hfl
    have hx := fmExtract_eq t s h sa hsa f (extractStart t.length k f len - f) (by omega) row hr
      (by rw [hrow, Nat.add_sub_cancel' (by omega)])
    simp only [ret_lfWalkM]
    rw [fmExtract] at hx
    rw [hx, List.take_take, Nat.min_eq_left (by omega)]

/-- Extraction walks exactly `start - from` LF steps, none for an empty range. -/
theorem time_extractSampledM (bwt : List Nat) (n k f len row : Nat) :
    (extractSampledM bwt n k f len row).time
      = if len = 0 then 0 else extractStart n k f len - f := by
  unfold extractSampledM
  split <;> simp [time_lfWalkM]

/-- Extraction walks at most `len + (k - 1)` LF steps. -/
theorem time_extractSampledM_le (bwt : List Nat) (n k f len row : Nat) (hk : 0 < k)
    (hfl : f + len ≤ n) : (extractSampledM bwt n k f len row).time ≤ len + (k - 1) := by
  rw [time_extractSampledM]
  have := extractStart_bounds n k f len hk hfl
  split <;> omega

end AlgoDesign.Strings
