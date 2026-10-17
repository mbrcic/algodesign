/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.SuffixArray.Basic

/-!
# The LCP array: Kasai's scan computes what the definition asks for

Sources: Kasai, Lee, Arimura, Arikawa and Park, *Linear-time longest-common-prefix computation in
suffix arrays and its applications* (CPM 2001); CLRS §32.5 (`COMPUTE-LCP`). Entry `r` is how long a
prefix the suffixes at `sa[r - 1]` and `sa[r]` share (`lcpEntry`); entry `0` is `0`. Kasai's scan
visits text positions instead, carrying `h` so each comparison resumes where the last one stopped;
`kasai_eq` says it returns the definition's array. The `O(n)` bound is not proved: this `kasai` is
quadratic as written.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- How long a prefix two lists share. -/
def lcpLen : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a = b then lcpLen as bs + 1 else 0
  | _, _ => 0

/-- Entry `r` of the LCP array, by its definition: the common-prefix length of the suffixes at
`sa[r - 1]` and `sa[r]`. Entry `0` is `0`, and so is a row past the array's end. -/
def lcpEntry (t : List Nat) (sa : List Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => if h : r + 1 < sa.length then lcpLen (suffix t sa[r]) (suffix t sa[r + 1]) else 0

/-! ## Kasai's running state -/

namespace Kasai

/-- After each step: the partial array is as long as the text. -/
def OneEntryPerRow (t : List Nat) (out : List Nat) : Prop := out.length = t.length

/-- After each step: the carry never exceeds the entry the next position's row will be given, so
the next comparison may safely resume past the first `h` characters. -/
def CarryNeverOvershoots (t sa : List Nat) (p h : Nat) : Prop :=
  p < t.length → h ≤ lcpEntry t sa (sa.idxOf p)

/-- After each step: every row whose suffix starts before `p` holds the definition's entry, and
every other row still holds `0`. -/
def EarlierRowsFilled (t sa : List Nat) (p : Nat) (out : List Nat) : Prop :=
  ∀ j (h : j < out.length) (h' : j < sa.length), out[j] = if sa[j] < p then lcpEntry t sa j else 0

/-- **Kasai's running state**, entering text position `p` with carry `h` and partial array `out`. -/
def Valid (t sa : List Nat) (p h : Nat) (out : List Nat) : Prop :=
  OneEntryPerRow t out ∧ CarryNeverOvershoots t sa p h ∧ EarlierRowsFilled t sa p out

instance (t out : List Nat) : Decidable (OneEntryPerRow t out) :=
  by unfold OneEntryPerRow; infer_instance

instance (t sa : List Nat) (p h : Nat) : Decidable (CarryNeverOvershoots t sa p h) :=
  by unfold CarryNeverOvershoots; infer_instance

instance (t sa : List Nat) (p : Nat) (out : List Nat) : Decidable (EarlierRowsFilled t sa p out) :=
  by unfold EarlierRowsFilled; infer_instance

instance (t sa : List Nat) (p h : Nat) (out : List Nat) : Decidable (Valid t sa p h out) :=
  inferInstanceAs (Decidable
    (OneEntryPerRow t out ∧ CarryNeverOvershoots t sa p h ∧ EarlierRowsFilled t sa p out))

end Kasai

/-- One position's resumed comparison: skip the first `h` characters, known to agree. -/
def resume (t : List Nat) (q p h : Nat) : Nat :=
  h + lcpLen (suffix t (q + h)) (suffix t (p + h))

/-- **Kasai's scan.** Walk the text positions `p` in order. When `p`'s row is `r + 1`, resume the
comparison against `sa[r]` at the carried offset `h`, then give back one unit of the carry. Rank
`0` has no predecessor and keeps its `0`. -/
def kasaiLoop (t : List Nat) (sa : List Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, _, out => out
  | fuel + 1, p, h, out =>
    match sa.idxOf p with
    | 0 => kasaiLoop t sa fuel (p + 1) (h - 1) out
    | r + 1 =>
      kasaiLoop t sa fuel (p + 1) (resume t sa[r]! p h - 1)
        (out.set (r + 1) (resume t sa[r]! p h))

/-- The LCP array of `t` by Kasai's algorithm, given its suffix array: one pass over the text
positions, from an all-zero array and a carry of `0`. -/
def kasai (t : List Nat) (sa : List Nat) : List Nat :=
  kasaiLoop t sa t.length 0 0 (List.replicate t.length 0)

/-! ### `lcpLen`, on its own -/

@[simp] private theorem lcpLen_nil_left (b : List Nat) : lcpLen [] b = 0 := by cases b <;> rfl

@[simp] private theorem lcpLen_nil_right (a : List Nat) : lcpLen a [] = 0 := by cases a <;> rfl

private theorem lcpLen_cons (a b : Nat) (as bs : List Nat) :
    lcpLen (a :: as) (b :: bs) = if a = b then lcpLen as bs + 1 else 0 := rfl

/-- A shared prefix is a prefix of the left string, so it is no longer. -/
private theorem lcpLen_le_left : ∀ (a b : List Nat), lcpLen a b ≤ a.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: as, b :: bs => by
    rw [lcpLen_cons]
    by_cases hab : a = b
    · simpa [hab] using lcpLen_le_left as bs
    · simp [hab]

/-- Dropping the first character of both strings shortens their common prefix by exactly one,
when there was one to lose. -/
private theorem lcpLen_tail (a b : List Nat) (h : 0 < lcpLen a b) :
    lcpLen a.tail b.tail = lcpLen a b - 1 := by
  cases a with
  | nil => simp at h
  | cons x as =>
    cases b with
    | nil => simp at h
    | cons y bs =>
      rw [lcpLen_cons] at h ⊢
      by_cases hxy : x = y
      · simp [hxy]
      · simp [hxy] at h

/-- **Resuming is sound.** If the first `m` characters agree, comparing from offset `m` and adding
`m` back gives the full common-prefix length. -/
private theorem lcpLen_resume : ∀ (m : Nat) (a b : List Nat), m ≤ lcpLen a b →
    lcpLen a b = m + lcpLen (a.drop m) (b.drop m)
  | 0, a, b, _ => by simp
  | m + 1, a, b, hm => by
    have hpos : 0 < lcpLen a b := Nat.lt_of_lt_of_le (Nat.succ_pos m) hm
    have htail := lcpLen_tail a b hpos
    have hrec := lcpLen_resume m a.tail b.tail (by omega)
    have hda : a.tail.drop m = a.drop (m + 1) := by
      rw [← List.drop_one, List.drop_drop, Nat.add_comm]
    have hdb : b.tail.drop m = b.drop (m + 1) := by
      rw [← List.drop_one, List.drop_drop, Nat.add_comm]
    rw [hda, hdb] at hrec
    omega

/-- **The sorted-neighbour bound, on lists.** Of two strings that both sort below a third, the
nearer one shares at least as long a prefix with it. -/
private theorem lcpLen_le_of_le : ∀ (x y z : List Nat), x ≤ y → y ≤ z →
    lcpLen x z ≤ lcpLen y z
  | [], _, _, _, _ => by simp
  | a :: as, [], _, hxy, _ => absurd hxy (List.not_le.mpr (List.nil_lt_cons a as))
  | _ :: _, _ :: _, [], _, _ => by simp
  | a :: as, b :: bs, c :: cs, hxy, hyz => by
    rw [lcpLen_cons, lcpLen_cons]
    by_cases hac : a = c
    · have hab := List.cons_le_cons_iff.mp hxy
      have hbc := List.cons_le_cons_iff.mp hyz
      have hb : b = c := by
        rcases hab with h | ⟨rfl, _⟩ <;> rcases hbc with h' | ⟨rfl, _⟩ <;> omega
      have has : as ≤ bs := by rcases hab with h | ⟨_, h⟩; · omega
                               · exact h
      have hbs : bs ≤ cs := by rcases hbc with h | ⟨_, h⟩; · omega
                               · exact h
      simp only [hac, hb, reduceIte]
      exact Nat.succ_le_succ (lcpLen_le_of_le as bs cs has hbs)
    · simp [hac]

/-! ### Reading the suffix array -/

/-- Suffix `i + 1` is suffix `i` with its first character dropped. -/
private theorem suffix_succ (t : List Nat) (i : Nat) : suffix t (i + 1) = (suffix t i).tail := by
  simp only [suffix, List.tail_drop]

/-- Shifting a suffix's start is dropping inside it. -/
private theorem suffix_add (t : List Nat) (i m : Nat) :
    suffix t (i + m) = (suffix t i).drop m := by
  simp only [suffix, List.drop_drop]

/-- A suffix array lists as many positions as the text has. -/
private theorem length_eq_of_valid {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    sa.length = t.length := by
  simpa using hsa.1.length_eq

/-- Every entry of a suffix array is a position of the text. -/
private theorem lt_length_of_mem {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {a : Nat}
    (ha : a ∈ sa) : a < t.length :=
  List.mem_range.mp (hsa.1.mem_iff.mp ha)

/-- Every position of the text appears in the suffix array. -/
private theorem mem_of_lt_length {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {p : Nat}
    (hp : p < t.length) : p ∈ sa :=
  hsa.1.mem_iff.mpr (List.mem_range.mpr hp)

/-- The suffix array is duplicate-free, being a permutation of a range. -/
private theorem nodup_of_valid {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) : sa.Nodup :=
  hsa.1.nodup_iff.mpr List.nodup_range

/-- Reading the array at an index that is in range. -/
private theorem sa_getElem! {sa : List Nat} {i : Nat} (hi : i < sa.length) : sa[i]! = sa[i] :=
  getElem!_pos sa i hi

/-- Every entry of a suffix array is a position of the text, read by index. -/
private theorem sa_lt_length {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {i : Nat}
    (hi : i < sa.length) : sa[i]! < t.length := by
  rw [sa_getElem! hi]; exact lt_length_of_mem hsa (List.getElem_mem hi)

/-- The array is sorted, so a smaller index carries a suffix that sorts no higher. -/
private theorem suffix_le_of_index_le {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩)
    {i j : Nat} (hij : i ≤ j) (hj : j < sa.length) :
    suffix t sa[i]! ≤ suffix t sa[j]! := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact List.le_refl _
  · have hi : i < sa.length := Nat.lt_trans hlt hj
    have hmi : i < (sa.map (suffix t)).length := by simpa using hi
    have hmj : j < (sa.map (suffix t)).length := by simpa using hj
    have hp := List.pairwise_iff_getElem.mp hsa.2 i j hmi hmj hlt
    rwa [List.getElem_map, List.getElem_map, ← sa_getElem! hi, ← sa_getElem! hj] at hp

/-- Distinct positions of one text carry distinct suffixes, so a bound between two of them is
strict unless the positions agree. -/
private theorem suffix_lt_of_le {t : List Nat} {i j : Nat} (hi : i < t.length) (hj : j < t.length)
    (hne : i ≠ j) (hle : suffix t i ≤ suffix t j) : suffix t i < suffix t j :=
  List.not_le.mp (fun hcon => hne (suffix_inj hi hj (List.le_antisymm hle hcon)))

/-- **The sorted-neighbour bound, on the array.** The immediate predecessor of an entry shares at
least as long a prefix with it as any earlier entry does. -/
private theorem lcpLen_pred_ge {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩)
    {q r : Nat} (hq : q < r) (hr : r < sa.length) :
    lcpLen (suffix t sa[q]!) (suffix t sa[r]!)
      ≤ lcpLen (suffix t sa[r - 1]!) (suffix t sa[r]!) := by
  have hr1 : r - 1 < sa.length := Nat.lt_of_le_of_lt (Nat.sub_le r 1) hr
  exact lcpLen_le_of_le _ _ _ (suffix_le_of_index_le hsa (by omega) hr1)
    (suffix_le_of_index_le hsa (Nat.sub_le r 1) hr)

/-! ### The inverse suffix array -/

/-- A position's row is an index of the array. -/
private theorem idxOf_lt {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {p : Nat}
    (hp : p < t.length) : sa.idxOf p < sa.length :=
  List.idxOf_lt_length_of_mem (mem_of_lt_length hsa hp)

/-- The row really is an inverse: the array at `p`'s row is `p`. -/
private theorem getElem_idxOf' {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {p : Nat}
    (hp : p < t.length) : sa[sa.idxOf p]! = p := by
  rw [sa_getElem! (idxOf_lt hsa hp)]
  exact List.getElem_idxOf (idxOf_lt hsa hp)

/-- Two indices carrying the same position are the same index. -/
private theorem index_inj {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {i j : Nat}
    (hi : i < sa.length) (hj : j < sa.length) (h : sa[i]! = sa[j]!) : i = j := by
  rw [sa_getElem! hi, sa_getElem! hj] at h
  exact (List.Nodup.getElem_inj_iff (nodup_of_valid hsa)).mp h

/-- A suffix that sorts strictly below another has a strictly smaller row. -/
private theorem idxOf_lt_idxOf {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {a b : Nat}
    (ha : a < t.length) (hb : b < t.length) (hlt : suffix t a < suffix t b) :
    sa.idxOf a < sa.idxOf b := by
  refine Nat.lt_of_not_le (fun hcon => ?_)
  have hle := suffix_le_of_index_le hsa hcon (idxOf_lt hsa ha)
  rw [getElem_idxOf' hsa ha, getElem_idxOf' hsa hb] at hle
  exact absurd hle (List.not_le.mpr hlt)

/-! ### The carry is always a valid place to resume -/

/-- `lcpEntry` at a row of the table, read through `!`. -/
theorem lcpEntry_of_lt {t sa : List Nat} {r : Nat} (hr : r < sa.length) :
    lcpEntry t sa r = if r = 0 then 0 else lcpLen (suffix t sa[r - 1]!) (suffix t sa[r]!) := by
  cases r with
  | zero => rfl
  | succ r =>
    simp [lcpEntry, hr, getElem!_pos sa r (by omega)]

/-- `Kasai.EarlierRowsFilled` read through `!`, when the array and the partial array are as long
as the text. -/
theorem Kasai.earlierRowsFilled_iff {t sa : List Nat} {p : Nat} {out : List Nat}
    (hout : out.length = t.length) (hsa : sa.length = t.length) :
    Kasai.EarlierRowsFilled t sa p out ↔
      ∀ j, j < t.length → out[j]! = if sa[j]! < p then lcpEntry t sa j else 0 := by
  constructor
  · intro h j hj
    rw [getElem!_pos out j (by omega), getElem!_pos sa j (by omega)]
    exact h j (by omega) (by omega)
  · intro h j h₁ h₂
    have := h j (by omega)
    rwa [getElem!_pos out j h₁, getElem!_pos sa j h₂] at this

/-- **The step the carry rests on.** Once the entry for text position `p` is stored, one less than
it still bounds what the next text position shares with its predecessor. -/
private theorem carry_le_next {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {q p : Nat}
    (hq : q < t.length) (hp : p < t.length) (hlt : suffix t q < suffix t p)
    (hnext : p + 1 < t.length) :
    lcpLen (suffix t q) (suffix t p) - 1 ≤ lcpEntry t sa (sa.idxOf (p + 1)) := by
  rcases Nat.lt_or_ge (lcpLen (suffix t q) (suffix t p)) 2 with hL | hL
  · omega
  have hne : q ≠ p := fun hcon => by rw [hcon] at hlt; exact List.lt_irrefl _ hlt
  have hcq : suffix t q = t[q] :: suffix t (q + 1) := by
    simp only [suffix, List.drop_eq_getElem_cons hq]
  have hcp : suffix t p = t[p] :: suffix t (p + 1) := by
    simp only [suffix, List.drop_eq_getElem_cons hp]
  have hchar : t[q]! = t[p]! := by
    rw [getElem!_pos t q hq, getElem!_pos t p hp]
    by_contra hcon
    rw [hcq, hcp, lcpLen_cons] at hL
    simp [hcon] at hL
  have htail : lcpLen (suffix t (q + 1)) (suffix t (p + 1))
      = lcpLen (suffix t q) (suffix t p) - 1 := by
    rw [suffix_succ, suffix_succ]
    exact lcpLen_tail _ _ (by omega)
  have hq1 : q + 1 < t.length := by
    have hb : lcpLen (suffix t q) (suffix t p) - 1 ≤ t.length - (q + 1) := by
      have hle := lcpLen_le_left (suffix t (q + 1)) (suffix t (p + 1))
      rw [htail] at hle
      simpa [suffix] using hle
    omega
  have hlt1 : suffix t (q + 1) < suffix t (p + 1) :=
    suffix_lt_of_le hq1 hnext (by omega)
      ((suffix_le_cons_iff t q p hq hp hchar).mp (List.le_of_lt hlt))
  have hrank := idxOf_lt_idxOf hsa hq1 hnext hlt1
  have hbound := lcpLen_pred_ge hsa hrank (idxOf_lt hsa hnext)
  rw [getElem_idxOf' hsa hq1, getElem_idxOf' hsa hnext, htail] at hbound
  rwa [lcpEntry_of_lt (idxOf_lt hsa hnext), ite_eq_right (by omega : ¬ sa.idxOf (p + 1) = 0),
    getElem_idxOf' hsa hnext]

/-! ### The scan -/

/-! ### Kasai's running state, step by step -/

/-- One step of `kasaiLoop` at text position `p`: the carry and the array it hands to `p + 1`. -/
def Kasai.step (t sa : List Nat) (p h : Nat) (out : List Nat) : Nat × List Nat :=
  match sa.idxOf p with
  | 0 => (h - 1, out)
  | r + 1 => (resume t sa[r]! p h - 1, out.set (r + 1) (resume t sa[r]! p h))

/-- `kasaiLoop` runs `Kasai.step` and goes on from `p + 1`. -/
theorem Kasai.kasaiLoop_succ (t sa : List Nat) (fuel p h : Nat) (out : List Nat) :
    kasaiLoop t sa (fuel + 1) p h out =
      kasaiLoop t sa fuel (p + 1) (Kasai.step t sa p h out).1 (Kasai.step t sa p h out).2 := by
  simp only [kasaiLoop, Kasai.step]
  split <;> rfl

/-- The scan starts in `Kasai.Valid`: carry `0`, an all-zero array, no position visited. -/
theorem Kasai.valid_init (t sa : List Nat) :
    Kasai.Valid t sa 0 0 (List.replicate t.length 0) := by
  unfold Kasai.Valid Kasai.OneEntryPerRow Kasai.CarryNeverOvershoots Kasai.EarlierRowsFilled
  refine ⟨by simp, fun _ => by omega, ?_⟩
  intro j _ _
  simp

/-- **Each step keeps `Kasai.Valid`.** The stored entry is the definition's, because the carry was
a safe place to resume; the carry handed on still bounds the next entry (`carry_le_next`). -/
theorem Kasai.valid_step {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) {p h : Nat}
    {out : List Nat} (hp : p < t.length) (hv : Kasai.Valid t sa p h out) :
    Kasai.Valid t sa (p + 1) (Kasai.step t sa p h out).1 (Kasai.step t sa p h out).2 := by
  have hlensa : sa.length = t.length := length_eq_of_valid hsa
  unfold Kasai.Valid at hv ⊢
  obtain ⟨hlen, hcarry, hout⟩ := hv
  unfold Kasai.OneEntryPerRow at hlen
  rw [Kasai.earlierRowsFilled_iff hlen hlensa] at hout
  unfold Kasai.CarryNeverOvershoots at hcarry ⊢
  unfold Kasai.OneEntryPerRow
  have hidx : sa.idxOf p < sa.length := idxOf_lt hsa hp
  have hpe : sa[sa.idxOf p]! = p := getElem_idxOf' hsa hp
  unfold Kasai.step
  rcases hr : sa.idxOf p with _ | r
  · -- Rank `0`: no predecessor, so nothing is compared and the entry keeps its `0`.
    have h0 : h = 0 := by
      have hc := hcarry hp
      rw [hr] at hc
      exact Nat.le_zero.mp hc
    refine ⟨hlen, fun _ => by dsimp only; omega, ?_⟩
    rw [Kasai.earlierRowsFilled_iff hlen hlensa]
    intro j hj
    rw [hout j hj]
    by_cases hjp : sa[j]! = p
    · have hj0 : j = 0 := by
        rw [← hr]
        exact index_inj hsa (by omega) hidx (by rw [hjp, hpe])
      simp [hj0, lcpEntry]
    · simp only [show (sa[j]! < p + 1) ↔ (sa[j]! < p) from by omega]
  · -- Rank `r + 1`: resume the comparison against `sa[r]`, store it, give one unit back.
    have hr1 : r + 1 < sa.length := hr ▸ hidx
    have hrlt : r < sa.length := Nat.lt_of_succ_lt hr1
    have hpe' : sa[r + 1]! = p := by rw [← hr]; exact hpe
    have hcar : h ≤ lcpLen (suffix t sa[r]!) (suffix t p) := by
      have hc := hcarry hp
      rw [hr, lcpEntry_of_lt hr1, ite_eq_right (Nat.succ_ne_zero r), Nat.add_sub_cancel, hpe']
        at hc
      exact hc
    have hres : resume t sa[r]! p h = lcpLen (suffix t sa[r]!) (suffix t p) := by
      rw [resume, suffix_add, suffix_add]
      exact (lcpLen_resume h _ _ hcar).symm
    have hentry : resume t sa[r]! p h = lcpEntry t sa (r + 1) := by
      rw [hres, lcpEntry_of_lt hr1, ite_eq_right (Nat.succ_ne_zero r), Nat.add_sub_cancel, hpe']
    -- `sa[r]` sorts strictly below `p`, which is what `carry_le_next` needs.
    have hqlt : suffix t sa[r]! < suffix t p := by
      refine suffix_lt_of_le (sa_lt_length hsa hrlt) hp (fun hcon => ?_) ?_
      · have := index_inj hsa hrlt hr1 (by rw [hcon, hpe'])
        omega
      · have := suffix_le_of_index_le hsa (Nat.le_succ r) hr1
        rwa [hpe'] at this
    refine ⟨by dsimp only; rw [List.length_set]; exact hlen, ?_, ?_⟩
    · intro hnext
      dsimp only
      rw [hres]
      exact carry_le_next hsa (sa_lt_length hsa hrlt) hp hqlt hnext
    · rw [Kasai.earlierRowsFilled_iff (by rw [List.length_set]; exact hlen) hlensa]
      intro j hj
      dsimp only
      have hjset : j < (out.set (r + 1) (resume t sa[r]! p h)).length := by
        rw [List.length_set]; omega
      rw [getElem!_pos _ j hjset, List.getElem_set]
      by_cases hjr : r + 1 = j
      · subst hjr
        rw [ite_eq_left rfl, hpe', ite_eq_left (Nat.lt_succ_self p), hentry]
      · rw [ite_eq_right hjr, ← getElem!_pos out j (by omega), hout j hj]
        have hjp : sa[j]! ≠ p := fun hcon =>
          hjr (index_inj hsa hr1 (by omega) (by rw [hpe', hcon]))
        simp only [show (sa[j]! < p + 1) ↔ (sa[j]! < p) from by omega]

/-- **`Kasai.Valid` gives the answer.** Entering position `p` in `Kasai.Valid`, with enough fuel,
the scan finishes the array with every entry the definition's. -/
theorem Kasai.kasaiLoop_eq_of_valid {t sa : List Nat} (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    ∀ (fuel p h : Nat) (out : List Nat), p + fuel = t.length → Kasai.Valid t sa p h out →
      kasaiLoop t sa fuel p h out = (List.range t.length).map (lcpEntry t sa)
  | 0, p, h, out, hfuel, ⟨hlen, _, hout⟩ => by
    unfold Kasai.OneEntryPerRow at hlen
    have hlensa : sa.length = t.length := length_eq_of_valid hsa
    rw [Kasai.earlierRowsFilled_iff hlen hlensa] at hout
    rw [show kasaiLoop t sa 0 p h out = out from rfl]
    refine List.ext_getElem (by simp [hlen]) ?_
    intro i h1 h2
    rw [hlen] at h1
    have hsaj : sa[i]! < p := by
      have := sa_lt_length hsa (i := i) (by omega)
      omega
    have hi := hout i h1
    rw [ite_eq_left hsaj] at hi
    rw [← getElem!_pos out i (by omega), hi]
    simp
  | fuel + 1, p, h, out, hfuel, hv => by
    rw [Kasai.kasaiLoop_succ]
    exact Kasai.kasaiLoop_eq_of_valid hsa fuel (p + 1) _ _ (by omega)
      (Kasai.valid_step hsa (by omega) hv)

/-- **Kasai's correctness.** The scan computes the definition's array: entry `r` is the
common-prefix length of the suffixes at `sa[r - 1]` and `sa[r]`, and entry `0` is `0`. -/
theorem kasai_eq (t : List Nat) (sa : List Nat) (h : SuffixArray.Valid ⟨t, sa⟩) :
    kasai t sa = (List.range sa.length).map fun r =>
      if r = 0 then 0 else lcpLen (suffix t sa[r - 1]!) (suffix t sa[r]!) := by
  rw [kasai, Kasai.kasaiLoop_eq_of_valid h t.length 0 0 _ (by omega) (Kasai.valid_init t sa),
    ← length_eq_of_valid h]
  exact List.map_congr_left fun r hr => lcpEntry_of_lt (List.mem_range.1 hr)

/-- The longest substring occurring at least twice: the first row reaching the largest entry, cut
to that length; `[]` if every entry is `0`. That it is the longest repeat is not proved. -/
def longestRepeat (t : List Nat) (sa : List Nat) : List Nat :=
  let best := (List.range sa.length).foldl
    (fun (acc : Nat × Nat) r => if acc.2 < lcpEntry t sa r then (r, lcpEntry t sa r) else acc)
    (0, 0)
  (suffix t sa[best.1]!).take best.2

end AlgoDesign.Strings
