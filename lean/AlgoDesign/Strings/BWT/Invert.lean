/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.BWT.Rotations

/-!
# Burrows–Wheeler transform: the last column rebuilds the text

The LF mapping `lf`, the walk `lfWalk` and the inverse `invertBwt`. `invertBwt_bwt`: walking `lf`
from the sentinel's row returns the text. The key fact is `lf_spec`: `lf r` is the row of text
position `sa[r] - 1`. `saOf` reads the suffix array off the same walk (`saOf_bwtOfSa`). The
transform of a text that ends with one `$` keeps `BWT.Valid` and `BWT.WellFormed` (`valid_bwtOfSa`).
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Last-to-first: row `r`'s last letter `c` is row `lf r`'s first. Counts the letters smaller
than `c`, plus the `c`s in the last column before `r`. -/
def lf (bwt : List Nat) (r : Nat) : Nat :=
  (bwt.filter (fun c => decide (c < bwt[r]!))).length
    + ((bwt.take r).filter (fun c => decide (c = bwt[r]!))).length

/-- `k` steps of the walk from row `r`, reading the last column as it goes. -/
def lfWalk (bwt : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, r => bwt[r]! :: lfWalk bwt k (lf bwt r)

/-- The inverse transform: walk `lf` from the row ending in the sentinel (the smallest letter) for
`n` steps; that spells the text backwards. -/
def invertBwt (bwt : List Nat) : List Nat :=
  (lfWalk bwt bwt.length (bwt.idxOf (bwt.min?.getD 0))).reverse

/-- The sentinel is the text's last character, read through `getLast`. -/
private theorem getLast_of_terminated {t : List Nat} {s : Nat} (h : Terminated t s) :
    t.getLast h.ne_nil = s :=
  (Option.some.inj (h.1.symm.trans (List.getLast?_eq_some_getLast h.ne_nil))).symm

/-- The sentinel is the smallest character the text carries. -/
private theorem sentinel_le_of_mem {t : List Nat} {s : Nat} (h : Terminated t s) :
    ∀ c ∈ t, s ≤ c := by
  intro c hc
  have hlast : t.getLast h.ne_nil = s := getLast_of_terminated h
  rw [← List.dropLast_append_getLast h.ne_nil] at hc
  rcases List.mem_append.mp hc with hc' | hc'
  · exact Nat.le_of_lt (h.2 c hc')
  · rw [List.mem_singleton] at hc'
    omega

/-- And it stands nowhere but at the end. -/
private theorem eq_last_of_eq_sentinel {t : List Nat} {s : Nat} (h : Terminated t s) {j : Nat}
    (hj : j < t.length) (hc : t[j]! = s) : j = t.length - 1 := by
  by_contra hne
  have := lt_getElem!_of_terminated h (k := j) (by omega)
  omega

/-- A strictly smaller first character settles a comparison between two suffixes on the spot. -/
private theorem suffix_lt_of_getElem!_lt {t : List Nat} {i j : Nat} (hi : i < t.length)
    (hj : j < t.length) (hlt : t[i]! < t[j]!) : suffix t i < suffix t j := by
  rw [getElem!_pos t i hi, getElem!_pos t j hj] at hlt
  simp only [suffix, List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj,
    List.cons_lt_cons_iff]
  exact Or.inl hlt

/-- A count splits into two counts when the two cases cover it and never overlap. -/
theorem countP_split {A B C : Nat → Bool} : ∀ {l : List Nat},
    (∀ x ∈ l, A x = (B x || C x)) → (∀ x ∈ l, B x = true → C x = false) →
    l.countP A = l.countP B + l.countP C := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro hor hex
    have hx := hor x List.mem_cons_self
    have hrec := ih (fun y hy => hor y (List.mem_cons_of_mem _ hy))
      (fun y hy => hex y (List.mem_cons_of_mem _ hy))
    rw [List.countP_cons, List.countP_cons, List.countP_cons, hrec]
    by_cases hB : B x = true
    · have hC : C x = false := hex x List.mem_cons_self hB
      rw [hB, hC] at hx
      simp only [Bool.or_false] at hx
      simp only [hx, hB, hC, Bool.false_eq_true, reduceIte]
      omega
    · have hB' : B x = false := by simpa using hB
      rw [hB'] at hx
      simp only [Bool.false_or] at hx
      simp only [hx, hB', Bool.false_eq_true, reduceIte]
      omega

/-- Stepping one position left, wrapping at the front, permutes the positions. -/
private theorem map_prev_perm_range (n : Nat) (hn : 0 < n) :
    ((List.range n).map (fun i => (i + n - 1) % n)).Perm (List.range n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have htail : ∀ k ∈ List.range m, (Nat.succ k + (m + 1) - 1) % (m + 1) = id k := by
    intro k hk
    have hkm : k < m := List.mem_range.mp hk
    rw [show Nat.succ k + (m + 1) - 1 = k + (m + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show k < m + 1 by omega)]
    rfl
  have hmap : (List.range (m + 1)).map (fun i => (i + (m + 1) - 1) % (m + 1))
      = m :: List.range m := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ List.cons ?_ ?_
    · simp [Nat.mod_eq_of_lt (by omega : m < m + 1)]
    · rw [show ((fun i => (i + (m + 1) - 1) % (m + 1)) ∘ Nat.succ)
        = (fun k => (Nat.succ k + (m + 1) - 1) % (m + 1)) from rfl,
        List.map_congr_left htail, List.map_id]
  rw [hmap, List.range_succ]
  exact (List.perm_append_singleton m (List.range m)).symm

/-- Reading the last column off row `r`. -/
private theorem getElem!_bwtOfSa (t sa : List Nat) (r : Nat) (hr : r < sa.length) :
    (bwtOfSa t sa)[r]! = t[(sa[r]! + t.length - 1) % t.length]! := by
  have hlen : r < (bwtOfSa t sa).length := by simpa [bwtOfSa] using hr
  rw [getElem!_pos _ r hlen, getElem!_pos sa r hr]
  simp only [bwtOfSa, List.getElem_map]

/-- Stepping one position left from the front wraps to the end. -/
private theorem prev_zero (n : Nat) (hn : 0 < n) : (0 + n - 1) % n = n - 1 := by
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

/-- Everywhere else it is the position before. -/
private theorem prev_pos (n a : Nat) (ha : a < n) (h0 : a ≠ 0) : (a + n - 1) % n = a - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  rw [show k + 1 + n - 1 = k + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show k < n by omega)]
  omega

/-- `saPos` names a real row, and it is the row of that suffix. -/
private theorem saPos_row (t sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) {p : Nat}
    (hp : p < t.length) : saPos t p < sa.length ∧ sa[saPos t p]! = p := by
  have hmem : p ∈ sa := hsa.1.mem_iff.mpr (List.mem_range.mpr hp)
  obtain ⟨r, hr, hrp⟩ := List.getElem_of_mem hmem
  have hcount := saPos_eq_count t sa hsa r hr
  rw [getElem!_pos sa r hr, hrp] at hcount
  rw [hcount, getElem!_pos sa r hr, hrp]
  exact ⟨hr, rfl⟩

/-- The rows before row `r` are exactly the rows whose suffix sorts strictly below row `r`'s. -/
private theorem take_eq_filter_suffix_lt (t sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩)
    (r : Nat) (hr : r < sa.length) :
    sa.filter (fun j => decide (suffix t j < suffix t sa[r]!)) = sa.take r := by
  obtain ⟨hperm, hsorted⟩ := hsa
  unfold SuffixArray.SuffixesSorted at hsorted
  rw [List.pairwise_map] at hsorted
  have hnodup : sa.Pairwise (· ≠ ·) := hperm.nodup_iff.mpr List.nodup_range
  have hmem : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (hperm.mem_iff.mp ha)
  have hsplit : sa.take r ++ sa.drop r = sa := List.take_append_drop r sa
  rw [← hsplit] at hsorted hnodup
  obtain ⟨-, hsortedD, hcross⟩ := List.pairwise_append.mp hsorted
  obtain ⟨-, -, hcrossne⟩ := List.pairwise_append.mp hnodup
  have hdrop : sa.drop r = sa[r] :: sa.drop (r + 1) := List.drop_eq_getElem_cons hr
  have hrmem : sa[r] ∈ sa.drop r := by rw [hdrop]; exact List.mem_cons_self
  have hge : ∀ b ∈ sa.drop r, suffix t sa[r] ≤ suffix t b := by
    rw [hdrop] at hsortedD ⊢
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact List.not_lt.mp (List.lt_irrefl _)
    · exact (List.pairwise_cons.mp hsortedD).1 b hb'
  rw [getElem!_pos sa r hr]
  have htake : (sa.take r).filter (fun j => decide (suffix t j < suffix t sa[r])) = sa.take r := by
    refine List.filter_eq_self.mpr ?_
    intro a ha
    have hamem : a ∈ sa := List.mem_of_mem_take ha
    have hle : suffix t a ≤ suffix t sa[r] := hcross a ha _ hrmem
    have hne : a ≠ sa[r] := hcrossne a ha _ hrmem
    simp only [decide_eq_true_eq]
    refine List.not_le.mp (fun hcon => hne ?_)
    exact suffix_inj (hmem a hamem) (hmem _ (List.getElem_mem hr)) (List.le_antisymm hle hcon)
  have hnil : (sa.drop r).filter (fun j => decide (suffix t j < suffix t sa[r])) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro b hb
    simp only [decide_eq_true_eq]
    exact fun hlt => absurd (hge b hb) (List.not_le.mpr hlt)
  have key : (sa.take r ++ sa.drop r).filter (fun j => decide (suffix t j < suffix t sa[r]))
      = sa.take r := by
    rw [List.filter_append, htake, hnil, List.append_nil]
  rwa [hsplit] at key

/-- Two rows ending in the same letter are in the order of the positions one step to the left. -/
private theorem prev_suffix_lt_iff (t : List Nat) (s : Nat) (h : Terminated t s) {a p : Nat}
    (ha : a < t.length) (hp : p < t.length)
    (hchar : t[(a + t.length - 1) % t.length]! = t[(p + t.length - 1) % t.length]!) :
    suffix t a < suffix t p ↔
      suffix t ((a + t.length - 1) % t.length) < suffix t ((p + t.length - 1) % t.length) := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have ha' : (a + t.length - 1) % t.length < t.length := Nat.mod_lt _ hn
  have hp' : (p + t.length - 1) % t.length < t.length := Nat.mod_lt _ hn
  by_cases hlast : (p + t.length - 1) % t.length = t.length - 1
  · have hps : t[(p + t.length - 1) % t.length]! = s := by
      rw [hlast]; exact getElem!_last_of_terminated h
    have halast : (a + t.length - 1) % t.length = t.length - 1 :=
      eq_last_of_eq_sentinel h ha' (hchar.trans hps)
    have hp0 : p = 0 := by
      by_contra h0
      rw [prev_pos t.length p hp h0] at hlast
      omega
    have ha0 : a = 0 := by
      by_contra h0
      rw [prev_pos t.length a ha h0] at halast
      omega
    rw [hp0, ha0]
    simp [List.lt_irrefl]
  · have hpne : p ≠ 0 := by
      intro h0
      rw [h0, prev_zero t.length hn] at hlast
      omega
    have hane : a ≠ 0 := by
      intro h0
      rw [h0, prev_zero t.length hn, getElem!_last_of_terminated h] at hchar
      exact hlast (eq_last_of_eq_sentinel h hp' hchar.symm)
    have hpsucc : (p + t.length - 1) % t.length + 1 = p := by
      rw [prev_pos t.length p hp hpne]; omega
    have hasucc : (a + t.length - 1) % t.length + 1 = a := by
      rw [prev_pos t.length a ha hane]; omega
    have hiff := suffix_le_cons_iff t ((p + t.length - 1) % t.length)
      ((a + t.length - 1) % t.length) hp' ha' hchar.symm
    rw [hpsucc, hasucc] at hiff
    rw [← List.not_le, ← List.not_le, ← hiff]

/-- `lf` lands on the row of the position one step to the left: smaller letters fill the rows
before `c`'s block, and earlier `c`s give the offset inside it. -/
private theorem lf_eq_saPos (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (r : Nat) (hr : r < sa.length) :
    lf (bwtOfSa t sa) r = saPos t ((sa[r]! + t.length - 1) % t.length) := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hmemsa : ∀ a ∈ sa, a < t.length := fun a ha => List.mem_range.mp (hsa.1.mem_iff.mp ha)
  have hp : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact hmemsa _ (List.getElem_mem hr)
  have hq : (sa[r]! + t.length - 1) % t.length < t.length := Nat.mod_lt _ hn
  have hchar := getElem!_bwtOfSa t sa r hr
  have hpart1 : (bwtOfSa t sa).countP
      (fun d => decide (d < t[(sa[r]! + t.length - 1) % t.length]!))
      = (List.range t.length).countP
        (fun j => decide (t[j]! < t[(sa[r]! + t.length - 1) % t.length]!)) := by
    rw [bwtOfSa, List.countP_map, hsa.1.countP_eq]
    conv_rhs => rw [← (map_prev_perm_range t.length hn).countP_eq]
    rw [List.countP_map]
    rfl
  have hpart2 : ((bwtOfSa t sa).take r).countP
      (fun d => decide (d = t[(sa[r]! + t.length - 1) % t.length]!))
      = (List.range t.length).countP
        (fun j => decide (t[j]! = t[(sa[r]! + t.length - 1) % t.length]!) &&
          decide (suffix t j < suffix t ((sa[r]! + t.length - 1) % t.length))) := by
    have hbt : (bwtOfSa t sa).take r
        = (sa.take r).map (fun p => t[(p + t.length - 1) % t.length]!) := by
      rw [bwtOfSa, List.map_take]
    rw [hbt, List.countP_map, ← take_eq_filter_suffix_lt t sa hsa r hr, List.countP_filter,
      hsa.1.countP_eq]
    conv_rhs => rw [← (map_prev_perm_range t.length hn).countP_eq]
    rw [List.countP_map]
    refine List.countP_congr ?_
    intro a hamem
    have han := List.mem_range.mp hamem
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (prev_suffix_lt_iff t s h han hp h1).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (prev_suffix_lt_iff t s h han hp h1).mpr h2⟩
  have hsplit : saPos t ((sa[r]! + t.length - 1) % t.length)
      = (List.range t.length).countP
          (fun j => decide (t[j]! < t[(sa[r]! + t.length - 1) % t.length]!))
        + (List.range t.length).countP
          (fun j => decide (t[j]! = t[(sa[r]! + t.length - 1) % t.length]!) &&
            decide (suffix t j < suffix t ((sa[r]! + t.length - 1) % t.length))) := by
    rw [saPos, ← List.countP_eq_length_filter]
    refine countP_split ?_ ?_
    · intro j hj
      have hjn := List.mem_range.mp hj
      by_cases h1 : t[j]! < t[(sa[r]! + t.length - 1) % t.length]!
      · rw [decide_eq_true (suffix_lt_of_getElem!_lt hjn hq h1), decide_eq_true h1]
        rfl
      · by_cases h2 : t[j]! = t[(sa[r]! + t.length - 1) % t.length]!
        · rw [decide_eq_false h1, decide_eq_true h2]
          rfl
        · have hgt : t[(sa[r]! + t.length - 1) % t.length]! < t[j]! := by omega
          have hnot : ¬ (suffix t j < suffix t ((sa[r]! + t.length - 1) % t.length)) :=
            List.le_of_lt (suffix_lt_of_getElem!_lt hq hjn hgt)
          rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false hnot]
          rfl
    · intro x _ hB
      simp only [decide_eq_true_eq] at hB
      rw [decide_eq_false (show ¬ (t[x]! = t[(sa[r]! + t.length - 1) % t.length]!) by omega)]
      rfl
  rw [lf, hchar, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    hpart1, hpart2, hsplit]

/-- `lf r` is the row of text position `(sa[r] - 1) mod n`. -/
theorem lf_spec (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (r : Nat) (hr : r < sa.length) :
    sa[lf (bwtOfSa t sa) r]! = (sa[r]! + t.length - 1) % t.length := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  rw [lf_eq_saPos t s h sa hsa r hr]
  exact (saPos_row t sa hsa (Nat.mod_lt _ hn)).2

/-- Stepping one position left from position `(j + 1) mod n` lands on position `j mod n`. -/
private theorem prev_mod_succ (n j : Nat) (hn : 0 < n) (hj : j + 1 ≤ n) :
    ((j + 1) % n + n - 1) % n = j % n := by
  by_cases heq : j + 1 = n
  · rw [heq, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (show n - 1 < n by omega),
      Nat.mod_eq_of_lt (show j < n by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show j + 1 < n by omega), show j + 1 + n - 1 = j + n by omega,
      Nat.add_mod_right]

/-- From the row of position `j`, `j` steps of `lf` read `t[0, j)` in reverse. -/
private theorem lfWalk_eq (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    ∀ j, j ≤ t.length →
      lfWalk (bwtOfSa t sa) j (saPos t (j % t.length)) = (t.take j).reverse := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hjlt : j < t.length := by omega
    have hmod : (j + 1) % t.length < t.length := Nat.mod_lt _ hn
    obtain ⟨hrow, hsaval⟩ := saPos_row t sa hsa hmod
    rw [lfWalk, getElem!_bwtOfSa t sa _ hrow, hsaval,
      lf_eq_saPos t s h sa hsa _ hrow, hsaval, prev_mod_succ t.length j hn hj,
      ih (by omega), Nat.mod_eq_of_lt hjlt, List.take_succ_eq_append_getElem hjlt,
      List.reverse_append, getElem!_pos t j hjlt]
    rfl

/-- From the row of position `(f + k) mod n`, `k` steps of `lf` read `t[f, f + k)` in reverse. -/
theorem lfWalk_slice (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (f : Nat) :
    ∀ k, f + k ≤ t.length →
      lfWalk (bwtOfSa t sa) k (saPos t ((f + k) % t.length)) = ((t.drop f).take k).reverse := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : f + k < t.length := by omega
    have hmod : (f + k + 1) % t.length < t.length := Nat.mod_lt _ hn
    obtain ⟨hrow, hsaval⟩ := saPos_row t sa hsa hmod
    have hdrop : k < (t.drop f).length := by simp; omega
    rw [show f + (k + 1) = f + k + 1 by omega, lfWalk, getElem!_bwtOfSa t sa _ hrow, hsaval,
      lf_eq_saPos t s h sa hsa _ hrow, hsaval, prev_mod_succ t.length (f + k) hn hk,
      ih (by omega), Nat.mod_eq_of_lt hlt, List.take_succ_eq_append_getElem hdrop,
      List.reverse_append, getElem!_pos t (f + k) hlt, List.getElem_drop]
    rfl

/-- `lf` never leaves the table: it maps a row of the suffix array to a row of it. -/
theorem lf_lt_length (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) (r : Nat) (hr : r < sa.length) :
    lf (bwtOfSa t sa) r < sa.length := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  rw [lf_eq_saPos t s h sa hsa r hr]
  exact (saPos_row t sa hsa (Nat.mod_lt _ hn)).1

/-- The last column's smallest entry is the sentinel. -/
private theorem min?_bwt (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) : (bwtOfSa t sa).min? = some s := by
  have hperm : (bwtOfSa t sa).Perm t := by
    rw [bwt_eq_rotations t s h sa hsa]
    exact bwtOfSorted_perm t
  refine List.min?_eq_some_iff.mpr ⟨hperm.mem_iff.mpr ?_, fun c hc => ?_⟩
  · rw [← getLast_of_terminated h]
    exact List.getLast_mem h.ne_nil
  · exact sentinel_le_of_mem h c (hperm.mem_iff.mp hc)

/-- The sentinel stands in exactly one row of the last column: the row of position `0`. -/
private theorem idxOf_sentinel (t : List Nat) (s : Nat) (h : Terminated t s)
    (sa : List Nat) (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    (bwtOfSa t sa).idxOf s = saPos t 0 := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hlen : (bwtOfSa t sa).length = sa.length := by simp [bwtOfSa]
  obtain ⟨hrow, hsaval⟩ := saPos_row t sa hsa hn
  have hbwt : ∀ k, k < sa.length → ((bwtOfSa t sa)[k]! = s ↔ k = saPos t 0) := by
    intro k hk
    rw [getElem!_bwtOfSa t sa k hk]
    constructor
    · intro hks
      have hkn : sa[k]! < t.length := by
        rw [getElem!_pos sa k hk]
        exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hk))
      have hprev := eq_last_of_eq_sentinel h (Nat.mod_lt _ hn) hks
      have hk0 : sa[k]! = 0 := by
        by_contra h0
        rw [prev_pos t.length _ hkn h0] at hprev
        omega
      have := saPos_eq_count t sa hsa k hk
      rw [hk0] at this
      omega
    · intro hks
      rw [hks, hsaval, prev_zero t.length hn]
      exact getElem!_last_of_terminated h
  have hfind : (bwtOfSa t sa).findIdx (fun c => c == s) = saPos t 0 := by
    refine (List.findIdx_eq (by omega)).mpr ⟨?_, ?_⟩
    · have := (hbwt (saPos t 0) hrow).mpr rfl
      rw [getElem!_pos (bwtOfSa t sa) _ (show saPos t 0 < _ by omega)] at this
      simpa using this
    · intro k hk
      have hklen : k < (bwtOfSa t sa).length := by omega
      have hne : ¬ ((bwtOfSa t sa)[k]! = s) := by
        intro hcon
        exact absurd ((hbwt k (by omega)).mp hcon) (by omega)
      rw [getElem!_pos (bwtOfSa t sa) k hklen] at hne
      simpa using hne
  exact hfind

/-- The last column alone rebuilds a terminated text. -/
theorem invertBwt_bwt (t : List Nat) (s : Nat) (h : Terminated t s) :
    invertBwt (bwtOfSorted t) = t := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hsa := valid_suffixArray t
  rw [← bwt_eq_rotations t s h (suffixArray t) hsa]
  have hlen : (bwtOfSa t (suffixArray t)).length = t.length := by
    simp only [bwtOfSa, List.length_map]
    exact hsa.1.length_eq.trans List.length_range
  rw [invertBwt, hlen, min?_bwt t s h _ hsa, Option.getD_some,
    idxOf_sentinel t s h _ hsa, ← Nat.mod_self t.length,
    lfWalk_eq t s h _ hsa t.length (Nat.le_refl _), List.reverse_reverse,
    List.take_of_length_le (Nat.le_refl _)]

/-! ## The inverting walk's state -/

/-- A walk over the rows of a suffix array stands at one of its rows. Both LF walks keep it: the
inverting walk's `LFWalk.Valid` and the sampled walk's `SampledLocate.Valid`. -/
def RowInTable (index : SuffixArray) (row : Nat) : Prop := row < index.positions.length

instance (index : SuffixArray) (row : Nat) : Decidable (RowInTable index row) :=
  by unfold RowInTable; infer_instance

namespace LFWalk

/-- **The inverting walk's running state**: the suffix array whose rows it walks, the row it stands
at, and the text position that row should hold. -/
structure Walk where
  /-- The text and its suffix array. -/
  index : SuffixArray
  /-- The row the walk stands at. -/
  row : Nat
  /-- The text position the walk has reached. -/
  position : Nat

/-- The walk's row is the row of its text position. -/
def RowOfPosition (w : Walk) : Prop :=
  ∀ h : w.row < w.index.positions.length, w.index.positions[w.row] = w.position

/-- Not in the box: the inverting walk stands at a row of the table, the row of its text
position; each `lf` step moves it to the position before. -/
def Valid (w : Walk) : Prop := RowInTable w.index w.row ∧ RowOfPosition w

instance (w : Walk) : Decidable (RowOfPosition w) :=
  inferInstanceAs (Decidable
    (∀ h : w.row < w.index.positions.length, w.index.positions[w.row] = w.position))

instance (w : Walk) : Decidable (Valid w) :=
  by unfold Valid; infer_instance

end LFWalk

/-- One `lf` step keeps `LFWalk.Valid`, one text position back, wrapping at the front. -/
theorem LFWalk.valid_lf {w : LFWalk.Walk} {s : Nat} (h : Terminated w.index.text s)
    (hsa : SuffixArray.Valid w.index) (hv : LFWalk.Valid w) :
    LFWalk.Valid ⟨w.index, lf (bwtOfSa w.index.text w.index.positions) w.row,
      (w.position + w.index.text.length - 1) % w.index.text.length⟩ := by
  obtain ⟨⟨t, sa⟩, r, p⟩ := w
  obtain ⟨hr, hp⟩ := hv
  unfold RowInTable at hr
  unfold LFWalk.RowOfPosition at hp
  dsimp only at hr hp h hsa ⊢
  refine ⟨lf_lt_length t s h sa hsa r hr, fun hl => ?_⟩
  dsimp only
  rw [← getElem!_pos sa _ hl, lf_spec t s h sa hsa r hr, getElem!_pos sa r hr, hp hr]

/-- From a valid walk at position `f + k`, `k` steps read `t[f, f + k)` backwards. -/
theorem LFWalk.lfWalk_eq_of_valid {w : LFWalk.Walk} {s : Nat} (h : Terminated w.index.text s)
    (hsa : SuffixArray.Valid w.index) (f k : Nat) (hk : f + k ≤ w.index.text.length)
    (hv : LFWalk.Valid w) (hpos : w.position = (f + k) % w.index.text.length) :
    lfWalk (bwtOfSa w.index.text w.index.positions) k w.row
      = ((w.index.text.drop f).take k).reverse := by
  obtain ⟨⟨t, sa⟩, r, p⟩ := w
  obtain ⟨hr, hp⟩ := hv
  unfold RowInTable at hr
  unfold LFWalk.RowOfPosition at hp
  dsimp only at hr hp h hsa hk hpos ⊢
  have hrow := saPos_eq_count t sa hsa r hr
  rw [getElem!_pos sa r hr, hp hr, hpos] at hrow
  rw [← hrow]
  exact lfWalk_slice t s h sa hsa f k hk

/-! ## The suffixes, read off the walk -/

/-- For `0 < a`, `(a mod n + n - 1) mod n` is `(a - 1) mod n`. -/
private theorem prev_mod (n a : Nat) (ha : 0 < a) : (a % n + n - 1) % n = (a - 1) % n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : a % n + n - 1 = a % n + (n - 1) := by omega
    have h2 : a - 1 + n = a + (n - 1) := by omega
    rw [h1, Nat.mod_add_mod, ← h2, Nat.add_mod_right]

/-- A terminated text holds its sentinel once: at the end, and strictly below everything else. -/
theorem count_sentinel {t : List Nat} {s : Nat} (h : Terminated t s) : t.count s = 1 := by
  have hne := h.ne_nil
  obtain ⟨hlast, hlt⟩ := h
  have hgl : t.getLast hne = s := by
    rw [List.getLast?_eq_some_getLast hne] at hlast; exact Option.some.inj hlast
  have hnot : s ∉ t.dropLast := fun hm => Nat.lt_irrefl s (hlt s hm)
  conv_lhs => rw [← List.dropLast_append_getLast hne, hgl]
  rw [List.count_append, List.count_eq_zero.mpr hnot]
  simp

/-- Row `idxOf 0` is the first row ending in the sentinel: `lf` takes it to row `0`. -/
theorem lf_idxOf_zero (bwt : List Nat) : lf bwt (bwt.idxOf 0) = 0 := by
  have h0 : bwt[bwt.idxOf 0]! = 0 := by
    by_cases hm : (0 : Nat) ∈ bwt
    · rw [getElem!_pos bwt _ (List.idxOf_lt_length_of_mem hm)]; exact List.getElem_idxOf _
    · rw [List.idxOf_eq_length hm]; simp
  rw [lf, h0]
  have hnil : (bwt.take (bwt.idxOf 0)).filter (fun c => decide (c = 0)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun a ha => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha
    have := List.not_of_lt_findIdx (p := fun c => c == 0) (xs := bwt) (i := j)
      (by have := hj; simp only [Nat.lt_min] at this; exact this.1)
    simpa using this
  simp [hnil]

/-- The row whose last letter is the sentinel is the row of text position `0`. -/
theorem idxOf_sentinel_bwtOfSa {t sa : List Nat} (h : Terminated t 0)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    (bwtOfSa t sa).idxOf 0 < sa.length ∧ sa[(bwtOfSa t sa).idxOf 0]! = 0 := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hlast : t[t.length - 1]! = 0 := by
    have hne := h.ne_nil
    obtain ⟨hl, _⟩ := h
    rw [List.getLast?_eq_getElem?] at hl
    rw [getElem!_pos t _ (by omega)]
    simpa [List.getElem?_eq_getElem (show t.length - 1 < t.length by omega)] using hl
  -- Position `0` stands in some row, and that row's last letter is the sentinel.
  have h0 : (0 : Nat) ∈ sa := hsa.1.mem_iff.mpr (List.mem_range.mpr hn)
  have hmem : (0 : Nat) ∈ bwtOfSa t sa := by
    refine List.mem_map.mpr ⟨0, h0, ?_⟩
    simpa [Nat.zero_add] using hlast
  have hlt : (bwtOfSa t sa).idxOf 0 < (bwtOfSa t sa).length := List.idxOf_lt_length_of_mem hmem
  have hbl : (bwtOfSa t sa).length = sa.length := by simp [bwtOfSa]
  refine ⟨hbl ▸ hlt, ?_⟩
  set r := (bwtOfSa t sa).idxOf 0 with hr
  have hr' : r < sa.length := hbl ▸ hlt
  have hget : (bwtOfSa t sa)[r] = 0 := List.getElem_idxOf hlt
  simp only [bwtOfSa, List.getElem_map] at hget
  rw [getElem!_pos sa r hr']
  have hp : sa[r] < t.length := List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr'))
  by_contra hne
  -- Any other position's preceding letter lies before the end, so it exceeds the sentinel.
  have hidx : (sa[r] + t.length - 1) % t.length = sa[r] - 1 := by
    rw [show sa[r] + t.length - 1 = (sa[r] - 1) + t.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [hidx, getElem!_pos t _ (by omega)] at hget
  have hdrop : t[sa[r] - 1] ∈ t.dropLast := by
    rw [show t[sa[r] - 1] = t.dropLast[sa[r] - 1]'(by simp; omega) by simp]
    exact List.getElem_mem _
  exact Nat.lt_irrefl 0 (hget ▸ h.2 _ hdrop)

/-- After `j ≤ n` steps from row `r`, `lf` stands on the row of position `(sa[r] + n - j) mod n`. -/
theorem iterate_lf_from {t sa : List Nat} (h : Terminated t 0) (hsa : SuffixArray.Valid ⟨t, sa⟩)
    (r : Nat) (hr : r < sa.length) :
    ∀ j, j ≤ t.length →
      (lf (bwtOfSa t sa))^[j] r < sa.length ∧
        sa[(lf (bwtOfSa t sa))^[j] r]! = (sa[r]! + t.length - j) % t.length := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hrt : sa[r]! < t.length := by
    rw [getElem!_pos sa r hr]
    exact List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem hr))
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨hr, ?_⟩
      simp only [Function.iterate_zero, id_eq, Nat.sub_zero]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hrt]
  | succ j ih =>
      intro hj
      obtain ⟨hr', hv⟩ := ih (by omega)
      rw [Function.iterate_succ_apply']
      refine ⟨lf_lt_length t 0 h sa hsa _ hr', ?_⟩
      rw [lf_spec t 0 h sa hsa _ hr', hv, prev_mod _ _ (by omega), Nat.sub_sub]

/-- The text position of row `r`: `n - 1` minus the steps the walk from row `0` takes to reach
it. -/
def posOf (bwt : List Nat) (r : Nat) : Nat :=
  bwt.length - 1 - ((List.range bwt.length).map fun j => (lf bwt)^[j] 0).idxOf r

/-- The suffix array the letters determine: each row's text position, read off the walk. -/
def saOf (bwt : List Nat) : List Nat := (List.range bwt.length).map (posOf bwt)

/-- One entry per row. -/
theorem length_saOf (bwt : List Nat) : (saOf bwt).length = bwt.length := by simp [saOf]

/-- **The suffixes come back from the letters.** On a text that ends with one `$`, the walk reads
the suffix array off the transform. -/
theorem saOf_bwtOfSa {t sa : List Nat} (h : Terminated t 0) (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    saOf (bwtOfSa t sa) = sa := by
  have hn : 0 < t.length := List.length_pos_iff.mpr h.ne_nil
  have hlen : sa.length = t.length := by rw [hsa.1.length_eq, List.length_range]
  have hbl : (bwtOfSa t sa).length = t.length := by rw [length_bwtOfSa, hlen]
  have hnd : sa.Nodup := hsa.1.nodup_iff.mpr List.nodup_range
  obtain ⟨hr0, hv0⟩ := idxOf_sentinel_bwtOfSa h hsa
  -- Row `0` holds the last position: `lf` takes the sentinel's row, position `0`, to it.
  have hsa0 : sa[0]! = t.length - 1 := by
    have := lf_spec t 0 h sa hsa _ hr0
    rw [lf_idxOf_zero, hv0, Nat.zero_add] at this
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  -- Step `j` of the walk from row `0` stands on the row of position `n - 1 - j`.
  have hwalk : ∀ j, j < t.length → (lf (bwtOfSa t sa))^[j] 0 < sa.length ∧
      sa[(lf (bwtOfSa t sa))^[j] 0]! = t.length - 1 - j := by
    intro j hj
    obtain ⟨h1, h2⟩ := iterate_lf_from h hsa 0 (by omega) j (by omega)
    refine ⟨h1, ?_⟩
    rw [h2, hsa0, show t.length - 1 + t.length - j = (t.length - 1 - j) + t.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hinj : ∀ r r', r < sa.length → r' < sa.length → sa[r]! = sa[r']! → r = r' := by
    intro r r' hr hr' he
    rw [getElem!_pos sa r hr, getElem!_pos sa r' hr'] at he
    exact (hnd.getElem_inj_iff).mp he
  have hWnd : ((List.range (bwtOfSa t sa).length).map
      fun j => (lf (bwtOfSa t sa))^[j] 0).Nodup := by
    rw [hbl]
    refine List.Nodup.map_on (fun j hj j' hj' he => ?_) List.nodup_range
    have hj := List.mem_range.mp hj
    have hj' := List.mem_range.mp hj'
    have : t.length - 1 - j = t.length - 1 - j' := by
      rw [← (hwalk j hj).2, ← (hwalk j' hj').2, he]
    omega
  refine List.ext_getElem (by rw [length_saOf, hbl, hlen]) fun r h1 h2 => ?_
  have hp : sa[r] < t.length := List.mem_range.mp (hsa.1.mem_iff.mp (List.getElem_mem h2))
  obtain ⟨hwr, hwv⟩ := hwalk (t.length - 1 - sa[r]) (by omega)
  have hrow : (lf (bwtOfSa t sa))^[t.length - 1 - sa[r]] 0 = r :=
    hinj _ _ hwr h2 (by rw [hwv, getElem!_pos sa r h2]; omega)
  rw [hbl] at hWnd
  have hidx : ((List.range t.length).map
      fun j => (lf (bwtOfSa t sa))^[j] 0).idxOf r = t.length - 1 - sa[r] := by
    have := List.Nodup.idxOf_getElem hWnd (t.length - 1 - sa[r]) (by simp; omega)
    simpa [hrow] using this
  simp only [saOf, List.getElem_map, List.getElem_range, posOf, hidx, hbl]
  omega

/-! ## The box as one predicate -/

/-- **The pieces split into the box's and the rest**: the box's two pieces and the sentinel read
on the letters are exactly `Valid` and `WellFormed`. -/
theorem BWT.pieces_iff_valid_wellFormed (x : Transform) :
    (BWT.SameLetters x ∧ BWT.LetterBeforeEachSuffix x ∧ BWT.SentinelOnce x) ↔
      BWT.Valid x ∧ BWT.WellFormed x := by
  simp only [BWT.Valid, BWT.WellFormed, and_assoc]

/-- The transform of a text that ends with one `$`, through any suffix array of it, keeps the
box, and is well formed. -/
theorem valid_bwtOfSa (t : List Nat) (h : Terminated t 0) (sa : List Nat)
    (hsa : SuffixArray.Valid ⟨t, sa⟩) :
    BWT.Valid ⟨t, bwtOfSa t sa⟩ ∧ BWT.WellFormed ⟨t, bwtOfSa t sa⟩ := by
  have hperm : (bwtOfSa t sa).Perm t := by
    rw [bwt_eq_rotations t 0 h sa hsa]; exact bwtOfSorted_perm t
  exact ⟨⟨hperm, fun sa' hsa' => by rw [map_letterBefore hsa', valid_unique hsa hsa']⟩, by
    unfold BWT.WellFormed BWT.SentinelOnce; rw [hperm.count_eq]; exact count_sentinel h⟩

end AlgoDesign.Strings
