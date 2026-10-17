/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RabinKarp.Collision
public import AlgoDesign.Strings.RabinKarp.Cost

/-!
# Rabin–Karp's expected cost over the drawn prime

Sources: Karp and Rabin (1987); Motwani and Raghavan §7.6. One search at one modulus costs one tick
per window plus `m` per fingerprint hit (`time_rabinKarpSearchM`); the hits are the occurrences and
the **false alarms**, and only the false alarms depend on the modulus. The modulus is drawn
uniformly from a finite set `S` of primes, and the expectation of `f` is the average `avgOver S f`.
-/

@[expose] public section

namespace AlgoDesign.Strings

open scoped Nat.Prime

/-- **False alarms**: the windows whose fingerprint equals the pattern's while their letters do
not. -/
def falseAlarms (base q : Nat) (text pat : List Nat) : Nat :=
  (List.range (text.length + 1 - pat.length)).countP
    fun j => fingerprint base q ((text.drop j).take pat.length) == fingerprint base q pat
      && (text.drop j).take pat.length != pat

/-- The windows equal to the pattern: its occurrences, counted at the window starts. -/
def occWindows (text pat : List Nat) : Nat :=
  (List.range (text.length + 1 - pat.length)).countP
    fun j => (text.drop j).take pat.length == pat

/-- A count splits along a second test. -/
private theorem countP_split {α : Type} (a b : α → Bool) :
    ∀ l : List α, l.countP a = l.countP (fun x => a x && b x) + l.countP (fun x => a x && !b x)
  | [] => rfl
  | x :: l => by
      simp only [List.countP_cons, countP_split a b l]
      cases a x <;> cases b x <;> simp <;> omega

/-- **The fingerprint hits are the occurrences and the false alarms.** A window equal to the
pattern always fingerprints like it. -/
theorem candidateCount_eq (base q : Nat) (text pat : List Nat) :
    candidateCount base q text pat = occWindows text pat + falseAlarms base q text pat := by
  unfold candidateCount occWindows falseAlarms
  rw [countP_split _ (fun j => (text.drop j).take pat.length == pat)]
  congr 1
  apply List.countP_congr
  intro j _
  constructor
  · intro h; simp only [Bool.and_eq_true] at h; exact h.2
  · intro h
    have h' := beq_iff_eq.mp h
    simp [h']

/-- The occurrences counted at the window starts are `occurrenceList`'s. -/
theorem occWindows_eq (text pat : List Nat) (hlen : pat.length ≤ text.length) :
    occWindows text pat = (occurrenceList text pat).length := by
  rw [occurrenceList_eq_windows]
  unfold occWindows
  rw [← List.countP_eq_length_filter,
    show text.length + 1 = (text.length + 1 - pat.length) + pat.length by omega,
    List.range_add, List.countP_append]
  have hzero : (List.map ((text.length + 1 - pat.length) + ·) (List.range pat.length)).countP
      (fun i => decide ((text.drop i).take pat.length = pat)) = 0 := by
    rw [List.countP_eq_zero]
    intro j hj hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
    have ha' := List.mem_range.mp ha
    have := congrArg List.length (of_decide_eq_true hw)
    simp only [List.length_take, List.length_drop] at this
    omega
  rw [hzero, Nat.add_zero, Nat.add_sub_cancel]
  apply List.countP_congr
  intro j _
  simp

/-- Summing counts over a set of keys: if each index is counted by at most `N` keys, the counts
over a list of indices sum to at most `length · N`. -/
private theorem sum_countP_le (S : Finset Nat) (g : Nat → Nat → Bool) (N : Nat) :
    ∀ L : List Nat, (∀ j ∈ L, (S.filter fun p => g p j).card ≤ N) →
      ∑ p ∈ S, L.countP (g p) ≤ L.length * N
  | [], _ => by simp
  | a :: l, h => by
      simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
      have hl := sum_countP_le S g N l fun j hj => h j (List.mem_cons_of_mem a hj)
      have ha := h a List.mem_cons_self
      rw [Finset.sum_boole] at *
      simp only [Nat.cast_id] at *
      have : (l.length + 1) * N = l.length * N + N := by ring
      omega

/-- **The false alarms, summed over the primes**: at most `windows · N` over any set `S` of primes,
when the letters are below `base` and `base ^ m ≤ 2 ^ N`. -/
theorem sum_falseAlarms_le {base N : Nat} (hb : 1 < base) (S : Finset Nat)
    (hS : ∀ p ∈ S, p.Prime) (text pat : List Nat) (hN : base ^ pat.length ≤ 2 ^ N)
    (htext : ∀ c ∈ text, c < base) (hpat : ∀ c ∈ pat, c < base) :
    ∑ p ∈ S, falseAlarms base p text pat ≤ (text.length + 1 - pat.length) * N := by
  unfold falseAlarms
  refine (sum_countP_le S _ N (List.range (text.length + 1 - pat.length)) ?_).trans
    (by rw [List.length_range])
  intro j hj
  have hj' := List.mem_range.mp hj
  set w := (text.drop j).take pat.length
  have hw : w.length = pat.length := by simp [w]; omega
  have hcw : ∀ c ∈ w, c < base := fun c hc =>
    htext c (List.mem_of_mem_drop (List.mem_of_mem_take hc))
  by_cases heq : w = pat
  · have : (S.filter fun p =>
        (fingerprint base p w == fingerprint base p pat && w != pat)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro p _
      simp [heq]
    rw [this]; simp
  · calc (S.filter fun p => (fingerprint base p w == fingerprint base p pat && w != pat)).card
        ≤ (S.filter fun p => fingerprint base p w = fingerprint base p pat).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Bool.and_eq_true, beq_iff_eq] at hp ⊢
          exact ⟨hp.1, hp.2.1⟩
      _ ≤ N := card_colliding_le hb hN S hS hw rfl hcw hpat heq

/-- **The expectation over a uniform draw from `S`**: the average of `f` over `S`. -/
noncomputable def avgOver (S : Finset Nat) (f : Nat → Nat) : ℝ :=
  (∑ p ∈ S, (f p : ℝ)) / S.card

/-- **The expected number of false alarms**, the modulus drawn uniformly from a set `S` of
primes: at most `windows · N / #S`. -/
theorem avg_falseAlarms_le {base N : Nat} (hb : 1 < base) (S : Finset Nat)
    (hS : ∀ p ∈ S, p.Prime) (text pat : List Nat) (hN : base ^ pat.length ≤ 2 ^ N)
    (htext : ∀ c ∈ text, c < base) (hpat : ∀ c ∈ pat, c < base) :
    avgOver S (fun p => falseAlarms base p text pat)
      ≤ ((text.length + 1 - pat.length : Nat) : ℝ) * N / S.card := by
  unfold avgOver
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [← Nat.cast_sum]
  exact_mod_cast sum_falseAlarms_le hb S hS text pat hN htext hpat

/-- **The same at the primes up to `T ≥ 2`**, through Chebyshev's lower bound on their number:
at most `windows · N · log T / (T · log 2 − log (T + 1))`. -/
theorem avg_falseAlarms_primesLE_le {base N : Nat} (hb : 1 < base) {T : Nat} (hT : 2 ≤ T)
    (text pat : List Nat) (hN : base ^ pat.length ≤ 2 ^ N)
    (htext : ∀ c ∈ text, c < base) (hpat : ∀ c ∈ pat, c < base) :
    avgOver T.primesLE (fun p => falseAlarms base p text pat)
      ≤ ((text.length + 1 - pat.length : Nat) : ℝ) * N * Real.log T
          / (T * Real.log 2 - Real.log (T + 1)) := by
  refine (avg_falseAlarms_le hb _ (fun _ hp => Nat.prime_of_mem_primesLE hp) text pat hN
    htext hpat).trans ?_
  rw [Nat.primesLE_card_eq_primeCounting]
  obtain ⟨hL, hpi⟩ := primeCounting_mul_log_ge hT
  have hlogT : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
  have hpipos : (0 : ℝ) < π T := pos_of_mul_pos_left (hL.trans_le hpi) hlogT.le
  have hWN : (0 : ℝ) ≤ ((text.length + 1 - pat.length : Nat) : ℝ) * N := by positivity
  rw [div_le_div_iff₀ hpipos hL]
  calc ((text.length + 1 - pat.length : Nat) : ℝ) * N * (T * Real.log 2 - Real.log (T + 1))
      ≤ ((text.length + 1 - pat.length : Nat) : ℝ) * N * ((π T : ℝ) * Real.log T) :=
        mul_le_mul_of_nonneg_left hpi hWN
    _ = ((text.length + 1 - pat.length : Nat) : ℝ) * N * Real.log T * π T := by ring

/-- **The expected cost, exactly**: `windows + m · (occurrences + expected false alarms)` over a
uniform draw from a nonempty set `S` of primes. -/
theorem avg_time_rabinKarpSearchM (base : Nat) (S : Finset Nat) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, p.Prime) (text pat : List Nat) (hpat : pat ≠ [])
    (hlen : pat.length ≤ text.length) :
    avgOver S (fun p => (rabinKarpSearchM base p text pat).time)
      = ((text.length + 1 - pat.length : Nat) : ℝ)
        + pat.length * ((occurrenceList text pat).length
          + avgOver S (fun p => falseAlarms base p text pat)) := by
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  unfold avgOver
  have hterm : ∀ p ∈ S, ((rabinKarpSearchM base p text pat).time : ℝ)
      = ((text.length + 1 - pat.length : Nat) : ℝ)
        + pat.length * ((occurrenceList text pat).length : ℝ)
        + pat.length * (falseAlarms base p text pat : ℝ) := by
    intro p hp
    rw [time_rabinKarpSearchM base (hS p hp).pos text pat hpat hlen, candidateCount_eq,
      occWindows_eq text pat hlen]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- **The expected cost, bounded**: at most `windows + m · occurrences + m · windows · N / #S`,
with `base ^ m ≤ 2 ^ N` and every letter below `base`. -/
theorem avg_time_rabinKarpSearchM_le {base N : Nat} (hb : 1 < base) (S : Finset Nat)
    (hne : S.Nonempty) (hS : ∀ p ∈ S, p.Prime) (text pat : List Nat) (hpat : pat ≠ [])
    (hlen : pat.length ≤ text.length) (hN : base ^ pat.length ≤ 2 ^ N)
    (htext : ∀ c ∈ text, c < base) (hpatc : ∀ c ∈ pat, c < base) :
    avgOver S (fun p => (rabinKarpSearchM base p text pat).time)
      ≤ ((text.length + 1 - pat.length : Nat) : ℝ)
        + pat.length * ((occurrenceList text pat).length
          + ((text.length + 1 - pat.length : Nat) : ℝ) * N / S.card) := by
  rw [avg_time_rabinKarpSearchM base S hne hS text pat hpat hlen]
  have := avg_falseAlarms_le hb S hS text pat hN htext hpatc
  gcongr

/-- **The expected cost at the primes up to `T ≥ 2`**: at most
`windows + m · (occurrences + windows · N · log T / (T · log 2 − log (T + 1)))`. -/
theorem avg_time_rabinKarpSearchM_primesLE_le {base N : Nat} (hb : 1 < base) {T : Nat}
    (hT : 2 ≤ T) (text pat : List Nat) (hpat : pat ≠ []) (hlen : pat.length ≤ text.length)
    (hN : base ^ pat.length ≤ 2 ^ N) (htext : ∀ c ∈ text, c < base)
    (hpatc : ∀ c ∈ pat, c < base) :
    avgOver T.primesLE (fun p => (rabinKarpSearchM base p text pat).time)
      ≤ ((text.length + 1 - pat.length : Nat) : ℝ)
        + pat.length * ((occurrenceList text pat).length
          + ((text.length + 1 - pat.length : Nat) : ℝ) * N * Real.log T
            / (T * Real.log 2 - Real.log (T + 1))) := by
  have hne : T.primesLE.Nonempty := ⟨2, by
    simp [Nat.primesLE, Nat.primesBelow, Nat.prime_two]; omega⟩
  rw [avg_time_rabinKarpSearchM base _ hne (fun _ hp => Nat.prime_of_mem_primesLE hp) text pat
    hpat hlen]
  have := avg_falseAlarms_primesLE_le hb hT text pat hN htext hpatc
  gcongr

end AlgoDesign.Strings
