/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RabinKarp.Search
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Chebyshev

/-!
# Rabin–Karp's box assumption: under a random prime, different windows rarely get equal numbers

Sources: Karp and Rabin (1987); Motwani and Raghavan, *Randomized Algorithms*, §7.6. Two different
windows are two different numbers below `base ^ k`; they collide at a prime `p` exactly when `p`
divides their difference, and a nonzero number below `2 ^ N` has fewer than `N` prime divisors.
-/

@[expose] public section

namespace AlgoDesign.Strings

open scoped Nat.Prime

/-- Box assumption, a large prime modulus picked at random: then different windows rarely get equal
numbers. Over the keys in `keys`, any two different windows of width `k` over letters below `base`
get equal numbers under at most `bound` keys. -/
def RarelyEqual (num : Nat → List Nat → Nat) (keys : Finset Nat) (base k bound : Nat) : Prop :=
  ∀ u v : List Nat, u.length = k → v.length = k → (∀ c ∈ u, c < base) → (∀ c ∈ v, c < base) →
    u ≠ v → (keys.filter fun key => num key u = num key v).card ≤ bound

/-- The number a window stands for: its letters as digits in radix `base`, most significant first,
unreduced. -/
def windowNum (base : Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc c => acc * base + c) 0

private theorem foldl_mod (base q : Nat) (w : List Nat) (acc : Nat) :
    w.foldl (fun acc c => (acc * base + c) % q) (acc % q)
      = w.foldl (fun acc c => acc * base + c) acc % q := by
  induction w generalizing acc with
  | nil => rfl
  | cons c w ih =>
      simp only [List.foldl_cons]
      rw [← ih]
      congr 1
      simp [Nat.add_mod, Nat.mul_mod]

/-- **The fingerprint is the window's number, reduced modulo `q`.** -/
theorem fingerprint_eq_mod (base q : Nat) (w : List Nat) :
    fingerprint base q w = windowNum base w % q := by
  simpa [fingerprint, windowNum] using foldl_mod base q w 0

/-- `[3, 1, 4]` in base `10` is `314`. -/
example : windowNum 10 [3, 1, 4] = 314 ∧ fingerprint 10 13 [3, 1, 4] = 314 % 13 := by decide

/-- Read most significant first, a window is `Nat.ofDigits` of its reverse. -/
theorem windowNum_eq_ofDigits (base : Nat) (w : List Nat) :
    windowNum base w = Nat.ofDigits base w.reverse := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w c ih =>
      simp only [windowNum, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, Nat.ofDigits_cons] at ih ⊢
      rw [ih]
      ring

/-- A window of width `k` over the letters below `base` is a number below `base ^ k`. -/
theorem windowNum_lt {base : Nat} (hb : 1 < base) {w : List Nat} (hw : ∀ c ∈ w, c < base) :
    windowNum base w < base ^ w.length := by
  rw [windowNum_eq_ofDigits, ← List.length_reverse]
  exact Nat.ofDigits_lt_base_pow_length hb (by simpa using hw)

/-- Different windows of one width, over the letters below `base`, are different numbers. -/
theorem windowNum_inj {base : Nat} (hb : 1 < base) {u v : List Nat} (hlen : u.length = v.length)
    (hu : ∀ c ∈ u, c < base) (hv : ∀ c ∈ v, c < base) (h : windowNum base u = windowNum base v) :
    u = v := by
  rw [windowNum_eq_ofDigits, windowNum_eq_ofDigits] at h
  exact List.reverse_injective
    (Nat.ofDigits_inj_of_len_eq hb (by simpa using hlen) (by simpa using hu) (by simpa using hv) h)

/-- A nonzero number below `2 ^ N` has fewer than `N` distinct prime factors. -/
theorem card_primeFactors_lt {d N : Nat} (hd : d ≠ 0) (hdN : d < 2 ^ N) :
    d.primeFactors.card < N := by
  have hprod : 2 ^ d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hle : ∏ p ∈ d.primeFactors, p ≤ d :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.prod_primeFactors_dvd d)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt (hprod.trans hle) hdN)

/-- **The counting form of the box assumption.** With `base ^ k ≤ 2 ^ N`, of any set of primes
at most `N` give two different windows of width `k` equal fingerprints. -/
theorem card_colliding_le {base k N : Nat} (hb : 1 < base) (hN : base ^ k ≤ 2 ^ N)
    (keys : Finset Nat) (hkeys : ∀ p ∈ keys, p.Prime) {u v : List Nat} (hu : u.length = k)
    (hv : v.length = k) (hcu : ∀ c ∈ u, c < base) (hcv : ∀ c ∈ v, c < base) (hne : u ≠ v) :
    (keys.filter fun p => fingerprint base p u = fingerprint base p v).card ≤ N := by
  set a := windowNum base u
  set b := windowNum base v
  have ha : a < 2 ^ N := (hu ▸ windowNum_lt hb hcu).trans_le hN
  have hb' : b < 2 ^ N := (hv ▸ windowNum_lt hb hcv).trans_le hN
  have hab : a ≠ b := fun h => hne (windowNum_inj hb (hu.trans hv.symm) hcu hcv h)
  have hd : (a - b) + (b - a) ≠ 0 := by omega
  have hdN : (a - b) + (b - a) < 2 ^ N := by omega
  have hsub : (keys.filter fun p => fingerprint base p u = fingerprint base p v)
      ⊆ ((a - b) + (b - a)).primeFactors := by
    intro p hp
    obtain ⟨hpk, hpe⟩ := Finset.mem_filter.mp hp
    rw [fingerprint_eq_mod, fingerprint_eq_mod] at hpe
    refine Nat.mem_primeFactors.mpr ⟨hkeys p hpk, ?_, hd⟩
    exact Nat.dvd_add (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hpe))
      (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hpe.symm))
  exact ((Finset.card_le_card hsub).trans (card_primeFactors_lt hd hdN).le)

/-- **The box assumption for the polynomial fingerprint**: `RarelyEqual` with bound `N` whenever
`base ^ k ≤ 2 ^ N`. -/
theorem rarelyEqual_fingerprint {base k N : Nat} (hb : 1 < base) (hN : base ^ k ≤ 2 ^ N)
    (keys : Finset Nat) (hkeys : ∀ p ∈ keys, p.Prime) :
    RarelyEqual (fingerprint base) keys base k N :=
  fun _ _ hu hv hcu hcv hne => card_colliding_le hb hN keys hkeys hu hv hcu hcv hne

/-- The same at the primes below `T`, the set the chapter's prime is drawn from. -/
theorem rarelyEqual_fingerprint_primesBelow {base k N : Nat} (hb : 1 < base) (hN : base ^ k ≤ 2 ^ N)
    (T : Nat) : RarelyEqual (fingerprint base) T.primesBelow base k N :=
  rarelyEqual_fingerprint hb hN _ fun _ hp => Nat.prime_of_mem_primesBelow hp

/-- `T + 1 < 2 ^ T` from `T = 2` on. -/
private theorem succ_lt_two_pow {T : Nat} (hT : 2 ≤ T) : T + 1 < 2 ^ T := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- Chebyshev's lower bound: for `T ≥ 2`, `T · log 2 − log (T + 1)` is positive and at most
`π(T) · log T`. -/
theorem primeCounting_mul_log_ge {T : Nat} (hT : 2 ≤ T) :
    0 < (T : ℝ) * Real.log 2 - Real.log (T + 1)
      ∧ (T : ℝ) * Real.log 2 - Real.log (T + 1) ≤ (π T : ℝ) * Real.log T := by
  refine ⟨?_, (Chebyshev.psi_ge T).trans (Chebyshev.psi_le_primeCounting_mul_log T)⟩
  have h1 : ((T + 1 : Nat) : ℝ) < ((2 ^ T : Nat) : ℝ) := by exact_mod_cast succ_lt_two_pow hT
  have h2 : Real.log (T + 1) < Real.log ((2 : ℝ) ^ T) := by
    apply Real.log_lt_log (by positivity)
    simpa using h1
  rw [Real.log_pow] at h2
  linarith

/-- **The fraction form of the box assumption.** With the modulus drawn uniformly from the primes up
to `T ≥ 2`, two different windows collide with probability at most
`N · log T / (T · log 2 − log (T + 1))`. -/
theorem collision_fraction_le {base k N : Nat} (hb : 1 < base) (hN : base ^ k ≤ 2 ^ N)
    {T : Nat} (hT : 2 ≤ T) {u v : List Nat} (hu : u.length = k) (hv : v.length = k)
    (hcu : ∀ c ∈ u, c < base) (hcv : ∀ c ∈ v, c < base) (hne : u ≠ v) :
    ((T.primesLE.filter fun p => fingerprint base p u = fingerprint base p v).card : ℝ) / (π T : ℝ)
      ≤ N * Real.log T / (T * Real.log 2 - Real.log (T + 1)) := by
  have hcount :
      ((T.primesLE.filter fun p => fingerprint base p u = fingerprint base p v).card : ℝ) ≤ N := by
    exact_mod_cast card_colliding_le hb hN _ (fun _ hp => Nat.prime_of_mem_primesLE hp)
      hu hv hcu hcv hne
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨hL, hpi⟩ := primeCounting_mul_log_ge hT
  have hpipos : (0 : ℝ) < π T := by
    have := hL.trans_le hpi
    exact pos_of_mul_pos_left this hlogT.le
  rw [div_le_div_iff₀ hpipos hL]
  calc ((T.primesLE.filter fun p => fingerprint base p u = fingerprint base p v).card : ℝ)
        * ((T : ℝ) * Real.log 2 - Real.log (T + 1))
      ≤ N * ((π T : ℝ) * Real.log T) :=
        mul_le_mul hcount hpi hL.le (Nat.cast_nonneg _)
    _ = N * Real.log T * π T := by ring

end AlgoDesign.Strings
