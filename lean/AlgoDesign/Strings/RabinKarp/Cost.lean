/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.RabinKarp.Search

/-!
# Rabin–Karp: cost

`rabinKarpSearchM` charges one tick per window and `m` per fingerprint hit, exactly
`(n − m + 1) + m · candidateCount` (`time_rabinKarpSearchM`); hashing the pattern and the first
window is
not charged. `polyRule` packages the polynomial fingerprint as a `WindowRule`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- `scan` with a cost: one tick per window, and `k` more when the fingerprints agree. -/
def scanM (base q high k patHash : Nat) (pat : List Nat) :
    Nat → Nat → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (List Nat)
  | _, _, [] => ⟨[], 0⟩
  | i, h, c :: t =>
      let here := if h == patHash && (c :: t).take k == pat then [i] else []
      let verify := if h == patHash then k else 0
      match (c :: t)[k]? with
      | some e =>
          let r := scanM base q high k patHash pat (i + 1) (rollHash base q high h c e) t
          ⟨here ++ r.ret, 1 + verify + r.time⟩
      | none => ⟨here, 1 + verify⟩

theorem ret_scanM (base q high k patHash : Nat) (pat : List Nat) :
    ∀ (t : List Nat) (i h : Nat),
      (scanM base q high k patHash pat i h t).ret = scan base q high k patHash pat i h t
  | [], _, _ => rfl
  | c :: t, i, h => by
      simp only [scanM, scan]
      split
      · next _ _ he => simp [he, ret_scanM base q high k patHash pat t]
      · next _ he => simp [he]

/-- The scan's cost under the rolling invariant: one tick per window, plus `k` per fingerprint
hit. -/
private theorem time_scanM (base : Nat) {q : Nat} (hq : 0 < q) {pat : List Nat} (hpat : pat ≠ []) :
    ∀ (t : List Nat) (i h : Nat), pat.length ≤ t.length →
      h = fingerprint base q (t.take pat.length) →
      (scanM base q (highPower base q pat.length) pat.length (fingerprint base q pat) pat i h
        t).time
        = (t.length + 1 - pat.length) + pat.length * candidateCount base q t pat := by
  obtain ⟨k, hk⟩ : ∃ k, pat.length = k + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (by simpa using hpat)
  intro t
  induction t with
  | nil => intro i h hl; simp only [List.length_nil] at hl; omega
  | cons c t ih =>
      intro i h hl hh
      have head : (if (h == fingerprint base q pat) = true then pat.length else 0)
          = pat.length * (if decide (fingerprint base q ((c :: t).take pat.length) =
              fingerprint base q pat) = true
              then 1 else 0) := by
        subst hh; simp only [beq_iff_eq, decide_eq_true_eq]; split <;> simp
      unfold candidateCount
      simp only [scanM]
      rcases he : (c :: t)[pat.length]? with _ | e
      · rw [hk, List.getElem?_cons_succ, List.getElem?_eq_none_iff] at he
        have hlen : (c :: t).length + 1 - pat.length = 1 := by
          simp only [List.length_cons] at hl ⊢; omega
        simp only [hlen, List.range_one, List.countP_singleton, List.drop_zero]
        rw [head]
      · rw [hk, List.getElem?_cons_succ] at he
        have hlt : k < t.length := (List.getElem?_eq_some_iff.mp he).1
        have hnext : rollHash base q (highPower base q pat.length) h c e
            = fingerprint base q (t.take pat.length) := by
          rw [hh, hk, List.take_succ_cons, List.take_add_one, he, Option.toList_some]
          have hw : (t.take k).length = k := List.length_take_of_le hlt.le
          have := rollHash_eq base hq c e (t.take k)
          rwa [hw] at this
        dsimp only
        rw [ih (i + 1) _ (by omega) hnext]
        unfold candidateCount
        have hlen : (c :: t).length + 1 - pat.length = (t.length + 1 - pat.length) + 1 := by
          simp only [List.length_cons]; omega
        rw [hlen, List.range_succ_eq_map, List.countP_cons, List.countP_map]
        simp only [Function.comp_def, List.drop_zero, List.drop_succ_cons, head]
        split <;> simp <;> ring

/-- Rabin–Karp with a cost: the two guards cost nothing, the scan what `time_scanM` says. -/
def rabinKarpSearchM (base q : Nat) (text pat : List Nat) :
    Cslib.Algorithms.Lean.TimeM ℕ (List Nat) :=
  if pat = [] then ⟨List.range (text.length + 1), 0⟩
  else if text.length < pat.length then ⟨[], 0⟩
  else
    scanM base q (highPower base q pat.length) pat.length (fingerprint base q pat) pat 0
      (fingerprint base q (text.take pat.length)) text

/-- Cost erasure: the timed search reports `rabinKarpSearch`'s positions, hence
`occurrenceList`'s. -/
theorem ret_rabinKarpSearchM (base q : Nat) (text pat : List Nat) :
    (rabinKarpSearchM base q text pat).ret = rabinKarpSearch base q text pat := by
  unfold rabinKarpSearchM rabinKarpSearch
  split
  · rfl
  · split
    · rfl
    · exact ret_scanM _ _ _ _ _ _ _ _ _

/-- **The cost, exactly**: `n − m + 1` windows, each one fingerprint comparison, and `m`
character comparisons for every window whose fingerprint equals the pattern's. -/
theorem time_rabinKarpSearchM (base : Nat) {q : Nat} (hq : 0 < q) (text pat : List Nat)
    (hpat : pat ≠ []) (hlen : pat.length ≤ text.length) :
    (rabinKarpSearchM base q text pat).time
      = (text.length + 1 - pat.length) + pat.length * candidateCount base q text pat := by
  unfold rabinKarpSearchM
  have hn : ¬ text.length < pat.length := by omega
  simp only [hpat, hn, ↓reduceIte]
  exact time_scanM base hq hpat text 0 _ hlen rfl

/-- **The worst case**: every window collides and is verified, `(n − m + 1)(m + 1)` in all. -/
theorem time_rabinKarpSearchM_le (base : Nat) {q : Nat} (hq : 0 < q) (text pat : List Nat) :
    (rabinKarpSearchM base q text pat).time
      ≤ (text.length + 1 - pat.length) * (pat.length + 1) := by
  by_cases hpat : pat = []
  · simp [rabinKarpSearchM, hpat]
  by_cases hlen : text.length < pat.length
  · simp [rabinKarpSearchM, hpat, hlen]
  rw [time_rabinKarpSearchM base hq text pat hpat (by omega)]
  have : candidateCount base q text pat ≤ text.length + 1 - pat.length := by
    unfold candidateCount
    exact (List.countP_le_length).trans (by simp)
  have := Nat.mul_le_mul_left pat.length this
  have hr : (text.length + 1 - pat.length) * (pat.length + 1)
      = pat.length * (text.length + 1 - pat.length) + (text.length + 1 - pat.length) := by ring
  omega

/-- **No spurious hit**: when no window collides with the pattern without equalling it, the
verified hits are exactly the occurrences, and the cost is `(n − m + 1) + m · occ`. -/
theorem time_rabinKarpSearchM_of_no_spurious (base : Nat) {q : Nat} (hq : 0 < q)
    (text pat : List Nat) (hpat : pat ≠ []) (hlen : pat.length ≤ text.length)
    (hns : ∀ j, j < text.length + 1 - pat.length →
      fingerprint base q ((text.drop j).take pat.length) = fingerprint base q pat →
        (text.drop j).take pat.length = pat) :
    (rabinKarpSearchM base q text pat).time
      = (text.length + 1 - pat.length) + pat.length * (occurrenceList text pat).length := by
  rw [time_rabinKarpSearchM base hq text pat hpat hlen]
  have hp1 : 0 < pat.length := List.length_pos_iff.mpr hpat
  have hnaive : (occurrenceList text pat).length =
      (List.range (text.length + 1 - pat.length)).countP
        (fun i => decide ((text.drop i).take pat.length = pat)) := by
    rw [occurrenceList_eq_windows]
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
  have hfp : candidateCount base q text pat = (List.range (text.length + 1 - pat.length)).countP
      (fun i => decide ((text.drop i).take pat.length = pat)) := by
    unfold candidateCount
    apply List.countP_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    constructor
    · intro hb
      exact decide_eq_true (hns j hj' (by simpa using hb))
    · intro hb
      have := of_decide_eq_true hb
      simp [this]
  rw [hfp, hnaive]

/-- `rollHash` with its cost: eight arithmetic operations, read off the definition. -/
def rollHashM (base q high h leaving entering : Nat) : Cslib.Algorithms.Lean.TimeM ℕ Nat :=
  ⟨rollHash base q high h leaving entering, 8⟩

/-- **The polynomial fingerprint is a window-numbering rule**, for every base and every positive
modulus. -/
def polyRule (base : Nat) {q : Nat} (hq : 0 < q) : WindowRule where
  num := fingerprint base q
  setup := highPower base q
  rollM := rollHashM base q
  ops := 8
  roll_eq c e w := rollHash_eq base hq c e w
  time_rollM_le _ _ _ _ := le_rfl

end AlgoDesign.Strings
