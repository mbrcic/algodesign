/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import AlgoDesign.Strings.RabinKarp.Spec

/-!
# Rabin–Karp: the search

The search the Rust `rabin_karp::search` runs, for every base and every positive modulus: the book
traces base `10` modulo `13`, the library draws a random prime with base `256`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- `base ^ (k - 1)` modulo `q`, CLRS's `h`: the weight of a width-`k` window's leftmost
character, one multiplication per position after the first, from an unreduced `1`. -/
def highPower (base q k : Nat) : Nat :=
  (fun h => h * base % q)^[k - 1] 1

/-- **One slide of the window**: drop the `leaving` character's weight, shift one digit, and add
the `entering` character, modulo `q`. Adding `q` first keeps the `Nat` subtraction exact. -/
def rollHash (base q high h leaving entering : Nat) : Nat :=
  ((h + q - leaving * high % q) % q * base + entering) % q

/-- The scan at position `i` on the rest of the text `c :: t`, with `h` the value carried for the
window there: report it if its value and its characters equal the pattern's, then roll on. -/
def scan (base q high k patHash : Nat) (pat : List Nat) : Nat → Nat → List Nat → List Nat
  | _, _, [] => []
  | i, h, c :: t =>
      let here := if h == patHash && (c :: t).take k == pat then [i] else []
      match (c :: t)[k]? with
      | some e => here ++ scan base q high k patHash pat (i + 1) (rollHash base q high h c e) t
      | none => here

/-- Las Vegas Rabin–Karp with a rolling fingerprint. The empty pattern occurs at every shift
`0 … text.length`, and a pattern longer than the text nowhere. -/
def rabinKarpSearch (base q : Nat) (text pat : List Nat) : List Nat :=
  if pat = [] then List.range (text.length + 1)
  else if text.length < pat.length then []
  else
    scan base q (highPower base q pat.length) pat.length (fingerprint base q pat) pat 0
      (fingerprint base q (text.take pat.length)) text

/-! ## The rolling step, modulo `q` -/

/-- Horner's rule without the reductions, in `ZMod q`: the value a list denotes there. -/
private def val (base q : Nat) (w : List Nat) : ZMod q :=
  w.foldl (fun (acc : ZMod q) (c : Nat) => acc * base + c) 0

/-- Reducing at every step of Horner's rule changes nothing modulo `q`. -/
private theorem foldl_cast (base q : Nat) (w : List Nat) (acc : Nat) :
    ((w.foldl (fun acc c => (acc * base + c) % q) acc : Nat) : ZMod q)
      = w.foldl (fun (acc : ZMod q) (c : Nat) => acc * base + c) (acc : ZMod q) := by
  induction w generalizing acc with
  | nil => rfl
  | cons c w ih => simp [List.foldl_cons, ih, ZMod.natCast_mod]

private theorem fingerprint_cast (base q : Nat) (w : List Nat) :
    ((fingerprint base q w : Nat) : ZMod q) = val base q w := by
  simpa [fingerprint, val] using foldl_cast base q w 0

/-- Horner's rule from a running value `a` is `a` shifted past the whole list, plus the list. -/
private theorem foldl_shift (base q : Nat) (w : List Nat) (a : ZMod q) :
    w.foldl (fun (acc : ZMod q) (c : Nat) => acc * base + c) a
      = a * (base : ZMod q) ^ w.length
        + w.foldl (fun (acc : ZMod q) (c : Nat) => acc * base + c) 0 := by
  induction w generalizing a with
  | nil => simp
  | cons c w ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, ih (0 * base + c)]
      ring

/-- The leading character of a window carries weight `base ^ (length of the rest)`. -/
private theorem val_cons (base q c : Nat) (w : List Nat) :
    val base q (c :: w) = (c : ZMod q) * (base : ZMod q) ^ w.length + val base q w := by
  simp only [val, List.foldl_cons]
  rw [foldl_shift]
  ring

private theorem val_append_singleton (base q e : Nat) (w : List Nat) :
    val base q (w ++ [e]) = val base q w * base + e := by
  simp [val, List.foldl_append]

/-- `highPower` is `base ^ (k - 1)` modulo `q`, whatever the unreduced starting `1` does. -/
theorem highPower_cast (base q k : Nat) :
    ((highPower base q k : Nat) : ZMod q) = (base : ZMod q) ^ (k - 1) := by
  unfold highPower
  generalize k - 1 = j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ZMod.natCast_mod, Nat.cast_mul, ih, pow_succ]

/-- A reduced value is below the modulus: `fingerprint` never returns `q` or more. -/
theorem fingerprint_lt {q : Nat} (hq : 0 < q) (base : Nat) (w : List Nat) :
    fingerprint base q w < q := by
  suffices ∀ acc, acc < q → w.foldl (fun acc c => (acc * base + c) % q) acc < q from this 0 hq
  induction w with
  | nil => intro acc h; exact h
  | cons c w ih => intro acc _; exact ih _ (Nat.mod_lt _ hq)

/-- **The rolling lemma.** Rolling the value of `c :: w` across, `c` leaving and `e` entering,
gives exactly the fingerprint of `w ++ [e]`: equal, not just congruent, as both are reduced below
`q`. -/
theorem rollHash_eq (base : Nat) {q : Nat} (hq : 0 < q) (c e : Nat) (w : List Nat) :
    rollHash base q (highPower base q (w.length + 1)) (fingerprint base q (c :: w)) c e
      = fingerprint base q (w ++ [e]) := by
  have hlt :
      rollHash base q (highPower base q (w.length + 1)) (fingerprint base q (c :: w)) c e < q :=
    Nat.mod_lt _ hq
  have hle : c * highPower base q (w.length + 1) % q ≤ fingerprint base q (c :: w) + q :=
    (Nat.mod_lt _ hq).le.trans (Nat.le_add_left _ _)
  rw [← Nat.mod_eq_of_lt hlt, ← Nat.mod_eq_of_lt (fingerprint_lt hq base (w ++ [e])),
    ← ZMod.natCast_eq_natCast_iff']
  unfold rollHash
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_sub hle,
    Nat.cast_add, ZMod.natCast_self, ZMod.natCast_mod, Nat.cast_mul, fingerprint_cast,
    fingerprint_cast,
    highPower_cast, val_cons, val_append_singleton, Nat.add_sub_cancel]
  ring

/-! ## The search -/

/-- No window of `t` of width `pat.length` equals `pat` once `t` is shorter than `pat`. -/
private theorem filter_short (t pat : List Nat) (h : t.length < pat.length) (l : List Nat) :
    l.filter (fun j => ((t.drop j).take pat.length = pat : Bool)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro j _ hj
  have := congrArg List.length (of_decide_eq_true hj)
  simp only [List.length_take, List.length_drop] at this
  omega

/-- **The scan under the rolling invariant.** Started at position `i` on the rest of the text `t`
with `h` the fingerprint of the window there, the scan reports `i` plus every offset at which `pat`
occurs in `t`. -/
theorem scan_eq (base : Nat) {q : Nat} (hq : 0 < q) {pat : List Nat} (hpat : pat ≠ []) :
    ∀ (t : List Nat) (i h : Nat), h = fingerprint base q (t.take pat.length) →
      scan base q (highPower base q pat.length) pat.length (fingerprint base q pat) pat i h t
        = ((List.range (t.length + 1)).filter
            fun j => ((t.drop j).take pat.length = pat : Bool)).map (i + ·) := by
  obtain ⟨k, hk⟩ : ∃ k, pat.length = k + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (by simpa using hpat)
  intro t
  induction t with
  | nil =>
      intro i h _
      simp [scan, hpat]
  | cons c t ih =>
      intro i h hh
      have here : (h == fingerprint base q pat && (c :: t).take pat.length == pat)
          = decide ((c :: t).take pat.length = pat) := by
        by_cases hw : (c :: t).take pat.length = pat
        · simp [hh, hw]
        · simp [hw]
      have rhs : ((List.range ((c :: t).length + 1)).filter
            fun j => (((c :: t).drop j).take pat.length = pat : Bool)).map (i + ·)
          = (if (c :: t).take pat.length = pat then [i] else [])
            ++ ((List.range (t.length + 1)).filter
                fun j => ((t.drop j).take pat.length = pat : Bool)).map ((i + 1) + ·) := by
        rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
        split <;> simp_all [List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]
      rw [rhs]
      simp only [scan, here]
      rcases he : (c :: t)[pat.length]? with _ | e
      · rw [hk, List.getElem?_cons_succ, List.getElem?_eq_none_iff] at he
        rw [filter_short t pat (by omega)]
        by_cases hw : (c :: t).take pat.length = pat <;> simp [hw]
      · dsimp only
        rw [ih (i + 1)]
        · by_cases hw : (c :: t).take pat.length = pat <;> simp [hw]
        · rw [hk, List.getElem?_cons_succ] at he
          have hlen : k < t.length := (List.getElem?_eq_some_iff.mp he).1
          rw [hh, hk, List.take_succ_cons, List.take_add_one, he, Option.toList_some]
          have hw : (t.take k).length = k := List.length_take_of_le hlen.le
          have := rollHash_eq base hq c e (t.take k)
          rwa [hw] at this

/-- **The specification.** The rolling search reports exactly the positions at which `pat`
occurs, for every base and every positive modulus. -/
theorem rabinKarpSearch_eq_occurrenceList (base : Nat) {q : Nat} (hq : 0 < q)
    (text pat : List Nat) : rabinKarpSearch base q text pat = occurrenceList text pat := by
  rw [occurrenceList_eq_windows]
  unfold rabinKarpSearch
  by_cases hpat : pat = []
  · subst hpat
    simp
  by_cases hshort : text.length < pat.length
  · rw [ite_eq_right hpat, ite_eq_left hshort]
    exact (filter_short text pat hshort _).symm
  · rw [ite_eq_right hpat, ite_eq_right hshort, scan_eq base hq hpat text 0 _ rfl]
    simp

/-- **The occurrences come in increasing order**, Rabin–Karp's own extra beyond the promise. -/
theorem rabinKarpSearch_pairwise_lt (base : Nat) {q : Nat} (hq : 0 < q) (text pat : List Nat) :
    (rabinKarpSearch base q text pat).Pairwise (· < ·) := by
  rw [rabinKarpSearch_eq_occurrenceList base hq]
  exact List.pairwise_lt_range.filter _

/-! ## The scan's running state -/

namespace RabinKarp

/-- The scan's first state: at position `0`, carrying the first window's number, nothing found. -/
def Scan.first (base modulus : Nat) (text pattern : List Nat) : Scan where
  text := text
  pattern := pattern
  base := base
  modulus := modulus
  start := 0
  rest := text
  number := fingerprint base modulus (text.take pattern.length)
  found := []
  rest_eq := (List.drop_zero).symm
  start_le := Nat.zero_le _

/-- **The scan one window on**: the window at the front of `c :: t` is reported if its letters
equal the pattern's, the cursor moves past `c`, and the state carries `number` for the next
window. -/
def Scan.next (s : Scan) (number c : Nat) (t : List Nat) (hr : s.rest = c :: t) : Scan where
  text := s.text
  pattern := s.pattern
  base := s.base
  modulus := s.modulus
  start := s.start + 1
  rest := t
  number := number
  found := s.found ++ if (c :: t).take s.pattern.length = s.pattern then [s.start] else []
  rest_eq := by
    have h := congrArg List.tail (hr.symm.trans s.rest_eq)
    simpa [List.tail_drop] using h
  start_le := by
    have h := congrArg List.length (hr.symm.trans s.rest_eq)
    simp only [List.length_cons, List.length_drop] at h
    omega

/-- **The scan, run on from a state**: what `scan` reports from the state's cursor to the end of
the text, rolling the number it carries. -/
def Scan.run (s : Scan) : List Nat :=
  scan s.base s.modulus (highPower s.base s.modulus s.pattern.length) s.pattern.length
    (fingerprint s.base s.modulus s.pattern) s.pattern s.start s.number s.rest

/-- **One slide's update of the number**, the library's: drop the leaving letter `c`'s weight,
shift one digit, add the entering letter `e` (`rollHash`). -/
def Scan.roll (s : Scan) (c e : Nat) : Nat :=
  rollHash s.base s.modulus (highPower s.base s.modulus s.pattern.length) s.number c e

/-- **Line 3's check, on the scan itself.** Whatever number it carries, every position the scan
reports from `i` on the rest of the text `t` is at or after `i`, and its window equals the pattern,
letter by letter. -/
theorem mem_scan {base q high k patHash : Nat} {pat : List Nat} :
    ∀ {t : List Nat} {i h j : Nat}, j ∈ scan base q high k patHash pat i h t →
      i ≤ j ∧ (t.drop (j - i)).take k = pat
  | [], _, _, _, hj => by simp [scan] at hj
  | c :: t, i, h, j, hj => by
      have hhere : j ∈ (if (h == patHash && (c :: t).take k == pat) = true then [i] else []) →
          i ≤ j ∧ ((c :: t).drop (j - i)).take k = pat := by
        intro hmem
        split at hmem
        · next hc =>
          rw [List.mem_singleton] at hmem
          subst hmem
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          simpa using hc.2
        · simp at hmem
      have hnext : ∀ h', j ∈ scan base q high k patHash pat (i + 1) h' t →
          i ≤ j ∧ ((c :: t).drop (j - i)).take k = pat := by
        intro h' hmem
        obtain ⟨hle, hw⟩ := mem_scan hmem
        refine ⟨by omega, ?_⟩
        rw [show j - i = (j - (i + 1)) + 1 by omega, List.drop_succ_cons]
        exact hw
      simp only [scan] at hj
      split at hj
      · rcases List.mem_append.1 hj with hmem | hmem
        · exact hhere hmem
        · exact hnext _ hmem
      · exact hhere hj

/-- **Every candidate is checked letter by letter** (box line 3): every position the scan reports,
from any state and whatever number it carries, is at or after the cursor and has its window equal
to the pattern. -/
theorem mem_run {s : Scan} {j : Nat} (hj : j ∈ s.run) :
    s.start ≤ j ∧ (s.text.drop j).take s.pattern.length = s.pattern := by
  obtain ⟨hle, hw⟩ := mem_scan hj
  refine ⟨hle, ?_⟩
  rw [s.rest_eq, List.drop_drop, show s.start + (j - s.start) = j by omega] at hw
  exact hw

/-- The scan's first state keeps `Valid`: it carries the first window's number and has found
nothing before position `0`. -/
theorem valid_first (base modulus : Nat) (text pattern : List Nat) :
    Valid (Scan.first base modulus text pattern) :=
  ⟨rfl, by simp [FoundSoFarExact, Scan.first]⟩

/-- The occurrences before `k` are the windows equal to the pattern among the first `k`
positions. -/
private theorem filter_range_filter_lt (P : Nat → Bool) :
    ∀ N k, k ≤ N →
      ((List.range N).filter P).filter (fun i => decide (i < k)) = (List.range k).filter P
  | 0, k, hk => by simp [Nat.le_zero.1 hk]
  | N + 1, k, hk => by
      rcases Nat.lt_or_eq_of_le hk with hk | rfl
      · rw [List.range_succ, List.filter_append, List.filter_append,
          filter_range_filter_lt P N k (by omega)]
        have hN : ¬ N < k := by omega
        cases P N <;> simp [hN]
      · rw [List.filter_eq_self.2]
        intro i hi
        simpa using List.mem_range.1 (List.mem_of_mem_filter hi)

/-- **One slide keeps `NumberMatchesWindow`** (box line 2). If a letter `e` enters behind the
window at the front of `c :: t`, the rolled number is the next window's (`rollHash_eq`). -/
theorem numberMatchesWindow_slide {s : Scan} (hq : 0 < s.modulus) (hpat : s.pattern ≠ [])
    {c e : Nat} {t : List Nat} (hr : s.rest = c :: t) (he : (c :: t)[s.pattern.length]? = some e)
    (hnum : NumberMatchesWindow s) : NumberMatchesWindow (s.next (s.roll c e) c t hr) := by
  obtain ⟨k, hk⟩ : ∃ k, s.pattern.length = k + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (by simpa using hpat)
  rw [hk, List.getElem?_cons_succ] at he
  have hlen : k < t.length := (List.getElem?_eq_some_iff.mp he).1
  unfold NumberMatchesWindow at hnum ⊢
  simp only [Scan.next, Scan.roll]
  rw [hnum, hr, hk, List.take_succ_cons, List.take_add_one, he, Option.toList_some]
  have hw : (t.take k).length = k := List.length_take_of_le hlen.le
  have := rollHash_eq s.base hq c e (t.take k)
  rwa [hw] at this

/-- **One slide keeps `RabinKarp.Valid`.** The number stays the window's
(`numberMatchesWindow_slide`), and the found list gains the cursor exactly when the window there
equals the pattern. -/
theorem valid_roll {s : Scan} (hq : 0 < s.modulus) (hpat : s.pattern ≠ []) {c e : Nat}
    {t : List Nat} (hr : s.rest = c :: t) (he : (c :: t)[s.pattern.length]? = some e)
    (hv : Valid s) : Valid (s.next (s.roll c e) c t hr) := by
  obtain ⟨hnum, hfound⟩ := hv
  refine ⟨numberMatchesWindow_slide hq hpat hr he hnum, ?_⟩
  change s.found ++ (if (c :: t).take s.pattern.length = s.pattern then [s.start] else []) =
      (occurrenceList s.text s.pattern).filter (fun i => decide (i < s.start + 1))
  unfold FoundSoFarExact at hfound
  have hs : s.start < s.text.length := by
    have h := congrArg List.length (hr.symm.trans s.rest_eq)
    simp only [List.length_cons, List.length_drop] at h
    omega
  rw [occurrenceList_eq_windows] at hfound ⊢
  rw [hfound, filter_range_filter_lt _ _ _ (by omega),
    filter_range_filter_lt _ _ _ (by omega), List.range_succ, List.filter_append]
  have hd : s.text.drop s.start = c :: t := (hr.symm.trans s.rest_eq).symm
  by_cases hw : (c :: t).take s.pattern.length = s.pattern <;> simp [hd, hw]

/-- **`NumberMatchesWindow` gives the scan's answer**: started at a state whose number is its
window's, the scan reports the cursor plus every offset at which the pattern occurs in the rest
(`scan_eq`). -/
theorem scan_eq_of_valid {s : Scan} (hq : 0 < s.modulus) (hpat : s.pattern ≠ [])
    (hv : NumberMatchesWindow s) :
    s.run = ((List.range (s.rest.length + 1)).filter
        fun j => ((s.rest.drop j).take s.pattern.length = s.pattern : Bool)).map (s.start + ·) :=
  scan_eq s.base hq hpat s.rest s.start s.number hv

/-- **`RabinKarp.Valid` finishes the answer**: from a valid state, what has been found and what the
scan reports from here on are every occurrence, in increasing order. -/
theorem found_append_run {s : Scan} (hq : 0 < s.modulus) (hpat : s.pattern ≠ [])
    (hv : Valid s) : s.found ++ s.run = occurrenceList s.text s.pattern := by
  rw [scan_eq_of_valid hq hpat hv.1, hv.2, occurrenceList_eq_windows]
  rw [filter_range_filter_lt _ _ _ (by have := s.start_le; omega), s.rest_eq, List.length_drop,
    show s.text.length + 1 = s.start + (s.text.length - s.start + 1) by
      have := s.start_le; omega,
    @List.range_add s.start (s.text.length - s.start + 1), List.filter_append, List.filter_map]
  congr 2
  exact List.filter_congr fun j _ => by simp [List.drop_drop]

/-- **The scan is the slide repeated.** From a state whose number is its window's, the scan reports
the cursor if the window there equals the pattern, then runs on from the next state, its number
rolled (`Scan.roll`). -/
theorem run_roll {s : Scan} {c e : Nat} {t : List Nat} (hr : s.rest = c :: t)
    (he : (c :: t)[s.pattern.length]? = some e) (hv : Valid s) :
    s.run = (if (c :: t).take s.pattern.length = s.pattern then [s.start] else []) ++
      (s.next (s.roll c e) c t hr).run := by
  have hnum : s.number = fingerprint s.base s.modulus ((c :: t).take s.pattern.length) := by
    rw [← hr]; exact hv.1
  unfold Scan.run
  rw [hr]
  simp only [scan, he]
  congr 1
  by_cases hw : (c :: t).take s.pattern.length = s.pattern
  · simp [hw, hnum]
  · simp [hw]

/-- **A search with a pattern is the scan run from its first state.** -/
theorem rabinKarpSearch_eq_run (base q : Nat) (text pat : List Nat) (hpat : pat ≠ []) :
    rabinKarpSearch base q text pat = (Scan.first base q text pat).run := by
  unfold rabinKarpSearch
  simp only [hpat, ↓reduceIte]
  split
  · next hshort =>
    symm
    refine List.eq_nil_iff_forall_not_mem.2 fun j hj => ?_
    have := congrArg List.length (mem_run hj).2
    simp only [Scan.first, List.length_take, List.length_drop] at this
    omega
  · rfl

end RabinKarp

/-- **A window-numbering rule**, box invariants 1 and 2: `num` numbers a window, `setup k` is
computed once per width before the scan, and `rollM` slides to the next window in at most `ops`
steps. -/
structure WindowRule where
  /-- The number of a window. -/
  num : List Nat → Nat
  /-- What is computed once per width, before the scan. -/
  setup : Nat → Nat
  /-- One slide, with its cost: setup value, previous number, leaving letter, entering letter. -/
  rollM : Nat → Nat → Nat → Nat → Cslib.Algorithms.Lean.TimeM ℕ Nat
  /-- The bound on one slide's cost, the same for every width. -/
  ops : Nat
  /-- The update gives the next window's number: `c` leaves `c :: w`, `e` enters. -/
  roll_eq : ∀ (c e : Nat) (w : List Nat),
    (rollM (setup (w.length + 1)) (num (c :: w)) c e).ret = num (w ++ [e])
  /-- One slide costs at most `ops`, whatever the width and the window. -/
  time_rollM_le : ∀ s h c e, (rollM s h c e).time ≤ ops

/-- Box invariant 1: equal windows get equal numbers. -/
theorem WindowRule.num_congr (R : WindowRule) {u v : List Nat} (h : u = v) : R.num u = R.num v :=
  congrArg R.num h

end AlgoDesign.Strings
