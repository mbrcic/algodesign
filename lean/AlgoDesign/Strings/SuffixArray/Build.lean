/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.SuffixArray.Basic

/-!
# Suffix array: construction by prefix doubling

Round `k` knows the order of the suffixes on their first `2 ^ k` characters (`Doubling.Valid`),
and round `k + 1` reads that order off as a pair of tags and sorts the pairs. The `O(n log n)`
running time is not proved: `refineTags` is quadratic as written.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-! ## Prefix doubling's running state -/

namespace Doubling

/-- After each round: one tag per position of the text. -/
def OneTagPerPosition (t : List Nat) (tag : List Nat) : Prop := tag.length = t.length

/-- After round `k`: the tags order the suffixes by their first `2 ^ k` characters, and nothing
finer. -/
def TagsOrderPrefixes (t : List Nat) (tag : List Nat) (k : Nat) : Prop :=
  ∀ i (hi : i < tag.length) j (hj : j < tag.length),
    tag[i] ≤ tag[j] ↔ (suffix t i).take (2 ^ k) ≤ (suffix t j).take (2 ^ k)

/-- **The doubling invariant**, the running state of prefix doubling. -/
def Valid (t : List Nat) (tag : List Nat) (k : Nat) : Prop :=
  OneTagPerPosition t tag ∧ TagsOrderPrefixes t tag k

instance (t tag : List Nat) : Decidable (OneTagPerPosition t tag) :=
  by unfold OneTagPerPosition; infer_instance

instance (t tag : List Nat) (k : Nat) : Decidable (TagsOrderPrefixes t tag k) :=
  by unfold TagsOrderPrefixes; infer_instance

instance decidableValid (t tag : List Nat) (k : Nat) : Decidable (Valid t tag k) :=
  by unfold Valid; infer_instance

end Doubling

/-- Round 0: tag each position by its own character. -/
def initialTags (t : List Nat) : List Nat := t

/-- Comparing one-character prefixes is comparing their characters. -/
private theorem singleton_le_singleton {a b : Nat} : [a] ≤ [b] ↔ a ≤ b := by
  change ¬ ([b] < [a]) ↔ a ≤ b
  rw [List.cons_lt_cons_iff]
  simp

/-- `Doubling.Valid`'s order piece, read through `!` at the text's positions. -/
theorem Doubling.Valid.le_iff {t tag : List Nat} {k : Nat} (h : Doubling.Valid t tag k)
    {i j : Nat} (hi : i < t.length) (hj : j < t.length) :
    tag[i]! ≤ tag[j]! ↔ (suffix t i).take (2 ^ k) ≤ (suffix t j).take (2 ^ k) := by
  have hi' : i < tag.length := h.1 ▸ hi
  have hj' : j < tag.length := h.1 ▸ hj
  rw [getElem!_pos tag i hi', getElem!_pos tag j hj']
  exact h.2 i hi' j hj'

/-- `Doubling.Valid` from its order piece read through `!`, and one tag per position. -/
theorem Doubling.valid_of_le_iff {t tag : List Nat} {k : Nat} (hlen : tag.length = t.length)
    (h : ∀ i, i < t.length → ∀ j, j < t.length →
      (tag[i]! ≤ tag[j]! ↔ (suffix t i).take (2 ^ k) ≤ (suffix t j).take (2 ^ k))) :
    Doubling.Valid t tag k := by
  refine ⟨hlen, fun i hi j hj => ?_⟩
  have := h i (hlen ▸ hi) j (hlen ▸ hj)
  rwa [getElem!_pos tag i hi, getElem!_pos tag j hj] at this

/-- **Base.** The invariant holds before any doubling: one character is `2 ^ 0` characters. -/
theorem Doubling.valid_initial (t : List Nat) :
    Doubling.Valid t (initialTags t) 0 := by
  refine Doubling.valid_of_le_iff rfl fun i hi j hj => ?_
  rw [initialTags, getElem!_pos t i hi, getElem!_pos t j hj]
  simp only [suffix, Nat.pow_zero, List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj,
    List.take_succ_cons, List.take_zero]
  exact singleton_le_singleton.symm

/-- **Conclusion.** Once the prefix a tag covers is the whole text, the invariant is suffix
order. -/
theorem valid_of_doubling (t : List Nat) (tag sa : List Nat) (k : Nat)
    (hk : t.length ≤ 2 ^ k) (htag : Doubling.Valid t tag k)
    (hperm : sa.Perm (List.range t.length))
    (hsorted : (sa.map (fun p => tag[p]!)).Pairwise (· ≤ ·)) :
    SuffixArray.Valid ⟨t, sa⟩ := by
  refine ⟨hperm, ?_⟩
  unfold SuffixArray.SuffixesSorted
  rw [List.pairwise_map] at hsorted ⊢
  refine hsorted.imp_of_mem ?_
  intro a b ha hb h
  have ha' : a < t.length := List.mem_range.mp (hperm.mem_iff.mp ha)
  have hb' : b < t.length := List.mem_range.mp (hperm.mem_iff.mp hb)
  have hta : (suffix t a).length ≤ 2 ^ k := by
    simp only [suffix, List.length_drop]; omega
  have htb : (suffix t b).length ≤ 2 ^ k := by
    simp only [suffix, List.length_drop]; omega
  have := (htag.le_iff ha' hb').mp h
  rwa [List.take_of_length_le hta, List.take_of_length_le htb] at this

/-- Round `k`'s key for position `i`: its own tag, paired with the tag `2 ^ k` further on,
shifted by one so that `0` means "nothing there". -/
def pairKey (t : List Nat) (tag : List Nat) (k : Nat) (i : Nat) : Nat × Nat :=
  (tag[i]!, if i + 2 ^ k < t.length then tag[i + 2 ^ k]! + 1 else 0)

/-- One doubling round: re-tag each position by how many positions carry a strictly smaller pair
key (`Prod.lexLt`). The Rust computes the same tagging with a counting sort. -/
def refineTags (t : List Nat) (tag : List Nat) (k : Nat) : List Nat :=
  (List.range t.length).map fun i =>
    ((List.range t.length).filter
      (fun j => decide ((pairKey t tag k j).lexLt (pairKey t tag k i)))).length

/-- Lexicographic order on pairs is irreflexive. -/
private theorem lexLt_irrefl (a : Nat × Nat) : ¬ a.lexLt a := by
  simp only [Prod.lexLt_def]
  omega

/-- Lexicographic order on pairs is transitive. -/
private theorem lexLt_trans {a b c : Nat × Nat} (h₁ : a.lexLt b) (h₂ : b.lexLt c) : a.lexLt c := by
  simp only [Prod.lexLt_def] at *
  omega

/-- Lexicographic order on pairs is total, so `¬ b < a` is `a ≤ b` and composes with `<`. -/
private theorem lexLt_trans_of_not {a b c : Nat × Nat} (h : ¬ b.lexLt a) (h' : c.lexLt a) :
    c.lexLt b := by
  simp only [Prod.lexLt_def] at *
  omega

/-- A strict `countP` comparison: `q` counts everything `p` counts, and one more besides. -/
theorem countP_lt_countP {p q : Nat → Bool} :
    ∀ {l : List Nat}, (∀ x ∈ l, p x = true → q x = true) → ∀ {b : Nat}, b ∈ l →
      p b = false → q b = true → l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ b hb; exact absurd hb (List.not_mem_nil)
  | cons x xs ih =>
    intro hpq b hb hpb hqb
    have hsub : ∀ y ∈ xs, p y = true → q y = true :=
      fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hb with rfl | hb'
    · have hmono : xs.countP p ≤ xs.countP q := List.countP_mono_left hsub
      simp only [hpb, hqb, Bool.false_eq_true, reduceIte]
      omega
    · have hlt := ih hsub hb' hpb hqb
      have hhead : (if p x = true then 1 else 0) ≤ (if q x = true then 1 else 0) := by
        by_cases hx : p x = true
        · simp [hx, hpq x List.mem_cons_self hx]
        · simp [hx]
      omega

/-- **The counting step preserves order.** One position's count sits below another's exactly when
its key does. -/
private theorem count_lt_le_count_iff {n : Nat} (f : Nat → Nat × Nat) (a b : Nat)
    (_ha : a < n) (hb : b < n) :
    ((List.range n).filter (fun j => decide ((f j).lexLt (f a)))).length
      ≤ ((List.range n).filter (fun j => decide ((f j).lexLt (f b)))).length
    ↔ ¬ (f b).lexLt (f a) := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  constructor
  · intro hle hlt
    have hstrict : (List.range n).countP (fun j => decide ((f j).lexLt (f b)))
        < (List.range n).countP (fun j => decide ((f j).lexLt (f a))) := by
      refine countP_lt_countP (fun x _ hx => ?_) (List.mem_range.mpr hb) ?_ ?_
      · simp only [decide_eq_true_eq] at hx ⊢
        exact lexLt_trans hx hlt
      · simp only [decide_eq_false_iff_not]
        exact lexLt_irrefl _
      · simpa using hlt
    omega
  · intro h
    refine List.countP_mono_left (fun x _ hx => ?_)
    simp only [decide_eq_true_eq] at hx ⊢
    exact lexLt_trans_of_not h hx

/-- Reading a refined tag off the list is reading the count that defined it. -/
private theorem refineTags_getElem (t tag : List Nat) (k i : Nat) (hi : i < t.length) :
    (refineTags t tag k)[i]! =
      ((List.range t.length).filter
        (fun j => decide ((pairKey t tag k j).lexLt (pairKey t tag k i)))).length := by
  have hlen : i < (refineTags t tag k).length := by
    simpa [refineTags] using hi
  rw [getElem!_pos _ i hlen]
  simp only [refineTags, List.getElem_map, List.getElem_range]

/-- Round `k`'s tags separate two positions exactly when the prefixes their tags cover do. -/
private theorem tag_lt_iff {t tag : List Nat} {k : Nat} (h : Doubling.Valid t tag k)
    {a b : Nat} (ha : a < t.length) (hb : b < t.length) :
    tag[a]! < tag[b]! ↔ (suffix t a).take (2 ^ k) < (suffix t b).take (2 ^ k) := by
  constructor
  · intro hlt
    refine List.not_le.mp (fun hcon => ?_)
    have := (h.le_iff hb ha).mpr hcon
    omega
  · intro hlt
    exact Nat.not_le.mp (fun hcon => (List.not_le.mpr hlt) ((h.le_iff hb ha).mp hcon))

/-- Round `k`'s tags tie two positions exactly when the prefixes their tags cover agree. -/
private theorem tag_eq_iff {t tag : List Nat} {k : Nat} (h : Doubling.Valid t tag k)
    {a b : Nat} (ha : a < t.length) (hb : b < t.length) :
    tag[a]! = tag[b]! ↔ (suffix t a).take (2 ^ k) = (suffix t b).take (2 ^ k) := by
  constructor
  · intro he
    exact List.le_antisymm ((h.le_iff ha hb).mp (by omega)) ((h.le_iff hb ha).mp (by omega))
  · intro he
    have h1 : (suffix t a).take (2 ^ k) ≤ (suffix t b).take (2 ^ k) := by
      rw [he]; exact List.le_refl _
    have h2 : (suffix t b).take (2 ^ k) ≤ (suffix t a).take (2 ^ k) := by
      rw [he]; exact List.le_refl _
    have := (h.le_iff ha hb).mpr h1
    have := (h.le_iff hb ha).mpr h2
    omega

/-- Dropping inside a suffix moves along it. -/
private theorem suffix_drop (t : List Nat) (a m : Nat) :
    (suffix t a).drop m = suffix t (a + m) := by
  simp only [suffix, List.drop_drop]

/-- Past the end of the text the second half is empty. -/
private theorem half_eq_nil {t : List Nat} {k a : Nat} (h : t.length ≤ a + 2 ^ k) :
    (suffix t (a + 2 ^ k)).take (2 ^ k) = [] := by
  rw [suffix, List.drop_eq_nil_of_le h, List.take_nil]

/-- Inside the text it is not empty, because a half is at least one character wide. -/
private theorem half_ne_nil {t : List Nat} {k a : Nat} (h : a + 2 ^ k < t.length) :
    (suffix t (a + 2 ^ k)).take (2 ^ k) ≠ [] := by
  intro hnil
  have hlen : ((suffix t (a + 2 ^ k)).take (2 ^ k)).length = 0 := by rw [hnil]; rfl
  rw [List.length_take, suffix, List.length_drop] at hlen
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  omega

/-- **The prefix splits.** A prefix of `m + n` characters compares as its first `m` characters
do, and on a tie as the `n` characters after them do. -/
private theorem take_add_lt_take_add (n : Nat) : ∀ (m : Nat) (l l' : List Nat),
    l.take (m + n) < l'.take (m + n) ↔
      l.take m < l'.take m ∨
        (l.take m = l'.take m ∧ (l.drop m).take n < (l'.drop m).take n) := by
  intro m
  induction m with
  | zero => intro l l'; simp [List.lt_irrefl]
  | succ m ih =>
    have hswap : m + 1 + n = (m + n) + 1 := by omega
    intro l l'
    cases l with
    | nil =>
      cases l' with
      | nil => simp [List.lt_irrefl]
      | cons c cs => rw [hswap]; simp [List.nil_lt_cons]
    | cons a as =>
      cases l' with
      | nil => simp
      | cons c cs =>
        rw [hswap]
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_lt_cons_iff,
          List.cons.injEq, ih as cs]
        tauto

/-- The second components of two keys compare exactly as the second halves do. -/
private theorem pairKey_snd_lt_iff {t tag : List Nat} {k : Nat} (h : Doubling.Valid t tag k)
    (a b : Nat) :
    (pairKey t tag k a).2 < (pairKey t tag k b).2 ↔
      (suffix t (a + 2 ^ k)).take (2 ^ k) < (suffix t (b + 2 ^ k)).take (2 ^ k) := by
  simp only [pairKey]
  by_cases ha : a + 2 ^ k < t.length <;> by_cases hb : b + 2 ^ k < t.length
  · simp only [ha, hb, reduceIte, Nat.add_lt_add_iff_right]
    exact tag_lt_iff h ha hb
  · simp only [ha, hb, reduceIte, half_eq_nil (Nat.le_of_not_lt hb)]
    simp
  · simp only [ha, hb, reduceIte, half_eq_nil (Nat.le_of_not_lt ha)]
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (half_ne_nil hb)
    rw [hc]
    simp [List.nil_lt_cons]
  · simp only [ha, hb, reduceIte, half_eq_nil (Nat.le_of_not_lt ha),
      half_eq_nil (Nat.le_of_not_lt hb)]
    simp [List.lt_irrefl]

/-- One round's key is a faithful key for a prefix twice as long. -/
private theorem lexLt_pairKey_iff {t tag : List Nat} {k : Nat} (h : Doubling.Valid t tag k)
    {a b : Nat} (ha : a < t.length) (hb : b < t.length) :
    (pairKey t tag k a).lexLt (pairKey t tag k b) ↔
      (suffix t a).take (2 ^ (k + 1)) < (suffix t b).take (2 ^ (k + 1)) := by
  have hfst : ∀ x : Nat, (pairKey t tag k x).1 = tag[x]! := fun _ => rfl
  have hsplit : (2 : Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by
    rw [Nat.pow_succ]; omega
  rw [hsplit, take_add_lt_take_add (2 ^ k) (2 ^ k), suffix_drop, suffix_drop,
    Prod.lexLt_def, hfst, hfst, tag_lt_iff h ha hb, tag_eq_iff h ha hb,
    pairKey_snd_lt_iff h a b]

/-- **The doubling step.** One round carries round `k`'s invariant to round `k + 1`: the first
`2 ^ (k + 1)` characters of suffix `i` are the first `2 ^ k` of suffix `i` followed by the first
`2 ^ k` of suffix `i + 2 ^ k`. -/
theorem Doubling.valid_succ (t : List Nat) (tag : List Nat) (k : Nat)
    (h : Doubling.Valid t tag k) :
    Doubling.Valid t (refineTags t tag k) (k + 1) := by
  refine Doubling.valid_of_le_iff (by simp [refineTags]) fun i hi j hj => ?_
  rw [refineTags_getElem t tag k i hi, refineTags_getElem t tag k j hj,
    count_lt_le_count_iff (pairKey t tag k) i j hi hj, ← List.not_lt]
  exact not_congr (lexLt_pairKey_iff h hj hi)

/-- **The loop.** `r` rounds of doubling; the round count is the recursion's argument, so the
kernel can reduce it. -/
def doublingRounds (t : List Nat) : Nat → List Nat
  | 0 => initialTags t
  | r + 1 => refineTags t (doublingRounds t r) r

/-- **The loop keeps the invariant**: after `r` rounds the tags order the suffixes on their first
`2 ^ r` characters. -/
private theorem Doubling.valid_doublingRounds (t : List Nat) :
    ∀ r, Doubling.Valid t (doublingRounds t r) r
  | 0 => Doubling.valid_initial t
  | r + 1 => Doubling.valid_succ t (doublingRounds t r) r (Doubling.valid_doublingRounds t r)

/-- The suffix array of `t`: run the doubling for `t.length` rounds, then list the positions in
tag order (`List.insertionSort`, which reduces in the kernel). -/
def suffixArray (t : List Nat) : List Nat :=
  let tag := doublingRounds t t.length
  List.insertionSort (fun a b => tag[a]! ≤ tag[b]!) (List.range t.length)

/-- **Construction correctness.** The doubling loop, run for `t.length` rounds and read off in
tag order, is a suffix array. -/
theorem valid_suffixArray (t : List Nat) : SuffixArray.Valid ⟨t, suffixArray t⟩ := by
  have htag := Doubling.valid_doublingRounds t t.length
  have : Std.Total (fun a b : Nat => (doublingRounds t t.length)[a]!
      ≤ (doublingRounds t t.length)[b]!) := ⟨fun _ _ => Nat.le_total _ _⟩
  have : IsTrans Nat (fun a b : Nat => (doublingRounds t t.length)[a]!
      ≤ (doublingRounds t t.length)[b]!) := ⟨fun _ _ _ => Nat.le_trans⟩
  refine valid_of_doubling t (doublingRounds t t.length) (suffixArray t) t.length
    (Nat.le_of_lt Nat.lt_two_pow_self) htag (List.perm_insertionSort _ _) ?_
  exact List.pairwise_map.mpr (List.pairwise_insertionSort _ _)

/-! ### The early exit

The Rust's loop also stops as soon as every tag is distinct: the tags then already give suffix
order. -/

/-- A prefix comparison that is strict settles the whole comparison: if the first `m` characters
of `l` sort below those of `l'`, so does `l`. -/
theorem lt_of_take_lt_take {m : Nat} {l l' : List Nat} (h : l.take m < l'.take m) :
    l < l' := by
  have hsplit := (take_add_lt_take_add (l.length + l'.length) m l l').mpr (Or.inl h)
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hsplit

/-- **Distinct tags are suffix order.** If round `k`'s tags are pairwise distinct, sorting by
them already lists the suffixes in order. -/
theorem valid_of_doubling_of_nodup (t : List Nat) (tag sa : List Nat) (k : Nat)
    (htag : Doubling.Valid t tag k) (hlen : tag.length = t.length) (hnodup : tag.Nodup)
    (hperm : sa.Perm (List.range t.length))
    (hsorted : (sa.map (fun p => tag[p]!)).Pairwise (· ≤ ·)) :
    SuffixArray.Valid ⟨t, sa⟩ := by
  refine ⟨hperm, ?_⟩
  unfold SuffixArray.SuffixesSorted
  rw [List.pairwise_map] at hsorted ⊢
  refine hsorted.imp_of_mem ?_
  intro a b ha hb hle
  have ha' : a < t.length := List.mem_range.mp (hperm.mem_iff.mp ha)
  have hb' : b < t.length := List.mem_range.mp (hperm.mem_iff.mp hb)
  by_cases hab : a = b
  · subst hab; exact List.le_refl _
  · have hne : tag[a]! ≠ tag[b]! := by
      rw [getElem!_pos tag a (by omega), getElem!_pos tag b (by omega)]
      exact fun he => hab ((List.Nodup.getElem_inj_iff hnodup).mp he)
    have hlt : tag[a]! < tag[b]! := by omega
    exact List.le_of_lt (lt_of_take_lt_take ((tag_lt_iff htag ha' hb').mp hlt))

/-- **The loop as the Rust runs it.** Before each round, stop if every tag is distinct or the
covered prefix spans the text; otherwise run one round. Returns the rounds run and the final tags.
`fuel`, started at `t.length`, never runs out. -/
def doublingLoop (t : List Nat) : Nat → Nat → List Nat → Nat × List Nat
  | 0, k, tag => (k, tag)
  | fuel + 1, k, tag =>
    if tag.Nodup ∨ t.length ≤ 2 ^ k then (k, tag)
    else doublingLoop t fuel (k + 1) (refineTags t tag k)

/-- How many doubling rounds the Rust's loop runs on `t`. -/
def earlyRounds (t : List Nat) : Nat := (doublingLoop t t.length 0 (initialTags t)).1

/-- The suffix array as the Rust's `suffix_array` computes it: the early-exit loop, read off in
tag order. -/
def suffixArrayEarly (t : List Nat) : List Nat :=
  let tag := (doublingLoop t t.length 0 (initialTags t)).2
  List.insertionSort (fun a b => tag[a]! ≤ tag[b]!) (List.range t.length)

/-- One round keeps the tag list as long as the text. -/
private theorem length_refineTags (t tag : List Nat) (k : Nat) :
    (refineTags t tag k).length = t.length := by
  simp [refineTags]

/-- **The loop's invariant.** The loop leaves tags one per position, satisfying the doubling
invariant for the rounds run, and either pairwise distinct or from a prefix that covers the text. -/
private theorem doublingLoop_spec (t : List Nat) : ∀ (fuel k : Nat) (tag : List Nat),
    fuel + k = t.length → Doubling.Valid t tag k → tag.length = t.length →
      Doubling.Valid t (doublingLoop t fuel k tag).2 (doublingLoop t fuel k tag).1 ∧
      (doublingLoop t fuel k tag).2.length = t.length ∧
      ((doublingLoop t fuel k tag).2.Nodup ∨ t.length ≤ 2 ^ (doublingLoop t fuel k tag).1)
  | 0, k, tag, hk, htag, hlen => by
    refine ⟨htag, hlen, Or.inr ?_⟩
    simp only [doublingLoop]
    have := @Nat.lt_two_pow_self k
    omega
  | fuel + 1, k, tag, hk, htag, hlen => by
    simp only [doublingLoop]
    split
    · next hstop => exact ⟨htag, hlen, hstop⟩
    · exact doublingLoop_spec t fuel (k + 1) (refineTags t tag k) (by omega)
        (Doubling.valid_succ t tag k htag) (length_refineTags t tag k)

/-- **The early exit is sound.** The Rust's loop, stopping on distinct tags or on a prefix
covering the text, returns a suffix array. -/
theorem valid_suffixArrayEarly (t : List Nat) : SuffixArray.Valid ⟨t, suffixArrayEarly t⟩ := by
  obtain ⟨htag, hlen, hstop⟩ := doublingLoop_spec t t.length 0 (initialTags t) (by omega)
    (Doubling.valid_initial t) rfl
  have : Std.Total (fun a b : Nat => (doublingLoop t t.length 0 (initialTags t)).2[a]!
      ≤ (doublingLoop t t.length 0 (initialTags t)).2[b]!) := ⟨fun _ _ => Nat.le_total _ _⟩
  have : IsTrans Nat (fun a b : Nat => (doublingLoop t t.length 0 (initialTags t)).2[a]!
      ≤ (doublingLoop t t.length 0 (initialTags t)).2[b]!) := ⟨fun _ _ _ => Nat.le_trans⟩
  have hperm := List.perm_insertionSort (fun a b : Nat =>
    (doublingLoop t t.length 0 (initialTags t)).2[a]!
      ≤ (doublingLoop t t.length 0 (initialTags t)).2[b]!) (List.range t.length)
  have hsorted := List.pairwise_map.mpr (List.pairwise_insertionSort (fun a b : Nat =>
    (doublingLoop t t.length 0 (initialTags t)).2[a]!
      ≤ (doublingLoop t t.length 0 (initialTags t)).2[b]!) (List.range t.length))
  rcases hstop with hnodup | hcover
  · exact valid_of_doubling_of_nodup t _ _ _ htag hlen hnodup hperm hsorted
  · exact valid_of_doubling t _ _ _ hcover htag hperm hsorted

/-- **The early exit changes nothing.** It returns exactly `suffixArray`'s array, since a text
has only one suffix array (`valid_unique`). -/
theorem suffixArrayEarly_eq (t : List Nat) : suffixArrayEarly t = suffixArray t :=
  valid_unique (valid_suffixArrayEarly t) (valid_suffixArray t)

end AlgoDesign.Strings
