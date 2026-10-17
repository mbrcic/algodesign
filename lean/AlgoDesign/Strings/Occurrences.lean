/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.List.Basic

/-!
# The occurrence promise

The Strings chapter's Rabin–Karp, suffix-array and FM-index boxes make one promise, "every
occurrence":

> **Promise:** every occurrence, overlapping ones too, and nothing else. (Rabin–Karp)
>
> **Promise:** every place the fragment starts, and nothing else. (suffix array)
>
> **Promise:** every start position, each exactly once, in no particular order. (FM-index locate)

This file is that promise, as the reader checks it: the operations a design that finds occurrences
offers (`Occurrences`), and the laws they obey on every valid value (`Promise`), one law per
sentence. A text and a pattern are lists of symbols (`List Nat`). Each structure states its contract
as `Contract` in its `Spec.lean` and proves it in its umbrella file. A design that changes the
representation (a new index, an AI's candidate) is held to these same laws.

**The contract.**
- Where a pattern `p` occurs in a text `t`: at every position `i` with `i ≤ t.length` whose rest of
  the text, `t.drop i`, starts with `p` (`Occurs`). The bound is part of the statement.
- So the empty pattern occurs at every position `0, 1, …, n`, the end of the text included: `n + 1`
  positions (`occurs_nil`).
- Occurrences may overlap: each position is judged on its own.
- `every`: each occurrence is reported. `nothing_else`: only occurrences are. `once_each`: none is
  reported twice. Together they fix the answer up to order (`Promise.perm`).
- No order is promised: the FM-index reports "in no particular order", and the suffix array reports
  in its own row order. An order a structure does keep (Rabin–Karp's increasing one) stays in its
  own `Contract`.
- The laws hold on every valid value, not only on built ones. So that `Valid := False` cannot meet
  them, the promise also asks that every text of the design's domain `Texts` builds a valid value
  that indexes exactly that text (`valid_build`, `text_build`), as the search tree's asks that the
  empty tree is valid. The domain is a parameter of `Promise`, so each `Contract` shows it: every
  text for Rabin–Karp and the suffix array, the texts of positive bytes for the FM-index.

**A text with its `$`.** The FM-index stores a terminated text `t = u ++ [$]`, `$` being `0`, the
smallest letter, found nowhere in `u` (the transform's assumption, `Terminated`). It answers about
the payload `u`: its `text` is `u`, and its positions are positions of `u`, `0` to `u.length`. A
pattern containing `$` is inside the promise, and the promise says it returns nothing: `u` holds no
`$`, so such a pattern occurs nowhere in `u` (`Promise.eq_nil_of_absent`). This covers the FM box's
Assumes, "one that does gets zero matches". For a pattern without `$`, the positions of
`u` are the positions in `t` before its last (`filter_range_append`): the form the FM-index's
`matchStarts` is in.

**What is not closed.** A `Contract` can still choose a narrow domain (`Texts := fun _ => False`);
there it is in the statement, for the reader and the checker to see.

**Counted steps.** A structure's `Contract` may bound the steps its counted search reports
(Rabin–Karp's `searchM`, the FM-index's `countM` and `locateM`), and ties its answer to the real
one. What such a bound holds, and what it does not, is said once, at `SearchTree.Within`
(`Searching/SearchTree.lean`).
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- **Where a pattern occurs:** `p` occurs in `t` at `i` when `i` is a position of `t`, `0` to
`t.length`, and the text from `i` on starts with `p`. -/
def Occurs (t p : List Nat) (i : Nat) : Prop := i ≤ t.length ∧ p <+: t.drop i

instance (t p : List Nat) (i : Nat) : Decidable (Occurs t p i) :=
  by unfold Occurs; infer_instance

/-- Every occurrence of `p` in `t`, in increasing order: the reference answer, up to order. -/
def occurrenceList (t p : List Nat) : List Nat :=
  (List.range (t.length + 1)).filter fun i => decide (Occurs t p i)

/-- **Goal:** the operations a design that finds occurrences needs, over values `S`, and the
invariant the design keeps. A design that leaves one out does not typecheck. -/
structure Occurrences (S : Type) where
  /-- Prepare a text for searching. -/
  build : List Nat → S
  /-- The text a value answers about. -/
  text : S → List Nat
  /-- Where a pattern occurs. -/
  search : S → List Nat → List Nat
  /-- The design's invariants. -/
  Valid : S → Prop

namespace Occurrences

variable {S : Type} (o : Occurrences S)

/-- **Promise:** every occurrence, overlapping ones too, each once, and nothing else, on every
valid value; every text of the domain `Texts` builds one. -/
structure Promise (Texts : List Nat → Prop) : Prop where
  /-- Every text of the domain builds a valid value. -/
  valid_build : ∀ t, Texts t → o.Valid (o.build t)
  /-- The value built from a text answers about that text. -/
  text_build : ∀ t, Texts t → o.text (o.build t) = t
  /-- "Every occurrence, overlapping ones too"; "every place the fragment starts"; "every start
  position". -/
  every : ∀ s, o.Valid s → ∀ p i, Occurs (o.text s) p i → i ∈ o.search s p
  /-- "And nothing else." -/
  nothing_else : ∀ s, o.Valid s → ∀ p i, i ∈ o.search s p → Occurs (o.text s) p i
  /-- "Each exactly once." -/
  once_each : ∀ s, o.Valid s → ∀ p, (o.search s p).Nodup

end Occurrences

/-- The empty pattern occurs at every position `0` to `n`, the end of the text included. -/
@[simp] theorem occurs_nil (t : List Nat) (i : Nat) : Occurs t [] i ↔ i ≤ t.length := by
  simp [Occurs]

theorem mem_occurrenceList {t p : List Nat} {i : Nat} :
    i ∈ occurrenceList t p ↔ Occurs t p i := by
  simp only [occurrenceList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1, h⟩⟩

theorem nodup_occurrenceList (t p : List Nat) : (occurrenceList t p).Nodup :=
  List.nodup_range.filter _

/-- A pattern holding a letter the text lacks occurs nowhere. -/
theorem not_occurs_of_absent {t p : List Nat} {a : Nat} (hp : a ∈ p) (ht : a ∉ t) (i : Nat) :
    ¬ Occurs t p i :=
  fun h => ht (List.mem_of_mem_drop (h.2.subset hp))

/-- **A text with its `$`:** for a pattern without the end letter `a`, its positions in `u ++ [a]`
before the last are its occurrences in `u`. The FM-index's `matchStarts (u ++ [$]) p` is the left
side. -/
theorem filter_range_append (u p : List Nat) {a : Nat} (ha : a ∉ p) :
    (List.range (u ++ [a]).length).filter (fun i => decide (p <+: (u ++ [a]).drop i)) =
      occurrenceList u p := by
  simp only [occurrenceList, List.length_append, List.length_singleton]
  refine List.filter_congr fun i hi => ?_
  have hi : i ≤ u.length := Nat.le_of_lt_succ (List.mem_range.1 hi)
  rw [List.drop_append_of_le_length hi]
  simp only [Occurs, hi, true_and, List.prefix_concat_iff]
  refine decide_eq_decide.2 ⟨?_, Or.inr⟩
  rintro (h | h)
  · exact absurd (h ▸ List.mem_append_right _ (List.mem_singleton_self a)) ha
  · exact h

/-- **Window by window:** the occurrence list is the positions whose window of the pattern's
length equals the pattern, the form Rabin–Karp's scan reads it in. -/
theorem occurrenceList_eq_windows (t p : List Nat) :
    occurrenceList t p =
      (List.range (t.length + 1)).filter fun i => (t.drop i).take p.length = p := by
  refine List.filter_congr fun i hi => ?_
  have hi : i ≤ t.length := Nat.le_of_lt_succ (List.mem_range.1 hi)
  simp only [Occurs, hi, true_and, List.prefix_iff_eq_take]
  exact decide_eq_decide.2 ⟨Eq.symm, Eq.symm⟩

namespace Occurrences

variable {S : Type} {o : Occurrences S} {Texts : List Nat → Prop}

/-- On a valid value, the answer holds exactly the occurrences. -/
theorem Promise.mem_iff (h : o.Promise Texts) {s : S} (hs : o.Valid s) (p : List Nat) (i : Nat) :
    i ∈ o.search s p ↔ Occurs (o.text s) p i :=
  ⟨h.nothing_else s hs p i, h.every s hs p i⟩

/-- On a valid value, the answer is every occurrence, each once, in some order. -/
theorem Promise.perm (h : o.Promise Texts) {s : S} (hs : o.Valid s) (p : List Nat) :
    (o.search s p).Perm (occurrenceList (o.text s) p) :=
  (List.perm_ext_iff_of_nodup (h.once_each s hs p) (nodup_occurrenceList _ _)).2 fun i => by
    rw [h.mem_iff hs, mem_occurrenceList]

/-- A pattern holding a letter the text lacks returns nothing: the FM-index's `$`. -/
theorem Promise.eq_nil_of_absent (h : o.Promise Texts) {s : S} (hs : o.Valid s) {p : List Nat}
    {a : Nat} (hp : a ∈ p) (ht : a ∉ o.text s) : o.search s p = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun i hi =>
    not_occurs_of_absent hp ht i (h.nothing_else s hs p i hi)

/-- The promise from "the answer is the occurrence list, rearranged", the form the libraries
prove: Rabin–Karp's search through `occurrenceList_eq_windows`, the FM-index's
`matchStarts` through `filter_range_append`. -/
theorem Promise.of_perm (valid_build : ∀ t, Texts t → o.Valid (o.build t))
    (text_build : ∀ t, Texts t → o.text (o.build t) = t)
    (perm : ∀ s, o.Valid s → ∀ p, (o.search s p).Perm (occurrenceList (o.text s) p)) :
    o.Promise Texts where
  valid_build := valid_build
  text_build := text_build
  every s hs p _ hi := (perm s hs p).mem_iff.2 (mem_occurrenceList.2 hi)
  nothing_else s hs p _ hi := mem_occurrenceList.1 ((perm s hs p).mem_iff.1 hi)
  once_each s hs p := (perm s hs p).nodup_iff.2 (nodup_occurrenceList _ _)

/-- The promise from membership and no repeats, the form the suffix array proves
(`mem_search_iff`). -/
theorem Promise.of_mem_iff (valid_build : ∀ t, Texts t → o.Valid (o.build t))
    (text_build : ∀ t, Texts t → o.text (o.build t) = t)
    (mem_iff : ∀ s, o.Valid s → ∀ p i, i ∈ o.search s p ↔ Occurs (o.text s) p i)
    (nodup : ∀ s, o.Valid s → ∀ p, (o.search s p).Nodup) :
    o.Promise Texts where
  valid_build := valid_build
  text_build := text_build
  every s hs p i := (mem_iff s hs p i).2
  nothing_else s hs p i := (mem_iff s hs p i).1
  once_each := nodup

end Occurrences

end AlgoDesign.Strings
