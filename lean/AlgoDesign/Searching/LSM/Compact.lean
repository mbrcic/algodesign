/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Write

/-!
# LSM-tree: compaction

The compaction that discharges `CompactSpec`: `mergeAt` merges two adjacent runs and `dropBottom`
collects the oldest run's tombstones; `compactAt` is the first followed, at the bottom, by the
second. Every in-range merge discharges `CompactSpec` on a valid store (`compactSpec_mergeAt`,
`compactSpec_compactAt`, `compactSpec_compact`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace LSM

variable {α β : Type} [LinearOrder α]

/-- What any compaction step must satisfy: it keeps every `get`, keeps every run sorted, and, given
two or more runs, leaves fewer. -/
def CompactSpec (before after : List (Run α β)) : Prop :=
  PreservesGet before after ∧
  (EachSorted before → EachSorted after) ∧
  (2 ≤ before.length → after.length < before.length)

/-- Doing nothing fails `CompactSpec` as soon as there are two runs to compact. -/
theorem not_compactSpec_self {t : List (Run α β)} (h : 2 ≤ t.length) : ¬ CompactSpec t t := by
  rintro ⟨-, -, hprogress⟩
  exact Nat.lt_irrefl _ (hprogress h)

/-! ## A compaction that discharges the obligation

Every merge the store performs merges a run into the next older one; on the runs flattened newest
first that is `compactAt i`, merging runs `i` and `i + 1`. Tombstones are dropped only when the
merged run is the oldest. -/

theorem lookup_cons (a : α) (r : Run α β) (rs : List (Run α β)) :
    lookup a (r :: rs) = (Run.lookup a r).or (lookup a rs) := by
  simp only [lookup]
  cases Run.lookup a r <;> rfl

/-- Merge run `i` into run `i + 1`, the next older, newer entries winning. If the merged run is
the oldest in the store, its tombstones are collected as well. Out of range, nothing changes. -/
def compactAt : Nat → List (Run α β) → List (Run α β)
  | 0, [newer, older] => [Run.dropTombstones (Run.mergeRuns newer older)]
  | 0, newer :: older :: r :: rest => Run.mergeRuns newer older :: r :: rest
  | i + 1, r :: rs => r :: compactAt i rs
  | _, t => t

/-- **The compaction step**: merge the two oldest runs into one, collecting its tombstones — the
merge into the bottom level. -/
def compact (t : List (Run α β)) : List (Run α β) := compactAt (t.length - 2) t

/-- An in-range step removes exactly one run. -/
theorem length_compactAt : ∀ {i : Nat} {t : List (Run α β)}, i + 1 < t.length →
    (compactAt i t).length + 1 = t.length
  | 0, [_, _], _ => rfl
  | 0, _ :: _ :: _ :: _, _ => rfl
  | i + 1, _ :: rs, h => by
      simp only [compactAt, List.length_cons] at h ⊢
      rw [length_compactAt (by omega)]

/-- Every step keeps every run sorted: a merge of sorted runs is sorted (`sorted_mergeRuns`), and
so is what is left of one after its tombstones go. -/
theorem runsSorted_compactAt : ∀ (i : Nat) {t : List (Run α β)}, EachSorted t →
    EachSorted (compactAt i t)
  | 0, [] , h | 0, [_], h => h
  | 0, [n, o], h => by
      intro r hr
      simp only [compactAt, List.mem_singleton] at hr
      subst hr
      exact Run.sorted_dropTombstones (Run.sorted_mergeRuns (h n (by simp)) (h o (by simp)))
  | 0, n :: o :: r :: rest, h => by
      intro q hq
      simp only [compactAt, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Run.sorted_mergeRuns (h n (by simp)) (h o (by simp))
      · exact h q (by simp [hq])
  | _ + 1, [], h => h
  | i + 1, r :: rs, h => by
      intro q hq
      simp only [compactAt, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h q (by simp)
      · exact runsSorted_compactAt i (t := rs)
          (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) q hq

/-- **A merge above the bottom changes no answer at all**, tombstones included: the merged run
answers as the pair did, newer first (`lookup_mergeRuns`), and that is what `lookup` asked of the
pair. -/
theorem preservesLookup_compactAt : ∀ {i : Nat} {t : List (Run α β)}, EachSorted t →
    i + 2 < t.length →
    PreservesLookup t (compactAt i t)
  | 0, n :: o :: r :: rest, h, _ => fun a => by
      simp only [compactAt, lookup_cons, Run.lookup_mergeRuns a (h n (by simp)), Option.or_assoc]
  | i + 1, r :: rs, h, hi => fun a => by
      simp only [List.length_cons] at hi
      have hv : EachSorted rs := fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [compactAt, lookup_cons, preservesLookup_compactAt (i := i) hv (by omega) a]

/-- **Any step keeps every value a client can `get`**, the bottom merge included: there a
tombstone becomes silence, and both answer "no value" (`lookup_dropTombstones_join`). -/
theorem preservesGet_compactAt : ∀ (i : Nat) {t : List (Run α β)}, EachSorted t →
    PreservesGet t (compactAt i t)
  | 0, [], _ | 0, [_], _ => PreservesGet.rfl
  | 0, [n, o], h => fun a => by
      have hm := Run.sorted_mergeRuns (h n (by simp)) (h o (by simp))
      simp only [get, compactAt, lookup_cons, lookup_nil, Option.or_none,
        Run.lookup_dropTombstones_join a hm, Run.lookup_mergeRuns a (h n (by simp))]
  | 0, n :: o :: r :: rest, h =>
      (preservesLookup_compactAt (i := 0) h (by simp)).preservesGet
  | _ + 1, [], _ => PreservesGet.rfl
  | i + 1, r :: rs, h => fun a => by
      have ih := preservesGet_compactAt i (t := rs) (fun q hq => h q (List.mem_cons_of_mem _ hq)) a
      simp only [get, compactAt, lookup_cons] at ih ⊢
      cases Run.lookup a r <;> simp [ih]

/-- **`compactAt` discharges `CompactSpec`** on a valid store, for any in-range pair of runs. -/
theorem compactSpec_compactAt {i : Nat} {t : List (Run α β)} (h : EachSorted t)
    (hi : i + 1 < t.length) :
    CompactSpec t (compactAt i t) :=
  ⟨preservesGet_compactAt i h, fun _ => runsSorted_compactAt i h,
    fun _ => by have := length_compactAt hi; omega⟩

/-! ### The two steps the store's policy is made of

`mergeAt` merges two adjacent runs and keeps tombstones; `dropBottom` collects the oldest run's
tombstones. `compactAt` is the first followed, at the bottom, by the second (`compactAt_of_lt`,
`compactAt_of_eq`). `dropBottom` removes no run, so it owes only `EachSorted` and `get`. -/

/-- Merge run `i` into run `i + 1`, the next older, newer entries winning, keeping tombstones. -/
def mergeAt : Nat → List (Run α β) → List (Run α β)
  | 0, newer :: older :: rest => Run.mergeRuns newer older :: rest
  | i + 1, r :: rs => r :: mergeAt i rs
  | _, t => t

/-- Collect the tombstones of the oldest run, the only one with nothing beneath it to shadow. -/
def dropBottom : List (Run α β) → List (Run α β)
  | [] => []
  | [r] => [Run.dropTombstones r]
  | r :: s :: rs => r :: dropBottom (s :: rs)

theorem length_mergeAt : ∀ {i : Nat} {t : List (Run α β)}, i + 1 < t.length →
    (mergeAt i t).length + 1 = t.length
  | 0, _ :: _ :: _, _ => rfl
  | i + 1, _ :: rs, h => by
      simp only [mergeAt, List.length_cons] at h ⊢
      rw [length_mergeAt (by omega)]

omit [LinearOrder α] in
theorem length_dropBottom : ∀ t : List (Run α β), (dropBottom t).length = t.length
  | [] | [_] => rfl
  | _ :: s :: rs => by simp only [dropBottom, List.length_cons, length_dropBottom (s :: rs)]

theorem runsSorted_mergeAt : ∀ (i : Nat) {t : List (Run α β)}, EachSorted t →
    EachSorted (mergeAt i t)
  | 0, [], h | 0, [_], h => h
  | 0, n :: o :: rest, h => by
      intro q hq
      simp only [mergeAt, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Run.sorted_mergeRuns (h n (by simp)) (h o (by simp))
      · exact h q (by simp [hq])
  | _ + 1, [], h => h
  | i + 1, r :: rs, h => by
      intro q hq
      simp only [mergeAt, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h q (by simp)
      · exact runsSorted_mergeAt i (t := rs) (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) q hq

theorem runsSorted_dropBottom : ∀ {t : List (Run α β)}, EachSorted t → EachSorted (dropBottom t)
  | [], h => h
  | [r], h => by
      intro q hq
      simp only [dropBottom, List.mem_singleton] at hq
      subst hq
      exact Run.sorted_dropTombstones (h r (by simp))
  | r :: s :: rs, h => by
      intro q hq
      simp only [dropBottom, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact h q (by simp)
      · exact runsSorted_dropBottom (t := s :: rs)
          (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) q hq

/-- **A merge that keeps its tombstones changes no answer at all**, wherever it happens. -/
theorem preservesLookup_mergeAt : ∀ (i : Nat) {t : List (Run α β)}, EachSorted t →
    PreservesLookup t (mergeAt i t)
  | 0, [], _ | 0, [_], _ => PreservesLookup.rfl
  | 0, n :: o :: rest, h => fun a => by
      simp only [mergeAt, lookup_cons, Run.lookup_mergeRuns a (h n (by simp)), Option.or_assoc]
  | _ + 1, [], _ => PreservesLookup.rfl
  | i + 1, r :: rs, h => fun a => by
      have hv : EachSorted rs := fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [mergeAt, lookup_cons, preservesLookup_mergeAt i hv a]

/-- **Collecting the bottom run's tombstones keeps every value a client can `get`.** -/
theorem preservesGet_dropBottom : ∀ {t : List (Run α β)}, EachSorted t →
    PreservesGet t (dropBottom t)
  | [], _ => PreservesGet.rfl
  | [r], h => fun a => by
      simp only [get, dropBottom, lookup_cons, lookup_nil, Option.or_none,
        Run.lookup_dropTombstones_join a (h r (by simp))]
  | r :: s :: rs, h => fun a => by
      have ih := preservesGet_dropBottom (t := s :: rs)
        (fun q hq => h q (List.mem_cons_of_mem _ hq)) a
      simp only [get, dropBottom, lookup_cons] at ih ⊢
      cases Run.lookup a r <;> simp [ih]

/-- An in-range merge is a compaction step in `CompactSpec`'s sense. -/
theorem compactSpec_mergeAt {i : Nat} {t : List (Run α β)} (h : EachSorted t)
    (hi : i + 1 < t.length) :
    CompactSpec t (mergeAt i t) :=
  ⟨(preservesLookup_mergeAt i h).preservesGet, fun _ => runsSorted_mergeAt i h,
    fun _ => by have := length_mergeAt hi; omega⟩

/-- Above the bottom, `compactAt` is `mergeAt`. -/
theorem compactAt_of_lt : ∀ {i : Nat} {t : List (Run α β)}, i + 2 < t.length →
    compactAt i t = mergeAt i t
  | 0, _ :: _ :: _ :: _, _ => rfl
  | i + 1, r :: rs, h => by
      simp only [List.length_cons] at h
      simp only [compactAt, mergeAt, compactAt_of_lt (i := i) (t := rs) (by omega)]

/-- At the bottom, `compactAt` is `mergeAt` followed by `dropBottom`. -/
theorem compactAt_of_eq : ∀ {i : Nat} {t : List (Run α β)}, i + 2 = t.length →
    compactAt i t = dropBottom (mergeAt i t)
  | 0, [_, _], _ => rfl
  | i + 1, r :: rs, h => by
      simp only [List.length_cons] at h
      have hlen := length_mergeAt (i := i) (t := rs) (by omega)
      rw [compactAt, mergeAt, compactAt_of_eq (i := i) (t := rs) (by omega)]
      rcases hm : mergeAt i rs with _ | ⟨s, rest⟩
      · rw [hm] at hlen; simp at hlen; omega
      · rfl

/-- **The bottom merge discharges `CompactSpec`** on every valid store. With fewer than two runs
there is nothing to merge, `compact` is the identity, and the progress conjunct asks nothing. -/
theorem compactSpec_compact {t : List (Run α β)} (h : EachSorted t) :
    CompactSpec t (compact t) := by
  by_cases hl : 2 ≤ t.length
  · exact compactSpec_compactAt h (by omega)
  · refine ⟨preservesGet_compactAt _ h, fun _ => runsSorted_compactAt _ h, fun h2 => absurd h2 hl⟩

/-! ### Steps inside a longer store

A step that keeps `lookup` or `get` keeps it with newer runs in front of it too. -/

theorem lookup_append (a : α) : ∀ xs ys : List (Run α β),
    lookup a (xs ++ ys) = (lookup a xs).or (lookup a ys)
  | [], ys => by simp
  | r :: xs, ys => by
      rw [List.cons_append, lookup_cons, lookup_cons, lookup_append a xs ys, Option.or_assoc]

/-- An empty run says nothing, wherever it stands. -/
theorem preservesLookup_nil_cons (t : List (Run α β)) : PreservesLookup t ([] :: t) := fun _ => rfl

theorem PreservesLookup.append_left (xs : List (Run α β)) {ys ys' : List (Run α β)}
    (h : PreservesLookup ys ys') : PreservesLookup (xs ++ ys) (xs ++ ys') := fun a => by
  rw [lookup_append, lookup_append, h a]

theorem PreservesLookup.append_right {xs xs' : List (Run α β)} (h : PreservesLookup xs xs')
    (ys : List (Run α β)) : PreservesLookup (xs ++ ys) (xs' ++ ys) := fun a => by
  rw [lookup_append, lookup_append, h a]

theorem PreservesGet.append_left (xs : List (Run α β)) {ys ys' : List (Run α β)}
    (h : PreservesGet ys ys') :
    PreservesGet (xs ++ ys) (xs ++ ys') := fun a => by
  have h := h a
  simp only [get] at h ⊢
  rw [lookup_append, lookup_append]
  cases lookup a xs <;> simp [h]

theorem _root_.AlgoDesign.Searching.Run.mergeRuns_nil_right (r : Run α β) :
    Run.mergeRuns r [] = r := by
  cases r <;> rfl

/-- Folding sorted runs together newest first, each older run losing a tied key, answers as the
runs did. This is level 0's merge. -/
theorem preservesLookup_foldl_mergeRuns : ∀ (rs : List (Run α β)) {r : Run α β}, Run.Sorted r →
    EachSorted rs → PreservesLookup (r :: rs) [rs.foldl Run.mergeRuns r] ∧
      Run.Sorted (rs.foldl Run.mergeRuns r)
  | [], r, hr, _ => ⟨PreservesLookup.rfl, hr⟩
  | x :: xs, r, hr, hv => by
      have hx : Run.Sorted x := hv x (by simp)
      have ih := preservesLookup_foldl_mergeRuns xs (Run.sorted_mergeRuns hr hx)
        (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      refine ⟨fun a => ?_, ih.2⟩
      rw [List.foldl_cons, ← ih.1 a, lookup_cons, lookup_cons, lookup_cons,
        Run.lookup_mergeRuns a hr, Option.or_assoc]

/-- Merging every run into one, oldest first, answers as the runs did. This is `compact_fully`'s
merge. -/
theorem lookup_foldr_mergeRuns (a : α) : ∀ (rs : List (Run α β)), EachSorted rs →
    Run.lookup a (rs.foldr Run.mergeRuns []) = lookup a rs
  | [], _ => rfl
  | x :: xs, hv => by
      have hx : Run.Sorted x := hv x (by simp)
      rw [List.foldr_cons, Run.lookup_mergeRuns a hx,
        lookup_foldr_mergeRuns a xs (fun q hq => hv q (List.mem_cons_of_mem _ hq)), lookup_cons]

theorem sorted_foldr_mergeRuns : ∀ (rs : List (Run α β)), EachSorted rs →
    Run.Sorted (rs.foldr Run.mergeRuns [])
  | [], _ => Run.sorted_nil
  | x :: xs, hv => Run.sorted_mergeRuns (hv x (by simp))
      (sorted_foldr_mergeRuns xs (fun q hq => hv q (List.mem_cons_of_mem _ hq)))

end LSM

end AlgoDesign.Searching
