/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Spec
public import AlgoDesign.Searching.LSM.Decide

/-!
# LSM-tree: merging runs

`Run.mergeRuns`, the two-pointer merge of two sorted runs with the newer winning a tied key, and
`Run.dropTombstones`, which collects a run's tombstones: every compaction step is built from these
two. A merge of sorted runs is sorted (`sorted_mergeRuns`) and answers each lookup as the newer run
shadowing the older (`lookup_mergeRuns`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Run

variable {α β : Type} [LinearOrder α]

@[simp] theorem sorted_nil : Sorted ([] : Run α β) := List.Pairwise.nil

@[simp] theorem sorted_singleton (e : α × Option β) : Sorted [e] := List.pairwise_singleton _ _

@[simp] theorem lookup_nil (a : α) : lookup a ([] : Run α β) = none := rfl

/-- One step of `mergeRuns` with the newer run's head `(k, v)` in hand, against the older run.
`rest` is `mergeRuns newer`, passed in rather than called, so that each of the two functions
recurses structurally on one run, so a merge evaluates by `decide`. The smaller key goes out
first; on a tied key the newer entry goes out and the older one is dropped. -/
def mergeStep (k : α) (v : Option β) (newer : Run α β) (rest : Run α β → Run α β) :
    Run α β → Run α β
  | [] => (k, v) :: newer
  | (k', v') :: older =>
      if k < k' then (k, v) :: rest ((k', v') :: older)
      else if k' < k then (k', v') :: mergeStep k v newer rest older
      else (k, v) :: rest older

/-- Two-pointer merge of two sorted runs, the newer one (the first argument) winning a tied key.
Rust: `merge_runs`. -/
def mergeRuns : Run α β → Run α β → Run α β
  | [], older => older
  | (k, v) :: newer, older => mergeStep k v newer (mergeRuns newer) older

/-- Drop every tombstone. Legal only for a run with nothing older beneath it, where a tombstone
shadows nothing. Rust: `drop_tombstones`. -/
def dropTombstones (r : Run α β) : Run α β := r.filter (fun p => p.2.isSome)

theorem lookup_cons (a k : α) (v : Option β) (r : Run α β) :
    lookup a ((k, v) :: r) = if k = a then some v else lookup a r := rfl

/-- A run that never mentions `a` says nothing about it. -/
theorem lookup_eq_none {a : α} {r : Run α β} (h : ∀ p ∈ r, p.1 ≠ a) : lookup a r = none := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨k, v⟩ := p
      simp [lookup_cons, h (k, v) (by simp), ih fun q hq => h q (by simp [hq])]

/-- Every entry of the merge comes from one of the two runs. -/
theorem mem_mergeRuns {p : α × Option β} :
    ∀ {newer older : Run α β}, p ∈ mergeRuns newer older → p ∈ newer ∨ p ∈ older
  | [], older, h => Or.inr h
  | (k, v) :: newer, older, h => by
      induction older with
      | nil => exact Or.inl (by simpa [mergeRuns, mergeStep] using h)
      | cons q older ih =>
          obtain ⟨k', v'⟩ := q
          simp only [mergeRuns, mergeStep] at h ih
          split_ifs at h with h₁ h₂
          · rcases List.mem_cons.mp h with rfl | h
            · simp
            · rcases mem_mergeRuns h with h | h <;> simp [h]
          · rcases List.mem_cons.mp h with rfl | h
            · simp
            · rcases ih h with h | h <;> simp [h]
          · rcases List.mem_cons.mp h with rfl | h
            · simp
            · rcases mem_mergeRuns h with h | h <;> simp [h]

/-- Two sorted runs merge into a sorted run. -/
theorem sorted_mergeRuns : ∀ {newer older : Run α β}, Sorted newer → Sorted older →
    Sorted (mergeRuns newer older)
  | [], _, _, ho => ho
  | (k, v) :: newer, older, hn, ho => by
      have hn' := List.pairwise_cons.mp hn
      induction older with
      | nil => simpa [mergeRuns, mergeStep] using hn
      | cons q older ih =>
          obtain ⟨k', v'⟩ := q
          have ho' := List.pairwise_cons.mp ho
          have ih := ih ho'.2
          simp only [mergeRuns, mergeStep] at ih ⊢
          split_ifs with h₁ h₂
          · refine List.pairwise_cons.mpr ⟨fun p hp => ?_, sorted_mergeRuns hn'.2 ho⟩
            rcases mem_mergeRuns hp with hp | hp
            · exact hn'.1 p hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · exact h₁
              · exact lt_trans h₁ (ho'.1 p hp)
          · refine List.pairwise_cons.mpr ⟨fun p hp => ?_, ih⟩
            have hp : p ∈ (k, v) :: newer ∨ p ∈ older := by
              rcases mem_mergeRuns (newer := (k, v) :: newer) (older := older)
                (by simpa [mergeRuns] using hp) with h | h
              · exact Or.inl h
              · exact Or.inr h
            rcases hp with hp | hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · exact h₂
              · exact lt_trans h₂ (hn'.1 p hp)
            · exact ho'.1 p hp
          · have hk : k = k' := le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)
            subst hk
            refine List.pairwise_cons.mpr ⟨fun p hp => ?_, sorted_mergeRuns hn'.2 ho'.2⟩
            rcases mem_mergeRuns hp with hp | hp
            · exact hn'.1 p hp
            · exact ho'.1 p hp

/-- **The merge answers as the pair did, newer first.** Looking a key up in the merged run is
looking it up in the newer run and, only if that says nothing, in the older one — which is
`LSM.lookup`'s shadowing rule for two adjacent runs, so replacing them by their merge changes no
answer. The newer run must be sorted: it is what guarantees that when an older key goes out
first, the newer run has no entry for it further on. -/
theorem lookup_mergeRuns (a : α) : ∀ {newer : Run α β}, Sorted newer → ∀ older : Run α β,
    lookup a (mergeRuns newer older) = (lookup a newer).or (lookup a older)
  | [], _, older => by simp [mergeRuns]
  | (k, v) :: newer, hn, older => by
      have hn' := List.pairwise_cons.mp hn
      induction older with
      | nil => simp [mergeRuns, mergeStep]
      | cons q older ih =>
          obtain ⟨k', v'⟩ := q
          simp only [mergeRuns, mergeStep] at ih ⊢
          split_ifs with h₁ h₂
          · rw [lookup_cons, lookup_mergeRuns a hn'.2]
            by_cases ha : k = a <;> simp [ha, lookup_cons]
          · rw [lookup_cons, ih, lookup_cons, lookup_cons]
            by_cases ha : k' = a
            · subst ha
              have hnone : lookup k' ((k, v) :: newer) = none := lookup_eq_none fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact ne_of_gt h₂
                · exact ne_of_gt (lt_trans h₂ (hn'.1 p hp))
              rw [lookup_cons] at hnone
              simp [hnone]
            · simp [ha]
          · have hk : k = k' := le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)
            subst hk
            rw [lookup_cons, lookup_mergeRuns a hn'.2]
            by_cases ha : k = a <;> simp [ha, lookup_cons]

theorem sorted_dropTombstones {r : Run α β} (h : Sorted r) : Sorted (dropTombstones r) :=
  List.Pairwise.filter _ h

/-- **Collecting tombstones changes only what a tombstone says.** A client asking for a value
cannot tell the difference: a live entry is kept, and a tombstone, which answered "no value",
becomes silence, which answers the same. The run must be sorted, so that no later entry for the
same key is uncovered when its tombstone goes. -/
theorem lookup_dropTombstones_join (a : α) {r : Run α β} (h : Sorted r) :
    (lookup a (dropTombstones r)).join = (lookup a r).join := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨k, v⟩ := p
      have h' := List.pairwise_cons.mp h
      have ih := ih h'.2
      cases v with
      | none =>
          simp only [dropTombstones, List.filter_cons, Option.isSome_none, Bool.false_eq_true,
            ite_false] at ih ⊢
          rw [ih, lookup_cons]
          by_cases ha : k = a
          · subst ha
            simp [lookup_eq_none fun p hp => ne_of_gt (h'.1 p hp)]
          · simp [ha]
      | some x =>
          simp only [dropTombstones, List.filter_cons, Option.isSome_some, ite_true] at ih ⊢
          rw [lookup_cons, lookup_cons]
          by_cases ha : k = a
          · simp [ha]
          · simpa [ha] using ih

omit [LinearOrder α] in
theorem clean_dropTombstones (r : Run α β) : Clean (dropTombstones r) := by
  unfold Clean dropTombstones
  intro p hp
  exact Option.isSome_iff_ne_none.mp (List.mem_filter.mp hp).2

/-- A merge is no longer than the two runs it merges. -/
theorem length_mergeRuns_le : ∀ (newer older : Run α β),
    (mergeRuns newer older).length ≤ newer.length + older.length
  | [], older => by simp [mergeRuns]
  | (k, v) :: newer, older => by
      induction older with
      | nil => simp [mergeRuns, mergeStep]
      | cons q older ih =>
          obtain ⟨k', v'⟩ := q
          simp only [mergeRuns, mergeStep] at ih ⊢
          split_ifs with h₁ h₂
          · have := length_mergeRuns_le newer ((k', v') :: older)
            simp only [List.length_cons] at this ⊢
            omega
          · simp only [List.length_cons] at ih ⊢
            omega
          · have := length_mergeRuns_le newer older
            simp only [List.length_cons] at this ⊢
            omega

omit [LinearOrder α] in
theorem length_dropTombstones_le (r : Run α β) : (dropTombstones r).length ≤ r.length :=
  List.length_filter_le _ _

end Run

namespace LSM

variable {α β : Type} [LinearOrder α]

/-! ## Lists of runs, newest first

The proofs reason about the store's runs as one list, newest first (`Store.runs`): what a merge or a
flush keeps is stated on such lists. -/

/-- Every run in the list sorted. -/
def EachSorted (t : List (Run α β)) : Prop := ∀ r ∈ t, Run.Sorted r

instance (t : List (Run α β)) : Decidable (EachSorted t) :=
  by unfold EachSorted; infer_instance

/-- Look `a` up in runs newest first: the first run that mentions `a` answers; `none` if none
does, `some none` for a tombstone. -/
def lookup (a : α) : List (Run α β) → Option (Option β)
  | [] => none
  | r :: rs => match Run.lookup a r with
      | some v => some v
      | none => lookup a rs

/-- `lookup` as a client sees it: a tombstone and absence both answer `none`. -/
def get (a : α) (t : List (Run α β)) : Option β := (lookup a t).join

/-- `lookup` is unchanged on every key. A merge above the bottom keeps it
(`preservesLookup_compactAt`). -/
def PreservesLookup (before after : List (Run α β)) : Prop := ∀ a, lookup a before = lookup a after

/-- `get` is unchanged on every key. Weaker than `PreservesLookup`: it lets a compaction collect a
tombstone once nothing older is left for it to shadow. -/
def PreservesGet (before after : List (Run α β)) : Prop := ∀ a, get a before = get a after

/-- `lookup` is the first answer any run gives, newest first. -/
theorem lookup_eq_findSome? (a : α) : ∀ t : List (Run α β), lookup a t = t.findSome? (Run.lookup a)
  | [] => rfl
  | r :: rs => by
      simp only [lookup, List.findSome?_cons]
      cases Run.lookup a r <;> simp [lookup_eq_findSome? a rs]

namespace Store

/-- `lookup` on the store's runs: a tombstone answers `some none`. -/
def lookup (a : α) (s : Store α β) : Option (Option β) := LSM.lookup a s.runs

/-- The store's `get` is `get` on its runs. -/
theorem get_eq (a : α) (s : Store α β) : get a s = LSM.get a s.runs := by
  simp [get, LSM.get, lookup_eq_findSome?]

end Store

end LSM

end AlgoDesign.Searching
