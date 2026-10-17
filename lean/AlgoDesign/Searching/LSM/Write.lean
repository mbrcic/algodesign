/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Merge

/-!
# LSM-tree: write

`write` prepends a singleton run: it is visible at once (`lookup_write_self`), touches nothing
already stored (`lookup_write_other`), and keeps `EachSorted` (`runsSorted_write`). Also the algebra
of `PreservesLookup` and `PreservesGet` that the compaction proofs compose with. -/

@[expose] public section

namespace AlgoDesign.Searching

namespace LSM

variable {α β : Type} [LinearOrder α]

@[simp] theorem runsSorted_nil : EachSorted ([] : List (Run α β)) := by simp [EachSorted]

@[simp] theorem runsSorted_singleton {r : Run α β} : EachSorted [r] ↔ Run.Sorted r := by
  simp [EachSorted]

@[simp] theorem lookup_nil (a : α) : lookup a ([] : List (Run α β)) = none := rfl

/-- **Write is `O(1)` on the hot path**: prepend a brand-new singleton run in front. Nothing
already present is walked, compared against, or rewritten — the entire "smart design" claim, made
checkable. -/
def write (a : α) (v : Option β) (t : List (Run α β)) : List (Run α β) := [(a, v)] :: t

@[simp] theorem lookup_write_self (a : α) (v : Option β) (t : List (Run α β)) :
    lookup a (write a v t) = some v := by
  simp [write, lookup, Run.lookup]

theorem lookup_write_other {a b : α} (hab : a ≠ b) (v : Option β) (t : List (Run α β)) :
    lookup b (write a v t) = lookup b t := by
  simp [write, lookup, Run.lookup, hab]

theorem runsSorted_write {a : α} {v : Option β} {t : List (Run α β)} (h : EachSorted t) :
    EachSorted (write a v t) := by
  intro r hr
  simp only [write, List.mem_cons] at hr
  rcases hr with rfl | hr
  · exact Run.sorted_singleton _
  · exact h r hr

@[refl] theorem PreservesLookup.rfl {t : List (Run α β)} : PreservesLookup t t := fun _ => Eq.refl _

theorem PreservesLookup.trans {t₁ t₂ t₃ : List (Run α β)} (h₁ : PreservesLookup t₁ t₂)
    (h₂ : PreservesLookup t₂ t₃) : PreservesLookup t₁ t₃ := fun a => (h₁ a).trans (h₂ a)

@[refl] theorem PreservesGet.rfl {t : List (Run α β)} : PreservesGet t t := fun _ => Eq.refl _

theorem PreservesGet.trans {t₁ t₂ t₃ : List (Run α β)} (h₁ : PreservesGet t₁ t₂)
    (h₂ : PreservesGet t₂ t₃) : PreservesGet t₁ t₃ := fun a => (h₁ a).trans (h₂ a)

/-- A compaction that keeps every tombstone owes the client nothing extra: the stronger
obligation implies the weaker one, so a tombstone-preserving merge is still a legal compaction.
The converse fails, which is the whole point of having both. -/
theorem PreservesLookup.preservesGet {before after : List (Run α β)}
    (h : PreservesLookup before after) :
    PreservesGet before after := fun a => by simp only [get, h a]

end LSM

end AlgoDesign.Searching
