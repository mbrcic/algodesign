/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Spec
public import Mathlib.Data.List.Basic

/-!
# The 1D range tree: the query

The query as a specification-level traversal: it descends into a side whenever the range can
reach it, entering the right side whenever `split ≤ hi`, so copies of a split key on both sides
are all reported. `query_eq_filter` is the promise: on a tree whose keys separate, the answer is
the stored keys in the strip `[lo, hi]` (`InStrip`), in order and with multiplicity. The walk
dBCKO give, which the Rust and the Python run, is `queryM` (`Cost.lean`), and it answers the same
(`ret_queryM`).
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace RangeTree1D

variable {α : Type} [LinearOrder α]

/-- Report every leaf in `[lo, hi]`, skipping a side the range cannot reach. -/
def query (lo hi : α) : RangeTree1D α → List α
  | leaf k => if lo ≤ k ∧ k ≤ hi then [k] else []
  | node s l r =>
      (if lo ≤ s then query lo hi l else []) ++ (if s ≤ hi then query lo hi r else [])

/-- **The range tree's promise.** On a tree whose keys separate, the query reports exactly the
in-range leaves, in order, each once. -/
theorem query_eq_filter {t : RangeTree1D α} (h : KeysSeparate t) (lo hi : α) :
    query lo hi t = (leaves t).filter (InStrip lo hi ·) := by
  induction t with
  | leaf k =>
    by_cases hk : lo ≤ k ∧ k ≤ hi <;> simp [query, leaves, hk]
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    simp only [query, leaves, List.filter_append]
    congr 1
    · split_ifs with hs
      · exact ihl hsl
      · symm
        rw [List.filter_eq_nil_iff]
        intro x hx hin
        simp only [decide_eq_true_eq] at hin
        exact hs (hin.1.trans (hl x hx))
    · split_ifs with hs
      · exact ihr hsr
      · symm
        rw [List.filter_eq_nil_iff]
        intro x hx hin
        simp only [decide_eq_true_eq] at hin
        exact hs ((hr x hx).trans hin.2)

end RangeTree1D
end AlgoDesign.Geometry
