/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Query

/-!
# The 1D range tree: cost

dBCKO's query (`FINDSPLITNODE`, `1DRANGEQUERY`), counted through `Cslib.Algorithms.Lean.TimeM`:
from the root it goes left while `hi < split` and right while `split < lo`; at the split node it
follows `lo` down the left side, reporting each right subtree hanging off that path whole, and
`hi` down the right side, reporting each left subtree whole. One tick per node on those paths and
one per point a whole subtree reports, as the Rust and the Python run it (going left only when
`hi < split`, so copies of a split key on its right are kept). `ret_queryM`: on a tree whose keys
separate it answers what `query` answers. `time_queryM_le_height`: at most `2 h + k + 1` ticks
on a tree of height `h` reporting `k` points, and `height_le_clog`: a tree that halves is at most
`⌈log₂ n⌉` tall.
-/

@[expose] public section

namespace AlgoDesign.Geometry

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RangeTree1D

variable {α : Type}

/-- The number of steps from the root down to the deepest leaf. -/
def height : RangeTree1D α → ℕ
  | leaf _ => 0
  | node _ l r => max (height l) (height r) + 1

/-- Report a whole subtree: one tick per point. -/
def reportM (t : RangeTree1D α) : TimeM ℕ (List α) := do
  tick (leaves t).length
  pure (leaves t)

theorem ret_reportM (t : RangeTree1D α) : (reportM t).ret = leaves t := by
  simp [reportM]

theorem time_reportM (t : RangeTree1D α) : (reportM t).time = (leaves t).length := by
  simp [reportM]

variable [LinearOrder α]

/-- The leaf at the end of a path: one tick, and its key if it is in range. -/
def leafM (lo hi k : α) : TimeM ℕ (List α) := do
  tick 1
  pure (if lo ≤ k ∧ k ≤ hi then [k] else [])

/-- Follow `lo` down from the split node's left child, reporting the right subtree whole wherever
the path goes left. -/
def lowWalkM (lo hi : α) : RangeTree1D α → TimeM ℕ (List α)
  | leaf k => leafM lo hi k
  | node s l r => do
      tick 1
      if lo ≤ s then do
        let a ← lowWalkM lo hi l
        let b ← reportM r
        pure (a ++ b)
      else lowWalkM lo hi r

/-- Follow `hi` down from the split node's right child, reporting the left subtree whole wherever
the path goes right. -/
def highWalkM (lo hi : α) : RangeTree1D α → TimeM ℕ (List α)
  | leaf k => leafM lo hi k
  | node s l r => do
      tick 1
      if s ≤ hi then do
        let a ← reportM l
        let b ← highWalkM lo hi r
        pure (a ++ b)
      else highWalkM lo hi l

/-- The query, counted: down to the split node, then the two walks. -/
def queryM (lo hi : α) : RangeTree1D α → TimeM ℕ (List α)
  | leaf k => leafM lo hi k
  | node s l r => do
      tick 1
      if hi < s then queryM lo hi l
      else if s < lo then queryM lo hi r
      else do
        let a ← lowWalkM lo hi l
        let b ← highWalkM lo hi r
        pure (a ++ b)

/-- The strip test the promise filters by, as a `Bool`. -/
abbrev inRange (lo hi x : α) : Bool := decide (InStrip lo hi x)

theorem filter_eq_self_of {xs : List α} {lo hi : α} (h : ∀ x ∈ xs, lo ≤ x ∧ x ≤ hi) :
    xs.filter (inRange lo hi) = xs :=
  List.filter_eq_self.mpr fun x hx => by simpa using h x hx

theorem filter_eq_nil_of {xs : List α} {lo hi : α} (h : ∀ x ∈ xs, ¬ (lo ≤ x ∧ x ≤ hi)) :
    xs.filter (inRange lo hi) = [] :=
  List.filter_eq_nil_iff.mpr fun x hx => by simpa using h x hx

theorem ret_leafM (lo hi k : α) : (leafM lo hi k).ret = [k].filter (inRange lo hi) := by
  by_cases hk : lo ≤ k ∧ k ≤ hi <;> simp [leafM, hk]

/-- The `lo` walk reports the in-range keys of a subtree lying wholly at or below `hi`. -/
theorem ret_lowWalkM {lo hi : α} {t : RangeTree1D α} (h : KeysSeparate t)
    (hhi : ∀ x ∈ leaves t, x ≤ hi) :
    (lowWalkM lo hi t).ret = (leaves t).filter (inRange lo hi) := by
  induction t with
  | leaf k => exact ret_leafM lo hi k
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    have hhl : ∀ x ∈ leaves l, x ≤ hi := fun x hx => hhi x (by simp [leaves, hx])
    have hhr : ∀ x ∈ leaves r, x ≤ hi := fun x hx => hhi x (by simp [leaves, hx])
    simp only [lowWalkM, ret_bind, leaves, List.filter_append]
    split_ifs with hs
    · simp only [ret_bind, ret_pure, ihl hsl hhl, ret_reportM]
      rw [filter_eq_self_of fun x hx => ⟨hs.trans (hr x hx), hhr x hx⟩]
    · rw [ihr hsr hhr, filter_eq_nil_of fun x hx hin => hs (hin.1.trans (hl x hx)), List.nil_append]

/-- The `hi` walk reports the in-range keys of a subtree lying wholly at or above `lo`. -/
theorem ret_highWalkM {lo hi : α} {t : RangeTree1D α} (h : KeysSeparate t)
    (hlo : ∀ x ∈ leaves t, lo ≤ x) :
    (highWalkM lo hi t).ret = (leaves t).filter (inRange lo hi) := by
  induction t with
  | leaf k => exact ret_leafM lo hi k
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    have hll : ∀ x ∈ leaves l, lo ≤ x := fun x hx => hlo x (by simp [leaves, hx])
    have hlr : ∀ x ∈ leaves r, lo ≤ x := fun x hx => hlo x (by simp [leaves, hx])
    simp only [highWalkM, ret_bind, leaves, List.filter_append]
    split_ifs with hs
    · simp only [ret_bind, ret_pure, ihr hsr hlr, ret_reportM]
      rw [filter_eq_self_of fun x hx => ⟨hll x hx, (hl x hx).trans hs⟩]
    · rw [ihl hsl hll, filter_eq_nil_of fun x hx hin => hs ((hr x hx).trans hin.2),
        List.append_nil]

/-- **The counted query answers as the query does**, on a tree whose keys separate. -/
theorem ret_queryM {t : RangeTree1D α} (h : KeysSeparate t) (lo hi : α) :
    (queryM lo hi t).ret = query lo hi t := by
  rw [query_eq_filter h]
  induction t with
  | leaf k => exact ret_leafM lo hi k
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    simp only [queryM, ret_bind, leaves, List.filter_append]
    split_ifs with h1 h2
    · rw [ihl hsl, filter_eq_nil_of fun x hx hin => absurd (h1.trans_le ((hr x hx).trans hin.2))
        (lt_irrefl _), List.append_nil]
    · rw [ihr hsr, filter_eq_nil_of fun x hx hin => absurd ((hin.1.trans (hl x hx)).trans_lt h2)
        (lt_irrefl _), List.nil_append]
    · simp only [ret_bind, ret_pure]
      rw [ret_lowWalkM hsl fun x hx => (hl x hx).trans (not_lt.mp h1),
        ret_highWalkM hsr fun x hx => (not_lt.mp h2).trans (hr x hx)]

theorem time_leafM (lo hi k : α) : (leafM lo hi k).time = 1 := by
  simp [leafM]

/-- The `lo` walk: one path, plus one tick per point it reports. -/
theorem time_lowWalkM_le (lo hi : α) (t : RangeTree1D α) :
    (lowWalkM lo hi t).time ≤ height t + 1 + (lowWalkM lo hi t).ret.length := by
  induction t with
  | leaf k => simp [lowWalkM, time_leafM, height]
  | node s l r ihl ihr =>
    simp only [lowWalkM, time_bind, time_tick, ret_bind, height]
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, time_reportM, ret_reportM,
        List.length_append]
      have := le_max_left (height l) (height r)
      omega
    · have := le_max_right (height l) (height r)
      omega

/-- The `hi` walk: one path, plus one tick per point it reports. -/
theorem time_highWalkM_le (lo hi : α) (t : RangeTree1D α) :
    (highWalkM lo hi t).time ≤ height t + 1 + (highWalkM lo hi t).ret.length := by
  induction t with
  | leaf k => simp [highWalkM, time_leafM, height]
  | node s l r ihl ihr =>
    simp only [highWalkM, time_bind, time_tick, ret_bind, height]
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, time_reportM, ret_reportM,
        List.length_append]
      have := le_max_right (height l) (height r)
      omega
    · have := le_max_left (height l) (height r)
      omega

/-- The counted query: two paths, plus one tick per point reported, plus one. -/
theorem time_queryM_le_height (lo hi : α) (t : RangeTree1D α) :
    (queryM lo hi t).time ≤ 2 * height t + (queryM lo hi t).ret.length + 1 := by
  induction t with
  | leaf k => simp [queryM, time_leafM, height]
  | node s l r ihl ihr =>
    simp only [queryM, time_bind, time_tick, ret_bind, height]
    have := le_max_left (height l) (height r)
    have := le_max_right (height l) (height r)
    split_ifs
    · omega
    · omega
    · simp only [time_bind, time_pure, ret_bind, ret_pure, List.length_append]
      have := time_lowWalkM_le lo hi l
      have := time_highWalkM_le lo hi r
      omega

omit [LinearOrder α] in
theorem length_leaves_pos (t : RangeTree1D α) : 0 < (leaves t).length := by
  induction t with
  | leaf k => simp [leaves]
  | node s l r ihl _ => simp only [leaves, List.length_append]; omega

omit [LinearOrder α] in
/-- **A tree that halves is at most `⌈log₂ n⌉` tall**, for `n` stored keys. -/
theorem height_le_clog {t : RangeTree1D α} (h : SplitsHalve t) :
    height t ≤ Nat.clog 2 (leaves t).length := by
  induction t with
  | leaf k => simp [height]
  | node s l r ihl ihr =>
    obtain ⟨h1, h2, hl, hr⟩ := h
    have hpos : 0 < (leaves r).length := length_leaves_pos r
    have hn : (leaves (node s l r)).length = (leaves l).length + (leaves r).length := by
      simp [leaves]
    rw [hn, height, Nat.clog_of_two_le (by decide) (by omega)]
    have hhalf : ((leaves l).length + (leaves r).length + 2 - 1) / 2 = (leaves l).length := by
      omega
    rw [hhalf]
    have := Nat.clog_mono_right 2 h1
    have := ihl hl
    have := ihr hr
    omega

/-- **The cost the box states:** on a valid tree of `n` keys, a query reporting `k` points takes
at most `2 ⌈log₂ n⌉ + k + 1` ticks. -/
theorem time_queryM_le {t : RangeTree1D α} (h : Valid t) (lo hi : α) :
    (queryM lo hi t).time ≤ 2 * Nat.clog 2 (leaves t).length + (query lo hi t).length + 1 := by
  have ht := time_queryM_le_height lo hi t
  have hh := height_le_clog h.2
  rw [ret_queryM h.1] at ht
  omega

end RangeTree1D
end AlgoDesign.Geometry
