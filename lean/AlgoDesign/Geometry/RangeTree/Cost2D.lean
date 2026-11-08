/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Cost
public import AlgoDesign.Geometry.RangeTree.Query2D

/-!
# The 2D range tree: the query as the Rust and the Python run it, counted

dBCKO `2DRANGEQUERY`, counted through `Cslib.Algorithms.Lean.TimeM`. An empty rectangle answers
nothing at once. Otherwise the walk goes down the tree on the first coordinate to the split node,
left while `hi < split` and right while `split < lo`; from there it follows `lo` down the left
side and `hi` down the right side. A subtree hanging inside the two paths is reported first: a
leaf by testing its point, an inner node by a 1D query of its stored associated tree on the
second coordinate (`yQueryM`, the 1D walk of `Cost.lean` on that coordinate). Each path ends at a
leaf, whose point is tested on both coordinates.

One tick per node on the walk's paths, one per node on an associated tree's paths, and one per
point reported, as in the 1D count. `queryM_spec`: the counted walk answers every stored point in
the rectangle, each as often as stored, and nothing else (`Query2DSpec`). `time_queryM_le`: at
most `4 ⌈log₂ n⌉ (⌈log₂ n⌉ + 1) + k + 1` ticks for `n` points and `k` reported, from
`time_walkM_le_height` (two paths of the tree's height, each node on them paying for one
associated query of at most `2 ⌈log₂ n⌉ + 1` steps beside its points: the associated tree halves,
so it is at most `⌈log₂ n⌉` tall) and `height_buildSorted` (the build is at most `⌈log₂ n⌉`
tall).
-/

@[expose] public section

namespace AlgoDesign.Geometry

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RangeTree2D

open RangeTree1D (half take_half_ne_nil drop_half_ne_nil leaves reportM)

variable {α : Type} [LinearOrder α]

/-! ## The associated tree: a 1D tree on the second coordinate -/

/-- The leaf at the end of an associated path: one tick, and its point if it is in range on the
second coordinate. -/
def yLeafM (lo hi p : Point 2 α) : TimeM ℕ (List (Point 2 α)) := do
  tick 1
  pure (if inY lo hi p then [p] else [])

/-- Follow `lo` down an associated tree, reporting the right subtree whole wherever the path goes
left. -/
def yLowWalkM (lo hi : Point 2 α) : RangeTree1D (Point 2 α) → TimeM ℕ (List (Point 2 α))
  | .leaf p => yLeafM lo hi p
  | .node s l r => do
      tick 1
      if lo 1 ≤ s 1 then do
        let a ← yLowWalkM lo hi l
        let b ← reportM r
        pure (a ++ b)
      else yLowWalkM lo hi r

/-- Follow `hi` down an associated tree, reporting the left subtree whole wherever the path goes
right. -/
def yHighWalkM (lo hi : Point 2 α) : RangeTree1D (Point 2 α) → TimeM ℕ (List (Point 2 α))
  | .leaf p => yLeafM lo hi p
  | .node s l r => do
      tick 1
      if s 1 ≤ hi 1 then do
        let a ← reportM l
        let b ← yHighWalkM lo hi r
        pure (a ++ b)
      else yHighWalkM lo hi l

/-- The 1D query on the second coordinate, counted: down to the split node, then the two walks. -/
def yQueryM (lo hi : Point 2 α) : RangeTree1D (Point 2 α) → TimeM ℕ (List (Point 2 α))
  | .leaf p => yLeafM lo hi p
  | .node s l r => do
      tick 1
      if hi 1 < s 1 then yQueryM lo hi l
      else if s 1 < lo 1 then yQueryM lo hi r
      else do
        let a ← yLowWalkM lo hi l
        let b ← yHighWalkM lo hi r
        pure (a ++ b)

theorem filter_inY_eq_self {xs : List (Point 2 α)} {lo hi : Point 2 α}
    (h : ∀ p ∈ xs, lo 1 ≤ p 1 ∧ p 1 ≤ hi 1) : xs.filter (inY lo hi) = xs :=
  List.filter_eq_self.mpr fun p hp => by simpa [inY] using h p hp

theorem filter_inY_eq_nil {xs : List (Point 2 α)} {lo hi : Point 2 α}
    (h : ∀ p ∈ xs, ¬ (lo 1 ≤ p 1 ∧ p 1 ≤ hi 1)) : xs.filter (inY lo hi) = [] :=
  List.filter_eq_nil_iff.mpr fun p hp => by simpa [inY] using h p hp

theorem ret_yLeafM (lo hi p : Point 2 α) : (yLeafM lo hi p).ret = [p].filter (inY lo hi) := by
  by_cases hp : inY lo hi p <;> simp [yLeafM, hp]

/-- The `lo` walk reports the in-range points of an associated subtree lying wholly at or below
`hi` on the second coordinate. -/
theorem ret_yLowWalkM {lo hi : Point 2 α} {t : RangeTree1D (Point 2 α)} (h : YSeparate t)
    (hhi : ∀ p ∈ leaves t, p 1 ≤ hi 1) :
    (yLowWalkM lo hi t).ret = (leaves t).filter (inY lo hi) := by
  induction t with
  | leaf p => exact ret_yLeafM lo hi p
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    have hhl : ∀ p ∈ leaves l, p 1 ≤ hi 1 := fun p hp => hhi p (by simp [leaves, hp])
    have hhr : ∀ p ∈ leaves r, p 1 ≤ hi 1 := fun p hp => hhi p (by simp [leaves, hp])
    simp only [yLowWalkM, ret_bind, leaves, List.filter_append]
    split_ifs with hs
    · simp only [ret_bind, ret_pure, ihl hsl hhl, RangeTree1D.ret_reportM]
      rw [filter_inY_eq_self fun p hp => ⟨hs.trans (hr p hp), hhr p hp⟩]
    · rw [ihr hsr hhr, filter_inY_eq_nil fun p hp hin => hs (hin.1.trans (hl p hp)),
        List.nil_append]

/-- The `hi` walk reports the in-range points of an associated subtree lying wholly at or above
`lo` on the second coordinate. -/
theorem ret_yHighWalkM {lo hi : Point 2 α} {t : RangeTree1D (Point 2 α)} (h : YSeparate t)
    (hlo : ∀ p ∈ leaves t, lo 1 ≤ p 1) :
    (yHighWalkM lo hi t).ret = (leaves t).filter (inY lo hi) := by
  induction t with
  | leaf p => exact ret_yLeafM lo hi p
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    have hll : ∀ p ∈ leaves l, lo 1 ≤ p 1 := fun p hp => hlo p (by simp [leaves, hp])
    have hlr : ∀ p ∈ leaves r, lo 1 ≤ p 1 := fun p hp => hlo p (by simp [leaves, hp])
    simp only [yHighWalkM, ret_bind, leaves, List.filter_append]
    split_ifs with hs
    · simp only [ret_bind, ret_pure, ihr hsr hlr, RangeTree1D.ret_reportM]
      rw [filter_inY_eq_self fun p hp => ⟨hll p hp, (hl p hp).trans hs⟩]
    · rw [ihl hsl hll, filter_inY_eq_nil fun p hp hin => hs ((hr p hp).trans hin.2),
        List.append_nil]

/-- The query on the second coordinate answers the in-range points of an associated tree whose
keys separate, in order. -/
theorem ret_yQueryM {lo hi : Point 2 α} {t : RangeTree1D (Point 2 α)} (h : YSeparate t) :
    (yQueryM lo hi t).ret = (leaves t).filter (inY lo hi) := by
  induction t with
  | leaf p => exact ret_yLeafM lo hi p
  | node s l r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := h
    simp only [yQueryM, ret_bind, leaves, List.filter_append]
    split_ifs with h1 h2
    · rw [ihl hsl, filter_inY_eq_nil fun p hp hin =>
        absurd (h1.trans_le ((hr p hp).trans hin.2)) (lt_irrefl _), List.append_nil]
    · rw [ihr hsr, filter_inY_eq_nil fun p hp hin =>
        absurd ((hin.1.trans (hl p hp)).trans_lt h2) (lt_irrefl _), List.nil_append]
    · simp only [ret_bind, ret_pure]
      rw [ret_yLowWalkM hsl fun p hp => (hl p hp).trans (not_lt.mp h1),
        ret_yHighWalkM hsr fun p hp => (not_lt.mp h2).trans (hr p hp)]

theorem time_yLeafM (lo hi p : Point 2 α) : (yLeafM lo hi p).time = 1 := by
  simp [yLeafM]

theorem time_yLowWalkM_le (lo hi : Point 2 α) (t : RangeTree1D (Point 2 α)) :
    (yLowWalkM lo hi t).time ≤ t.height + 1 + (yLowWalkM lo hi t).ret.length := by
  induction t with
  | leaf p => simp [yLowWalkM, time_yLeafM, RangeTree1D.height]
  | node s l r ihl ihr =>
    simp only [yLowWalkM, time_bind, time_tick, ret_bind, RangeTree1D.height]
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, RangeTree1D.time_reportM,
        RangeTree1D.ret_reportM, List.length_append]
      have := le_max_left l.height r.height
      omega
    · have := le_max_right l.height r.height
      omega

theorem time_yHighWalkM_le (lo hi : Point 2 α) (t : RangeTree1D (Point 2 α)) :
    (yHighWalkM lo hi t).time ≤ t.height + 1 + (yHighWalkM lo hi t).ret.length := by
  induction t with
  | leaf p => simp [yHighWalkM, time_yLeafM, RangeTree1D.height]
  | node s l r ihl ihr =>
    simp only [yHighWalkM, time_bind, time_tick, ret_bind, RangeTree1D.height]
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, RangeTree1D.time_reportM,
        RangeTree1D.ret_reportM, List.length_append]
      have := le_max_right l.height r.height
      omega
    · have := le_max_left l.height r.height
      omega

theorem time_yQueryM_le_height (lo hi : Point 2 α) (t : RangeTree1D (Point 2 α)) :
    (yQueryM lo hi t).time ≤ 2 * t.height + (yQueryM lo hi t).ret.length + 1 := by
  induction t with
  | leaf p => simp [yQueryM, time_yLeafM, RangeTree1D.height]
  | node s l r ihl ihr =>
    simp only [yQueryM, time_bind, time_tick, ret_bind, RangeTree1D.height]
    have := le_max_left l.height r.height
    have := le_max_right l.height r.height
    split_ifs
    · omega
    · omega
    · simp only [time_bind, time_pure, ret_bind, ret_pure, List.length_append]
      have := time_yLowWalkM_le lo hi l
      have := time_yHighWalkM_le lo hi r
      omega

/-! ## The walk on the first coordinate -/

/-- The leaf at the end of a path: one tick, and its point if it is in the rectangle. -/
def leafM (lo hi p : Point 2 α) : TimeM ℕ (List (Point 2 α)) := do
  tick 1
  pure (if InRectangle lo hi p then [p] else [])

/-- A subtree lying inside the range on the first coordinate: a leaf tests its point, an inner
node queries its associated tree on the second coordinate. -/
def reportSubtreeM (lo hi : Point 2 α) : RangeTree2D α → TimeM ℕ (List (Point 2 α))
  | .leaf p => leafM lo hi p
  | .node _ A _ _ => yQueryM lo hi A

/-- Follow `lo` down from the split node's left child: wherever the path goes left, the right
subtree is reported first. -/
def lowWalkM (lo hi : Point 2 α) : RangeTree2D α → TimeM ℕ (List (Point 2 α))
  | .leaf p => leafM lo hi p
  | .node s _ l r => do
      tick 1
      if lo 0 ≤ s then do
        let b ← reportSubtreeM lo hi r
        let a ← lowWalkM lo hi l
        pure (b ++ a)
      else lowWalkM lo hi r

/-- Follow `hi` down from the split node's right child: wherever the path goes right, the left
subtree is reported first. -/
def highWalkM (lo hi : Point 2 α) : RangeTree2D α → TimeM ℕ (List (Point 2 α))
  | .leaf p => leafM lo hi p
  | .node s _ l r => do
      tick 1
      if s ≤ hi 0 then do
        let a ← reportSubtreeM lo hi l
        let b ← highWalkM lo hi r
        pure (a ++ b)
      else highWalkM lo hi l

/-- Down to the split node on the first coordinate, then the two walks. -/
def walkM (lo hi : Point 2 α) : RangeTree2D α → TimeM ℕ (List (Point 2 α))
  | .leaf p => leafM lo hi p
  | .node s _ l r => do
      tick 1
      if hi 0 < s then walkM lo hi l
      else if s < lo 0 then walkM lo hi r
      else do
        let a ← lowWalkM lo hi l
        let b ← highWalkM lo hi r
        pure (a ++ b)

/-- **The 2D query, counted** (dBCKO `2DRANGEQUERY`, as the Rust and the Python run it): no tree,
or a rectangle empty on either coordinate, answers nothing at once; otherwise the walk. -/
def queryM (lo hi : Point 2 α) : Option (RangeTree2D α) → TimeM ℕ (List (Point 2 α))
  | none => pure []
  | some t => if hi 0 < lo 0 ∨ hi 1 < lo 1 then pure [] else walkM lo hi t

/-! ## The counted query answers the rectangle -/

theorem ret_leafM (lo hi p : Point 2 α) :
    (leafM lo hi p).ret = (points (.leaf p)).filter (InRectangle lo hi ·) := by
  simp only [leafM, ret_bind, ret_pure, points, List.filter_singleton]
  by_cases hp : InRectangle lo hi p
  · simp only [decide_eq_true hp, Bool.cond_true]; split_ifs; rfl
  · simp only [decide_eq_false hp, Bool.cond_false]; split_ifs; rfl

/-- No point of a list is in the rectangle when all lie past one of its edges. -/
theorem filter_rect_eq_nil {xs : List (Point 2 α)} {lo hi : Point 2 α}
    (h : ∀ p ∈ xs, ¬ (lo 0 ≤ p 0 ∧ p 0 ≤ hi 0)) : xs.filter (InRectangle lo hi ·) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp hin
  simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
  exact h p hp hin.1

/-- A subtree lying inside the range on the first coordinate reports its points in the rectangle,
in some order. -/
theorem ret_reportSubtreeM {lo hi : Point 2 α} {t : RangeTree2D α} (ha : Assembled t)
    (hx : ∀ p ∈ points t, lo 0 ≤ p 0 ∧ p 0 ≤ hi 0) :
    (reportSubtreeM lo hi t).ret.Perm ((points t).filter (InRectangle lo hi ·)) := by
  cases t with
  | leaf p => rw [reportSubtreeM, ret_leafM]
  | node s A l r =>
    obtain ⟨-, -, hA, hy, -, -, -⟩ := ha
    rw [reportSubtreeM, ret_yQueryM hy]
    refine (hA.filter _).trans (List.Perm.of_eq (List.filter_congr fun p hp => ?_))
    simp only [inY, InRectangle, Fin.forall_fin_two, decide_eq_decide]
    exact ⟨fun h => ⟨hx p hp, h⟩, fun h => h.2⟩

/-- The `lo` walk reports the points in the rectangle of a subtree lying wholly at or below `hi`
on the first coordinate. -/
theorem ret_lowWalkM {lo hi : Point 2 α} {t : RangeTree2D α} (ha : Assembled t)
    (hhi : ∀ p ∈ points t, p 0 ≤ hi 0) :
    (lowWalkM lo hi t).ret.Perm ((points t).filter (InRectangle lo hi ·)) := by
  induction t with
  | leaf p => rw [lowWalkM, ret_leafM]
  | node s A l r ihl ihr =>
    obtain ⟨hl, hr, -, -, -, hal, har⟩ := ha
    have hhl : ∀ p ∈ points l, p 0 ≤ hi 0 := fun p hp => hhi p (List.mem_append_left _ hp)
    have hhr : ∀ p ∈ points r, p 0 ≤ hi 0 := fun p hp => hhi p (List.mem_append_right _ hp)
    simp only [lowWalkM, ret_bind, points, List.filter_append]
    split_ifs with h
    · simp only [ret_bind, ret_pure]
      exact ((ret_reportSubtreeM har fun p hp => ⟨h.trans (hr p hp), hhr p hp⟩).append
        (ihl hal hhl)).trans List.perm_append_comm
    · rw [filter_rect_eq_nil fun p hp hin => h (hin.1.trans (hl p hp)), List.nil_append]
      exact ihr har hhr

/-- The `hi` walk reports the points in the rectangle of a subtree lying wholly at or above `lo`
on the first coordinate. -/
theorem ret_highWalkM {lo hi : Point 2 α} {t : RangeTree2D α} (ha : Assembled t)
    (hlo : ∀ p ∈ points t, lo 0 ≤ p 0) :
    (highWalkM lo hi t).ret.Perm ((points t).filter (InRectangle lo hi ·)) := by
  induction t with
  | leaf p => rw [highWalkM, ret_leafM]
  | node s A l r ihl ihr =>
    obtain ⟨hl, hr, -, -, -, hal, har⟩ := ha
    have hll : ∀ p ∈ points l, lo 0 ≤ p 0 := fun p hp => hlo p (List.mem_append_left _ hp)
    have hlr : ∀ p ∈ points r, lo 0 ≤ p 0 := fun p hp => hlo p (List.mem_append_right _ hp)
    simp only [highWalkM, ret_bind, points, List.filter_append]
    split_ifs with h
    · simp only [ret_bind, ret_pure]
      exact (ret_reportSubtreeM hal fun p hp => ⟨hll p hp, (hl p hp).trans h⟩).append
        (ihr har hlr)
    · rw [filter_rect_eq_nil fun p hp hin => h ((hr p hp).trans hin.2), List.append_nil]
      exact ihl hal hll

/-- The walk reports the points of an assembled tree in the rectangle, in some order. -/
theorem ret_walkM {lo hi : Point 2 α} {t : RangeTree2D α} (ha : Assembled t) :
    (walkM lo hi t).ret.Perm ((points t).filter (InRectangle lo hi ·)) := by
  induction t with
  | leaf p => rw [walkM, ret_leafM]
  | node s A l r ihl ihr =>
    obtain ⟨hl, hr, -, -, -, hal, har⟩ := ha
    simp only [walkM, ret_bind, points, List.filter_append]
    split_ifs with h1 h2
    · rw [filter_rect_eq_nil (xs := points r) fun p hp hin =>
        absurd (h1.trans_le ((hr p hp).trans hin.2)) (lt_irrefl _), List.append_nil]
      exact ihl hal
    · rw [filter_rect_eq_nil (xs := points l) fun p hp hin =>
        absurd ((hin.1.trans (hl p hp)).trans_lt h2) (lt_irrefl _), List.nil_append]
      exact ihr har
    · simp only [ret_bind, ret_pure]
      exact (ret_lowWalkM hal fun p hp => (hl p hp).trans (not_lt.mp h1)).append
        (ret_highWalkM har fun p hp => (not_lt.mp h2).trans (hr p hp))

/-- **The counted 2D query meets the 2D obligation** (`Query2DSpec`): built over any points, the
empty list included, the walk the Rust and the Python run answers every stored point inside the
rectangle, edges included, each as often as it is stored, and nothing else, in some order. -/
theorem queryM_spec : Query2DSpec (α := α) build (fun lo hi o => (queryM lo hi o).ret) := by
  intro ps lo hi
  have hperm := List.mergeSort_perm ps (fun a b => decide (a 0 ≤ b 0))
  simp only [build]
  split_ifs with h
  · rw [h] at hperm
    simp [queryM, hperm.symm.eq_nil]
  · have hs : (ps.mergeSort (fun a b => decide (a 0 ≤ b 0))).Pairwise (fun a b => a 0 ≤ b 0) :=
      (List.pairwise_mergeSort
        (fun _ _ _ hab hbc =>
          decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
        (fun a b => by simpa using le_total (a 0) (b 0)) ps).imp (of_decide_eq_true ·)
    simp only [queryM]
    split_ifs with he
    · have hnil : ps.filter (InRectangle lo hi ·) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p _ hin
        simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
        rcases he with he | he
        · exact absurd ((hin.1.1.trans hin.1.2).trans_lt he) (lt_irrefl _)
        · exact absurd ((hin.2.1.trans hin.2.2).trans_lt he) (lt_irrefl _)
      rw [hnil]
      rfl
    · refine (ret_walkM (assembled_buildSorted _ h hs)).trans ?_
      rw [points_buildSorted]
      exact hperm.filter _

/-- The counted query answers what the specification-level query answers, in some order. -/
theorem queryM_perm_query (ps : List (Point 2 α)) (lo hi : Point 2 α) :
    (queryM lo hi (build ps)).ret.Perm (query lo hi (build ps)) :=
  (queryM_spec ps lo hi).trans (query_build ps lo hi).symm

/-! ## The cost -/

/-- The number of steps from the root down to the deepest leaf of the tree on the first
coordinate. -/
def height : RangeTree2D α → ℕ
  | .leaf _ => 0
  | .node _ _ l r => max (height l) (height r) + 1

theorem time_leafM (lo hi p : Point 2 α) : (leafM lo hi p).time = 1 := by
  simp [leafM]

/-- A subtree of at most `n` points is reported in at most `2 ⌈log₂ n⌉ + 1` ticks beside one per
point. -/
theorem time_reportSubtreeM_le {lo hi : Point 2 α} {t : RangeTree2D α} {n : ℕ} (ha : Assembled t)
    (hn : (points t).length ≤ n) :
    (reportSubtreeM lo hi t).time ≤ 2 * Nat.clog 2 n + 1 + (reportSubtreeM lo hi t).ret.length := by
  cases t with
  | leaf p => simp only [reportSubtreeM, time_leafM]; omega
  | node s A l r =>
    obtain ⟨-, -, hA, -, hsh, -, -⟩ := ha
    simp only [reportSubtreeM]
    have hlen : (leaves A).length ≤ n := by rw [hA.length_eq]; exact hn
    have := Nat.clog_mono_right 2 hlen
    have := RangeTree1D.height_le_clog hsh
    have := time_yQueryM_le_height lo hi A
    omega

omit [LinearOrder α] in
theorem length_points_le_left {s : α} {A : RangeTree1D (Point 2 α)} {l r : RangeTree2D α} {n : ℕ}
    (hn : (points (.node s A l r)).length ≤ n) : (points l).length ≤ n := by
  simp only [points, List.length_append] at hn; omega

omit [LinearOrder α] in
theorem length_points_le_right {s : α} {A : RangeTree1D (Point 2 α)} {l r : RangeTree2D α} {n : ℕ}
    (hn : (points (.node s A l r)).length ≤ n) : (points r).length ≤ n := by
  simp only [points, List.length_append] at hn; omega

/-- The `lo` walk: one path, each node on it paying for one subtree's report, plus one tick per
point. -/
theorem time_lowWalkM_le {lo hi : Point 2 α} {t : RangeTree2D α} {n : ℕ} (ha : Assembled t)
    (hn : (points t).length ≤ n) :
    (lowWalkM lo hi t).time ≤
      height t * (2 * Nat.clog 2 n + 2) + 1 + (lowWalkM lo hi t).ret.length := by
  induction t with
  | leaf p => simp [lowWalkM, time_leafM, height]
  | node s A l r ihl ihr =>
    obtain ⟨-, -, -, -, -, hal, har⟩ := ha
    have hnl := length_points_le_left hn
    have hnr := length_points_le_right hn
    simp only [lowWalkM, time_bind, time_tick, ret_bind, height]
    generalize hc : 2 * Nat.clog 2 n + 2 = c at *
    have hml := Nat.mul_le_mul_right c (le_max_left (height l) (height r))
    have hmr := Nat.mul_le_mul_right c (le_max_right (height l) (height r))
    have hsucc : (max (height l) (height r) + 1) * c = max (height l) (height r) * c + c :=
      Nat.succ_mul _ _
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, List.length_append]
      have := time_reportSubtreeM_le (lo := lo) (hi := hi) har hnr
      have := ihl hal hnl
      omega
    · have := ihr har hnr
      omega

/-- The `hi` walk: one path, each node on it paying for one subtree's report, plus one tick per
point. -/
theorem time_highWalkM_le {lo hi : Point 2 α} {t : RangeTree2D α} {n : ℕ} (ha : Assembled t)
    (hn : (points t).length ≤ n) :
    (highWalkM lo hi t).time ≤
      height t * (2 * Nat.clog 2 n + 2) + 1 + (highWalkM lo hi t).ret.length := by
  induction t with
  | leaf p => simp [highWalkM, time_leafM, height]
  | node s A l r ihl ihr =>
    obtain ⟨-, -, -, -, -, hal, har⟩ := ha
    have hnl := length_points_le_left hn
    have hnr := length_points_le_right hn
    simp only [highWalkM, time_bind, time_tick, ret_bind, height]
    generalize hc : 2 * Nat.clog 2 n + 2 = c at *
    have hml := Nat.mul_le_mul_right c (le_max_left (height l) (height r))
    have hmr := Nat.mul_le_mul_right c (le_max_right (height l) (height r))
    have hsucc : (max (height l) (height r) + 1) * c = max (height l) (height r) * c + c :=
      Nat.succ_mul _ _
    split_ifs
    · simp only [time_bind, time_pure, ret_bind, ret_pure, List.length_append]
      have := time_reportSubtreeM_le (lo := lo) (hi := hi) hal hnl
      have := ihr har hnr
      omega
    · have := ihl hal hnl
      omega

/-- **The walk's cost, by height**: on an assembled tree of height `h` over at most `n` points,
two paths of `h` nodes, each paying for one associated query of at most `2 ⌈log₂ n⌉ + 1` steps,
plus one tick per point reported, plus one. -/
theorem time_walkM_le_height {lo hi : Point 2 α} {t : RangeTree2D α} {n : ℕ} (ha : Assembled t)
    (hn : (points t).length ≤ n) :
    (walkM lo hi t).time ≤
      2 * (height t * (2 * Nat.clog 2 n + 2)) + (walkM lo hi t).ret.length + 1 := by
  induction t with
  | leaf p => simp [walkM, time_leafM, height]
  | node s A l r ihl ihr =>
    obtain ⟨-, -, -, -, -, hal, har⟩ := ha
    have hnl := length_points_le_left hn
    have hnr := length_points_le_right hn
    simp only [walkM, time_bind, time_tick, ret_bind, height]
    have hlow := time_lowWalkM_le (lo := lo) (hi := hi) hal hnl
    have hhigh := time_highWalkM_le (lo := lo) (hi := hi) har hnr
    generalize hc : 2 * Nat.clog 2 n + 2 = c at *
    have hml := Nat.mul_le_mul_right c (le_max_left (height l) (height r))
    have hmr := Nat.mul_le_mul_right c (le_max_right (height l) (height r))
    have hc : 2 ≤ c := by omega
    have hsucc : (max (height l) (height r) + 1) * c = max (height l) (height r) * c + c :=
      Nat.succ_mul _ _
    split_ifs
    · have := ihl hal hnl
      omega
    · have := ihr har hnr
      omega
    · simp only [time_bind, time_pure, ret_bind, ret_pure, List.length_append]
      omega

/-- **The 2D build is at most `⌈log₂ n⌉` tall**: every node sends `⌈m/2⌉` of its `m` points
left. -/
theorem height_buildSorted (xs : List (Point 2 α)) (h : xs ≠ []) :
    height (buildSorted xs h) ≤ Nat.clog 2 xs.length := by
  rw [buildSorted]
  split_ifs with hlen
  · simp [height]
  · simp only [height]
    have hl := height_buildSorted (xs.take (half xs)) (take_half_ne_nil h)
    have hr := height_buildSorted (xs.drop (half xs)) (drop_half_ne_nil hlen)
    have h1 : (xs.take (half xs)).length = (xs.length + 2 - 1) / 2 := by
      simp only [List.length_take, half]; omega
    have h2 : (xs.drop (half xs)).length ≤ (xs.length + 2 - 1) / 2 := by
      simp only [List.length_drop, half]; omega
    rw [h1] at hl
    have := Nat.clog_mono_right 2 h2
    rw [Nat.clog_of_two_le (by decide) (by omega)]
    omega
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- **The cost of the 2D query** (dBCKO §5.3, `O(log² n + k)`): over `n` points, a query reporting
`k` of them takes at most `4 ⌈log₂ n⌉ (⌈log₂ n⌉ + 1) + k + 1` ticks: two paths of at most
`⌈log₂ n⌉` nodes, each node on them paying for one associated query of at most `2 ⌈log₂ n⌉ + 1`
steps, plus one tick per point reported, plus one. -/
theorem time_queryM_le (ps : List (Point 2 α)) (lo hi : Point 2 α) :
    (queryM lo hi (build ps)).time ≤
      4 * Nat.clog 2 ps.length * (Nat.clog 2 ps.length + 1) +
        (ps.filter (InRectangle lo hi ·)).length + 1 := by
  have hk := (queryM_spec ps lo hi).length_eq
  have hperm := List.mergeSort_perm ps (fun a b => decide (a 0 ≤ b 0))
  by_cases h : ps.mergeSort (fun a b => decide (a 0 ≤ b 0)) = []
  · have hb : build ps = none := by unfold build; simp [h]
    rw [hb]
    simp [queryM]
  · have hb : build ps = some (buildSorted _ h) := by unfold build; simp [h]
    rw [hb] at hk ⊢
    simp only [queryM] at hk ⊢
    split_ifs at hk ⊢ with he
    · simp
    · have ha := assembled_buildSorted _ h ((List.pairwise_mergeSort
        (fun _ _ _ hab hbc =>
          decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
        (fun a b => by simpa using le_total (a 0) (b 0)) ps).imp (of_decide_eq_true ·))
      have hn : (points (buildSorted _ h)).length ≤ ps.length := by
        rw [points_buildSorted, hperm.length_eq]
      have ht := time_walkM_le_height (lo := lo) (hi := hi) ha hn
      have hh := height_buildSorted _ h
      rw [hperm.length_eq] at hh
      have hm := Nat.mul_le_mul_right (2 * Nat.clog 2 ps.length + 2) hh
      have : 2 * (Nat.clog 2 ps.length * (2 * Nat.clog 2 ps.length + 2)) =
          4 * Nat.clog 2 ps.length * (Nat.clog 2 ps.length + 1) := by ring
      omega

end RangeTree2D
end AlgoDesign.Geometry
