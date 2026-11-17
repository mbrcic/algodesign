/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.RangeTree.Build

/-!
# The 2D range tree: the build and the query

dBCKO §5.3 (`2DRANGEQUERY`). The build sorts the points by their first coordinate and halves them
as the 1D build halves its keys (`RangeTree1D.half`): the first `⌈n/2⌉` go left and the split is
the first coordinate of the last of them, the lower median. Every inner node also carries its
associated tree: the 1D build (`RangeTree1D.build`) over the points below it sorted by the second
coordinate, so each of its inner keys is the point at the lower median, compared on the second
coordinate, as the Rust's and the Python's `RangeTree1D::from_sorted` build it. The query here
walks the tree on the first coordinate; a subtree known to lie wholly inside the range on that
coordinate is answered by filtering its associated tree's points on the second coordinate (dBCKO
query it by a 1D range search, which `Cost2D.lean`'s `queryM` runs; the answer is the same).

`query_build` proves `Query2DSpec`: the query answers every stored point
inside the rectangle, each as often as it is stored, and nothing else, in some order. The proof
goes through `Assembled`, what the build guarantees of every tree it makes: each split separates
its two sides on the first coordinate, and each associated tree holds exactly the points below its
node, separates them on the second coordinate and halves them.
-/

@[expose] public section

namespace AlgoDesign.Geometry

/-- The 2D range tree (dBCKO §5.3), as the Rust and the Python build it: a range tree on the first
coordinate whose every inner node also holds its **associated tree**, a 1D range tree of the
points below it on the second coordinate (points in its leaves, each inner key the point at the
lower median, compared on the second coordinate). The type itself holds none of this:
`Assembled` (`Query2D.lean`) states what the query needs, that each split separates its two
sides on the first coordinate, and each associated tree holds exactly the points below its node,
separates them on the second coordinate and halves them. -/
inductive RangeTree2D (α : Type) where
  /-- A leaf holds one point. -/
  | leaf (p : Point 2 α)
  /-- An inner node: a split on the first coordinate, the associated tree of the points below it
  on the second, and its two sides. -/
  | node (split : α) (assoc : RangeTree1D (Point 2 α)) (l r : RangeTree2D α)

namespace RangeTree2D

variable {α : Type} [LinearOrder α]

/-- The 2D range tree's query. Built over any points, the empty list included, a 2D tree answers
a rectangle query with every stored point inside the rectangle, edges included, each as often as
it is stored, and nothing else, in any order. `query_build` (`Query2D.lean`) proves it of the
Lean build and query. -/
def Query2DSpec (build : List (Point 2 α) → Option (RangeTree2D α))
    (query : Point 2 α → Point 2 α → Option (RangeTree2D α) → List (Point 2 α)) : Prop :=
  ∀ ps lo hi, (query lo hi (build ps)).Perm (ps.filter (InRectangle lo hi ·))

end RangeTree2D

namespace RangeTree2D

open RangeTree1D (half take_half_ne_nil drop_half_ne_nil leaves)

variable {α : Type} [LinearOrder α]

/-- The stored points, the leaves left to right. -/
def points : RangeTree2D α → List (Point 2 α)
  | .leaf p => [p]
  | .node _ _ l r => points l ++ points r

omit [LinearOrder α] in
theorem mergeSort_ne_nil {xs : List (Point 2 α)} {f : Point 2 α → Point 2 α → Bool}
    (h : xs ≠ []) : xs.mergeSort f ≠ [] := by
  intro h'
  have hp := List.mergeSort_perm xs f
  rw [h'] at hp
  exact h hp.symm.eq_nil

/-- Build over points already sorted by the first coordinate: the first `⌈n/2⌉` go left, the split
is the first coordinate of the last of them (the lower median), and every inner node carries the
points below it sorted by the second coordinate. -/
def buildSorted (xs : List (Point 2 α)) (h : xs ≠ []) : RangeTree2D α :=
  if hlen : xs.length ≤ 1 then .leaf (xs.head h)
  else
    .node (((xs.take (half xs)).getLast (take_half_ne_nil h)) 0)
      (RangeTree1D.build (xs.mergeSort (fun a b => decide (a 1 ≤ b 1))) (mergeSort_ne_nil h))
      (buildSorted (xs.take (half xs)) (take_half_ne_nil h))
      (buildSorted (xs.drop (half xs)) (drop_half_ne_nil hlen))
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- The build from points in any order: sort them by the first coordinate, then build; `none` for
no points. -/
def build (ps : List (Point 2 α)) : Option (RangeTree2D α) :=
  let xs := ps.mergeSort (fun a b => decide (a 0 ≤ b 0))
  if h : xs = [] then none else some (buildSorted xs h)

/-- `p` is between `lo` and `hi` on the second coordinate, edges included. -/
def inY (lo hi p : Point 2 α) : Bool := decide (lo 1 ≤ p 1 ∧ p 1 ≤ hi 1)

/-- The 2D query (dBCKO `2DRANGEQUERY`): walk the tree on the first coordinate; a subtree known to
lie wholly inside the range on that coordinate (`bl`: every point in it is at least `lo 0`; `br`:
at most `hi 0`) is answered by its associated tree's points, filtered on the second coordinate
(dBCKO run a 1D range search there, which `Cost2D.lean`'s `queryM` runs; the answer is the
same). -/
def go (lo hi : Point 2 α) : Bool → Bool → RangeTree2D α → List (Point 2 α)
  | _, _, .leaf p => if InRectangle lo hi p then [p] else []
  | bl, br, .node s A l r =>
      if bl && br then (leaves A).filter (inY lo hi)
      else (if lo 0 ≤ s then go lo hi bl (br || decide (s ≤ hi 0)) l else [])
        ++ (if s ≤ hi 0 then go lo hi (bl || decide (lo 0 ≤ s)) br r else [])

/-- The query on a built tree; no tree answers nothing. -/
def query (lo hi : Point 2 α) : Option (RangeTree2D α) → List (Point 2 α)
  | none => []
  | some t => go lo hi false false t

/-- Every inner key of an associated tree separates its two sides on the second coordinate:
nothing on its left is larger there, nothing on its right is smaller. -/
def YSeparate : RangeTree1D (Point 2 α) → Prop
  | .leaf _ => True
  | .node s l r =>
      (∀ p ∈ leaves l, p 1 ≤ s 1) ∧ (∀ p ∈ leaves r, s 1 ≤ p 1) ∧ YSeparate l ∧ YSeparate r

/-- What the build guarantees of a tree: every split separates its two sides on the first
coordinate (nothing on its left is larger, nothing on its right is smaller), and every associated
tree holds the points below its node, in some order, separates them on the second coordinate and
halves them (the 1D tree's two invariants, on that coordinate). -/
def Assembled : RangeTree2D α → Prop
  | .leaf _ => True
  | .node s A l r =>
      (∀ p ∈ points l, p 0 ≤ s) ∧ (∀ p ∈ points r, s ≤ p 0) ∧
        (leaves A).Perm (points l ++ points r) ∧ YSeparate A ∧ RangeTree1D.SplitsHalve A ∧
        Assembled l ∧ Assembled r

/-- The build stores exactly the points it was given, in order. -/
theorem points_buildSorted (xs : List (Point 2 α)) (h : xs ≠ []) :
    points (buildSorted xs h) = xs := by
  rw [buildSorted]
  split_ifs with hlen
  · match xs, h, hlen with
    | [a], _, _ => rfl
    | _ :: _ :: _, _, hlen => simp at hlen
  · simp only [points]
    rw [points_buildSorted, points_buildSorted, List.take_append_drop]
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- In a list sorted by the first coordinate, no point is past the last on it. -/
theorem le_getLast_of_sorted {xs : List (Point 2 α)} (hs : xs.Pairwise (fun a b => a 0 ≤ b 0))
    (h : xs ≠ []) {p : Point 2 α} (hp : p ∈ xs) : p 0 ≤ (xs.getLast h) 0 := by
  rw [← List.dropLast_append_getLast h] at hs hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (List.pairwise_append.mp hs).2.2 p hp _ (List.mem_singleton_self _)
  · rw [List.mem_singleton.mp hp]

/-- In a list sorted by the second coordinate, no point is past the last on it. -/
theorem y_le_getLast_of_sorted {xs : List (Point 2 α)} (hs : xs.Pairwise (fun a b => a 1 ≤ b 1))
    (h : xs ≠ []) {p : Point 2 α} (hp : p ∈ xs) : p 1 ≤ (xs.getLast h) 1 := by
  rw [← List.dropLast_append_getLast h] at hs hp
  rcases List.mem_append.mp hp with hp | hp
  · exact (List.pairwise_append.mp hs).2.2 p hp _ (List.mem_singleton_self _)
  · rw [List.mem_singleton.mp hp]

/-- **The associated tree of a list sorted by the second coordinate separates on it.** -/
theorem ySeparate_build (xs : List (Point 2 α)) (h : xs ≠ [])
    (hs : xs.Pairwise (fun a b => a 1 ≤ b 1)) : YSeparate (RangeTree1D.build xs h) := by
  rw [RangeTree1D.build]
  split_ifs with hlen
  · trivial
  · have hsplit := hs
    rw [← List.take_append_drop (half xs) xs] at hsplit
    refine ⟨fun p hp => ?_, fun p hp => ?_,
      ySeparate_build _ _ (hs.sublist (List.take_sublist _ _)),
      ySeparate_build _ _ (hs.sublist (List.drop_sublist _ _))⟩
    · rw [RangeTree1D.leaves_build] at hp
      exact y_le_getLast_of_sorted (hs.sublist (List.take_sublist _ _)) _ hp
    · rw [RangeTree1D.leaves_build] at hp
      exact (List.pairwise_append.mp hsplit).2.2 _ (List.getLast_mem _) p hp
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- **The build of points sorted by the first coordinate is assembled.** -/
theorem assembled_buildSorted (xs : List (Point 2 α)) (h : xs ≠ [])
    (hs : xs.Pairwise (fun a b => a 0 ≤ b 0)) : Assembled (buildSorted xs h) := by
  rw [buildSorted]
  split_ifs with hlen
  · trivial
  · have hsplit := hs
    rw [← List.take_append_drop (half xs) xs] at hsplit
    refine ⟨fun p hp => ?_, fun p hp => ?_, ?_, ySeparate_build _ _ ?_,
      RangeTree1D.splitsHalve_build _ _,
      assembled_buildSorted _ _ (hs.sublist (List.take_sublist _ _)),
      assembled_buildSorted _ _ (hs.sublist (List.drop_sublist _ _))⟩
    · rw [points_buildSorted] at hp
      exact le_getLast_of_sorted (hs.sublist (List.take_sublist _ _)) _ hp
    · rw [points_buildSorted] at hp
      exact (List.pairwise_append.mp hsplit).2.2 _ (List.getLast_mem _) p hp
    · rw [RangeTree1D.leaves_build, points_buildSorted, points_buildSorted, List.take_append_drop]
      exact List.mergeSort_perm _ _
    · exact (List.pairwise_mergeSort
        (fun _ _ _ hab hbc =>
          decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
        (fun a b => by simpa using le_total (a 1) (b 1)) xs).imp (of_decide_eq_true ·)
termination_by xs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, half]
  all_goals omega

/-- **The walk answers the stored points in the rectangle**, in some order, on an assembled tree,
whenever what `bl` and `br` claim of the subtree holds. -/
theorem go_perm (lo hi : Point 2 α) :
    ∀ (t : RangeTree2D α) (bl br : Bool), Assembled t →
      (bl → ∀ p ∈ points t, lo 0 ≤ p 0) → (br → ∀ p ∈ points t, p 0 ≤ hi 0) →
      (go lo hi bl br t).Perm ((points t).filter (InRectangle lo hi ·))
  | .leaf p, bl, br, _, _, _ => by
    simp only [go, points, List.filter_singleton]
    by_cases hp : InRectangle lo hi p
    · simp only [decide_eq_true hp, Bool.cond_true]; split_ifs; rfl
    · simp only [decide_eq_false hp, Bool.cond_false]; split_ifs; rfl
  | .node s A l r, bl, br, ⟨hl, hr, hA, _, _, hal, har⟩, hbl, hbr => by
    simp only [go]
    split_ifs with hb hlo hhi hhi
    · -- both sides of the range are known: the associated tree's points answer
      obtain ⟨hb1, hb2⟩ := Bool.and_eq_true_iff.mp hb
      have hin := hbl hb1
      have hax := hbr hb2
      refine (hA.filter _).trans (List.Perm.of_eq (List.filter_congr fun p hp => ?_))
      simp only [inY, InRectangle, Fin.forall_fin_two, decide_eq_decide]
      exact ⟨fun h => ⟨⟨hin p hp, hax p hp⟩, h⟩, fun h => h.2⟩
    all_goals simp only [points, List.filter_append]
    all_goals refine List.Perm.append ?_ ?_
    · refine go_perm lo hi l _ _ hal (fun h p hp => hbl h p (List.mem_append_left _ hp)) ?_
      intro h p hp
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hbr h p (List.mem_append_left _ hp)
      · exact (hl p hp).trans (of_decide_eq_true h)
    · refine go_perm lo hi r _ _ har ?_ (fun h p hp => hbr h p (List.mem_append_right _ hp))
      intro h p hp
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hbl h p (List.mem_append_right _ hp)
      · exact (of_decide_eq_true h).trans (hr p hp)
    · refine go_perm lo hi l _ _ hal (fun h p hp => hbl h p (List.mem_append_left _ hp)) ?_
      intro h p hp
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hbr h p (List.mem_append_left _ hp)
      · exact (hl p hp).trans (of_decide_eq_true h)
    · rw [List.filter_eq_nil_iff.mpr]
      intro p hp hin
      simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
      exact hhi ((hr p hp).trans hin.1.2)
    · rw [List.filter_eq_nil_iff.mpr]
      intro p hp hin
      simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
      exact hlo (hin.1.1.trans (hl p hp))
    · refine go_perm lo hi r _ _ har ?_ (fun h p hp => hbr h p (List.mem_append_right _ hp))
      intro h p hp
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hbl h p (List.mem_append_right _ hp)
      · exact (of_decide_eq_true h).trans (hr p hp)
    · rw [List.filter_eq_nil_iff.mpr]
      intro p hp hin
      simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
      exact hlo (hin.1.1.trans (hl p hp))
    · rw [List.filter_eq_nil_iff.mpr]
      intro p hp hin
      simp only [InRectangle, Fin.forall_fin_two, decide_eq_true_eq] at hin
      exact hhi ((hr p hp).trans hin.1.2)

/-- **The 2D range tree's query** (`Query2DSpec`): built over any points, the empty list
included, the tree answers a rectangle query with every stored point inside the rectangle, edges
included, each as often as it is stored, and nothing else, in some order. -/
theorem query_build : Query2DSpec (α := α) build query := by
  intro ps lo hi
  have hperm := List.mergeSort_perm ps (fun a b => decide (a 0 ≤ b 0))
  simp only [build]
  split_ifs with h
  · rw [h] at hperm
    simp [query, hperm.symm.eq_nil]
  · have hs : (ps.mergeSort (fun a b => decide (a 0 ≤ b 0))).Pairwise (fun a b => a 0 ≤ b 0) :=
      (List.pairwise_mergeSort
        (fun _ _ _ hab hbc =>
          decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true hbc)))
        (fun a b => by simpa using le_total (a 0) (b 0)) ps).imp (of_decide_eq_true ·)
    refine (go_perm lo hi _ false false (assembled_buildSorted _ h hs) (by simp) (by simp)).trans ?_
    rw [points_buildSorted]
    exact hperm.filter _

end RangeTree2D
end AlgoDesign.Geometry
