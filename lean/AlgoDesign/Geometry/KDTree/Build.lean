/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Spec

/-!
# Building a k-d tree

dBCKO §5.2 (`BUILDKDTREE`, p. 100), with the points in the leaves. At depth `depth` the node's
axis is `depth mod d`; its points are sorted along that axis, the first `⌈n/2⌉` go left and the rest
right, and the split is the axis coordinate of the last point sent left. One point makes a leaf.
This is what the Rust (`n.div_ceil(2)`, by median selection) and the Python (`(n + 1) // 2`, from
presorted lists) build with a bucket of 1.

A tree has at least one point, so `build` takes a nonempty list; `ofList` is the total form, `none`
exactly for no points. `valid_build` proves the tree keeps box invariants 1 and 2 (`CutsSeparate`,
`CutsHalve`), and `points_build` that it holds the input's points, each as often as given.
-/

@[expose] public section

namespace AlgoDesign.Geometry.KDTree

variable {d : ℕ} {α : Type} [LinearOrder α]

/-- The points sorted along axis `a`, least coordinate first. -/
def sortAlong (a : Fin d) (ps : List (Point d α)) : List (Point d α) :=
  ps.insertionSort (fun x y => x a ≤ y a)

theorem sortAlong_perm (a : Fin d) (ps : List (Point d α)) : (sortAlong a ps).Perm ps :=
  List.perm_insertionSort _ _

theorem sortAlong_sorted (a : Fin d) (ps : List (Point d α)) :
    (sortAlong a ps).Pairwise (fun x y => x a ≤ y a) :=
  haveI : Std.Total (fun x y : Point d α => x a ≤ y a) := ⟨fun x y => le_total (x a) (y a)⟩
  haveI : IsTrans (Point d α) (fun x y => x a ≤ y a) := ⟨fun _ _ _ => le_trans⟩
  List.pairwise_insertionSort _ _

theorem length_sortAlong (a : Fin d) (ps : List (Point d α)) :
    (sortAlong a ps).length = ps.length :=
  List.length_insertionSort _ _

variable [NeZero d]

/-- Build at depth `depth`: one point makes a leaf; more are sorted along axis `depth mod d`, the
first `⌈n/2⌉` built on the left at the next depth and the rest on the right, split at the axis
coordinate of the last point sent left. -/
def buildAt (depth : ℕ) (ps : List (Point d α)) (h : ps ≠ []) : KDTree d α :=
  if h1 : ps.length ≤ 1 then leaf (ps.head h)
  else
    let a : Fin d := Fin.ofNat d depth
    let s := sortAlong a ps
    let m := (ps.length + 1) / 2
    have hs : s.length = ps.length := length_sortAlong a ps
    node a ((s[m - 1]'(by omega)) a)
      (buildAt (depth + 1) (s.take m) (by
        rw [← List.length_pos_iff, List.length_take]; omega))
      (buildAt (depth + 1) (s.drop m) (by
        rw [← List.length_pos_iff, List.length_drop]; omega))
termination_by ps.length
decreasing_by
  · simp only [List.length_take, length_sortAlong]; omega
  · simp only [List.length_drop, length_sortAlong]; omega

/-- **The k-d build** over a nonempty list of points, starting on axis 0. -/
def build (ps : List (Point d α)) (h : ps ≠ []) : KDTree d α := buildAt 0 ps h

/-- The build as a total function: `none` exactly for no points. -/
def ofList (ps : List (Point d α)) : Option (KDTree d α) :=
  if h : ps = [] then none else some (build ps h)

theorem valid_points_buildAt (depth : ℕ) (ps : List (Point d α)) (h : ps ≠ []) :
    (buildAt depth ps h).Valid ∧ (buildAt depth ps h).points.Perm ps := by
  rw [buildAt]
  split_ifs with h1
  · obtain ⟨p, rest, rfl⟩ := List.exists_cons_of_ne_nil h
    have : rest = [] := by simpa using h1
    subst this
    exact ⟨⟨trivial, trivial⟩, List.Perm.refl _⟩
  · set a : Fin d := Fin.ofNat d depth
    set s := sortAlong a ps with hsdef
    set m := (ps.length + 1) / 2 with hm
    have hs : s.length = ps.length := length_sortAlong a ps
    have hsort := sortAlong_sorted a ps
    rw [← hsdef] at hsort
    have hrel : ∀ i j (hi : i < s.length) (hj : j < s.length), i ≤ j → s[i] a ≤ s[j] a := by
      intro i j hi hj hij
      rcases hij.lt_or_eq with hlt | rfl
      · exact List.pairwise_iff_getElem.1 hsort i j hi hj hlt
      · exact le_rfl
    obtain ⟨⟨hsl, hhl⟩, hpl⟩ := valid_points_buildAt (depth + 1) (s.take m)
      (by rw [← List.length_pos_iff, List.length_take]; omega)
    obtain ⟨⟨hsr, hhr⟩, hpr⟩ := valid_points_buildAt (depth + 1) (s.drop m)
      (by rw [← List.length_pos_iff, List.length_drop]; omega)
    refine ⟨⟨⟨?_, ?_, hsl, hsr⟩, ?_, ?_, hhl, hhr⟩, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (hpl.mem_iff.1 hx)
      simp only [List.length_take] at hi
      rw [List.getElem_take]
      exact hrel _ _ _ _ (by omega)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (hpr.mem_iff.1 hx)
      simp only [List.length_drop] at hi
      rw [List.getElem_drop]
      exact hrel _ _ _ _ (by omega)
    · rw [hpl.length_eq, hpr.length_eq, List.length_take, List.length_drop]; omega
    · rw [hpl.length_eq, hpr.length_eq, List.length_take, List.length_drop]; omega
    · refine (hpl.append hpr).trans ?_
      rw [List.take_append_drop]
      exact sortAlong_perm a ps
termination_by ps.length
decreasing_by
  · simp only [List.length_take, length_sortAlong]; omega
  · simp only [List.length_drop, length_sortAlong]; omega

/-- **The build keeps box invariants 1 and 2**: its cuts separate its points and split them in
half. -/
theorem valid_build (ps : List (Point d α)) (h : ps ≠ []) : (build ps h).Valid :=
  (valid_points_buildAt 0 ps h).1

/-- **The build holds the input's points**, each as often as given. -/
theorem points_build (ps : List (Point d α)) (h : ps ≠ []) : (build ps h).points.Perm ps :=
  (valid_points_buildAt 0 ps h).2

theorem ofList_eq_none {ps : List (Point d α)} : ofList ps = none ↔ ps = [] := by
  unfold ofList; split_ifs with h <;> simp [h]

theorem ofList_eq_some {ps : List (Point d α)} {t : KDTree d α} (h : ofList ps = some t) :
    ∃ hne : ps ≠ [], build ps hne = t := by
  unfold ofList at h
  split_ifs at h with hne
  exact ⟨hne, Option.some.inj h⟩

end AlgoDesign.Geometry.KDTree
