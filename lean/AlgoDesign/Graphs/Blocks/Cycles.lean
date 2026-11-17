/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Basic
public import Mathlib.Data.List.Perm.Subperm

/-!
# Bridges, cut vertices and blocks: deciding the blocks

`SameBlock` asks for a cycle, a path that may be as long as the network. `paths` lists every path
from one vertex to another through distinct vertices without a given link, by trying each link at
the current vertex in turn; `mem_paths` proves it lists exactly those paths. A path through distinct
vertices has at most as many vertices as there are ends of links, so `2 m` steps are enough, and
`onCycleWithB_iff` proves the search answers `OnCycleWith`. That makes `SameBlock` decidable.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

/-- The steps out of `x`: for each end of a link at `x`, the link's id and its other end, links
in id order. -/
def stepsFrom (g : Graph) (x : ℕ) : List (ℕ × ℕ) :=
  (List.range g.links.length).flatMap fun i => (g.links[i]?).toList.flatMap fun l =>
    (if l.1 = x then [(i, l.2)] else []) ++ (if l.2 = x then [(i, l.1)] else [])

theorem mem_stepsFrom {g : Graph} {x f y : ℕ} : (f, y) ∈ stepsFrom g x ↔ Joins g f x y := by
  simp only [stepsFrom, List.mem_flatMap, List.mem_range, Option.mem_toList, List.mem_append,
    Joins]
  constructor
  · rintro ⟨i, -, ⟨a, b⟩, hl, h⟩
    split_ifs at h <;> simp_all
  · intro h
    have hf : f < g.links.length := by
      rcases h with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1
    refine ⟨f, hf, ?_⟩
    rcases h with h | h
    · exact ⟨(x, y), h, by simp⟩
    · exact ⟨(y, x), h, by simp⟩

/-- The steps of every path from `x` to `t` of at most `k` steps, through vertices not in `seen`,
without link `e`; `seen` holds `x`. A path stops when it reaches `t`. -/
def paths (g : Graph) (e t : ℕ) : ℕ → List ℕ → ℕ → List (List (ℕ × ℕ))
  | 0, _, x => if x = t then [[]] else []
  | k + 1, seen, x =>
    if x = t then [[]]
    else (stepsFrom g x).flatMap fun s =>
      if s.1 = e ∨ s.2 ∈ seen then [] else (paths g e t k (s.2 :: seen) s.2).map (s :: ·)

theorem endOf_nil (x : ℕ) : endOf x [] = x := rfl

theorem endOf_cons (x : ℕ) (s : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    endOf x (s :: rest) = endOf s.2 rest := by
  simp [endOf, List.getLast_cons]

/-- The last vertex of a path through distinct vertices is not its first, unless it has no steps. -/
theorem endOf_ne {x : ℕ} {s : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (h : (x :: (s :: rest).map Prod.snd).Nodup) : endOf x (s :: rest) ≠ x := by
  intro he
  have hm : endOf x (s :: rest) ∈ (s :: rest).map Prod.snd := by
    simp only [endOf]
    rw [List.getLast_cons (by simp)]
    exact List.getLast_mem _
  rw [he] at hm
  exact (List.nodup_cons.mp h).1 hm

theorem mem_paths_succ {g : Graph} {e t k x : ℕ} {seen : List ℕ} {steps : List (ℕ × ℕ)} :
    steps ∈ paths g e t (k + 1) seen x ↔ (x = t ∧ steps = []) ∨
      (x ≠ t ∧ ∃ s ∈ stepsFrom g x, s.1 ≠ e ∧ s.2 ∉ seen ∧
        ∃ rest ∈ paths g e t k (s.2 :: seen) s.2, steps = s :: rest) := by
  simp only [paths]
  split_ifs with h
  · simp [h, eq_comm]
  · simp only [List.mem_flatMap, h, false_and, false_or, ne_eq, not_false_eq_true, true_and]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    by_cases hc : s.1 = e ∨ s.2 ∈ seen
    · simp only [hc, ite_true, List.not_mem_nil, false_iff]
      rintro ⟨h1, h2, -⟩
      rcases hc with hc | hc
      · exact h1 hc
      · exact h2 hc
    · simp only [not_or] at hc
      simp only [hc, or_self, ite_false, List.mem_map, not_false_eq_true, true_and]
      exact ⟨fun ⟨r, hr, he⟩ => ⟨r, hr, he.symm⟩, fun ⟨r, hr, he⟩ => ⟨r, hr, he.symm⟩⟩

/-- **`paths` lists exactly the paths**: from `x` (in `seen`) to `t`, of at most `k` steps,
through distinct vertices outside `seen`, without link `e`. -/
theorem mem_paths {g : Graph} {e t : ℕ} :
    ∀ (k : ℕ) (seen : List ℕ) (x : ℕ) (steps : List (ℕ × ℕ)), x ∈ seen →
    (steps ∈ paths g e t k seen x ↔
      Trail g x steps ∧ endOf x steps = t ∧ (x :: steps.map Prod.snd).Nodup ∧
        (∀ y ∈ steps.map Prod.snd, y ∉ seen) ∧ e ∉ steps.map Prod.fst ∧ steps.length ≤ k)
  | 0, seen, x, [], _ => by simp [paths, Trail, endOf_nil, eq_comm]
  | 0, seen, x, s :: rest, _ => by
    simp only [paths]
    split_ifs <;> simp
  | k + 1, seen, x, [], _ => by
    rw [mem_paths_succ]
    simp [Trail, endOf_nil]
  | k + 1, seen, x, (f, y) :: rest, hx => by
    rw [mem_paths_succ]
    constructor
    · rintro (⟨-, h⟩ | ⟨hxt, ⟨f', y'⟩, hs, hf, hy, r, hr, hrr⟩)
      · simp at h
      simp only [List.cons.injEq, Prod.mk.injEq] at hrr
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hrr
      obtain ⟨htr, hend, hnd, hout, he, hlen⟩ :=
        (mem_paths k _ _ _ (List.mem_cons_self ..)).mp hr
      refine ⟨⟨mem_stepsFrom.mp hs, htr⟩, by rw [endOf_cons]; exact hend, ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hnd ⊢
        exact ⟨⟨fun hxy => hy (hxy ▸ hx), fun hm => hout x hm (List.mem_cons_of_mem _ hx)⟩,
          hnd⟩
      · simp only [List.map_cons, List.mem_cons, forall_eq_or_imp]
        exact ⟨hy, fun z hz hzs => hout z hz (List.mem_cons_of_mem _ hzs)⟩
      · simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨Ne.symm hf, he⟩
      · simp only [List.length_cons]
        omega
    · rintro ⟨⟨hj, htr⟩, hend, hnd, hout, he, hlen⟩
      simp only [List.map_cons, List.mem_cons, not_or] at he
      simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hout
      refine Or.inr ⟨fun hxt => endOf_ne hnd (hend.trans hxt.symm), (f, y), mem_stepsFrom.mpr hj,
        Ne.symm he.1, hout.1, rest, (mem_paths k (y :: seen) y rest (List.mem_cons_self ..)).mpr
          ⟨htr, by rw [endOf_cons] at hend; exact hend, ?_, ?_, he.2, ?_⟩, rfl⟩
      · simp only [List.map_cons] at hnd
        exact (List.nodup_cons.mp hnd).2
      · intro z hz hzs
        rcases List.mem_cons.mp hzs with rfl | hzs
        · simp only [List.map_cons] at hnd
          exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hz
        · exact hout.2 z hz hzs
      · simp only [List.length_cons] at hlen
        omega

/-- Every end of every link, two per link. -/
def ends (g : Graph) : List ℕ := g.links.flatMap fun l => [l.1, l.2]

theorem length_ends (g : Graph) : (ends g).length = 2 * g.links.length := by
  unfold ends
  induction g.links with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem mem_ends_of_joins {g : Graph} {f a b : ℕ} (h : Joins g f a b) :
    a ∈ ends g ∧ b ∈ ends g := by
  unfold ends
  rcases h with h | h
  · have hm := List.mem_of_getElem? h
    exact ⟨List.mem_flatMap.mpr ⟨_, hm, by simp⟩, List.mem_flatMap.mpr ⟨_, hm, by simp⟩⟩
  · have hm := List.mem_of_getElem? h
    exact ⟨List.mem_flatMap.mpr ⟨_, hm, by simp⟩, List.mem_flatMap.mpr ⟨_, hm, by simp⟩⟩

/-- Every vertex a walk steps to is an end of a link. -/
theorem mem_ends_of_trail {g : Graph} :
    ∀ {x : ℕ} {steps : List (ℕ × ℕ)}, Trail g x steps → ∀ y ∈ steps.map Prod.snd, y ∈ ends g
  | _, [], _, _, hy => by simp at hy
  | _, (f, z) :: rest, h, y, hy => by
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact (mem_ends_of_joins h.1).2
    · exact mem_ends_of_trail h.2 y hy

/-- The search for a cycle through `e` holding `f`: a path from `e`'s far end back to its near
end, of at most `2 m` steps. -/
def onCycleWithB (g : Graph) (e f : ℕ) : Bool :=
  match g.links[e]? with
  | some (a, b) =>
    a != b && (paths g e a (2 * g.links.length) [b] b).any fun s => f ∈ s.map Prod.fst
  | none => false

/-- **The search answers `OnCycleWith`.** -/
theorem onCycleWithB_iff {g : Graph} {e f : ℕ} :
    onCycleWithB g e f = true ↔ OnCycleWith g e f := by
  unfold OnCycleWith
  rcases hl : g.links[e]? with _ | ⟨a, b⟩
  · simp [onCycleWithB, hl]
  · simp only [onCycleWithB, hl, Bool.and_eq_true, bne_iff_ne, List.any_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hab, s, hs, hf⟩
      obtain ⟨htr, hend, hnd, -, he, -⟩ := (mem_paths _ [b] b s (by simp)).mp hs
      exact ⟨a, b, rfl, hab, s, htr, hnd, hend, he, hf⟩
    · rintro ⟨a', b', h', hab, s, htr, hnd, hend, he, hf⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      refine ⟨hab, s, (mem_paths _ [b] b s (by simp)).mpr ⟨htr, hend, hnd, ?_, he, ?_⟩, hf⟩
      · intro y hy hyb
        rw [List.mem_singleton] at hyb
        subst hyb
        exact (List.nodup_cons.mp hnd).1 hy
      · have hsub : (b :: s.map Prod.snd) ⊆ ends g := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact (mem_ends_of_joins (Or.inl hl)).2
          · exact mem_ends_of_trail htr y hy
        have := (hnd.subperm hsub).length_le
        simp only [List.length_cons, List.length_map, length_ends] at this
        omega

instance (g : Graph) (e f : ℕ) : Decidable (OnCycleWith g e f) :=
  decidable_of_iff _ onCycleWithB_iff

instance (g : Graph) (e f : ℕ) : Decidable (SameBlock g e f) := by
  unfold SameBlock; infer_instance

instance (g : Graph) (r : Report) : Decidable (BlocksAgree g r) := by
  unfold BlocksAgree
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ ?_))) <;> infer_instance

end AlgoDesign.Graphs.Blocks
