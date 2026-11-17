/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.AlgorithmT

/-!
# Algorithm T: facts the correctness proof uses

Vertices reaching each other (`Mutual`) form an equivalence; a path from a vertex with some property
to one without crosses an arrow from a vertex with it to one without (`exists_cross`). The vertices
a retreating path reaches (`reachList`, read off `retreatReach`): each vertex reaches itself, the
lists only grow as retreats are added, every vertex on a list reaches its owner back, and every
vertex on a list other than its owner is the head of a retreat. The climb-back number is the least
entry number on the list (`le_climbBack_iff`). Popping `F` stops at the first vertex whose low value
is below the bound (`popFollowers_append`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

open Relation

variable {g : Digraph}

/-! ## Vertices reaching each other -/

theorem mutual_refl (v : ℕ) : Mutual g v v := ⟨ReflTransGen.refl, ReflTransGen.refl⟩

theorem Mutual.symm {u v : ℕ} (h : Mutual g u v) : Mutual g v u := ⟨h.2, h.1⟩

theorem Mutual.trans {u v x : ℕ} (h : Mutual g u v) (h' : Mutual g v x) : Mutual g u x :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem reaches_of_arrow {u v : ℕ} (h : g.Arrow u v) : g.Reaches u v := ReflTransGen.single h

/-- **A path leaving a set crosses out of it**: from a vertex with `P` to one without, some arrow
of the path goes from a vertex with `P` to one without. -/
theorem exists_cross (P : ℕ → Prop) {a b : ℕ} (h : g.Reaches a b) (ha : P a) (hb : ¬ P b) :
    ∃ x y, g.Reaches a x ∧ P x ∧ g.Arrow x y ∧ ¬ P y ∧ g.Reaches y b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact absurd ha hb
  | head hac hcb ih =>
    rename_i a c
    by_cases hc : P c
    · obtain ⟨x, y, hcx, hx, hxy, hy, hyb⟩ := ih hc
      exact ⟨x, y, ReflTransGen.head hac hcx, hx, hxy, hy, hyb⟩
    · exact ⟨a, c, ReflTransGen.refl, ha, hac, hc, hcb⟩

/-- On a well-formed graph, a vertex reached from another vertex is a vertex of the graph. -/
theorem lt_of_reaches (hg : g.WellFormed) {u v : ℕ} (hu : u < g.n) (h : g.Reaches u v) :
    v < g.n := by
  induction h with
  | refl => exact hu
  | tail _ hxy _ => exact (hg _ hxy).2

/-! ## The vertices a retreating path reaches -/

namespace AlgorithmT

/-- The list of vertices reachable from `v` along retreating paths, after `b` retreats of `log`. -/
def reachList (g : Digraph) (log : List (ℕ × ℕ)) (b v : ℕ) : List ℕ :=
  (retreatReach g log b).getD v []

theorem retreatReach_length (log : List (ℕ × ℕ)) :
    ∀ b, (retreatReach g log b).length = g.n
  | 0 => by simp [retreatReach]
  | b + 1 => by simp [retreatReach]

theorem mem_reachList_zero {log : List (ℕ × ℕ)} {v x : ℕ} :
    x ∈ reachList g log 0 v ↔ v < g.n ∧ x = v := by
  unfold reachList retreatReach
  by_cases hv : v < g.n
  · simp [List.getD_eq_getElem?_getD, hv]
  · simp [List.getD_eq_getElem?_getD, hv]

theorem mem_reachList_succ {log : List (ℕ × ℕ)} {b v x : ℕ} :
    x ∈ reachList g log (b + 1) v ↔ v < g.n ∧ (x ∈ reachList g log b v ∨
      ∃ y, log[b]? = some (v, y) ∧ Mutual g v y ∧ x ∈ reachList g log b y) := by
  unfold reachList
  conv_lhs => unfold retreatReach
  by_cases hv : v < g.n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv,
      Option.map_some, Option.getD_some, List.mem_append, hv, true_and]
    rcases hb : log[b]? with _ | ⟨a, y⟩
    · simp
    · by_cases ha : a = v ∧ Mutual g a y
      · obtain ⟨rfl, hm⟩ := ha
        simp [hm]
      · simp only [ha, ite_false, List.not_mem_nil, or_false, Option.some.injEq, Prod.mk.injEq]
        constructor
        · exact Or.inl
        · rintro (h | ⟨y', ⟨rfl, rfl⟩, hm, -⟩)
          · exact h
          · exact absurd ⟨rfl, hm⟩ ha
  · have : ¬ v < (List.range g.n).length := by simpa using hv
    simp [List.getD_eq_getElem?_getD, hv]

theorem retreatReach_congr {log log' : List (ℕ × ℕ)} :
    ∀ b, (∀ c < b, log[c]? = log'[c]?) → retreatReach g log b = retreatReach g log' b
  | 0, _ => rfl
  | b + 1, h => by
    have ih := retreatReach_congr b fun c hc => h c (by omega)
    simp only [retreatReach, ih, h b (by omega)]

/-- The lists after the first `b` retreats do not see later ones. -/
theorem reachList_append {log : List (ℕ × ℕ)} (e : List (ℕ × ℕ)) {b : ℕ} (hb : b ≤ log.length)
    (v : ℕ) : reachList g (log ++ e) b v = reachList g log b v := by
  unfold reachList
  rw [retreatReach_congr b fun c hc => List.getElem?_append_left (by omega)]

theorem self_mem_reachList {log : List (ℕ × ℕ)} {v : ℕ} (hv : v < g.n) :
    ∀ b, v ∈ reachList g log b v
  | 0 => mem_reachList_zero.2 ⟨hv, rfl⟩
  | b + 1 => mem_reachList_succ.2 ⟨hv, Or.inl (self_mem_reachList hv b)⟩

theorem reachList_mono {log : List (ℕ × ℕ)} {b v x : ℕ} (h : x ∈ reachList g log b v) :
    ∀ k, x ∈ reachList g log (b + k) v
  | 0 => h
  | k + 1 => by
    have := reachList_mono h k
    rw [← Nat.add_assoc]
    refine mem_reachList_succ.2 ⟨?_, Or.inl this⟩
    by_contra hv
    have : reachList g log (b + k) v = [] := by
      unfold reachList
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [retreatReach_length]; omega)]
      rfl
    simp_all

theorem lt_of_mem_reachList {log : List (ℕ × ℕ)} :
    ∀ {b v x : ℕ}, x ∈ reachList g log b v → v < g.n
  | 0, _, _, h => (mem_reachList_zero.1 h).1
  | _ + 1, _, _, h => (mem_reachList_succ.1 h).1

/-- Every vertex on `v`'s list reaches `v` and is reached from it. -/
theorem mutual_of_mem_reachList {log : List (ℕ × ℕ)} :
    ∀ {b v x : ℕ}, x ∈ reachList g log b v → Mutual g v x
  | 0, v, x, h => by
    obtain ⟨-, rfl⟩ := mem_reachList_zero.1 h
    exact mutual_refl _
  | b + 1, v, x, h => by
    rcases (mem_reachList_succ.1 h).2 with h | ⟨y, -, hm, hy⟩
    · exact mutual_of_mem_reachList h
    · exact hm.trans (mutual_of_mem_reachList hy)

/-- Every vertex on `v`'s list other than `v` is the head of a retreat. -/
theorem head_of_mem_reachList {log : List (ℕ × ℕ)} :
    ∀ {b v x : ℕ}, x ∈ reachList g log b v → x = v ∨ ∃ a, (a, x) ∈ log
  | 0, v, x, h => Or.inl (mem_reachList_zero.1 h).2
  | b + 1, v, x, h => by
    rcases (mem_reachList_succ.1 h).2 with h | ⟨y, hb, -, hy⟩
    · exact head_of_mem_reachList h
    · rcases head_of_mem_reachList hy with rfl | hx
      · exact Or.inr ⟨v, List.mem_of_getElem? hb⟩
      · exact Or.inr hx

/-- A vertex's list holds only itself until a retreat starts at it. -/
theorem source_of_mem_reachList {log : List (ℕ × ℕ)} :
    ∀ {b v x : ℕ}, x ∈ reachList g log b v → x = v ∨ ∃ y, (v, y) ∈ log
  | 0, v, x, h => Or.inl (mem_reachList_zero.1 h).2
  | b + 1, v, x, h => by
    rcases (mem_reachList_succ.1 h).2 with h | ⟨y, hb, -, -⟩
    · exact source_of_mem_reachList h
    · exact Or.inr ⟨y, List.mem_of_getElem? hb⟩

/-! ## The climb-back number -/

theorem le_foldr_min_iff (f : ℕ → ℕ) (k init : ℕ) :
    ∀ l : List ℕ, k ≤ l.foldr (fun x m => min (f x) m) init ↔ k ≤ init ∧ ∀ x ∈ l, k ≤ f x
  | [] => by simp
  | a :: l => by
    simp only [List.foldr_cons, le_min_iff, le_foldr_min_iff f k init l, List.mem_cons,
      forall_eq_or_imp]
    tauto

theorem climbBack_eq (w : Walk) (v : ℕ) : climbBack (g := g) w v =
    (reachList g w.retreats w.retreats.length v).foldr (fun x m => min (w.pre x) m) (w.pre v) :=
  rfl

theorem le_climbBack_iff {w : Walk} {v k : ℕ} : k ≤ climbBack (g := g) w v ↔
    k ≤ w.pre v ∧ ∀ x ∈ reachList g w.retreats w.retreats.length v, k ≤ w.pre x := by
  rw [climbBack_eq]
  exact le_foldr_min_iff _ _ _ _

theorem climbBack_le_pre (w : Walk) (v : ℕ) : climbBack (g := g) w v ≤ w.pre v :=
  (le_climbBack_iff.1 le_rfl).1

theorem climbBack_le_of_mem {w : Walk} {v x : ℕ}
    (hx : x ∈ reachList g w.retreats w.retreats.length v) : climbBack (g := g) w v ≤ w.pre x :=
  (le_climbBack_iff.1 le_rfl).2 x hx

theorem exists_climbBack (w : Walk) (v : ℕ) : climbBack (g := g) w v = w.pre v ∨
    ∃ x ∈ reachList g w.retreats w.retreats.length v, climbBack (g := g) w v = w.pre x := by
  rw [climbBack_eq]
  generalize reachList g w.retreats w.retreats.length v = l
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons, exists_eq_or_imp]
    rcases le_total (w.pre a) (l.foldr (fun x m => min (w.pre x) m) (w.pre v)) with h | h
    · exact Or.inr (Or.inl (min_eq_left h))
    · rw [min_eq_right h]
      rcases ih with h' | ⟨x, hx, h'⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inr ⟨x, hx, h'⟩)

/-- Two walks with the same entry numbers on `v`'s list and the same lists have the same
climb-back number at `v`. -/
theorem climbBack_congr {w w' : Walk} {v : ℕ}
    (hl : reachList g w'.retreats w'.retreats.length v =
      reachList g w.retreats w.retreats.length v)
    (hv : w'.pre v = w.pre v)
    (hp : ∀ x ∈ reachList g w.retreats w.retreats.length v, w'.pre x = w.pre x) :
    climbBack (g := g) w' v = climbBack (g := g) w v := by
  rw [climbBack_eq, climbBack_eq, hl, hv]
  generalize reachList g w.retreats w.retreats.length v = l at hp ⊢
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, hp a List.mem_cons_self,
      ih fun x hx => hp x (List.mem_cons_of_mem _ hx)]

/-! ## Order in a list that grows at the end -/

theorem pair_sublist_of_append {l : List ℕ} {x z v : ℕ} (h : [x, z].Sublist (l ++ [v]))
    (hz : z ≠ v) : [x, z].Sublist l := by
  obtain ⟨l1, l2, he, h1, h2⟩ := List.sublist_append_iff.1 h
  rcases List.sublist_singleton.1 h2 with rfl | rfl
  · rw [List.append_nil] at he
    exact he ▸ h1
  · have := congrArg List.getLast? he
    rw [List.getLast?_concat] at this
    exact absurd (by simpa using this) hz

theorem not_pair_sublist_append {l : List ℕ} {z v : ℕ} (hv : v ∉ l) :
    ¬ [v, z].Sublist (l ++ [v]) := by
  intro h
  obtain ⟨l1, l2, he, h1, h2⟩ := List.sublist_append_iff.1 h
  rcases List.sublist_singleton.1 h2 with rfl | rfl
  · rw [List.append_nil] at he
    exact hv (h1.subset (he ▸ List.mem_cons_self))
  · rcases l1 with _ | ⟨a, l1⟩
    · simp at he
    · simp only [List.cons_append, List.cons.injEq] at he
      exact hv (he.1 ▸ h1.subset List.mem_cons_self)

theorem pair_sublist_append {l : List ℕ} {x v : ℕ} (hx : x ∈ l) : [x, v].Sublist (l ++ [v]) :=
  (List.singleton_sublist.2 hx).append (List.Sublist.refl [v])

/-! ## Popping `F` -/

theorem popFollowers_append (low : ℕ → ℕ) (lv : ℕ) {C : List ℕ}
    (hC : ∀ c ∈ C.head?, low c < lv) :
    ∀ B : List ℕ, (∀ x ∈ B, lv ≤ low x) → popFollowers low lv (B ++ C) = (B, C)
  | [], _ => by
    cases C with
    | nil => rfl
    | cons c C => simp [popFollowers, Nat.not_le.2 (hC c rfl)]
  | x :: B, h => by
    simp only [List.cons_append, popFollowers, h x List.mem_cons_self, ↓reduceIte,
      popFollowers_append low lv hC B fun y hy => h y (List.mem_cons_of_mem _ hy)]

end AlgorithmT

end AlgoDesign.Graphs.Scc
