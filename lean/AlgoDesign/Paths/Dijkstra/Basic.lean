/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Decide
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Cheapest paths: facts about rows and paths

The facts the walk's proofs share: what a row holds, how a path grows by one arrow and comes apart
at its last arrow or at its first vertex outside a set, and why the arrows tried are all
different. -/

@[expose] public section

namespace AlgoDesign.Paths

open AlgoDesign.Graphs

/-! ## Rows -/

theorem mem_out {g : Digraph} {v w i : ℕ} :
    (w, i) ∈ g.out v ↔ w < g.n ∧ g.arrows[i]? = some (v, w) := by
  simp only [Digraph.out, Digraph.idsBetween, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨ha, hj⟩
  · rintro ⟨hw, hi⟩
    exact ⟨w, hw, i, ⟨(List.getElem?_eq_some_iff.mp hi).1, hi⟩, rfl, rfl⟩

/-- The ids in a row are all different. -/
theorem nodup_out_ids (g : Digraph) (v : ℕ) : ((g.out v).map Prod.snd).Nodup := by
  simp only [Digraph.out, List.map_flatMap, List.map_map]
  refine List.nodup_flatMap.2 ⟨fun w _ => ?_, ?_⟩
  · simp only [Function.comp_def, List.map_id_fun', id_eq]
    exact List.nodup_range.filter _
  · refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro i hia hib
    simp only [Digraph.idsBetween, Function.comp_def, List.map_id', List.mem_filter,
      decide_eq_true_eq] at hia hib
    rw [hia.2] at hib
    simp only [Option.some.injEq, Prod.mk.injEq] at hib
    exact hab hib.2.2

namespace Network

variable {N : Network}

/-! ## Paths -/

theorem target_eq {i a b : ℕ} (h : N.g.arrows[i]? = some (a, b)) : N.target i = b := by
  simp [target, List.getD_eq_getElem?_getD, h]

theorem ends_append_singleton {u : ℕ} {p : List ℕ} {i w : ℕ} :
    N.ends u (p ++ [i]) = some w ↔ ∃ x, N.ends u p = some x ∧ N.g.arrows[i]? = some (x, w) := by
  induction p generalizing u with
  | nil =>
    simp only [List.nil_append, ends, Option.some.injEq, exists_eq_left']
    cases h : N.g.arrows[i]? with
    | none => simp
    | some a =>
      obtain ⟨a, b⟩ := a
      by_cases hab : a = u
      · subst hab; simp
      · simp [hab]
  | cons j p ih =>
    simp only [List.cons_append, ends]
    cases N.g.arrows[j]? with
    | none => simp
    | some a =>
      obtain ⟨a, b⟩ := a
      by_cases hab : a = u
      · simp [hab, ih]
      · simp [hab]

theorem visits_append_singleton (u : ℕ) (p : List ℕ) (i : ℕ) :
    N.visits u (p ++ [i]) = N.visits u p ++ [N.target i] := by
  simp [visits]

theorem pathCost_append (p q : List ℕ) : N.pathCost (p ++ q) = N.pathCost p + N.pathCost q := by
  simp [pathCost]

theorem pathCost_nonneg (h : N.NoArrowBelowZero) (p : List ℕ) : 0 ≤ N.pathCost p := by
  unfold pathCost
  refine List.sum_nonneg fun c hc => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
  unfold arrowCost
  rw [List.getD_eq_getElem?_getD]
  cases hi : N.cost[i]? with
  | none => simp
  | some c => exact h c (List.mem_of_getElem? hi)

theorem isPath_nil (s : ℕ) : N.IsPath s [] s := ⟨rfl, by simp [visits]⟩

theorem isPath_nil_iff {s v : ℕ} : N.IsPath s [] v ↔ v = s := by
  simp [IsPath, ends, visits, eq_comm]

/-- **A path grows by one arrow** to a vertex it has not passed. -/
theorem IsPath.snoc {s : ℕ} {p : List ℕ} {x i w : ℕ} (hp : N.IsPath s p x)
    (hi : N.g.arrows[i]? = some (x, w)) (hw : w ∉ N.visits s p) :
    N.IsPath s (p ++ [i]) w ∧ N.visits s (p ++ [i]) = N.visits s p ++ [w] := by
  have hv : N.visits s (p ++ [i]) = N.visits s p ++ [w] := by
    rw [visits_append_singleton, target_eq hi]
  refine ⟨⟨ends_append_singleton.2 ⟨x, hp.1, hi⟩, ?_⟩, hv⟩
  rw [hv, List.nodup_append]
  exact ⟨hp.2, List.nodup_singleton w, fun a ha b hb => by
    rw [List.mem_singleton] at hb; subst hb; exact fun h => hw (h ▸ ha)⟩

/-- **A path comes apart at its last arrow.** -/
theorem IsPath.eq_snoc {s : ℕ} {p : List ℕ} {w : ℕ} (hp : N.IsPath s p w) (hne : p ≠ []) :
    ∃ q i x, p = q ++ [i] ∧ N.IsPath s q x ∧ N.g.arrows[i]? = some (x, w) ∧
      w ∉ N.visits s q ∧ N.visits s p = N.visits s q ++ [w] := by
  obtain ⟨q, i, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left hne
  rw [List.concat_eq_append] at hp ⊢
  obtain ⟨x, hx, hi⟩ := ends_append_singleton.1 hp.1
  have hv : N.visits s (q ++ [i]) = N.visits s q ++ [w] := by
    rw [visits_append_singleton, target_eq hi]
  have hnd := hp.2
  rw [hv, List.nodup_append] at hnd
  exact ⟨q, i, x, rfl, ⟨hx, hnd.1⟩, hi, fun h => hnd.2.2 w h w (by simp) rfl, hv⟩

/-- A path's vertices end at its end. -/
theorem IsPath.visits_eq {s : ℕ} {p : List ℕ} {v : ℕ} (hp : N.IsPath s p v) :
    N.visits s p = (N.visits s p).dropLast ++ [v] := by
  rcases eq_or_ne p [] with rfl | hne
  · rw [isPath_nil_iff.1 hp]; rfl
  · obtain ⟨q, i, x, rfl, -, -, -, hv⟩ := hp.eq_snoc hne
    rw [hv, List.dropLast_concat]

theorem IsPath.mem_visits {s : ℕ} {p : List ℕ} {v : ℕ} (hp : N.IsPath s p v) :
    v ∈ N.visits s p := by
  rw [hp.visits_eq]; simp

/-- In a path, a vertex before the last is not the last. -/
theorem IsPath.ne_of_mem_dropLast {s : ℕ} {p : List ℕ} {v y : ℕ} (hp : N.IsPath s p v)
    (hy : y ∈ (N.visits s p).dropLast) : y ≠ v := by
  have hnd := hp.2
  rw [hp.visits_eq, List.nodup_append] at hnd
  exact fun h => hnd.2.2 y hy v (by simp) h

/-- A path's vertices are the start and vertices of the graph. -/
theorem IsPath.lt_of_mem {s : ℕ} {p : List ℕ} {v y : ℕ} (hN : N.WellFormed) (hs : s < N.g.n)
    (hp : N.IsPath s p v) (hy : y ∈ N.visits s p) : y < N.g.n := by
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hs
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    have hlt := lt_of_ends hp.1 i hi
    have hmem : N.g.arrows[i] ∈ N.g.arrows := List.getElem_mem hlt
    rw [target, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact (hN.1 _ hmem).2

theorem IsPath.lt {s : ℕ} {p : List ℕ} {v : ℕ} (hN : N.WellFormed) (hs : s < N.g.n)
    (hp : N.IsPath s p v) : v < N.g.n :=
  hp.lt_of_mem hN hs hp.mem_visits

/-- A path's arrows lead from its start to its end. -/
theorem reaches_of_ends {u : ℕ} {p : List ℕ} {v : ℕ} (h : N.ends u p = some v) :
    N.g.Reaches u v := by
  induction p generalizing u with
  | nil => simp only [ends, Option.some.injEq] at h; subst h; exact Relation.ReflTransGen.refl
  | cons j p ih =>
    simp only [ends] at h
    split at h
    · rename_i a b hj
      split_ifs at h with hau
      subst hau
      exact Relation.ReflTransGen.head (List.mem_of_getElem? hj) (ih h)
    · exact absurd h (by simp)

end Network

namespace Dijkstra

open Network

variable {N : Network}

theorem through_mono {S S' : List ℕ} {s : ℕ} {p : List ℕ} (h : Through N S s p)
    (hS : ∀ x ∈ S, x ∈ S') : Through N S' s p := fun x hx => hS x (h x hx)

theorem through_nil (S : List ℕ) (s : ℕ) : Through N S s [] := by simp [Through, visits]

/-- With nothing settled, the only path through settled vertices is the empty one. -/
theorem eq_nil_of_through_nil {s : ℕ} {p : List ℕ} (h : Through N [] s p) : p = [] := by
  cases p with
  | nil => rfl
  | cons i p =>
    exact absurd (h s (by simp [visits, List.dropLast_cons_cons])) (by simp)

/-- **A path comes apart at its first vertex outside `S`**: a path through `S` to that vertex, then
the rest. -/
theorem split_first_outside {S : List ℕ} {s : ℕ} :
    ∀ {p : List ℕ} {v : ℕ}, N.IsPath s p v → (∃ y ∈ N.visits s p, y ∉ S) →
      ∃ q r y, p = q ++ r ∧ N.IsPath s q y ∧ y ∉ S ∧ Through N S s q := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro v hp ⟨y, hy, hyS⟩
    simp only [visits, List.map_nil, List.mem_singleton] at hy
    subst hy
    exact ⟨[], [], y, rfl, isPath_nil y, hyS, through_nil S y⟩
  | append_singleton p i ih =>
    intro v hp ⟨y, hy, hyS⟩
    obtain ⟨q, j, x, hqj, hq, -, -, hv⟩ := hp.eq_snoc (by simp)
    obtain ⟨rfl, hij⟩ := List.append_inj' hqj rfl
    obtain rfl : i = j := by simpa using hij
    by_cases hall : ∀ z ∈ N.visits s p, z ∈ S
    · refine ⟨p ++ [i], [], v, by simp, hp, fun hvS => ?_, ?_⟩
      · rw [hv] at hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hyS (hall y hy)
        · rw [List.mem_singleton.1 hy] at hyS; exact hyS hvS
      · intro z hz
        rw [hv, List.dropLast_concat] at hz
        exact hall z hz
    · push Not at hall
      obtain ⟨q', r, y', rfl, hq', hy'S, ht⟩ := ih hq hall
      exact ⟨q', r ++ [i], y', by simp, hq', hy'S, ht⟩

/-- The arrows tried, from vertices listed once, are all different. -/
theorem nodup_tried {st : State} (h : st.settled.Nodup) : (tried N st).Nodup := by
  unfold tried
  refine List.nodup_flatMap.2 ⟨fun v _ => nodup_out_ids N.g v, ?_⟩
  refine h.pairwise_of_forall_ne fun a _ b _ hab => ?_
  intro i hia hib
  obtain ⟨⟨w, j⟩, hw, rfl⟩ := List.mem_map.1 hia
  obtain ⟨⟨w', j'⟩, hw', hj⟩ := List.mem_map.1 hib
  simp only at hj
  subst hj
  have h1 := (mem_out.1 hw).2
  rw [(mem_out.1 hw').2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact hab h1.1.symm

/-- Every arrow tried is an arrow of the graph. -/
theorem lt_of_mem_tried {st : State} {i : ℕ} (h : i ∈ tried N st) : i < N.g.arrows.length := by
  obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 h
  obtain ⟨⟨w, j⟩, hw, rfl⟩ := List.mem_map.1 hv
  exact (List.getElem?_eq_some_iff.1 (mem_out.1 hw).2).1

theorem length_tried_le {st : State} (h : st.settled.Nodup) :
    (tried N st).length ≤ N.g.arrows.length := by
  simpa using (nodup_tried h).length_le_of_subset
    (fun i hi => List.mem_range.2 (lt_of_mem_tried hi))

end Dijkstra

end AlgoDesign.Paths
