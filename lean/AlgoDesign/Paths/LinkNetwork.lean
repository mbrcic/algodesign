/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph
public import AlgoDesign.Graphs.UnionFind.Promise
public import Mathlib.Data.List.Sublists
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Paths: links with costs

Source: the Paths chapter, "After the big snow".

A **link network** (`LinkNetwork`) is an undirected `Graph` and one integer cost per link, listed
by link id, the undirected sibling of `Network`. Two links between the same two vertices may cost
differently, so a set of links is a list of link ids, not of vertex pairs.

A set of links `F` **joins** two vertices when a chain of its links leads from one to the other
(`Joins`): the Graphs chapter's `Joined` over the links' ends, the relation whose classes are the
union-find's groups. `F` **closes no cycle** when none of its links joins two vertices the others
already join (`ClosesNoCycle`); so a loop, or a link twice, closes a cycle. A **spanning forest**
is a set of the graph's links that joins every two vertices the graph joins and closes no cycle,
and a **cheapest** one has no other below its total. These are specification definitions, written
to be read and to compute in the kernel: whether `F` joins two vertices is decided by merging
`F`'s links in the Graphs chapter's union-find, and a question about every set of links by the
sublists of the link ids.
-/

@[expose] public section

namespace AlgoDesign.Paths

open AlgoDesign.Graphs AlgoDesign.Graphs.UnionFind

/-- A link network: an undirected graph and the cost of each of its links, listed by link id. -/
structure LinkNetwork where
  /-- The vertices and links. -/
  g : Graph
  /-- The cost of each link, by link id. -/
  cost : List ℤ
deriving DecidableEq, Repr

namespace LinkNetwork

variable (N : LinkNetwork)

/-- Every link joins two vertices of the graph, and every link has one cost. -/
def WellFormed : Prop := N.g.WellFormed ∧ N.cost.length = N.g.links.length

instance : DecidablePred WellFormed := fun N =>
  inferInstanceAs (Decidable (N.g.WellFormed ∧ N.cost.length = N.g.links.length))

/-- The cost of link `i`. -/
def linkCost (i : ℕ) : ℤ := N.cost.getD i 0

/-- The two ends of link `i`. -/
def ends (i : ℕ) : ℕ × ℕ := N.g.links.getD i (0, 0)

/-- **The links `F` join `u` and `v`**: a chain of links of `F`, each read either way, leads from
`u` to `v`; every vertex is joined to itself. -/
def Joins (F : List ℕ) (u v : ℕ) : Prop := Joined (F.map N.ends) u v

/-- **The total cost** of the links `F`. -/
def total (F : List ℕ) : ℤ := (F.map N.linkCost).sum

/-- **The links `F` join every two vertices the graph joins.** -/
def JoinsWhatGraphJoins (F : List ℕ) : Prop := ∀ u v, N.g.Connected u v → N.Joins F u v

/-- **The links `F` close no cycle**: no link of `F` joins two vertices the other links of `F`
already join. -/
def ClosesNoCycle (F : List ℕ) : Prop := ∀ i ∈ F, ¬ N.Joins (F.erase i) (N.ends i).1 (N.ends i).2

/-- **A spanning forest**: links of the graph that join every two vertices the graph joins and close
no cycle. -/
def IsSpanningForest (F : List ℕ) : Prop :=
  (∀ i ∈ F, i < N.g.links.length) ∧ N.JoinsWhatGraphJoins F ∧ N.ClosesNoCycle F

/-- **A cheapest spanning forest**: a spanning forest, and no spanning forest has a smaller
total. -/
def CheapestForest (F : List ℕ) : Prop :=
  N.IsSpanningForest F ∧ ∀ F', N.IsSpanningForest F' → N.total F ≤ N.total F'

/-! ## Joining, decided by the union-find -/

/-- A number above every vertex the pairs `us` and the vertices `u`, `v` name. -/
def bound (us : List (ℕ × ℕ)) (u v : ℕ) : ℕ :=
  (u :: v :: us.flatMap fun p => [p.1, p.2]).foldr max 0 + 1

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem lt_bound {us : List (ℕ × ℕ)} {u v : ℕ} :
    (∀ p ∈ us, p.1 < bound us u v ∧ p.2 < bound us u v) ∧ u < bound us u v ∧
      v < bound us u v := by
  refine ⟨fun p hp => ⟨Nat.lt_succ_of_le (le_foldr_max ?_), Nat.lt_succ_of_le (le_foldr_max ?_)⟩,
    Nat.lt_succ_of_le (le_foldr_max (by simp)), Nat.lt_succ_of_le (le_foldr_max (by simp))⟩ <;>
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨p, hp, by simp⟩))

/-- Whether a run of merges joined two items, decided by running it in the union-find. -/
instance decidableJoined (us : List (ℕ × ℕ)) (u v : ℕ) : Decidable (Joined us u v) :=
  decidable_of_iff (((init (bound us u v)).unions us).root u =
      ((init (bound us u v)).unions us).root v)
    (same_unions_iff lt_bound.1 lt_bound.2.1 lt_bound.2.2)

instance (F : List ℕ) (u v : ℕ) : Decidable (N.Joins F u v) :=
  inferInstanceAs (Decidable (Joined _ u v))

variable {N}

theorem joins_mono {F G : List ℕ} (h : ∀ i ∈ F, i ∈ G) {u v : ℕ} (hj : N.Joins F u v) :
    N.Joins G u v :=
  Relation.EqvGen.mono (fun a b hab => by
    obtain ⟨i, hi, he⟩ := List.mem_map.1 hab
    exact List.mem_map.2 ⟨i, h i hi, he⟩) u v hj

theorem joins_congr {F G : List ℕ} (h : ∀ i, i ∈ F ↔ i ∈ G) {u v : ℕ} :
    N.Joins F u v ↔ N.Joins G u v :=
  ⟨joins_mono fun i => (h i).1, joins_mono fun i => (h i).2⟩

theorem Joins.refl (F : List ℕ) (u : ℕ) : N.Joins F u u := Relation.EqvGen.refl u

theorem Joins.symm {F : List ℕ} {u v : ℕ} (h : N.Joins F u v) : N.Joins F v u :=
  Relation.EqvGen.symm u v h

theorem Joins.trans {F : List ℕ} {u v w : ℕ} (h₁ : N.Joins F u v) (h₂ : N.Joins F v w) :
    N.Joins F u w :=
  Relation.EqvGen.trans u v w h₁ h₂

/-- A link of `F` joins its two ends. -/
theorem joins_of_mem {F : List ℕ} {i : ℕ} (h : i ∈ F) : N.Joins F (N.ends i).1 (N.ends i).2 :=
  Relation.EqvGen.rel _ _ (List.mem_map.2 ⟨i, h, rfl⟩)

theorem ends_of_lt {i : ℕ} (h : i < N.g.links.length) : N.ends i = N.g.links[i] :=
  by simp [ends, List.getD_eq_getElem?_getD, h]

/-- The links `F` join every two vertices the graph joins exactly when they join the two ends of
every link. -/
theorem joinsWhatGraphJoins_iff {F : List ℕ} :
    N.JoinsWhatGraphJoins F ↔ ∀ i < N.g.links.length, N.Joins F (N.ends i).1 (N.ends i).2 := by
  constructor
  · intro h i hi
    refine h _ _ (Relation.ReflTransGen.single (Or.inl ?_))
    rw [ends_of_lt hi]
    exact List.getElem_mem hi
  · intro h u v huv
    induction huv with
    | refl => exact Joins.refl _ _
    | tail _ hwv ih =>
      refine ih.trans ?_
      rcases hwv with hl | hl <;> obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hl
      · have := h i hi; rwa [ends_of_lt hi, he] at this
      · have := h i hi; rw [ends_of_lt hi, he] at this; exact this.symm

instance (F : List ℕ) : Decidable (N.JoinsWhatGraphJoins F) :=
  decidable_of_iff' _ joinsWhatGraphJoins_iff

instance (F : List ℕ) : Decidable (N.ClosesNoCycle F) := by
  unfold ClosesNoCycle; infer_instance

instance (F : List ℕ) : Decidable (N.IsSpanningForest F) := by
  unfold IsSpanningForest; infer_instance

/-! ## Deciding questions about every set of links -/

/-- Links that close no cycle are all different. -/
theorem ClosesNoCycle.nodup {F : List ℕ} (h : N.ClosesNoCycle F) : F.Nodup := by
  refine List.nodup_iff_count_le_one.2 fun a => ?_
  by_cases ha : a ∈ F
  · have hn : a ∉ F.erase a := fun hm => h a ha (joins_of_mem hm)
    have := List.count_erase_self (a := a) (l := F)
    rw [List.count_eq_zero.2 hn] at this
    omega
  · rw [List.count_eq_zero.2 ha]; omega

theorem closesNoCycle_perm {F G : List ℕ} (h : F.Perm G) :
    N.ClosesNoCycle F ↔ N.ClosesNoCycle G := by
  have key : ∀ {F G : List ℕ}, F.Perm G → N.ClosesNoCycle F → N.ClosesNoCycle G :=
    fun hp hF i hi hj => hF i (hp.mem_iff.2 hi)
      ((joins_congr fun k => ((hp.erase i).mem_iff)).2 hj)
  exact ⟨key h, key h.symm⟩

theorem total_perm {F G : List ℕ} (h : F.Perm G) : N.total F = N.total G :=
  (h.map _).sum_eq

theorem isSpanningForest_perm {F G : List ℕ} (h : F.Perm G) :
    N.IsSpanningForest F ↔ N.IsSpanningForest G := by
  unfold IsSpanningForest JoinsWhatGraphJoins
  rw [closesNoCycle_perm h]
  simp only [h.mem_iff, joins_congr (fun i => h.mem_iff)]

/-- Every spanning forest is a sublist of the link ids, up to order. -/
theorem IsSpanningForest.exists_sublist {F : List ℕ} (h : N.IsSpanningForest F) :
    ∃ G ∈ (List.range N.g.links.length).sublists, G.Perm F := by
  obtain ⟨G, hG, hsub⟩ := List.subperm_of_subset h.2.2.nodup
    (fun i hi => List.mem_range.2 (h.1 i hi))
  exact ⟨G, List.mem_sublists.2 hsub, hG⟩

theorem cheapestForest_iff {F : List ℕ} :
    N.CheapestForest F ↔ N.IsSpanningForest F ∧
      ∀ F' ∈ (List.range N.g.links.length).sublists, N.IsSpanningForest F' →
        N.total F ≤ N.total F' := by
  refine and_congr_right fun _ => ⟨fun h F' _ => h F', fun h F' hF' => ?_⟩
  obtain ⟨G, hG, hp⟩ := hF'.exists_sublist
  rw [← total_perm hp]
  exact h G hG ((isSpanningForest_perm hp).2 hF')

instance (F : List ℕ) : Decidable (N.CheapestForest F) :=
  decidable_of_iff' _ cheapestForest_iff

end LinkNetwork

/-! ## Examples, checked by the kernel -/

/-- Two links between 0 and 1: either alone is a spanning forest, both together close a cycle, and
the cheaper one is the cheapest. -/
example : LinkNetwork.CheapestForest ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ [1] ∧
    ¬ LinkNetwork.CheapestForest ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ [0] ∧
    ¬ LinkNetwork.ClosesNoCycle ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ [0, 1] := by
  decide

/-- A loop closes a cycle. -/
example : ¬ LinkNetwork.ClosesNoCycle ⟨⟨2, [(1, 1)]⟩, [0]⟩ [0] := by decide

end AlgoDesign.Paths
