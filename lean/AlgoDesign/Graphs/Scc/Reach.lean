/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Dedup
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Strong components: searching by sweeps finds exactly what is reachable

`mem_reachFrom_iff`: `n` sweeps of `grow` from a vertex `u < n` find exactly the vertices reachable
from `u` by steps of `next`, when every step stays below `n`. Each sweep either adds a vertex or
changes nothing, and once a sweep changes nothing no later sweep does; only `n` vertices exist, so
by sweep `n` the found set is closed under a step, and holds everything reachable.

Then the searches on a graph's rows: `forward g` steps along arrows, `backward g` against them
(`mem_forward`, `mem_backward`), so on a well-formed graph a search on the rows finds exactly the
vertices reachable (`mem_reachFrom_forward`), and reachability is decidable, as is whether two
vertices of a `Graph` are in one piece.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

open Digraph

/-! ## Searching by sweeps

A search from a vertex, written to be read and to compute in the kernel: each sweep adds every
vertex one step on from the vertices found so far. `n` sweeps find everything reachable
(`Scc.mem_reachFrom_iff`, `Reach.lean`). -/

/-- One sweep: the vertices found, and every vertex one step of `next` on from them, in increasing
order. -/
def grow (n : ℕ) (next : ℕ → List ℕ) (found : List ℕ) : List ℕ :=
  (List.range n).filter fun v => v ∈ found || found.any fun u => v ∈ next u

/-- `k` sweeps of `grow`, the first argument being `k`. -/
def search (n : ℕ) (next : ℕ → List ℕ) : ℕ → List ℕ → List ℕ
  | 0, found => found
  | k + 1, found => search n next k (grow n next found)

/-- The vertices reachable from `u` by steps of `next`, among `0 .. n - 1`: `n` sweeps. -/
def reachFrom (n : ℕ) (next : ℕ → List ℕ) (u : ℕ) : List ℕ := search n next n [u]

/-- The vertices one arrow on from `v`, read off `v`'s row. -/
def forward (g : Digraph) (v : ℕ) : List ℕ := (g.out v).map Prod.fst

/-- The vertices one arrow back from `v`, read off `v`'s reversed row. -/
def backward (g : Digraph) (v : ℕ) : List ℕ := (g.into v).map Prod.fst

/-- `u` and `v` reach each other. -/
def Mutual (g : Digraph) (u v : ℕ) : Prop := g.Reaches u v ∧ g.Reaches v u

open Relation

variable {n : ℕ} {next : ℕ → List ℕ}

theorem mem_grow {s : List ℕ} {v : ℕ} :
    v ∈ grow n next s ↔ v < n ∧ (v ∈ s ∨ ∃ u ∈ s, v ∈ next u) := by
  simp [grow, List.mem_filter, List.any_eq_true]

/-- `grow` reads only which vertices were found, not their order or repeats. -/
theorem grow_congr {s t : List ℕ} (h : ∀ v, v ∈ s ↔ v ∈ t) : grow n next s = grow n next t := by
  unfold grow
  congr 1
  funext v
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, h]

/-- A sweep taken last is a sweep taken first. -/
theorem search_succ' (k : ℕ) (s : List ℕ) :
    search n next (k + 1) s = grow n next (search n next k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (grow n next s)

/-- A found set is closed when a sweep adds nothing to it. -/
def Closed (n : ℕ) (next : ℕ → List ℕ) (s : List ℕ) : Prop := ∀ v, v ∈ grow n next s ↔ v ∈ s

/-- Every vertex found is reachable from `u`, if every vertex started from is. -/
theorem reach_of_mem_search {u : ℕ} :
    ∀ (k : ℕ) (s : List ℕ), (∀ v ∈ s, ReflTransGen (fun a b => b ∈ next a) u v) →
      ∀ v ∈ search n next k s, ReflTransGen (fun a b => b ∈ next a) u v := by
  intro k
  induction k with
  | zero => exact fun s hs => hs
  | succ k ih =>
    intro s hs
    refine ih _ fun v hv => ?_
    obtain ⟨-, hv | ⟨w, hw, hvw⟩⟩ := mem_grow.mp hv
    · exact hs v hv
    · exact (hs w hw).tail hvw

/-- Every sweep keeps what was found, while what was found lies below `n`. -/
theorem subset_grow {s : List ℕ} (hs : ∀ v ∈ s, v < n) {v : ℕ} (hv : v ∈ s) :
    v ∈ grow n next s :=
  mem_grow.mpr ⟨hs v hv, Or.inl hv⟩

theorem lt_of_mem_grow {s : List ℕ} {v : ℕ} (hv : v ∈ grow n next s) : v < n :=
  (mem_grow.mp hv).1

theorem lt_of_mem_search {s : List ℕ} (hs : ∀ v ∈ s, v < n) :
    ∀ (k : ℕ), ∀ v ∈ search n next k s, v < n
  | 0 => hs
  | k + 1 => by
    rw [search_succ']
    exact fun _ hv => lt_of_mem_grow hv

/-- Every sweep keeps what was found. -/
theorem subset_search {s : List ℕ} (hs : ∀ v ∈ s, v < n) :
    ∀ (k : ℕ), ∀ {v}, v ∈ s → v ∈ search n next k s
  | 0 => fun hv => hv
  | k + 1 => fun hv => by
    rw [search_succ']
    exact subset_grow (lt_of_mem_search hs k) (subset_search hs k hv)

/-- Once a sweep adds nothing, no later sweep does. -/
theorem closed_grow {s : List ℕ} (h : Closed n next s) : Closed n next (grow n next s) := by
  intro v
  rw [grow_congr h]

/-- Each sweep before the found set closes adds a vertex: after `k` sweeps from one vertex, either
the set is closed or it holds at least `k + 1` vertices. -/
theorem closed_or_card {s : List ℕ} (hs : ∀ v ∈ s, v < n) (hne : s ≠ []) :
    ∀ k, Closed n next (search n next k s) ∨ k + 1 ≤ (search n next k s).toFinset.card
  | 0 => Or.inr (by
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil s hne
      exact Finset.card_pos.mpr ⟨v, List.mem_toFinset.mpr hv⟩)
  | k + 1 => by
    rw [search_succ']
    rcases closed_or_card hs hne k with hc | hk
    · exact Or.inl (closed_grow hc)
    · by_cases hc : Closed n next (search n next k s)
      · exact Or.inl (closed_grow hc)
      · right
        have hlt := lt_of_mem_search (next := next) hs k
        have hsub : (search n next k s).toFinset ⊆ (grow n next (search n next k s)).toFinset :=
          fun v hv => List.mem_toFinset.mpr (subset_grow hlt (List.mem_toFinset.mp hv))
        have hne' : (search n next k s).toFinset ≠ (grow n next (search n next k s)).toFinset := by
          intro heq
          apply hc
          intro v
          rw [← List.mem_toFinset, ← heq, List.mem_toFinset]
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
        omega

/-- A found set below `n` holds at most `n` vertices. -/
theorem card_le {s : List ℕ} (hs : ∀ v ∈ s, v < n) : s.toFinset.card ≤ n := by
  calc s.toFinset.card ≤ (Finset.range n).card :=
        Finset.card_le_card fun v hv => Finset.mem_range.mpr (hs v (List.mem_toFinset.mp hv))
    _ = n := Finset.card_range n

/-- After `n` sweeps from one vertex, the found set is closed. -/
theorem closed_search {s : List ℕ} (hs : ∀ v ∈ s, v < n) (hne : s ≠ []) :
    Closed n next (search n next n s) := by
  rcases closed_or_card (next := next) hs hne n with hc | hk
  · exact hc
  · have := card_le (lt_of_mem_search (next := next) hs n)
    omega

/-- A closed set holds everything reachable from its members, when every step stays below
`n`. -/
theorem mem_of_closed {s : List ℕ} (hc : Closed n next s) (hnext : ∀ a, ∀ b ∈ next a, b < n)
    {u v : ℕ} (hu : u ∈ s) (h : ReflTransGen (fun a b => b ∈ next a) u v) : v ∈ s := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact (hc _).mp (mem_grow.mpr ⟨hnext _ _ hbc, Or.inr ⟨_, ih, hbc⟩⟩)

/-- **Searching by sweeps finds exactly what is reachable**: from `u < n`, when every step stays
below `n`. -/
theorem mem_reachFrom_iff (hnext : ∀ a, ∀ b ∈ next a, b < n) {u v : ℕ} (hu : u < n) :
    v ∈ reachFrom n next u ↔ ReflTransGen (fun a b => b ∈ next a) u v := by
  have hs : ∀ w ∈ [u], w < n := by simpa using hu
  constructor
  · exact reach_of_mem_search n [u] (by simp [ReflTransGen.refl]) v
  · intro h
    exact mem_of_closed (closed_search hs (by simp)) hnext (subset_search hs n (by simp)) h

/-! ## Searching a graph's rows -/

variable {g : Digraph}

theorem mem_out {v w i : ℕ} : (w, i) ∈ g.out v ↔ w < g.n ∧ g.arrows[i]? = some (v, w) := by
  simp only [Digraph.out, Digraph.idsBetween, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨ha, hj⟩
  · rintro ⟨hw, hi⟩
    exact ⟨w, hw, i, ⟨(List.getElem?_eq_some_iff.mp hi).1, hi⟩, rfl, rfl⟩

theorem mem_into {v w i : ℕ} : (w, i) ∈ g.into v ↔ w < g.n ∧ g.arrows[i]? = some (w, v) := by
  simp only [Digraph.into, Digraph.idsBetween, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, j, ⟨-, hj⟩, rfl, rfl⟩
    exact ⟨ha, hj⟩
  · rintro ⟨hw, hi⟩
    exact ⟨w, hw, i, ⟨(List.getElem?_eq_some_iff.mp hi).1, hi⟩, rfl, rfl⟩

/-- A step forward is an arrow to a vertex of the graph. -/
theorem mem_forward {v w : ℕ} : w ∈ forward g v ↔ w < g.n ∧ g.Arrow v w := by
  unfold forward Digraph.Arrow
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨w', i⟩, hm, rfl⟩
    obtain ⟨hw, hi⟩ := mem_out.mp hm
    exact ⟨hw, List.mem_iff_getElem?.mpr ⟨i, hi⟩⟩
  · rintro ⟨hw, h⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact ⟨(w, i), mem_out.mpr ⟨hw, hi⟩, rfl⟩

/-- A step backward is an arrow from a vertex of the graph. -/
theorem mem_backward {v w : ℕ} : w ∈ backward g v ↔ w < g.n ∧ g.Arrow w v := by
  unfold backward Digraph.Arrow
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨w', i⟩, hm, rfl⟩
    obtain ⟨hw, hi⟩ := mem_into.mp hm
    exact ⟨hw, List.mem_iff_getElem?.mpr ⟨i, hi⟩⟩
  · rintro ⟨hw, h⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
    exact ⟨(w, i), mem_into.mpr ⟨hw, hi⟩, rfl⟩

/-- On a well-formed graph, a step forward is an arrow. -/
theorem forward_eq (hg : g.WellFormed) : (fun a b => b ∈ forward g a) = g.Arrow := by
  funext a b
  exact propext (mem_forward.trans ⟨fun h => h.2, fun h => ⟨(hg _ h).2, h⟩⟩)

/-- **On a well-formed graph, a search on the rows finds exactly the vertices reachable.** -/
theorem mem_reachFrom_forward (hg : g.WellFormed) {u v : ℕ} (hu : u < g.n) :
    v ∈ reachFrom g.n (forward g) u ↔ g.Reaches u v := by
  rw [mem_reachFrom_iff (fun _ _ hb => (mem_forward.mp hb).1) hu, forward_eq hg]
  rfl

/-! ## Reachability is decidable -/

/-- The heads of the arrows leaving `v`, read off the arrow list. -/
def heads (g : Digraph) (v : ℕ) : List ℕ := (g.arrows.filter fun a => a.1 = v).map Prod.snd

/-- A bound above every vertex an arrow touches, and above `n`. -/
def bound (g : Digraph) : ℕ := g.n + (g.arrows.map fun a => a.1 + a.2 + 1).sum

theorem lt_bound {a : ℕ × ℕ} (ha : a ∈ g.arrows) : a.1 < bound g ∧ a.2 < bound g := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun a : ℕ × ℕ => a.1 + a.2 + 1) ha)
  unfold bound
  omega

theorem mem_heads {v w : ℕ} : w ∈ heads g v ↔ g.Arrow v w := by
  simp only [heads, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists,
    exists_eq_right, Digraph.Arrow]

theorem heads_eq : (fun a b => b ∈ heads g a) = g.Arrow := by
  funext a b
  exact propext mem_heads

/-- Reachability, decided by a search over every vertex an arrow touches. -/
instance decidableReaches (g : Digraph) (u v : ℕ) : Decidable (g.Reaches u v) :=
  if hu : u < bound g then
    decidable_of_iff (v ∈ reachFrom (bound g) (heads g) u) (by
      rw [mem_reachFrom_iff (fun _ _ hb => (lt_bound (mem_heads.mp hb)).2) hu, heads_eq]
      rfl)
  else
    decidable_of_iff (u = v) (by
      constructor
      · rintro rfl
        exact ReflTransGen.refl
      · intro h
        rcases ReflTransGen.cases_head h with h | ⟨b, hab, -⟩
        · exact h
        · exact absurd (lt_bound hab).1 hu)

instance (g : Digraph) (u v : ℕ) : Decidable (Mutual g u v) := by
  unfold Mutual; infer_instance

namespace AlgorithmT

/-- The vertices reachable from each vertex along a retreating path inside its strong component
whose every arrow the walk has come back over (Tarjan–Zwick p. 7: retreats on the path's arrows
happened in the reverse of their order along it). Taking the retreats in order, the arrow
retreated `b`-th can start such a path only if the rest of the path uses arrows retreated before
it: entry `v` after `b` retreats is `v` with every vertex a path from `v` reaches whose first
arrow is among the first `b` retreats. -/
def retreatReach (g : Digraph) (log : List (ℕ × ℕ)) : ℕ → List (List ℕ)
  | 0 => (List.range g.n).map fun v => [v]
  | b + 1 =>
    let r := retreatReach g log b
    (List.range g.n).map fun v =>
      r.getD v [] ++ match log[b]? with
        | some (x, y) => if x = v ∧ Mutual g x y then r.getD y [] else []
        | none => []

end AlgorithmT

end AlgoDesign.Graphs.Scc

namespace AlgoDesign.Graphs.Blocks

/-! ## Connectivity is decidable

Whether two vertices of a `Graph` are in one piece, decided by a search, so that `Blocks.pieces`
can count the pieces. -/

open Relation

/-- The neighbours of `v`, read off the link list: one per end of a link at `v`. -/
def nbrs (g : Graph) (v : ℕ) : List ℕ :=
  (g.links.filter fun l => l.1 = v).map Prod.snd ++ (g.links.filter fun l => l.2 = v).map Prod.fst

theorem mem_nbrs {g : Graph} {v w : ℕ} : w ∈ nbrs g v ↔ g.Link v w := by
  simp only [nbrs, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists,
    Graph.Link]
  constructor
  · rintro (⟨a, b, ⟨h, rfl⟩, rfl⟩ | ⟨a, b, ⟨h, rfl⟩, rfl⟩) <;> simp_all
  · rintro (h | h)
    · exact Or.inl ⟨v, w, ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨w, v, ⟨h, rfl⟩, rfl⟩

theorem nbrs_eq (g : Graph) : (fun a b => b ∈ nbrs g a) = g.Link := by
  funext a b
  exact propext mem_nbrs

/-- The links read both ways, as a directed graph. -/
def both (g : Graph) : Digraph := ⟨g.n, g.links ++ g.links.map Prod.swap⟩

theorem both_reaches (g : Graph) : (both g).Reaches = g.Connected := by
  have : (both g).Arrow = g.Link := by
    funext u v
    simp [Digraph.Arrow, both, Graph.Link]
  simp only [Digraph.Reaches, Graph.Connected, this]

/-- Whether two vertices are in one piece, decided by a search. -/
instance decidableConnected (g : Graph) (u v : ℕ) : Decidable (g.Connected u v) :=
  if h : g.WellFormed ∧ u < g.n then
    decidable_of_iff (v ∈ Scc.reachFrom g.n (nbrs g) u) (by
      rw [Scc.mem_reachFrom_iff (fun _ _ hb => ?_) h.2, nbrs_eq]
      · rfl
      · rcases mem_nbrs.mp hb with hb | hb
        · exact (h.1 _ hb).2
        · exact (h.1 _ hb).1)
  else decidable_of_iff ((both g).Reaches u v) (by rw [both_reaches])

end AlgoDesign.Graphs.Blocks
