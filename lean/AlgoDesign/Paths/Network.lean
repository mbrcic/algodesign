/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.Permutation

/-!
# Paths: arrows with costs

Source: the Paths chapter.

A **network** (`Network`) is a `Digraph` and one integer cost per arrow, listed by arrow id. Two
arrows between the same two vertices may cost differently, so a path is the list of the ids of the
arrows it takes, not of the vertices it passes. A path may pass a vertex more than once (`IsWalk`);
`IsPath` is a path that never comes back to a vertex it has passed. A path that comes back to its
first vertex and passes no vertex twice on the way is a cycle (`IsCycle`).

The cost of a path is the sum of its arrows' costs; the cheapest cost over a set of paths
(`CheapestAmong`) is one that some path of the set costs, and that no path of the set beats. These
are specification definitions, written to be read and to compute in the kernel: `candidates`
lists every list of distinct arrow ids, so each question about all paths decides on a small
network.
-/

@[expose] public section

namespace AlgoDesign.Paths

open AlgoDesign.Graphs

/-- A network: a directed graph and the cost of each of its arrows, listed by arrow id. -/
structure Network where
  /-- The vertices and arrows. -/
  g : Digraph
  /-- The cost of each arrow, by arrow id. -/
  cost : List ℤ
deriving DecidableEq, Repr

namespace Network

variable (N : Network)

/-- Every arrow joins two vertices of the graph, and every arrow has one cost. -/
def WellFormed : Prop := N.g.WellFormed ∧ N.cost.length = N.g.arrows.length

instance : DecidablePred WellFormed := fun N =>
  inferInstanceAs (Decidable (N.g.WellFormed ∧ N.cost.length = N.g.arrows.length))

/-- **No arrow costs less than 0.** -/
def NoArrowBelowZero : Prop := ∀ c ∈ N.cost, 0 ≤ c

instance : DecidablePred NoArrowBelowZero := fun N =>
  inferInstanceAs (Decidable (∀ c ∈ N.cost, 0 ≤ c))

/-- The cost of arrow `i`. -/
def arrowCost (i : ℕ) : ℤ := N.cost.getD i 0

/-- The vertex arrow `i` leaves. -/
def source (i : ℕ) : ℕ := (N.g.arrows.getD i (0, 0)).1

/-- The vertex arrow `i` points to. -/
def target (i : ℕ) : ℕ := (N.g.arrows.getD i (0, 0)).2

/-- Where the arrows `p`, taken in order from `u`, arrive, when each leaves the vertex the one
before it arrived at; `none` when one does not. -/
def ends : ℕ → List ℕ → Option ℕ
  | u, [] => some u
  | u, i :: p =>
    match N.g.arrows[i]? with
    | some (a, b) => if a = u then ends b p else none
    | none => none

/-- The vertices the arrows `p` pass from `u`: `u`, then the vertex each arrow points to. -/
def visits (u : ℕ) (p : List ℕ) : List ℕ := u :: p.map N.target

/-- **`p` is a path from `s` to `v`**: its arrows lead from `s` to `v`, and it passes no vertex
twice. -/
def IsPath (s : ℕ) (p : List ℕ) (v : ℕ) : Prop := N.ends s p = some v ∧ (N.visits s p).Nodup

instance (s : ℕ) (p : List ℕ) (v : ℕ) : Decidable (N.IsPath s p v) := by
  unfold IsPath; infer_instance

/-- **The cost of a path**: the sum of its arrows' costs. -/
def pathCost (p : List ℕ) : ℤ := (p.map N.arrowCost).sum

/-- A known cost is at most `b`: there is one, and it is not above `b`. -/
def AtMost : Option ℤ → ℤ → Prop
  | some d, b => d ≤ b
  | none, _ => False

instance (c : Option ℤ) (b : ℤ) : Decidable (AtMost c b) := by
  cases c <;> unfold AtMost <;> infer_instance

/-- **`c` is the cheapest cost from `s` to `v` over the paths `ok` admits**: no such path costs
less than `c`, and some such path costs exactly `c`; `c` is `none` exactly when there is no such
path. -/
def CheapestAmong (ok : List ℕ → Prop) (s v : ℕ) (c : Option ℤ) : Prop :=
  (∀ p, N.IsPath s p v → ok p → AtMost c (N.pathCost p)) ∧
    ∀ d ∈ c, ∃ p, N.IsPath s p v ∧ ok p ∧ N.pathCost p = d

/-- **`c` is the cost of the cheapest path from `s` to `v`**, `none` when no path leads there. -/
def Cheapest (s v : ℕ) (c : Option ℤ) : Prop := N.CheapestAmong (fun _ => True) s v c

/-! ## Deciding questions about every path -/

/-- Every list of distinct arrow ids. -/
def candidates : List (List ℕ) := (List.range N.g.arrows.length).sublists.flatMap List.permutations'

variable {N}

theorem lt_of_ends {u : ℕ} {p : List ℕ} {v : ℕ} (h : N.ends u p = some v) :
    ∀ i ∈ p, i < N.g.arrows.length := by
  induction p generalizing u with
  | nil => simp
  | cons j p ih =>
    simp only [ends] at h
    split at h
    · rename_i a b hj
      split_ifs at h
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact (List.getElem?_eq_some_iff.1 hj).1
      · exact ih h i hi
    · exact absurd h (by simp)

/-- A path passes no arrow twice. -/
theorem IsPath.nodup {s : ℕ} {p : List ℕ} {v : ℕ} (h : N.IsPath s p v) : p.Nodup :=
  (List.nodup_cons.1 h.2).2.of_map _

/-- Every path is among the `candidates`. -/
theorem IsPath.mem_candidates {s : ℕ} {p : List ℕ} {v : ℕ} (h : N.IsPath s p v) :
    p ∈ N.candidates := by
  obtain ⟨q, hq, hsub⟩ := List.subperm_of_subset h.nodup
    (fun i hi => List.mem_range.2 (lt_of_ends h.1 i hi))
  exact List.mem_flatMap.2 ⟨q, List.mem_sublists.2 hsub, List.mem_permutations'.2 hq.symm⟩

theorem cheapestAmong_iff {ok : List ℕ → Prop} {s v : ℕ} {c : Option ℤ} :
    N.CheapestAmong ok s v c ↔
      (∀ p ∈ N.candidates, N.IsPath s p v → ok p → AtMost c (N.pathCost p)) ∧
        ∀ d ∈ c, ∃ p ∈ N.candidates, N.IsPath s p v ∧ ok p ∧ N.pathCost p = d := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p _ => h1 p, fun d hd => ?_⟩
    obtain ⟨p, hp, hok, hc⟩ := h2 d hd
    exact ⟨p, hp.mem_candidates, hp, hok, hc⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => h1 p hp.mem_candidates hp, fun d hd => ?_⟩
    obtain ⟨p, -, hp, hok, hc⟩ := h2 d hd
    exact ⟨p, hp, hok, hc⟩

instance (ok : List ℕ → Prop) [DecidablePred ok] (s v : ℕ) (c : Option ℤ) :
    Decidable (N.CheapestAmong ok s v c) :=
  decidable_of_iff' _ cheapestAmong_iff

instance (s v : ℕ) (c : Option ℤ) : Decidable (N.Cheapest s v c) :=
  inferInstanceAs (Decidable (N.CheapestAmong (fun _ => True) s v c))

/-! ## Paths that may pass a vertex again, and cycles -/

variable (N) in
/-- **`p` is a path from `s` to `v`**: its arrows lead from `s` to `v`; unlike `IsPath`, it may pass
a vertex more than once. Its cost is `pathCost p` too. -/
def IsWalk (s : ℕ) (p : List ℕ) (v : ℕ) : Prop := N.ends s p = some v

instance (s : ℕ) (p : List ℕ) (v : ℕ) : Decidable (N.IsWalk s p v) := by
  unfold IsWalk; infer_instance

variable (N) in
/-- **`p` is a cycle through `v`**: a path of at least one arrow from `v` back to `v` that passes
no vertex twice before it comes back. -/
def IsCycle (v : ℕ) (p : List ℕ) : Prop := p ≠ [] ∧ N.IsWalk v p v ∧ (N.visits v p).dropLast.Nodup

instance (v : ℕ) (p : List ℕ) : Decidable (N.IsCycle v p) := by
  unfold IsCycle; infer_instance

/-- A path that passes no vertex twice is a path. -/
theorem IsPath.isWalk {s : ℕ} {p : List ℕ} {v : ℕ} (h : N.IsPath s p v) : N.IsWalk s p v := h.1

end Network

/-! ## Examples, checked by the kernel -/

/-- Two arrows from 0 to 1 that cost differently: the cheaper one is the cheapest path. -/
example : Network.Cheapest ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ 0 1 (some 3) := by decide

/-- No path leads back to 0. -/
example : Network.Cheapest ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ 1 0 none := by decide

end AlgoDesign.Paths
