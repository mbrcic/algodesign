/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Logic.Relation
public import Mathlib.Data.List.Range
public import Mathlib.Order.Basic

/-!
# Graphs: vertices, arrows and links

Sources: the Graphs chapter; Ahuja, Magnanti and Orlin, *Network Flows* (1993), §2.3, the forward
and reverse star, p. 38: "we will store each arc (i, j) of an undirected network twice".

A **directed graph** (`Digraph`) is a number of vertices `0 .. n - 1` and a list of arrows; an
arrow's id is its position in the list. Loops and doubled arrows are allowed: each algorithm says
what it accepts. An **undirected graph** (`Graph`) is the same with links in place of arrows; a
link joins its two vertices both ways.

Each vertex's row lists the arrows leaving it as (neighbour, id) pairs, sorted by neighbour and then
by id, the order every algorithm of the chapter walks them in, in all three languages. `Digraph.out`
is that row, `Digraph.into` the row of the arrows turned around, and `Graph.adj` an undirected
vertex's row: a link appears once in each end's row, and a loop twice in its vertex's row. These are
specification functions, written to be read and to compute in the kernel, not to be fast.
-/

@[expose] public section

namespace AlgoDesign.Graphs

/-- A directed graph: vertices `0 .. n - 1` and arrows `(from, to)`; an arrow's id is its index. -/
structure Digraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The arrows, as (from, to); the id of an arrow is its position. -/
  arrows : List (ℕ × ℕ)
deriving DecidableEq, Repr

namespace Digraph

variable (g : Digraph)

/-- Every arrow joins two vertices of the graph. -/
def WellFormed : Prop := ∀ a ∈ g.arrows, a.1 < g.n ∧ a.2 < g.n

instance : DecidablePred WellFormed := fun g =>
  inferInstanceAs (Decidable (∀ a ∈ g.arrows, a.1 < g.n ∧ a.2 < g.n))

/-- There is an arrow from `u` to `v`. -/
def Arrow (u v : ℕ) : Prop := (u, v) ∈ g.arrows

instance (u v : ℕ) : Decidable (g.Arrow u v) := inferInstanceAs (Decidable ((u, v) ∈ g.arrows))

/-- `u` reaches `v`: zero or more arrows lead from `u` to `v`. -/
def Reaches : ℕ → ℕ → Prop := Relation.ReflTransGen g.Arrow

/-- The ids of the arrows from `v` to `w`, in increasing order. -/
def idsBetween (v w : ℕ) : List ℕ :=
  (List.range g.arrows.length).filter fun i => g.arrows[i]? = some (v, w)

/-- **The row of `v`**: every arrow leaving `v` as (neighbour, id), sorted by neighbour, then id. -/
def out (v : ℕ) : List (ℕ × ℕ) :=
  (List.range g.n).flatMap fun w => (g.idsBetween v w).map fun i => (w, i)

/-- **The reversed row of `v`**: every arrow entering `v` as (neighbour, id), sorted the same
way. -/
def into (v : ℕ) : List (ℕ × ℕ) :=
  (List.range g.n).flatMap fun w => (g.idsBetween w v).map fun i => (w, i)

/-- The graph with every arrow turned around, each keeping its id. -/
def reverse : Digraph := ⟨g.n, g.arrows.map Prod.swap⟩

end Digraph

/-- An undirected graph: vertices `0 .. n - 1` and links `{a, b}`; a link's id is its index. -/
structure Graph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The links, each given by its two ends; the id of a link is its position. -/
  links : List (ℕ × ℕ)
deriving DecidableEq, Repr

namespace Graph

variable (g : Graph)

/-- Every link joins two vertices of the graph. -/
def WellFormed : Prop := ∀ a ∈ g.links, a.1 < g.n ∧ a.2 < g.n

instance : DecidablePred WellFormed := fun g =>
  inferInstanceAs (Decidable (∀ a ∈ g.links, a.1 < g.n ∧ a.2 < g.n))

/-- A link joins `u` and `v`, either way round. -/
def Link (u v : ℕ) : Prop := (u, v) ∈ g.links ∨ (v, u) ∈ g.links

instance (u v : ℕ) : Decidable (g.Link u v) :=
  inferInstanceAs (Decidable ((u, v) ∈ g.links ∨ (v, u) ∈ g.links))

/-- `u` and `v` are in one piece: zero or more links lead from one to the other. -/
def Connected : ℕ → ℕ → Prop := Relation.ReflTransGen g.Link

/-- The entries link `i` gives in `v`'s row towards `w`: one per end at `v` whose other end is
`w`, so a loop at `v` gives two. -/
def entries (v w i : ℕ) : List ℕ :=
  match g.links[i]? with
  | some (a, b) =>
    (if a = v ∧ b = w then [i] else []) ++ (if b = v ∧ a = w then [i] else [])
  | none => []

/-- **The row of `v`**: one entry (neighbour, id) per end of a link at `v`, sorted by neighbour,
then id. A link between two vertices is in both rows; a loop is twice in its vertex's row. -/
def adj (v : ℕ) : List (ℕ × ℕ) :=
  (List.range g.n).flatMap fun w =>
    ((List.range g.links.length).flatMap fun i => g.entries v w i).map fun i => (w, i)

end Graph

/-! ## Examples, checked by the kernel -/

/-- Rows are sorted by neighbour, then id, whatever order the arrows came in. -/
example : (Digraph.out ⟨3, [(0, 2), (0, 1), (0, 2), (1, 0)]⟩ 0) = [(1, 1), (2, 0), (2, 2)] := by
  decide

example : (Digraph.into ⟨3, [(0, 2), (0, 1), (0, 2), (1, 0)]⟩ 2) = [(0, 0), (0, 2)] := by decide

/-- A link is in both ends' rows with one id; a loop is twice in its vertex's row. -/
example : Graph.adj ⟨2, [(0, 1), (1, 1)]⟩ 1 = [(0, 0), (1, 1), (1, 1)] := by decide

example : Graph.adj ⟨2, [(0, 1), (1, 1)]⟩ 0 = [(1, 0)] := by decide

end AlgoDesign.Graphs
