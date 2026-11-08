/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Spec
public import AlgoDesign.Graphs.TopoOrder.Spec

/-!
# Cheapest paths in a graph with no cycle: the specification

Sources: the Paths chapter, "What is this all about?"; Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms* (4th ed.), §22.2, DAG-SHORTEST-PATHS (p. 617): "As it processes each
vertex, it relaxes each edge that leaves the vertex"; Sedgewick and Wayne, *Algorithms* (4th ed.),
`AcyclicSP` (Prop. S, p. 658); Dasgupta, Papadimitriou and Vazirani, *Algorithms*, §4.7 (p. 130).
The order is the Graphs chapter's Kahn order (`TopoOrder.kahn`).

The walk takes the vertices in a topological order. For each vertex with a known cost, it tries
every arrow out of it, in its row's order: when the arrow's end has no known cost, or the arrow
gives less, the end gets the new cost and this vertex as its previous one. The start is known at
cost 0. Arrows may be negative. On a graph with a cycle there is no topological order,
and the answer is Kahn's stuck set.

This is a supporting algorithm: it has no design box, and so no contract in Lean;
`Valid` and the theorems in `DagOrder/Walk.lean` state what it does.

- The answer → `dagPaths` (`Walk.lean`): each vertex's cost and previous vertex, or the vertices
  that could not be placed.
- Every vertex that can be reached gets the cost of its cheapest path, whatever the arrows cost →
  `dagPaths_reached`; the previous vertices lead back along a path of that cost →
  `dagPaths_previous`; a vertex that cannot be reached is reported unreachable →
  `dagPaths_unreached`; on a graph with a cycle, the answer is Kahn's stuck set → `dagPaths_stuck`.
- Invariant → `Valid`: `InOrder`, `KnownIsCheapestThroughDone`, `PreviousLeadsBack`, held at the
  start and kept by every step → `valid_start`, `valid_step`.
- One look at every vertex and every arrow → `dagPaths_cost`: `looks`, the vertices the walk takes
  and their row entries, at most `n + m`; Kahn's order costs as much again (`TopoOrder.kahn_cost`).
-/

@[expose] public section

namespace AlgoDesign.Paths.DagOrder

open Network Graphs
open Dijkstra (Through LeadsBack Answer)

/-! ## The walk's state -/

/-- **The state of the walk.** -/
structure State where
  /-- The vertices taken so far, in the order taken. -/
  done : List ℕ
  /-- The vertices still to take, in the order they will be taken. -/
  todo : List ℕ
  /-- Each vertex's known cost; `none` while no arrow has reached it. -/
  known : ℕ → Option ℤ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ

/-- The vertices taken, then the ones still to take, are a topological order. -/
def InOrder (N : Network) (st : State) : Prop := TopoOrder.IsTopoOrder N.g (st.done ++ st.todo)

/-- Every vertex's known cost is the cheapest over the paths on which every earlier vertex has been
taken. -/
def KnownIsCheapestThroughDone (N : Network) (s : ℕ) (st : State) : Prop :=
  ∀ v < N.g.n, N.CheapestAmong (Through N st.done s) s v (st.known v)

/-- Following the previous vertices back from a vertex with a known cost gives a path from the
start of exactly that cost, every earlier vertex of it taken. -/
def PreviousLeadsBack (N : Network) (s : ℕ) (st : State) : Prop :=
  st.prev s = none ∧ ∀ v < N.g.n, ∀ d ∈ st.known v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
    Through N st.done s p ∧ LeadsBack st.prev s (N.visits s p)

/-- Take steps while vertices are left to take, at most `f` of them. -/
def runSteps (step : State → State) : ℕ → State → State
  | 0, st => st
  | f + 1, st => if st.todo = [] then st else runSteps step f (step st)

/-- The answer a finished walk gives. -/
def answer (st : State) : Answer := ⟨st.known, st.prev⟩

/-- **The walk's looks**: each vertex taken, and each entry of its row. -/
def looks (N : Network) (st : State) : ℕ := (st.done.map fun v => (N.g.out v).length + 1).sum

/-- **A legal state of the walk.** -/
def Valid (N : Network) (s : ℕ) (st : State) : Prop :=
  InOrder N st ∧ KnownIsCheapestThroughDone N s st ∧ PreviousLeadsBack N s st

end AlgoDesign.Paths.DagOrder
