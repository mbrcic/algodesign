/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph

/-!
# Topological order: the specification

Sources: the Graphs chapter, "Readiness"; Weiss, *Data Structures and Algorithm Analysis in C++*
(4th ed.), §9.2, Fig. 9.7 (p. 385), for Kahn's walk with a queue; Ahuja, Magnanti and Orlin,
*Network Flows* (1993), pp. 77–78, for the vertices left when the walk stops, each with an arrow in
from another of them; Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.),
§20.4, Theorem 20.12, for the DFS order; cp-algorithms ("Checking a graph for acyclicity and
finding a cycle") and Laaksonen, *Competitive Programmer's Handbook*, for the cycle written
`w, …, v, w`.

> **Goal:** Put the vertices in an order where each comes after everything it waits for, or show
> that no such order exists.
>
> **Promise:** Every vertex appears once, and every arrow points forward. If no order exists, the
> answer is the stuck set, and each vertex in it still waits for one in the set.
>
> **Idea:** Topological order. Take any vertex that waits for nothing more. Taking it may free
> others.
>
> **Invariants:**
>
> 1. Each placed vertex comes after everything it waits for.
> 2. Each unplaced vertex counts the unplaced vertices it still waits for.
> 3. The ready list holds exactly the unplaced vertices whose count is zero.
>
> **Cost:** One look at every vertex and every arrow.
>
> **Assumes:** The arrows do not change while the order is built. If one does, the order can be
> wrong.

The vertices are the vertices `0, …, n - 1` of a `Digraph`, and an arrow `(u, v)` says `v` waits for
`u`. Loops and doubled arrows are allowed: a doubled arrow counts twice, and a vertex with a loop
waits on itself, so it is stuck.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`TopoOrder.contract` proves the library's operations, `ops`, meet it.

- Goal [required] → Kahn's answer, `kahn`, a field of `Ops`: an order, or a reason none exists.
- Promise [proved] → `Ops.OrdersOrStuck`: `KahnPromise`, a topological order or the stuck vertices.
  The formal statement adds to the box line that the one a stuck vertex waits for can be itself (a
  loop), and that the stuck set is the whole of what cannot be placed.
- Idea [mentioned] → taking a vertex that waits for nothing anymore is `Ops.kahnStep`. The queue is
  first in, first out, as Weiss prints it; the promise holds for any order of taking ready vertices.
- Invariants [proved] → `Valid`, one piece per box line: 1 `PlacedAfterWaits`,
  2 `CountsUnplacedWaits`, 3 `ReadyIsZero`. Line 2 counts arrows, so a doubled arrow counts twice.
  Not in the box: the invariants hold along the walk, `Ops.stepKeeps`, from its start,
  `Ops.emptyValid`; the walk starts from its graph and keeps it, `Ops.carries` and
  `Ops.keepsGraph`, and Kahn's answer is read off it, `Ops.walks`; the arrows join vertices of
  the graph, `Digraph.WellFormed`; the DFS order's promise, `DfsPromise`, a cycle in place of the
  stuck set, outside the contract.
- Cost [argued] → `Ops.OneLookEach`: `looks`, the vertices taken and their row entries, proved at
  most `n + m`; the start's own pass over every vertex and arrow argued, by its definition.
- Assumes [mentioned] → the arrows do not change while ordering: every procedure takes the graph
  as a value. Not in the box: an arrow from one vertex to another means the first must finish
  before the second, as above.
-/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

open Digraph

/-! ## What an answer means -/

/-- **`u` comes before `v` in `l`**: the two appear in `l` in that order. -/
def Before (l : List ℕ) (u v : ℕ) : Prop := [u, v].Sublist l

/-- **A topological order** of `g`: every vertex `0, …, n - 1` exactly once, and every arrow
pointing forward. A loop makes this impossible: its vertex would come before itself. -/
def IsTopoOrder (g : Digraph) (l : List ℕ) : Prop :=
  l.Perm (List.range g.n) ∧ ∀ a ∈ g.arrows, Before l a.1 a.2

/-- **Every vertex in `l` comes after everything it waits for**: each vertex appears once, and every
arrow into a vertex of `l` comes from a vertex earlier in `l`. -/
def AfterWaits (g : Digraph) (l : List ℕ) : Prop :=
  l.Nodup ∧ ∀ a ∈ g.arrows, a.2 ∈ l → Before l a.1 a.2

/-- **Each member of `s` still waits on a member of `s`**, possibly itself: some arrow into it
comes from `s`. -/
def WaitsInside (g : Digraph) (s : List ℕ) : Prop :=
  ∀ v ∈ s, ∃ u ∈ s, g.Arrow u v

/-- The vertices of `g` outside `s`, in increasing order. -/
def outside (g : Digraph) (s : List ℕ) : List ℕ := (List.range g.n).filter (· ∉ s)

/-- **The vertices outside `s` can be placed**: some order of them has every one after everything
it waits for. -/
def RestPlaceable (g : Digraph) (s : List ℕ) : Prop :=
  ∃ l, l.Perm (outside g s) ∧ AfterWaits g l

/-- **The vertices that could not be placed**: a nonempty set of vertices, listed in increasing
order, each still waiting on one of them, possibly itself; and every other vertex can be placed. The
second half makes the set the whole of what is stuck: a vertex left out of it would have to be
placeable, and a vertex waiting on a member is not. -/
def IsStuck (g : Digraph) (s : List ℕ) : Prop :=
  s ≠ [] ∧ s.Pairwise (· < ·) ∧ (∀ v ∈ s, v < g.n) ∧ WaitsInside g s ∧ RestPlaceable g s

/-! ## Kahn's walk

The walk's state: the graph it orders; the vertices placed so far, in order; for each vertex, a
count of what it still waits for; and the queue of ready vertices, front first. -/

/-- **The state of Kahn's walk.** -/
structure KahnState where
  /-- The graph being ordered. -/
  g : Digraph
  /-- The vertices placed so far, in the order they were placed. -/
  placed : List ℕ
  /-- For each vertex not yet placed, how many arrows into it come from vertices not yet placed. -/
  count : ℕ → ℕ
  /-- The ready vertices, front first. -/
  queue : List ℕ

/-- Box invariant 1: each placed vertex comes after everything it waits for. Each placed vertex is
a vertex of the graph, placed once, and every arrow into it comes from a vertex placed earlier. -/
def PlacedAfterWaits (st : KahnState) : Prop :=
  AfterWaits st.g st.placed ∧ ∀ v ∈ st.placed, v < st.g.n

/-- Box invariant 2: each unplaced vertex counts the unplaced vertices it still waits for. The
count is of arrows, so a doubled arrow counts twice. -/
def CountsUnplacedWaits (st : KahnState) : Prop :=
  ∀ v < st.g.n, v ∉ st.placed →
    st.count v = st.g.arrows.countP (fun a => a.2 = v ∧ a.1 ∉ st.placed)

/-- Box invariant 3: the ready vertices are exactly the unplaced vertices with none left to wait
for. The queue holds each of them once and nothing else. -/
def ReadyIsZero (st : KahnState) : Prop :=
  st.queue.Nodup ∧ (∀ v ∈ st.queue, v < st.g.n ∧ v ∉ st.placed ∧ st.count v = 0) ∧
    ∀ v < st.g.n, v ∉ st.placed → st.count v = 0 → v ∈ st.queue

/-- Take steps while the queue is not empty, at most `f` of them. -/
def runSteps (step : KahnState → KahnState) : ℕ → KahnState → KahnState
  | 0, st => st
  | f + 1, st => if st.queue = [] then st else runSteps step f (step st)

/-- The answer a finished walk gives: the order if every vertex was placed, else the vertices not
placed, in increasing order. -/
def answer (g : Digraph) (st : KahnState) : Except (List ℕ) (List ℕ) :=
  if st.placed.length = g.n then .ok st.placed else .error (outside g st.placed)

/-- **What Kahn's answer means**: a topological order, or the stuck set. -/
def KahnPromise (g : Digraph) : Except (List ℕ) (List ℕ) → Prop
  | .ok l => IsTopoOrder g l
  | .error s => IsStuck g s

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `TopoOrder.lean` proves the library's operations meet it
(`TopoOrder.contract`). -/

/-- The operations the box speaks of: Kahn's start and step, and Kahn's whole walk, read off the
state its steps reach. An answer is `.ok` an order, or `.error` the vertices that could not be
placed. -/
structure Ops where
  /-- Kahn's start: nothing placed, every vertex's count, the ready vertices queued. -/
  kahnStart : Digraph → KahnState
  /-- One step of Kahn's walk: place the front of the queue. -/
  kahnStep : KahnState → KahnState
  /-- Kahn's method: the order, or the stuck set. -/
  kahn : Digraph → Except (List ℕ) (List ℕ)
  /-- The design's invariants, on the walk's state. -/
  Valid : KahnState → Prop
  /-- Kahn's answer is read off the state its steps reach from its start, at most one step per
  vertex, so the invariants and the cost are of the walk that answers. -/
  walks : ∀ g, kahn g = answer g (runSteps kahnStep g.n (kahnStart g))
  /-- The start carries the graph it is given. -/
  carries : ∀ g, (kahnStart g).g = g
  /-- A step keeps the walk's graph. -/
  keepsGraph : ∀ st, (kahnStep st).g = st.g
  /-- On a well-formed graph the start keeps the invariants. -/
  emptyValid : ∀ g : Digraph, g.WellFormed → Valid (kahnStart g)
  /-- Every step from a nonempty queue keeps the invariants. -/
  stepKeeps : ∀ st, st.g.WellFormed → Valid st → st.queue ≠ [] → Valid (kahnStep st)

/-- **Every vertex exactly once, with every arrow pointing forward; or the vertices that could
not be placed, each still waiting on one of them, possibly itself**, on a graph whose arrows join
its vertices. -/
def Ops.OrdersOrStuck (o : Ops) : Prop :=
  ∀ g : Digraph, g.WellFormed → KahnPromise g (o.kahn g)

/-! ## The cost -/

/-- **The walk's looks**: each vertex taken, and each entry of its row. -/
def looks (g : Digraph) (st : KahnState) : ℕ := (st.placed.map fun v => (g.out v).length + 1).sum

/-- **One look at every vertex and every arrow**: over the walk, each vertex taken and each entry
of its row, once. -/
def Ops.OneLookEach (o : Ops) : Prop :=
  ∀ g : Digraph, looks g (runSteps o.kahnStep g.n (o.kahnStart g)) ≤ g.n + g.arrows.length

/-- **A legal state of Kahn's walk**: the box's three invariants. -/
def Valid (st : KahnState) : Prop :=
  PlacedAfterWaits st ∧ CountsUnplacedWaits st ∧ ReadyIsZero st

/-- **The topological order's contract**, the part of the design Lean checks, one field per box
field and one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Put the vertices in an order where each comes after everything it waits for, or show
  -- that no such order exists.
  /-- Promise: an order, or the vertices that could not be placed. -/
  promise :
    o.OrdersOrStuck  -- every vertex once, arrows forward; or vertices that could not be placed
  -- Idea: Topological order. Take any vertex that waits for nothing more. Taking it may free
  -- others.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    PlacedAfterWaits st ∧     -- 1. each placed vertex comes after everything it waits for
    CountsUnplacedWaits st ∧  -- 2. each unplaced vertex counts what it still waits for
    ReadyIsZero st            -- 3. the ready list holds exactly the unplaced at count zero
  /-- Cost: one look at every vertex and every arrow. -/
  cost : o.OneLookEach  -- one look at every vertex and every arrow
  -- Assumes: The arrows do not change while the order is built. If one does, the order can be
  -- wrong.

end AlgoDesign.Graphs.TopoOrder
