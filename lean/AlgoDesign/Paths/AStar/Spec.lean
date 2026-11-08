/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Spec

/-!
# Heading for the goal: the specification

Sources: the Paths chapter, "Heading for the address"; Hart, Nilsson and Raphael, "A Formal Basis
for the Heuristic Determination of Minimum Cost Paths", IEEE Trans. SSC 4 (1968), p. 102, for the
search that adds an estimate of the cost to go and stops when the goal is chosen; Cormen,
Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §23.3, for the changed cost
of an arrow, its cost plus the estimate at its end minus the estimate at its start.

> **Goal:** Find the cheapest path from a start to one goal, settling as few vertices as its
> estimate allows.
>
> **Promise:** The cheapest-paths promise (@dsg-m6-dijkstra), for the goal.
>
> **Idea:** Best-first search guided by a lower bound on what remains. Add to each vertex's known
> cost an estimate of the cost still to go, and settle the vertex whose sum is smallest.
>
> **Invariants:**
>
> 1. The estimate is at least zero, is zero at the goal, and along any arrow drops by no more
>    than the arrow costs.
>
> **Cost:** Each vertex is settled at most once, so the work grows no faster than Dijkstra's; how
> many vertices are settled depends on the estimate.

The search runs on a `Network` from a start `s` to a goal `t`, with an estimate given as a list, one
number per vertex (`estimate`). Its state is the cheapest-paths walk's, with the estimate and the
goal: each vertex's known cost, its previous vertex, and a queue whose entries carry the known cost
plus the estimate. Read with the changed costs (`changed`), the search is the cheapest-paths walk to
the goal, and every key is that walk's key plus the estimate at the start (`shifted`).

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`AStar.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `astar`, a field of `Ops`: each vertex's cost and previous vertex.
  Settling few vertices is the estimate's work, mentioned under Cost.
- Promise [proved] → three parts, the cheapest-paths promise for the goal: `Ops.GoalGetsCheapest`,
  `Ops.PreviousGivesPath`, `Ops.UnreachedReported`. Not in the box: the invariants hold along the
  search, `Ops.stepKeeps`, from its start, `Ops.emptyValid`; the search starts from its network,
  estimate, start and goal and keeps them, `Ops.carries` and `Ops.keepsNetwork`.
- Idea [mentioned] → adding the estimate to the known cost in each queue entry is `Ops.step`; the
  next entry is the smallest by key, then by vertex id; a settled vertex is never reopened, and the
  search stops when the goal comes off the queue.
- Invariants [proved] → `Valid`:
  1 [proved] `EstimateIsConsistent`.
  The estimate is given and never changes, so invariant 1 is a condition on it: the start and all
  three promise parts take it as a hypothesis (`Consistent`), and the steps keep it because they
  keep the estimate.
  Not in the box: `WellFormed`, which the steps keep together with `Valid`,
  `Ops.stepKeepsWellFormed`, from the start, `Ops.emptyWellFormed`; its one piece is
  `WalkIsCheapestPathsOnChangedCosts`.
- Cost [mentioned] → `SettledAtMostOnce` and `WorkAsCheapestPaths`, proved: as for the cheapest
  paths, each arrow tried at most once and at most one queue entry per try besides the start's;
  the logarithm per entry, argued as for the cheapest paths; how many vertices are settled depends
  on the estimate: mentioned.
- Assumes [none] → the box assumes nothing. The cheapest paths' assumption, no negative arrow,
  holds of the changed costs by invariant 1 (`noArrowBelowZero_changed`).
-/

@[expose] public section

namespace AlgoDesign.Paths.AStar

open Network Dijkstra

/-- The estimate at vertex `v`, from a list with one number per vertex. -/
def estimate (est : List ℤ) (v : ℕ) : ℤ := est.getD v 0

/-- **The changed costs**: arrow `i` from `a` to `b` costs its cost plus the estimate at `b` minus
the estimate at `a`. -/
def changed (N : Network) (est : List ℤ) : Network :=
  ⟨N.g, (List.range N.g.arrows.length).map fun i =>
    N.arrowCost i + estimate est (N.target i) - estimate est (N.source i)⟩

/-- **The state of the search**: the cheapest-paths walk's state on the real network, with the
estimate and the goal. -/
structure State extends Dijkstra.State where
  /-- The estimate, one number per vertex. -/
  est : List ℤ
  /-- The goal. -/
  goal : ℕ

/-- **The estimate keeps box invariant 1 on a network, for a goal**: it is at least zero, is
zero at the goal, and along any arrow drops by no more than the arrow costs. -/
def Consistent (N : Network) (t : ℕ) (est : List ℤ) : Prop :=
  (∀ v < N.g.n, 0 ≤ estimate est v) ∧ estimate est t = 0 ∧
    ∀ i < N.g.arrows.length, estimate est (N.source i) ≤ N.arrowCost i + estimate est (N.target i)

/-- The search's state read on the changed costs: the changed network, each known cost plus the
estimate at its vertex, and each queue key, minus the estimate at the start. -/
def shifted (st : State) : Dijkstra.State :=
  { st.toState with
    net := changed st.net st.est
    known := fun v => (st.known v).map (· + estimate st.est v - estimate st.est st.source)
    queue := st.queue.map fun e => (e.1 - estimate st.est st.source, e.2) }

/-- Box invariant 1: the estimate is at least zero, is zero at the goal, and along any arrow
drops by no more than the arrow costs. -/
def EstimateIsConsistent (st : State) : Prop :=
  Consistent st.net st.goal st.est

/-- Not in the box: read on the changed costs, the search's state is a legal and well-formed state
of the cheapest-paths walk. -/
def WalkIsCheapestPathsOnChangedCosts (st : State) : Prop :=
  Dijkstra.Valid (shifted st) ∧ Dijkstra.WellFormed (shifted st)

/-- **A well-formed search state**: the condition the search needs beyond the box, which its steps
keep together with `Valid`. -/
def WellFormed (st : State) : Prop :=
  WalkIsCheapestPathsOnChangedCosts st

/-- **Each vertex is settled at most once.** -/
def SettledAtMostOnce (st : State) : Prop := st.settled.Nodup

/-- **The work grows no faster than the cheapest paths'**: each arrow is tried at most once, and
each try adds at most one entry to the queue, besides the start's. -/
def WorkAsCheapestPaths (N : Network) (st : State) : Prop :=
  (tried N st.toState).Nodup ∧ st.pushed ≤ (tried N st.toState).length + 1

/-- Take steps while the queue is not empty, at most `f` of them, but stop as soon as the goal `t`
comes off the queue unsettled: settle it, and try none of its arrows. -/
def runTo (step : State → State) (t : ℕ) : ℕ → State → State
  | 0, st => st
  | f + 1, st =>
    match st.queue with
    | [] => st
    | (_, u) :: q =>
      if u = t ∧ u ∉ st.settled then { st with settled := st.settled ++ [u], queue := q }
      else runTo step t f (step st)

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `AStar.lean` proves the library's procedures meet it
(`AStar.contract`). -/

/-- The procedures the box speaks of: the search's start and step, and the whole search to the
goal, read off the state its steps reach. -/
structure Ops where
  /-- The start: only the start vertex known, at cost 0, and queued with its estimate. -/
  start : Network → List ℤ → ℕ → ℕ → State
  /-- One step: take the smallest entry off the queue, and settle its vertex unless it is settled
  already. -/
  step : Network → State → State
  /-- The search from a start to a goal: each vertex's cost and previous vertex. -/
  astar : Network → List ℤ → ℕ → ℕ → Answer
  /-- The design's invariants, on the search's state. -/
  Valid : State → Prop
  /-- The answer is read off the state the steps reach from the start, stopped at the goal, at
  most one step per entry the queue can receive. -/
  walks : ∀ N est s t, astar N est s t =
    answer (runTo (step N) t (N.g.arrows.length + 1) (start N est s t)).toState
  /-- The start carries the network, the estimate, the start vertex and the goal it is given. -/
  carries : ∀ N est s t, (start N est s t).net = N ∧ (start N est s t).est = est ∧
    (start N est s t).source = s ∧ (start N est s t).goal = t
  /-- A step keeps the search's network, estimate, start vertex and goal. -/
  keepsNetwork : ∀ N st, (step N st).net = st.net ∧ (step N st).est = st.est ∧
    (step N st).source = st.source ∧ (step N st).goal = st.goal
  /-- On a well-formed network, with an estimate that keeps box invariant 1, the start keeps the
  invariants. -/
  emptyValid : ∀ N : Network, N.WellFormed → ∀ est s t, Consistent N t est → s < N.g.n →
    Valid (start N est s t)
  /-- On a well-formed network, with an estimate that keeps box invariant 1, the start is well
  formed. -/
  emptyWellFormed : ∀ N : Network, N.WellFormed → ∀ est s t, Consistent N t est → s < N.g.n →
    WellFormed (start N est s t)
  /-- Every step from a nonempty queue keeps the invariants. -/
  stepKeeps : ∀ N : Network, N.WellFormed → ∀ st, st.net = N → st.source < N.g.n → Valid st →
    WellFormed st → st.queue ≠ [] → Valid (step N st)
  /-- Every step from a nonempty queue keeps the search well formed. -/
  stepKeepsWellFormed : ∀ N : Network, N.WellFormed → ∀ st, st.net = N → st.source < N.g.n →
    Valid st → WellFormed st → st.queue ≠ [] → WellFormed (step N st)

/-- The state the search to `t` ends in. -/
abbrev Ops.final (o : Ops) (N : Network) (est : List ℤ) (s t : ℕ) : State :=
  runTo (o.step N) t (N.g.arrows.length + 1) (o.start N est s t)

/-- **The goal, if it can be reached, gets the cost of its cheapest path**, on a well-formed
network with an estimate that keeps box invariant 1. -/
def Ops.GoalGetsCheapest (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ est s t, Consistent N t est → s < N.g.n →
    t < N.g.n → N.g.Reaches s t → ∃ d, (o.astar N est s t).cost t = some d ∧ N.Cheapest s t (some d)

/-- **Following the goal's recorded previous vertex back to the start gives a path of exactly its
cost.** -/
def Ops.PreviousGivesPath (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ est s t, Consistent N t est → s < N.g.n →
    t < N.g.n → ∀ d ∈ (o.astar N est s t).cost t,
      ∃ p, N.IsPath s p t ∧ N.pathCost p = d ∧ LeadsBack (o.astar N est s t).prev s (N.visits s p)

/-- **A goal that cannot be reached is reported as unreachable.** -/
def Ops.UnreachedReported (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ est s t, Consistent N t est → s < N.g.n →
    t < N.g.n → ¬ N.g.Reaches s t → (o.astar N est s t).cost t = none

/-- **A legal state of the search**: the box's invariant. -/
def Valid (st : State) : Prop :=
  EstimateIsConsistent st

/-- **The search's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Find the cheapest path from a start to one goal, settling as few vertices as its estimate
  -- allows.
  /-- Promise: the cheapest-paths promise, for the goal. -/
  promise :
    o.GoalGetsCheapest ∧    -- the goal gets the cost of its cheapest path
    o.PreviousGivesPath ∧   -- its previous vertices lead back along a path of that cost
    o.UnreachedReported     -- a goal that cannot be reached is reported unreachable
  -- Idea: Best-first search guided by a lower bound on what remains. Add to each vertex's known
  -- cost an estimate of the cost still to go, and settle the vertex whose sum is smallest.
  /-- Invariants: the box's one. -/
  invariants : ∀ st, o.Valid st ↔
    EstimateIsConsistent st   -- 1. at least zero, zero at the goal, drops by
                              --    no more than the arrow costs
  /-- Cost: each vertex settled at most once, so the work grows no faster than Dijkstra's. -/
  cost : ∀ N : Network, ∀ est s t,
    SettledAtMostOnce (o.final N est s t) ∧   -- each vertex settled at most once
      WorkAsCheapestPaths N (o.final N est s t)  -- so the work grows no faster than Dijkstra's
    -- how many vertices are settled depends on the estimate: mentioned

end AlgoDesign.Paths.AStar
