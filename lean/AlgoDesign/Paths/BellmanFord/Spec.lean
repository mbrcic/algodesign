/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Spec

/-!
# Cheapest paths with negative arrows: the specification

Sources: the Paths chapter, "Downhill pays"; Kleinberg and Tardos, *Algorithm
Design*, §6.8 (pp. 292–297), for the rounds and for stopping when a round changes nothing
(p. 297, as Dasgupta, Papadimitriou and Vazirani, *Algorithms*, p. 129), and pp. 295–296, (6.26),
for rounds that read each cost as it is now; Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms* (4th ed.), §22.1 (p. 612), for reporting only the cycles the start reaches, (22.11)
(p. 636) for what a recorded previous vertex keeps, and Lemma 22.16 and its proof (pp. 635–637) for
the cycles the previous vertices close; cp-algorithms, "Bellman–Ford algorithm" (`bellman_ford.md`
l. 154, commit ebd43c8), for finding the cycle: from the last vertex the check round lowered,
follow the previous vertices back `n` steps.

> **Goal:** Find the cheapest paths from one vertex when some arrows are negative, or show a
> negative cycle.
>
> **Promise:** If the start reaches no negative cycle, every vertex it reaches gets the cost of its
> cheapest path, with a path of that cost. Otherwise the answer is a negative cycle that the start
> reaches.
>
> **Idea:** Dynamic programming over the number of arrows used. Each round tries every arrow once;
> one more round that still lowers a cost shows a negative cycle.
>
> **Invariants:**
>
> 1. After any number of rounds, every vertex's cost is the cost of some path to it (a path may
>    pass a vertex more than once), and no more than the cheapest over paths with at most that many
>    arrows.
>
> **Cost:** One round fewer than the number of vertices, each trying every arrow, plus one check
> round: vertices times arrows.

The rounds run on a `Network`, from a start vertex `s`. A path is a list of arrow ids
(`Network.IsWalk`), and may pass a vertex more than once; one that passes no vertex twice is a
`Network.IsPath`.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`BellmanFord.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `bellmanFord`, a field of `Ops`: each vertex's cost and previous
  vertex, or a negative cycle (`CycleBelowZero`), as its list of vertices.
- Promise [proved] → three parts: `Ops.NoCycleGivesCheapest`, `Ops.CycleIsBelowZero`,
  `Ops.CycleWhenOneExists`. The path of a vertex's cost is the one its recorded previous vertices
  lead back along. Not in the box: the invariants hold after every round, `Ops.stepKeeps`, from
  the start, `Ops.emptyValid`; the rounds start from their network and start vertex and keep them,
  `Ops.carries` and `Ops.keepsNetwork`.
- Idea [mentioned] → one round is `Ops.round`: it reads each cost as it is now, trying the
  vertices by increasing id and each vertex's row in order, and records a previous vertex when a
  cost drops. The rounds stop at the first that lowers nothing, and no more rounds run than there
  are vertices; when the last still lowers a cost, `answer` follows the previous vertices back
  from the last vertex it lowered to the cycle.
- Invariants [proved] → `Valid`:
  1 [proved] `CostIsWalkAtMostCheapest`.
  Not in the box: `WellFormed`, which every round keeps together with `Valid`,
  `Ops.stepKeepsWellFormed`, from the start, `Ops.emptyWellFormed`; its pieces are
  `PathWithinTries`, `PreviousArrowFits`, `RecordedCyclesBelowZero`, `NoPreviousKeepsStart`.
- Cost [proved] → `Ops.VerticesTimesArrows`: `State.rounds`, at most the number of vertices, and
  `State.tried`, the arrows tried, the rounds times the arrows.
- Assumes [none] → the box assumes nothing.
-/

@[expose] public section

namespace AlgoDesign.Paths.BellmanFord

open Network
open Dijkstra (Answer LeadsBack)

/-! ## The rounds' state -/

/-- **The state after some rounds.** -/
structure State where
  /-- The network the rounds run on. -/
  net : Network
  /-- The start vertex. -/
  source : ℕ
  /-- Each vertex's cost; `none` while no path has reached it. -/
  cost : ℕ → Option ℤ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ
  /-- How many rounds have run. -/
  rounds : ℕ
  /-- The last vertex the last round lowered; `none` when it lowered nothing. -/
  lowered : Option ℕ
  /-- How many arrows the rounds have tried. -/
  tried : ℕ

/-- Box invariant 1: after any number of rounds, every vertex's cost is the cost of some path to
it (a path may pass a vertex more than once), and no more than the cheapest over paths with at most
that many arrows. -/
def CostIsWalkAtMostCheapest (st : State) : Prop :=
  ∀ v < st.net.g.n,
    (∀ d ∈ st.cost v, ∃ p, st.net.IsWalk st.source p v ∧ st.net.pathCost p = d) ∧
      ∀ p, st.net.IsWalk st.source p v → p.length ≤ st.rounds →
        AtMost (st.cost v) (st.net.pathCost p)

/-- Not in the box: the path a cost is the cost of has at most as many arrows as arrows tried so
far. -/
def PathWithinTries (st : State) : Prop :=
  ∀ v < st.net.g.n, ∀ d ∈ st.cost v,
    ∃ p, st.net.IsWalk st.source p v ∧ p.length ≤ st.tried ∧ st.net.pathCost p = d

/-- Not in the box: an arrow leads from each vertex's previous vertex to it, and the previous
vertex's cost plus the arrow's is at most the vertex's cost. -/
def PreviousArrowFits (st : State) : Prop :=
  ∀ v < st.net.g.n, ∀ u ∈ st.prev v,
    ∃ i < st.net.g.arrows.length, st.net.g.arrows[i]? = some (u, v) ∧
      ∃ du ∈ st.cost u, ∃ dv ∈ st.cost v, du + st.net.arrowCost i ≤ dv

/-- **`c` is a cycle the previous vertices close**: vertices of the network, each the previous
vertex of the one after it, the first again last, and no vertex twice before that. -/
def RecordsClose (N : Network) (prev : ℕ → Option ℕ) (c : List ℕ) : Prop :=
  (∀ v ∈ c, v < N.g.n) ∧ c.IsChain (fun a b => prev b = some a) ∧ 2 ≤ c.length ∧
    c.head? = c.getLast? ∧ c.dropLast.Nodup

/-- Not in the box: every cycle the previous vertices close has arrows with a negative total. -/
def RecordedCyclesBelowZero (st : State) : Prop :=
  ∀ c, RecordsClose st.net st.prev c →
    ∃ v p, st.net.IsWalk v p v ∧ st.net.visits v p = c ∧ st.net.pathCost p < 0

/-- Not in the box: a vertex that records no previous vertex keeps its first cost, 0 for the start
and none for every other vertex. -/
def NoPreviousKeepsStart (st : State) : Prop :=
  ∀ v < st.net.g.n, st.prev v = none → st.cost v = if v = st.source then some 0 else none

/-- **A well-formed state after some rounds**: the conditions the rounds need beyond the box,
which every round keeps together with `Valid`. -/
def WellFormed (st : State) : Prop :=
  PathWithinTries st ∧ PreviousArrowFits st ∧ RecordedCyclesBelowZero st ∧
    NoPreviousKeepsStart st

/-- Run rounds until one lowers nothing, at most `f` of them. -/
def runRounds (round : State → State) : ℕ → State → State
  | 0, st => st
  | f + 1, st => if (round st).lowered = none then round st else runRounds round f (round st)

/-! ## The answer -/

/-- One step back along the records: the previous vertex, or the vertex itself when it records
none. -/
def stepBack (prev : ℕ → Option ℕ) (v : ℕ) : ℕ := (prev v).getD v

/-- The vertices passed following the records back from `v` until `y` comes back, `y` last, at
most `f` steps. -/
def collect (prev : ℕ → Option ℕ) (y : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, v =>
    if stepBack prev v = y then [y] else stepBack prev v :: collect prev y f (stepBack prev v)

/-- **The cycle a round that still lowers a cost shows**: from `x`, the last vertex it lowered,
follow the records back `n` steps to a vertex `y`, follow them on until `y` comes back, and turn
the list around, so each vertex is followed by the one its arrow points to. -/
def cycleFrom (prev : ℕ → Option ℕ) (n x : ℕ) : List ℕ :=
  ((stepBack prev)^[n] x :: collect prev ((stepBack prev)^[n] x) n ((stepBack prev)^[n] x)).reverse

/-- The answer the rounds give: each vertex's cost and previous vertex when the last round lowered
nothing, and otherwise the cycle it shows. -/
def answer (N : Network) (st : State) : Except (List ℕ) Answer :=
  match st.lowered with
  | none => .ok ⟨st.cost, st.prev⟩
  | some x => .error (cycleFrom st.prev N.g.n x)

/-- **`c` is a negative cycle that the start reaches**: the vertices of a cycle through a
vertex that `s` reaches, the first vertex again last, whose arrows have a negative total. -/
def CycleBelowZero (N : Network) (s : ℕ) (c : List ℕ) : Prop :=
  ∃ v p, N.IsCycle v p ∧ N.visits v p = c ∧ N.pathCost p < 0 ∧ N.g.Reaches s v

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `BellmanFord.lean` proves the library's procedures meet it
(`BellmanFord.contract`). -/

/-- The procedures the box speaks of: the start and one round, and the whole run, read off the
state its rounds reach. -/
structure Ops where
  /-- The start: no rounds run, only the start vertex has a cost, 0. -/
  start : Network → ℕ → State
  /-- One round: try every arrow, reading each cost as it is now. -/
  round : Network → State → State
  /-- The run: each vertex's cost and previous vertex, or a negative cycle. -/
  bellmanFord : Network → ℕ → Except (List ℕ) Answer
  /-- The design's invariants, on the state after some rounds. -/
  Valid : State → Prop
  /-- The answer is read off the state the rounds reach from the start, at most one round per
  vertex, so the invariants and the cost are of the run that answers. -/
  walks : ∀ N s, bellmanFord N s = answer N (runRounds (round N) N.g.n (start N s))
  /-- The start carries the network and the start vertex it is given. -/
  carries : ∀ N s, (start N s).net = N ∧ (start N s).source = s
  /-- A round keeps the network and the start vertex. -/
  keepsNetwork : ∀ N st, (round N st).net = st.net ∧ (round N st).source = st.source
  /-- On a well-formed network the start keeps the invariants. -/
  emptyValid : ∀ N : Network, N.WellFormed → ∀ s < N.g.n, Valid (start N s)
  /-- On a well-formed network the start is well formed. -/
  emptyWellFormed : ∀ N : Network, N.WellFormed → ∀ s < N.g.n, WellFormed (start N s)
  /-- Every round keeps the invariants. -/
  stepKeeps : ∀ N : Network, N.WellFormed → ∀ st, st.net = N → st.source < N.g.n → Valid st →
    WellFormed st → Valid (round N st)
  /-- Every round keeps the state well formed. -/
  stepKeepsWellFormed : ∀ N : Network, N.WellFormed → ∀ st, st.net = N → st.source < N.g.n →
    Valid st → WellFormed st → WellFormed (round N st)

/-- The state the run ends in. -/
abbrev Ops.final (o : Ops) (N : Network) (s : ℕ) : State :=
  runRounds (o.round N) N.g.n (o.start N s)

/-- **If the start reaches no negative cycle, every vertex it reaches gets the cost of its
cheapest path, with a path of that cost**: the one its recorded previous vertices lead back
along; on a well-formed network. -/
def Ops.NoCycleGivesCheapest (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s < N.g.n, (¬ ∃ c, CycleBelowZero N s c) →
    ∃ a, o.bellmanFord N s = .ok a ∧ ∀ v < N.g.n, N.Cheapest s v (a.cost v) ∧
      ∀ d ∈ a.cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧ LeadsBack a.prev s (N.visits s p)

/-- **Otherwise the answer is a negative cycle that the start reaches**, first half: a cycle
answered is negative and the start reaches it, on a well-formed network. -/
def Ops.CycleIsBelowZero (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s < N.g.n, ∀ c, o.bellmanFord N s = .error c →
    CycleBelowZero N s c

/-- **Otherwise the answer is a negative cycle that the start reaches**, second half: when the
start reaches a negative cycle, the answer is a cycle, on a well-formed network. -/
def Ops.CycleWhenOneExists (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s < N.g.n, (∃ c, CycleBelowZero N s c) →
    ∃ c, o.bellmanFord N s = .error c

/-! ## The cost -/

/-- **One round fewer than the number of vertices, each trying every arrow, plus one check round:
vertices times arrows**: at most one round per vertex, each trying every arrow, on a well-formed
network. -/
def Ops.VerticesTimesArrows (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s, (o.final N s).rounds ≤ N.g.n ∧
    (o.final N s).tried = (o.final N s).rounds * N.g.arrows.length

/-- **A legal state after some rounds**: the box's invariant. -/
def Valid (st : State) : Prop :=
  CostIsWalkAtMostCheapest st

/-- **The cheapest paths' contract with negative arrows**, the part of the design Lean checks,
one field per box field and one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Find the cheapest paths from one vertex when some arrows are negative, or show a
  -- negative cycle.
  /-- Promise: cheapest costs and paths without a negative cycle, else a negative cycle. -/
  promise :
    o.NoCycleGivesCheapest ∧  -- no negative cycle: each vertex gets its cheapest cost and path
    o.CycleIsBelowZero ∧      -- otherwise: a cycle answered is negative and reached
    o.CycleWhenOneExists      -- otherwise: the answer is a cycle
  -- Idea: Dynamic programming over the number of arrows used. Each round tries every arrow once;
  -- one more round that still lowers a cost shows a negative cycle.
  /-- Invariants: the box's one. -/
  invariants : ∀ st, o.Valid st ↔
    CostIsWalkAtMostCheapest st  -- 1. each cost is a path's, at most the cheapest within
                                 --    as many arrows as rounds
  /-- Cost: at most one round per vertex, each trying every arrow. -/
  cost : o.VerticesTimesArrows  -- vertices times arrows

end AlgoDesign.Paths.BellmanFord
