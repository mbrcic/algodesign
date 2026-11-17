/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Network

/-!
# Cheapest paths: the specification

Sources: the Paths chapter, "The quickest way there"; Weiss, *Data Structures and Algorithm Analysis
in C++* (4th ed.), §9.3.2, Fig. 9.31 (p. 399), and Kleinberg and Tardos, *Algorithm Design*, §4.4
(p. 180), for the walk that settles a vertex once and never changes it again; Goldberg and
Harrelson, "Computing the shortest path: A* search meets graph theory" (SODA 2005), for breaking
ties by vertex id.

> **Goal:** Find the cheapest path from one vertex to every other.
>
> **Promise:** Every vertex that can be reached gets the cost of its cheapest path, and following
> each vertex's recorded previous vertex back to the start gives a path of exactly that cost. A
> vertex that cannot be reached is reported as unreachable.
>
> **Idea:** Best-first search. Always settle the unsettled vertex with the smallest known cost, then
> try every arrow out of it.
>
> **Invariants:**
>
> 1. Every settled vertex's cost is its cheapest, and a settled vertex is never settled again.
> 2. Every unsettled vertex's known cost is the cheapest over paths on which every earlier vertex is
>    settled.
>
> **Cost:** Each arrow is tried once, and each try may add one entry to the queue; the work grows
> with the number of arrows times the logarithm of the queue's size.
>
> **Assumes:** No arrow costs less than 0. With one such arrow, a settled cost can be wrong.

The walk runs on a `Network`, from a start vertex `s`. A path is a list of arrow ids
(`Network.IsPath`), so two arrows between the same vertices may cost differently.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Dijkstra.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `dijkstra`, a field of `Ops`: each vertex's cost and previous
  vertex.
- Promise [proved] → three parts: `Ops.ReachedGetCheapest`, `Ops.PreviousGivesPath`,
  `Ops.UnreachedReported`. Only the first needs the box's Assumes; the other two hold whatever the
  arrows cost. Not in the box: the invariants hold along the walk, `Ops.stepKeeps`, from its
  start, `Ops.emptyValid`; the walk starts from its network and start vertex and keeps them,
  `Ops.carries` and `Ops.keepsNetwork`.
- Idea [mentioned] → settling the smallest entry of the queue and trying the arrows out of it is
  `Ops.step`. The queue keeps every entry (cost, vertex) it is given, and the next is the smallest
  by cost, then by vertex id. A settled vertex is skipped when it comes off the queue again, and
  an arrow into it changes nothing; a previous vertex is recorded only when a known cost drops.
- Invariants [proved] → `Valid`:
  1 [proved] `SettledAreCheapest`.
  2 [proved] `KnownIsCheapestThroughSettled`.
  Not in the box: `WellFormed`, which the steps keep together with `Valid`,
  `Ops.stepKeepsWellFormed`, from the start, `Ops.emptyWellFormed`; its pieces are
  `StartSettledFirst`, `SettledRowsTried`, `QueueHoldsKnown`, `PreviousLeadsBack`.
- Cost [argued] → `Ops.EachArrowTriedOnce`: `tried`, the arrows tried, each at most once, and
  `State.pushed`, the entries the queue receives, at most one more than the arrows tried, proved; so
  at most one more than the arrows. The logarithm per entry is the binary heap's in the Rust and
  the Python; the Lean's queue is a sorted list, so it is argued: Weiss, §9.3.2.
- Assumes [proved] → `Network.NoArrowBelowZero`, a hypothesis of `Ops.ReachedGetCheapest`, and of
  `Ops.emptyValid` and `Ops.stepKeeps`. Its second sentence is checked by the kernel on the
  chapter's three-vertex map, `settled_cost_can_be_wrong`: the walk settles the Square at 2, whose
  cheapest path costs 1.
-/

@[expose] public section

namespace AlgoDesign.Paths.Dijkstra

open Network

/-! ## The walk's state -/

/-- **The order of the queue's entries**: by cost, then by vertex id. -/
def EntryLe (a b : ℤ × ℕ) : Prop := a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2

/-- **The state of the walk.** -/
structure State where
  /-- The network the walk runs on. -/
  net : Network
  /-- The start vertex. -/
  source : ℕ
  /-- The settled vertices, in the order they were settled. -/
  settled : List ℕ
  /-- Each vertex's known cost; `none` while no arrow has reached it. -/
  known : ℕ → Option ℤ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ
  /-- The queue's entries (cost, vertex), smallest first. -/
  queue : List (ℤ × ℕ)
  /-- How many entries the queue has received. -/
  pushed : ℕ

/-- **Every earlier vertex of the path `p` from `s` is in `S`**: all its vertices but the last. -/
def Through (N : Network) (S : List ℕ) (s : ℕ) (p : List ℕ) : Prop :=
  ∀ x ∈ (N.visits s p).dropLast, x ∈ S

/-- **Following the recorded previous vertices back gives the list `l`**: each vertex of `l` after
the first records the one before it, and the start records none. -/
def LeadsBack (prev : ℕ → Option ℕ) (s : ℕ) (l : List ℕ) : Prop :=
  prev s = none ∧ l.IsChain fun a b => prev b = some a

/-- Box invariant 1: every settled vertex's cost is its cheapest, and a settled vertex is never
settled again. -/
def SettledAreCheapest (st : State) : Prop :=
  st.settled.Nodup ∧
    ∀ v ∈ st.settled, st.known v ≠ none ∧ st.net.Cheapest st.source v (st.known v)

/-- Box invariant 2: every unsettled vertex's known cost is the cheapest over paths on which every
earlier vertex is settled. -/
def KnownIsCheapestThroughSettled (st : State) : Prop :=
  ∀ v < st.net.g.n, v ∉ st.settled →
    st.net.CheapestAmong (Through st.net st.settled st.source) st.source v (st.known v)

/-- Not in the box: once a vertex is settled, the start is the first. -/
def StartSettledFirst (st : State) : Prop :=
  st.settled ≠ [] → st.settled.head? = some st.source

/-- Not in the box: every arrow from a settled vertex to an unsettled one has been tried; the
unsettled vertex's known cost is at most the settled one's plus the arrow's. -/
def SettledRowsTried (st : State) : Prop :=
  ∀ x ∈ st.settled, ∀ e ∈ st.net.g.out x, e.1 ∉ st.settled →
    ∀ dx ∈ st.known x, AtMost (st.known e.1) (dx + st.net.arrowCost e.2)

/-- Not in the box: the queue is in order, holds each unsettled vertex's known cost, and each entry
is a vertex of the graph, not below its known cost. -/
def QueueHoldsKnown (st : State) : Prop :=
  st.queue.Pairwise EntryLe ∧
    (∀ v < st.net.g.n, v ∉ st.settled → ∀ d ∈ st.known v, (d, v) ∈ st.queue) ∧
    ∀ e ∈ st.queue, e.2 < st.net.g.n ∧ AtMost (st.known e.2) e.1

/-- Not in the box: following the previous vertices back from a vertex with a known cost gives a
path from the start of exactly that cost, every earlier vertex of it settled. -/
def PreviousLeadsBack (st : State) : Prop :=
  st.prev st.source = none ∧ ∀ v < st.net.g.n, ∀ d ∈ st.known v,
    ∃ p, st.net.IsPath st.source p v ∧ st.net.pathCost p = d ∧
      Through st.net st.settled st.source p ∧
        LeadsBack st.prev st.source (st.net.visits st.source p)

/-- **A well-formed walk state**: the conditions the walk needs beyond the box, which its steps
keep together with `Valid`. -/
def WellFormed (st : State) : Prop :=
  StartSettledFirst st ∧ SettledRowsTried st ∧ QueueHoldsKnown st ∧ PreviousLeadsBack st

/-- Take steps while the queue is not empty, at most `f` of them. -/
def runSteps (step : State → State) : ℕ → State → State
  | 0, st => st
  | f + 1, st => if st.queue = [] then st else runSteps step f (step st)

/-- **The walk's answer**: each vertex's cost, `none` for a vertex that cannot be reached, and its
previous vertex. -/
structure Answer where
  /-- Each vertex's cost; `none` reports it unreachable. -/
  cost : ℕ → Option ℤ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ

/-- The answer a finished walk gives. -/
def answer (st : State) : Answer := ⟨st.known, st.prev⟩

/-- **The arrows the walk has tried**: those out of each settled vertex, in its row's order. -/
def tried (N : Network) (st : State) : List ℕ :=
  st.settled.flatMap fun v => (N.g.out v).map Prod.snd

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `Dijkstra.lean` proves the library's procedures meet it
(`Dijkstra.contract`). -/

/-- The procedures the box speaks of: the walk's start and step, and the whole walk, read off the
state its steps reach. -/
structure Ops where
  /-- The start: only the start vertex known, at cost 0, and queued. -/
  start : Network → ℕ → State
  /-- One step: take the smallest entry off the queue, and settle its vertex unless it is settled
  already. -/
  step : Network → State → State
  /-- The walk: each vertex's cost and previous vertex. -/
  dijkstra : Network → ℕ → Answer
  /-- The design's invariants, on the walk's state. -/
  Valid : State → Prop
  /-- The answer is read off the state the steps reach from the start, at most one step per entry
  the queue can receive, so the invariants and the cost are of the walk that answers. -/
  walks : ∀ N s, dijkstra N s =
    answer (runSteps (step N) (N.g.arrows.length + 1) (start N s))
  /-- The start carries the network and the start vertex it is given. -/
  carries : ∀ N s, (start N s).net = N ∧ (start N s).source = s
  /-- A step keeps the walk's network and start vertex. -/
  keepsNetwork : ∀ N st, (step N st).net = st.net ∧ (step N st).source = st.source
  /-- On a well-formed network with no negative arrow, the start keeps the invariants. -/
  emptyValid : ∀ N : Network, N.WellFormed → N.NoArrowBelowZero → ∀ s < N.g.n,
    Valid (start N s)
  /-- On a well-formed network with no negative arrow, the start is well formed. -/
  emptyWellFormed : ∀ N : Network, N.WellFormed → N.NoArrowBelowZero → ∀ s < N.g.n,
    WellFormed (start N s)
  /-- Every step from a nonempty queue keeps the invariants. -/
  stepKeeps : ∀ N : Network, N.WellFormed → N.NoArrowBelowZero → ∀ st, st.net = N →
    st.source < N.g.n → Valid st → WellFormed st → st.queue ≠ [] → Valid (step N st)
  /-- Every step from a nonempty queue keeps the walk well formed. -/
  stepKeepsWellFormed : ∀ N : Network, N.WellFormed → N.NoArrowBelowZero → ∀ st, st.net = N →
    st.source < N.g.n → Valid st → WellFormed st → st.queue ≠ [] → WellFormed (step N st)

/-- The state the walk ends in. -/
abbrev Ops.final (o : Ops) (N : Network) (s : ℕ) : State :=
  runSteps (o.step N) (N.g.arrows.length + 1) (o.start N s)

/-- **Every vertex that can be reached gets the cost of its cheapest path**, on a well-formed
network with no negative arrow. -/
def Ops.ReachedGetCheapest (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → N.NoArrowBelowZero → ∀ s < N.g.n, ∀ v < N.g.n, N.g.Reaches s v →
    ∃ d, (o.dijkstra N s).cost v = some d ∧ N.Cheapest s v (some d)

/-- **Following each vertex's recorded previous vertex back to the start gives a path of exactly
that cost**, on a well-formed network. -/
def Ops.PreviousGivesPath (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s < N.g.n, ∀ v < N.g.n, ∀ d ∈ (o.dijkstra N s).cost v,
    ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧ LeadsBack (o.dijkstra N s).prev s (N.visits s p)

/-- **A vertex that cannot be reached is reported as unreachable**, on a well-formed network. -/
def Ops.UnreachedReported (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ s < N.g.n, ∀ v < N.g.n, ¬ N.g.Reaches s v →
    (o.dijkstra N s).cost v = none

/-! ## The cost -/

/-- **Each arrow is tried once, and each try may add one entry to the queue**: over the walk, the
arrows tried, each at most once, and the entries the queue receives, at most one more. -/
def Ops.EachArrowTriedOnce (o : Ops) : Prop :=
  ∀ N : Network, ∀ s, (tried N (o.final N s)).Nodup ∧
    (o.final N s).pushed ≤ (tried N (o.final N s)).length + 1

/-- **A legal state of the walk**: the box's two invariants. -/
def Valid (st : State) : Prop :=
  SettledAreCheapest st ∧ KnownIsCheapestThroughSettled st

/-- **The cheapest paths' contract**, the part of the design Lean checks, one field per box field
and one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Find the cheapest path from one vertex to every other.
  /-- Promise: cheapest costs, the paths back, and the unreachable vertices. -/
  promise :
    o.ReachedGetCheapest ∧   -- every vertex that can be reached gets its cheapest cost
    o.PreviousGivesPath ∧    -- the previous vertices lead back along a path of that cost
    o.UnreachedReported      -- a vertex that cannot be reached is reported unreachable
  -- Idea: Best-first search. Always settle the unsettled vertex with the smallest known cost,
  -- then try every arrow out of it.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    SettledAreCheapest st ∧             -- 1. every settled vertex's cost is its cheapest,
                                        --    and none is settled again
    KnownIsCheapestThroughSettled st    -- 2. every unsettled vertex's known cost is the
                                        --    cheapest through settled vertices
  /-- Cost: each arrow tried once, each try adding at most one entry to the queue. -/
  cost : o.EachArrowTriedOnce  -- over the walk, the start's entry besides; the logarithm per
                               -- entry is argued
  -- Assumes: No arrow costs less than 0. With one such arrow, a settled cost can be wrong.

end AlgoDesign.Paths.Dijkstra
