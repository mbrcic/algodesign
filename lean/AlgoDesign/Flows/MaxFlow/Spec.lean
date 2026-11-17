/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph

/-!
# Max flow: the specification

Sources: the Flow chapter, "Max flow"; Ford and Fulkerson, "Maximal flow through a network"
(1956), for adding along paths and the cut; Ahuja, Magnanti and Orlin, *Network Flows* (1993),
§2.4 and §6.3, for the residual network of paired arrows.

> **Goal:** Move as much as possible from a source to a sink through a flow network, and prove that
> nothing more fits.
>
> **Promise:** A flow that respects every arrow's capacity and loses nothing at any vertex, and
> beside it a cut: the source on one side, the sink on the other, and the capacities of arrows
> leaving the source's side add up to the flow amount. No flow exceeds any cut, so this flow is
> the largest.
>
> **Idea:** Augmentation over residual state: every unit sent can be taken back, so a later path
> may undo part of an earlier one. A **path rule** picks each next path, until none is left.
>
> **Invariants:**
>
> 1. No arrow carries more than its capacity, or a negative amount.
> 2. At every vertex except the source and the sink, what comes in goes out.
> 3. The flow on every arrow is an integer.
>
> **Cost:** One search per added path. How many paths depends on the
> path rule. With integer capacities every rule finishes. Rules that take the fewest arrows
> first finish within a bound set by the network's size alone, not by its capacities.
>
> **Assumes:** Capacities are integers.

A network (`Network`) is a `Digraph` with a capacity per arrow, listed by arrow id, a source and a
sink. A flow (`Flow`) is the amount on each arrow, by arrow id. The remaining capacity pairs every
arrow with its way back (`ResidualArrow`): `along i` has the room arrow `i` has left, `back i` the
amount arrow `i` carries, which can be taken back.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`MaxFlow.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `Ops.maxFlow`, a field of `Ops`: a flow and the source's side of a
  cut.
- Promise [proved] → three parts: `Ops.ReturnsAFlow`, `Ops.CutMatchesFlow`, `Ops.Largest`. Not
  in the box: the invariants hold from the zero flow, `Ops.startValid`, and after every round,
  `Ops.roundsKeep`; the answer is what the rounds sent, `Ops.walks`; every added path was
  augmenting in its turn and carried at least one unit, `Ops.augments`. A flow here is an integer
  flow (`Flow`, a natural number per arrow), so "the largest" is compared with integer flows; that
  no flow with fractional amounts is larger follows from the same cut and is argued.
- Idea [proved] → the path rule is the open choice, `PathRule`. A rule that keeps
  `PathRule.Promise` and adds a number of paths bounded by the network's size gives a
  contract-keeping max flow (`PathRule.contract`, `Loop.lean`). The library's rule is Dinic's;
  Edmonds–Karp's and capacity scaling's are the others it ships. Capacity scaling keeps the
  promise, but its number of paths grows with the capacities (argued), so it is not held to
  that bound.
- Invariants [proved] → `Valid`:
  1 [proved] `WithinCapacity`; no negative amount, since an amount is a natural number.
  2 [proved] `Conserved`.
  3 [proved] by the type: an amount is a natural number.
  Not in the box: `WellFormed`, one amount per arrow.
- Cost [argued] → `Ops.FinishesWithIntegers` and `Ops.BoundSetBySize`, proved for the
  library's rule; one search per added path is argued from each rule's procedure.
- Assumes [proved] → by the type: a capacity is a natural number, an integer (the box) that is
  ≥ 0 (the network definition).

## Choosing a path rule

Every path rule is held to the same three-part promise, `PathRule.Promise`; a new rule that keeps
it, and adds a number of paths bounded by the network's size, gets the whole contract above from
one proof. A speed requirement is stated without naming an
algorithm, as one of these:

- `Ops.AugmentationsAtMostNM`: at most n·m added paths (Edmonds–Karp's rule meets it);
- `Ops.RoundsAtMostN`: at most n rounds (Dinic's rule meets it);
- `Ops.BoundSetBySize`: some bound set by n and m alone (both meet it).

To choose among rules that keep the promise, run several on your own networks with the workbench
(`Flows/Workbench`), which checks every answer against this contract and reports rounds, added paths
and time, and keep those that no other rule beats on both code size and time.
-/

@[expose] public section

namespace AlgoDesign.Flows

open AlgoDesign.Graphs

/-- A network: a directed graph, the capacity of each arrow by arrow id, a source and a sink. -/
structure Network where
  /-- The vertices and arrows. -/
  g : Digraph
  /-- The capacity of each arrow, by arrow id. -/
  cap : List ℕ
  /-- Where the flow starts. -/
  source : ℕ
  /-- Where the flow ends. -/
  sink : ℕ
deriving DecidableEq, Repr

namespace Network

variable (N : Network)

/-- Every arrow joins two vertices of the graph and has one capacity; the source and the sink are
two different vertices of the graph. -/
def WellFormed : Prop :=
  N.g.WellFormed ∧ N.cap.length = N.g.arrows.length ∧ N.source < N.g.n ∧ N.sink < N.g.n ∧
    N.source ≠ N.sink

/-- The arrow ids. -/
def ids : List ℕ := List.range N.g.arrows.length

/-- The capacity of arrow `i`. -/
def capOf (i : ℕ) : ℕ := N.cap.getD i 0

/-- The vertex arrow `i` leaves. -/
def tail (i : ℕ) : ℕ := (N.g.arrows.getD i (0, 0)).1

/-- The vertex arrow `i` points to. -/
def head (i : ℕ) : ℕ := (N.g.arrows.getD i (0, 0)).2

end Network

/-- A flow: the amount on each arrow, by arrow id. -/
abbrev Flow := List ℕ

/-- The amount on arrow `i`. -/
def Flow.on (f : Flow) (i : ℕ) : ℕ := f.getD i 0

/-- The zero flow on `N`. -/
def Flow.zero (N : Network) : Flow := List.replicate N.g.arrows.length 0

/-- What leaves `v` along the flow `f`. -/
def outflow (N : Network) (f : Flow) (v : ℕ) : ℕ :=
  ((N.ids.filter fun i => N.tail i = v).map f.on).sum

/-- What enters `v` along the flow `f`. -/
def inflow (N : Network) (f : Flow) (v : ℕ) : ℕ :=
  ((N.ids.filter fun i => N.head i = v).map f.on).sum

/-- **The flow amount**: what leaves the source, less what comes back into it. -/
def value (N : Network) (f : Flow) : ℤ := (outflow N f N.source : ℤ) - inflow N f N.source

/-! ## A flow's state -/

/-- **A flow on its network**, the state the rounds change. -/
structure State where
  /-- The network. -/
  net : Network
  /-- The amount on each arrow. -/
  flow : Flow

/-- Box invariant 1: no arrow carries more than its capacity, or a negative amount. -/
def WithinCapacity (st : State) : Prop :=
  ∀ i < st.net.g.arrows.length, st.flow.on i ≤ st.net.capOf i

/-- Box invariant 2: at every vertex except the source and the sink, what comes in goes out. -/
def Conserved (st : State) : Prop :=
  ∀ v < st.net.g.n, v ≠ st.net.source → v ≠ st.net.sink →
    inflow st.net st.flow v = outflow st.net st.flow v

/-- Not in the box: the flow lists one amount per arrow. -/
def WellFormed (st : State) : Prop := st.flow.length = st.net.g.arrows.length

/-- **`f` is a flow on `N`**: it respects every arrow's capacity and loses nothing at any vertex. -/
def IsFlow (N : Network) (f : Flow) : Prop :=
  WithinCapacity ⟨N, f⟩ ∧ Conserved ⟨N, f⟩ ∧ WellFormed ⟨N, f⟩

/-! ## The remaining capacity -/

/-- An arrow of the remaining capacity: along arrow `i`, or back against it. -/
inductive ResidualArrow where
  /-- Along arrow `i`, with the room it has left. -/
  | along (i : ℕ)
  /-- Back against arrow `i`, taking back what it carries. -/
  | back (i : ℕ)
deriving DecidableEq, Repr

namespace ResidualArrow

/-- The arrow of the network it belongs to. -/
def id : ResidualArrow → ℕ
  | along i => i
  | back i => i

/-- The vertex it leaves. -/
def tail (N : Network) : ResidualArrow → ℕ
  | along i => N.tail i
  | back i => N.head i

/-- The vertex it points to. -/
def head (N : Network) : ResidualArrow → ℕ
  | along i => N.head i
  | back i => N.tail i

/-- **Its residual capacity** under the flow `f`: what arrow `i` has left, or what it carries. -/
def residualCapacity (N : Network) (f : Flow) : ResidualArrow → ℕ
  | along i => N.capOf i - f.on i
  | back i => f.on i

end ResidualArrow

/-- Where the residual arrows `p`, taken in order from `u`, arrive, when each is an arrow of `N`
and leaves the vertex the one before it arrived at; `none` when one does not. -/
def ends (N : Network) : ℕ → List ResidualArrow → Option ℕ
  | u, [] => some u
  | u, a :: p =>
    if a.id < N.g.arrows.length ∧ a.tail N = u then ends N (a.head N) p else none

/-- The vertices the residual arrows `p` pass from `u`. -/
def visits (N : Network) (u : ℕ) (p : List ResidualArrow) : List ℕ := u :: p.map (·.head N)

/-- **An augmenting path**: from the source to the sink in the remaining capacity, every arrow of
it with room, passing no vertex twice. -/
def IsAugmentingPath (N : Network) (f : Flow) (p : List ResidualArrow) : Prop :=
  ends N N.source p = some N.sink ∧ (visits N N.source p).Nodup ∧
    ∀ a ∈ p, 0 < a.residualCapacity N f

/-- **One added path**: the path and the amount sent along it. -/
structure Augmentation where
  /-- The path, in the remaining capacity. -/
  path : List ResidualArrow
  /-- The amount sent. -/
  amount : ℕ
deriving DecidableEq, Repr

/-- Send `x` along one residual arrow: along arrow `i` adds to it, back against it takes away. -/
def sendOne (x : ℕ) (f : Flow) : ResidualArrow → Flow
  | .along i => f.modify i (· + x)
  | .back i => f.modify i (· - x)

/-- Send `x.amount` along every arrow of `x.path`. -/
def Augmentation.apply (f : Flow) (x : Augmentation) : Flow := x.path.foldl (sendOne x.amount) f

/-- Apply the added paths in order. -/
def applyAll (f : Flow) (xs : List Augmentation) : Flow := xs.foldl Augmentation.apply f

/-- **Each added path is augmenting when its turn comes**: under the flow the earlier ones left,
and its amount fits the room of every arrow on it. -/
def FitInTurn (N : Network) : Flow → List Augmentation → Prop
  | _, [] => True
  | f, x :: xs =>
    (IsAugmentingPath N f x.path ∧ ∀ a ∈ x.path, x.amount ≤ a.residualCapacity N f) ∧
      FitInTurn N (x.apply f) xs

/-! ## The open choice: a path rule -/

/-- **A path rule**: one round sends more along paths it chooses, or sends nothing. It may keep
something from one round to the next (Dinic's rule keeps nothing; capacity scaling keeps its
threshold). -/
structure PathRule where
  /-- What the rule keeps between rounds. -/
  Memory : Type
  /-- What it keeps before the first round. -/
  start : Network → Memory
  /-- One round on the current flow: what it keeps next, and the paths it added, in order. -/
  round : Network → Memory → Flow → Memory × List Augmentation

/-- **It sends only along augmenting paths**: every path a round adds is augmenting when its turn
comes. -/
def PathRule.SendsAlongAugmentingPaths (r : PathRule) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ m f, IsFlow N f → FitInTurn N f (r.round N m f).2

/-- **A round that sends adds at least 1**: every path it adds carries at least one unit. -/
def PathRule.AddsAtLeastOne (r : PathRule) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ m f, IsFlow N f → ∀ x ∈ (r.round N m f).2, 1 ≤ x.amount

/-- **It sends nothing only when no augmenting path is left.** -/
def PathRule.NoneOnlyWhenDone (r : PathRule) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ m f, IsFlow N f → (r.round N m f).2 = [] →
    ∀ p, ¬ IsAugmentingPath N f p

/-- **The promise every path rule keeps**, so the loop around it answers with a largest flow and
its cut. -/
structure PathRule.Promise (r : PathRule) : Prop where
  /-- It sends only along augmenting paths. -/
  sendsAlong : r.SendsAlongAugmentingPaths
  /-- A round that sends adds at least 1. -/
  addsAtLeastOne : r.AddsAtLeastOne
  /-- It sends nothing only when no augmenting path is left. -/
  noneOnlyWhenDone : r.NoneOnlyWhenDone

/-! ## The answer -/

/-- **The capacity of a cut**: the capacities of the arrows leaving the source's side `side`. -/
def cutCapacity (N : Network) (side : List ℕ) : ℕ :=
  ((N.ids.filter fun i => N.tail i ∈ side ∧ N.head i ∉ side).map N.capOf).sum

/-- **The answer**: a flow, and the source's side of a cut. -/
structure Answer where
  /-- The amount on each arrow. -/
  flow : Flow
  /-- The vertices on the source's side of the cut. -/
  side : List ℕ

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `MaxFlow.lean` proves the library's procedures meet it
(`MaxFlow.contract`). -/

/-- The procedures the box speaks of: the answer, and the paths each round added, in order. -/
structure Ops where
  /-- The answer: a flow and the source's side of a cut. -/
  maxFlow : Network → Answer
  /-- The paths each round added, in order; rounds that added nothing are not listed. -/
  rounds : Network → List (List Augmentation)
  /-- The design's invariants, on a flow's state. -/
  Valid : State → Prop
  /-- The answer's flow is what the rounds sent, from the zero flow. -/
  walks : ∀ N, (maxFlow N).flow = (rounds N).foldl applyAll (Flow.zero N)
  /-- The zero flow keeps the invariants. -/
  startValid : ∀ N : Network, N.WellFormed → Valid ⟨N, Flow.zero N⟩
  /-- Every round keeps the invariants. -/
  roundsKeep : ∀ N : Network, N.WellFormed → ∀ k ≤ (rounds N).length,
    Valid ⟨N, ((rounds N).take k).foldl applyAll (Flow.zero N)⟩
  /-- Every path the rounds added was augmenting when its turn came, its amount fitting every
  arrow on it, and carried at least one unit. -/
  augments : ∀ N : Network, N.WellFormed →
    FitInTurn N (Flow.zero N) (rounds N).flatten ∧ ∀ x ∈ (rounds N).flatten, 1 ≤ x.amount

/-- **A flow that respects every arrow's capacity and loses nothing at any vertex.** -/
def Ops.ReturnsAFlow (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → IsFlow N (o.maxFlow N).flow

/-- **Beside it a cut: the source on one side, the sink on the other, and the capacities of arrows
leaving the source's side add up to the flow amount.** -/
def Ops.CutMatchesFlow (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed →
    N.source ∈ (o.maxFlow N).side ∧ N.sink ∉ (o.maxFlow N).side ∧
      (cutCapacity N (o.maxFlow N).side : ℤ) = value N (o.maxFlow N).flow

/-- **This flow is the largest**: no flow on the network has a larger amount. -/
def Ops.Largest (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ f, IsFlow N f → value N f ≤ value N (o.maxFlow N).flow

/-! ## The cost -/

/-- All the paths the rounds added. -/
def Ops.added (o : Ops) (N : Network) : List Augmentation := (o.rounds N).flatten

/-- **With integer capacities every rule finishes**: it adds at most as many paths as the
largest flow amount. -/
def Ops.FinishesWithIntegers (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ((o.added N).length : ℤ) ≤ value N (o.maxFlow N).flow

/-- **A bound set by the network's size alone, not by its capacities**: the number of added paths
is at most some function of the number of vertices and of arrows. -/
def Ops.BoundSetBySize (o : Ops) : Prop :=
  ∃ b : ℕ → ℕ → ℕ, ∀ N : Network, N.WellFormed →
    (o.added N).length ≤ b N.g.n N.g.arrows.length

/-- **At most n·m added paths**, for n vertices and m arrows. -/
def Ops.AugmentationsAtMostNM (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → (o.added N).length ≤ N.g.n * N.g.arrows.length

/-- **At most n rounds**, for n vertices. -/
def Ops.RoundsAtMostN (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → (o.rounds N).length ≤ N.g.n

/-- **A legal flow**: the box's invariants 1 and 2; invariant 3 holds by the type. -/
def Valid (st : State) : Prop :=
  WithinCapacity st ∧ Conserved st

/-- **The max-flow contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Move as much as possible from a source to a sink through a flow network, and prove that
  -- nothing more fits.
  /-- Promise: a flow, a cut of the same amount, and so the largest flow. -/
  promise :
    o.ReturnsAFlow ∧     -- a flow that respects every capacity and loses nothing
    o.CutMatchesFlow ∧   -- a cut whose capacity is the flow amount
    o.Largest            -- no flow exceeds any cut, so this flow is the largest
  -- Idea: Augmentation over residual state: every unit sent can be taken back, so a later path
  -- may undo part of an earlier one. A **path rule** picks each next path, until none is left.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    WithinCapacity st ∧   -- 1. no arrow carries more than its capacity, or a negative amount
    Conserved st          -- 2. what comes in goes out, except at the source and the sink
                          -- 3. true by construction: every amount is a natural number
  /-- Cost: every rule finishes, and the library's within a bound set by size alone. -/
  cost :
    o.FinishesWithIntegers ∧       -- at most as many added paths as the flow amount
    o.BoundSetBySize               -- one search per added path is argued
  -- Assumes: Capacities are integers.

end AlgoDesign.Flows
