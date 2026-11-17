/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Spec

/-!
# Cheapest flow of a given amount: the specification

Sources: the Flow chapter, "Heights keep the search safe"; Ahuja, Magnanti and Orlin, *Network
Flows* (1993), §9.7 (successive shortest paths, p. 320) and its reduced costs (p. 323, the
opposite sign convention); Edmonds and Karp, "Theoretical improvements in algorithmic efficiency
for network flow problems" (1972), for the first heights all zero.

> **Goal:** Send a requested amount from the source to the sink as cheaply as possible, and prove
> that no cheaper way exists.
>
> **Promise:** A flow of the requested amount, cheapest among all flows of that amount, and heights
> on the vertices under which every unsaturated arrow has a changed cost of at least
> zero. If the network cannot carry the amount: the largest amount, cheapest for it, with the
> cut that proves the amount.
>
> **Idea:** The path rule "cheapest": best-first search on changed costs, stopped when the sink is
> settled. Taking a unit back refunds its cost; chapter 6's heights keep every unsaturated arrow at
> zero or more, so Dijkstra finds the cheapest path to add.
>
> **Invariants:**
>
> 1. Max flow's invariants 1–3.
> 2. The current flow is the cheapest for its current amount.
> 3. Under the heights, every unsaturated arrow has a changed cost of at least zero, at
>    every vertex, reached by the last search or not.
>
> **Cost:** One best-first search per round; the rounds grow with the requested amount.
>
> **Assumes:** No original arrow has a negative cost.

A problem (`Problem`) is a max-flow `Network`, one integer cost per arrow, listed by arrow id, and
the requested amount. A flow's cost is the sum over the arrows of cost times amount. The residual
capacity is max flow's (`ResidualArrow`): `along i` costs what arrow `i` costs, `back i` refunds
it, so it costs minus that. Under heights `h`, a residual arrow's changed cost is its cost plus the
height at its start minus the height at its end.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`MinCostFlow.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `Ops.minCostFlow`, a field of `Ops`: a flow, heights on the
  vertices, and the source's side of a cut.
- Promise [proved] → four parts: `Ops.SendsAFlow`, `Ops.CheapestForItsAmount`,
  `Ops.HeightsFit`, `Ops.ShortOnlyAtACut`. Not in the box: the invariants hold from the zero flow
  and the zero heights, `Ops.startsLevel` and `Ops.startValid`, and after every step with the
  heights after it, `Ops.roundsKeep`; the answer is what the rounds sent, `Ops.walks`; every added
  path was augmenting in its turn and carried at least one unit, `Ops.augments`. A flow here is an
  integer flow (max flow's `Flows.Flow`, a natural number per arrow), so "cheapest among all
  flows" is compared with integer flows; that no flow with fractional amounts is cheaper follows
  from the same heights and is argued.
- Idea [proved] → the loop of max flow with the cheapest path rule, stopped at the requested
  amount; a step's search settles vertices by changed cost and stops when the sink is settled;
  afterwards every settled vertex adds its cost from the source to its height, and every other
  vertex adds the sink's.
- Invariants [proved] → `Valid`:
  1 [proved] `FlowRespected`, max flow's `Valid` on the same network and flow.
  2 [proved] `CheapestForAmount`.
  3 [proved] `HeightsFitEverywhere`.
  Not in the box: `WellFormed`, one amount per arrow and one height per vertex.
- Cost [argued] → `Ops.RoundsAtMostAmount`: at most as many rounds as the requested amount, proved;
  one best-first search per round is argued from the procedure.
- Assumes [proved] → `Problem.NoArrowBelowZero`, a hypothesis of the promise parts and of
  `Ops.startValid`: it is what makes the zero heights fit.
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

/-- **A cheapest-flow problem**: a network, the cost of each arrow by arrow id, and the requested
amount. -/
structure Problem where
  /-- The network, with its capacities, source and sink. -/
  net : Network
  /-- The cost of each arrow, by arrow id. -/
  cost : List ℤ
  /-- The amount to send from the source to the sink. -/
  amount : ℕ
deriving DecidableEq, Repr

namespace Problem

variable (P : Problem)

/-- The network is well formed and every arrow has one cost. -/
def WellFormed : Prop := P.net.WellFormed ∧ P.cost.length = P.net.g.arrows.length

/-- **No arrow costs less than 0.** -/
def NoArrowBelowZero : Prop := ∀ c ∈ P.cost, 0 ≤ c

/-- The cost of arrow `i`. -/
def costOf (i : ℕ) : ℤ := P.cost.getD i 0

/-- **The cost of a flow**: each arrow's cost times the amount on it, summed. -/
def flowCost (f : Flow) : ℤ := (P.net.ids.map fun i => P.costOf i * f.on i).sum

/-- The cost of a residual arrow: along an arrow its cost, back against it the refund. -/
def residualCost : ResidualArrow → ℤ
  | .along i => P.costOf i
  | .back i => -P.costOf i

end Problem

/-- Heights on the vertices, listed by vertex. -/
abbrev Heights := List ℤ

/-- The height of vertex `v`. -/
def Heights.at (h : Heights) (v : ℕ) : ℤ := h.getD v 0

/-- **The changed cost** of a residual arrow under the heights `h`: its cost plus the height at
its start minus the height at its end. -/
def changedCost (P : Problem) (h : Heights) (a : ResidualArrow) : ℤ :=
  P.residualCost a + h.at (a.tail P.net) - h.at (a.head P.net)

/-! ## The state of the rounds -/

/-- **A flow with heights on its problem**, the state the rounds change. -/
structure State where
  /-- The problem. -/
  prob : Problem
  /-- The amount on each arrow. -/
  flow : Flow
  /-- The height of each vertex. -/
  heights : Heights

/-- Box invariant 1: max flow's invariants 1–3. -/
def FlowRespected (st : State) : Prop := Flows.Valid ⟨st.prob.net, st.flow⟩

/-- Box invariant 2: the current flow is the cheapest for its current amount. -/
def CheapestForAmount (st : State) : Prop :=
  ∀ g, IsFlow st.prob.net g → value st.prob.net g = value st.prob.net st.flow →
    st.prob.flowCost st.flow ≤ st.prob.flowCost g

/-- Box invariant 3: under the heights, every unsaturated arrow has a changed cost of at
least zero, at every vertex, reached by the last search or not. -/
def HeightsFitEverywhere (st : State) : Prop :=
  ∀ a : ResidualArrow, a.id < st.prob.net.g.arrows.length →
    0 < a.residualCapacity st.prob.net st.flow → 0 ≤ changedCost st.prob st.heights a

/-- Not in the box: one amount per arrow and one height per vertex. -/
def WellFormed (st : State) : Prop :=
  st.flow.length = st.prob.net.g.arrows.length ∧ st.heights.length = st.prob.net.g.n

/-! ## The answer -/

/-- **The answer**: a flow, heights on the vertices, and the source's side of a cut. -/
structure Answer where
  /-- The amount on each arrow. -/
  flow : Flow
  /-- The height of each vertex. -/
  heights : Heights
  /-- The vertices on the source's side of the cut; it proves the amount when the network cannot
  carry the requested one. -/
  side : List ℕ

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `MinCostFlow.lean` proves the library's procedures meet it
(`MinCostFlow.contract`). -/

/-- The procedures the box speaks of: the answer, the paths each step added, in order, and the
heights after each step. -/
structure Ops where
  /-- The answer: a flow, heights and the source's side of a cut. -/
  minCostFlow : Problem → Answer
  /-- The path each step added, with its amount, in order. -/
  rounds : Problem → List Augmentation
  /-- The heights after the first `k` rounds; before the first round, all zero. -/
  heightsAfter : Problem → ℕ → Heights
  /-- The design's invariants, on a state of the rounds. -/
  Valid : State → Prop
  /-- The answer's flow is what the rounds sent, from the zero flow, and its heights are those
  after the last step. -/
  walks : ∀ P, (minCostFlow P).flow = applyAll (Flow.zero P.net) (rounds P) ∧
    (minCostFlow P).heights = heightsAfter P (rounds P).length
  /-- The rounds start from zero heights. -/
  startsLevel : ∀ P, heightsAfter P 0 = List.replicate P.net.g.n 0
  /-- The zero flow with zero heights keeps the invariants, when no arrow costs less than 0. -/
  startValid : ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    Valid ⟨P, Flow.zero P.net, heightsAfter P 0⟩
  /-- Every round keeps the invariants: the flow after the first `k` rounds, with the heights after
  them. -/
  roundsKeep : ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero → ∀ k ≤ (rounds P).length,
    Valid ⟨P, applyAll (Flow.zero P.net) ((rounds P).take k), heightsAfter P k⟩
  /-- Every path the rounds added was augmenting when its turn came, its amount fitting every arrow
  on it, and carried at least one unit. -/
  augments : ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    FitInTurn P.net (Flow.zero P.net) (rounds P) ∧ ∀ x ∈ rounds P, 1 ≤ x.amount

/-- **A flow of the requested amount**: a flow, carrying at most the amount asked for; exactly it
unless the network cannot carry it, when `Ops.ShortOnlyAtACut`'s cut proves the amount sent the
largest. -/
def Ops.SendsAFlow (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    IsFlow P.net (o.minCostFlow P).flow ∧ value P.net (o.minCostFlow P).flow ≤ P.amount

/-- **Cheapest among all flows of that amount.** -/
def Ops.CheapestForItsAmount (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    CheapestForAmount ⟨P, (o.minCostFlow P).flow, (o.minCostFlow P).heights⟩

/-- **Heights on the vertices under which every unsaturated arrow has a changed cost of
at least zero.** -/
def Ops.HeightsFit (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    HeightsFitEverywhere ⟨P, (o.minCostFlow P).flow, (o.minCostFlow P).heights⟩

/-- **If the network cannot carry the amount: the largest amount, cheapest for it, with the cut
that proves the amount**: when less than the requested amount is sent, the source is on the side,
the sink is not, and the capacities of the arrows leaving the side add up to the amount sent. -/
def Ops.ShortOnlyAtACut (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero →
    value P.net (o.minCostFlow P).flow < P.amount →
      P.net.source ∈ (o.minCostFlow P).side ∧ P.net.sink ∉ (o.minCostFlow P).side ∧
        (cutCapacity P.net (o.minCostFlow P).side : ℤ) = value P.net (o.minCostFlow P).flow

/-! ## The cost -/

/-- **The rounds grow with the requested amount**: at most as many rounds as the amount, each
adding at least one unit. -/
def Ops.RoundsAtMostAmount (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → P.NoArrowBelowZero → (o.rounds P).length ≤ P.amount

/-- **A legal state of the rounds**: the box's three invariants. -/
def Valid (st : State) : Prop :=
  FlowRespected st ∧ CheapestForAmount st ∧ HeightsFitEverywhere st

/-- **The cheapest flow's contract**, the part of the design Lean checks, one field per box field
and one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Send a requested amount from the source to the sink as cheaply as possible, and prove
  -- that no cheaper way exists.
  /-- Promise: a flow of the amount, cheapest for it, heights that prove it, a cut when short. -/
  promise :
    o.SendsAFlow ∧             -- a flow of the requested amount
    o.CheapestForItsAmount ∧   -- cheapest among all flows of that amount
    o.HeightsFit ∧             -- heights under which no arrow with room has a negative changed cost
    o.ShortOnlyAtACut          -- the largest amount, with the cut that proves it, when short
  -- Idea: The path rule "cheapest": best-first search on changed costs, stopped when the sink is
  -- settled. Taking a unit back refunds its cost; chapter 6's heights keep every unsaturated arrow
  -- at zero or more, so Dijkstra finds the cheapest path to add.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    FlowRespected st ∧         -- 1. max flow's invariants 1–3
    CheapestForAmount st ∧     -- 2. the current flow is the cheapest for its current amount
    HeightsFitEverywhere st    -- 3. every arrow with room has a changed cost of at least zero
  /-- Cost: the rounds grow with the requested amount. -/
  cost : o.RoundsAtMostAmount   -- one best-first search per round is argued
  -- Assumes: No original arrow has a negative cost.

end AlgoDesign.Flows.MinCostFlow
