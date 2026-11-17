/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Loop

/-!
# The design project's contract: a path rule for your own networks

Source: the Flow chapter's design project. The reader states the requirements, asks an AI for
several path rules, runs them on their own networks, keeps those no other rule beats on both code
size and time (the Pareto frontier, chapter 1's term), and picks one. The box's top half is the
problem, and it is fixed before any candidate exists:

> **Goal:** Choose a path rule for your own networks: one that keeps the max-flow promise, meets
> the speed requirement you chose, and that no other rule beats on both code size and time.
>
> **Promise:** On every network, a flow and beside it a cut of the same amount, so the largest
> flow, reached by adding along augmenting paths, each carrying at least one unit.
>
> **Cost:** the speed requirement you chose, counted from the rule's rounds; time and code size,
> measured on the bench on your networks.
>
> **Assumes:** your networks; capacities are integers.

The box, field by field. `Contract`, last in this file, is the part Lean checks.

- Goal [mentioned] → the bench keeps the rules no other beats on both code size and time; Lean
  states no frontier.
- Promise [required] → `Contract.promise`, four parts. Three are the max-flow box's, read on the
  answer of the loop around the candidate's rule, `PathRule.maxFlow`: `Ops.ReturnsAFlow`,
  `Ops.CutMatchesFlow`, `Ops.Largest`. The fourth, `Ops.AddsAlongAugmentingPaths`, makes the
  rounds and paths the bench counts real rounds of augmenting paths; only with it is the loop a
  max-flow `Ops`, `Ops.loop`.
- Idea [none] → the box has none: the candidate's own path rule, `Ops.rule`.
- Invariants [none] → the box has none: a rule's invariants are its own, and the bench does not
  read them.
- Cost [measured] → `Contract.cost`, `Ops.MeetsSpeed`: the speed requirement the reader chose
  from the menu in the max-flow spec, counted from the rule's rounds on `Ops.loop`. Time and code
  size are measured on the bench, not stated here.
- Assumes [measured] → the reader's networks, in the bench; integer capacities by the type.

Words: a candidate is a path rule (`PathRule`), and the bench runs it inside the max-flow loop
(`PathRule.run`), which applies the paths each round reports. The speed menu: `Ops.RoundsAtMostN`,
`Ops.AugmentationsAtMostNM`, `Ops.BoundSetBySize` of the max-flow spec, or any conjunction of
them.
-/

@[expose] public section

namespace AlgoDesign.Flows.Workbench

/-- A candidate: the path rule the reader asked for. -/
structure Ops where
  /-- The candidate's path rule: what it keeps between rounds, and one round. -/
  rule : PathRule

/-- **Reached by adding along augmenting paths, each carrying at least one unit**: every path the
rounds added was augmenting when its turn came, its amount fitting every arrow on it, and carried
at least one unit. -/
def Ops.AddsAlongAugmentingPaths (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed →
    FitInTurn N (Flow.zero N) (o.rule.run N).1.flatten ∧
      ∀ x ∈ (o.rule.run N).1.flatten, 1 ≤ x.amount

/-- The max-flow procedures of a candidate whose rounds add along augmenting paths: the loop around
its rule, its answer and its rounds. The candidate claims no invariants here. -/
def Ops.loop (o : Ops) (h : o.AddsAlongAugmentingPaths) : Flows.Ops where
  maxFlow := o.rule.maxFlow
  rounds N := (o.rule.run N).1
  Valid _ := True
  walks N := o.rule.run_walks N
  startValid _ _ := trivial
  roundsKeep _ _ _ _ := trivial
  augments := h

/-- **A flow that respects every arrow's capacity and loses nothing at any vertex**, the max-flow
promise's first part, of the loop around the candidate's rule. -/
def Ops.ReturnsAFlow (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → IsFlow N (o.rule.maxFlow N).flow

/-- **Beside it a cut: the source on one side, the sink on the other, and the capacities of arrows
leaving the source's side add up to the flow amount**, the max-flow promise's second part. -/
def Ops.CutMatchesFlow (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed →
    N.source ∈ (o.rule.maxFlow N).side ∧ N.sink ∉ (o.rule.maxFlow N).side ∧
      (cutCapacity N (o.rule.maxFlow N).side : ℤ) = value N (o.rule.maxFlow N).flow

/-- **This flow is the largest**: no flow on the network has a larger amount, the max-flow
promise's third part. -/
def Ops.Largest (o : Ops) : Prop :=
  ∀ N : Network, N.WellFormed → ∀ f, IsFlow N f → value N f ≤ value N (o.rule.maxFlow N).flow

/-- **It meets the speed requirement you chose**, from the menu in the max-flow spec, counted from
the rule's rounds. -/
def Ops.MeetsSpeed (o : Ops) (speed : Flows.Ops → Prop) : Prop :=
  ∀ h, speed (o.loop h)

/-- **The design project's contract**, the part of it Lean checks, for the speed requirement
`speed`. It is the box's top half, which the human wrote: every candidate owes all of it. The
bottom half (idea, invariants) is the candidate's. -/
structure Contract (o : Ops) (speed : Flows.Ops → Prop) : Prop where
  -- Goal: Choose a path rule for your own networks: one that keeps the max-flow promise, meets
  -- the speed requirement you chose, and that no other rule beats on both code size and time.
  /-- Promise: a flow, a cut of the same amount, the largest, along augmenting paths. -/
  promise :
    o.ReturnsAFlow ∧              -- a flow that respects every capacity and loses nothing
    o.CutMatchesFlow ∧            -- a cut whose capacity is the flow amount
    o.Largest ∧                   -- no flow exceeds any cut, so this flow is the largest
    o.AddsAlongAugmentingPaths    -- every counted path augmenting in its turn, at least one unit
  -- Idea: none in the box; the candidate's own path rule.
  -- Invariants: none in the box; the candidate's own.
  /-- Cost: the speed requirement you chose, counted from the rule's rounds. -/
  cost : o.MeetsSpeed speed
  -- Cost: time and code size, measured by the bench on your networks, not stated here.
  -- Assumes: your networks; capacities are integers.

end AlgoDesign.Flows.Workbench
