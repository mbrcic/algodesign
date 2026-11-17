/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Spec

/-!
# Matching people with objects: the specification

Sources: the Flow chapter, "Who gets the quiet rooms?"; Korte and Vygen, *Combinatorial
Optimization*, the matching network of unit capacities from a source to every person and from
every object to a sink; König (1931) for the cover; Hall (1935) for the blocked group.

> **Goal:** Match as many people as possible with objects they accept, at most one each, and show
> what stops a larger matching.
>
> **Promise:** A maximum matching, and beside it a cover: as many people and objects as there are
> pairs, with every acceptable pair incident to one of them, so no matching is larger. If some
> person stays unmatched, a blocked group: some people who together accept fewer objects than
> there are of them.
>
> **Idea:** Reduction to max flow (The design 7.1): one unit of capacity from a source to every
> person, on every acceptable pair, and from every object to a sink. An integer flow is a
> matching.
>
> **Invariants:**
>
> 1. Those of max flow, on this network.
>
> **Cost:** As max flow; at most one step per person.

A problem (`Problem`) is a number of people, a number of objects and the acceptable pairs, each a
person and an object. The matching network (`Problem.network`) has the source at vertex 0, person
`p` at `1 + p`, object `o` after all the people, at `1 + people + o`, and the sink last. Its arrows
come in three blocks, each in order: the source to every person, then one arrow per acceptable
pair in input order, then every object to the sink; every arrow carries 1. A pair is matched when
its arrow carries the unit (`carried`).

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Matching.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `Ops.maxMatching`, a field of `Ops`: the matched pairs, a cover
  and, when someone stays unmatched, a blocked group.
- Promise [proved] → three parts: `Ops.MaximumMatching`, `Ops.CoverAsLarge`,
  `Ops.BlockedGroupWhenShort`. "So no matching is larger" is why the first part's bound follows
  from the second (`matching_le_cover`, in `Matching/Read.lean`). Not in the box: the invariants
  hold from the zero flow, `Ops.startValid`, and after every round, `Ops.roundsKeep`; the pairs
  are those whose arrows carry the unit in the flow the rounds sent, `Ops.walks`; every added path
  was augmenting in its turn and carried at least one unit, `Ops.augments`.
- Idea [proved] → the library's max flow on `Problem.network`; the cover is read from its last
  search: the people it did not reach and the objects it reached; the blocked group is the people
  it reached and the objects they accept.
- Invariants [proved] → `Valid`:
  1 [proved] `FlowRespected`, max flow's `Valid` on the matching network.
- Cost [argued] → `Ops.StepsAtMostPeople`: at most as many added paths as people, proved; "as max
  flow" is argued from the procedure, the library's max flow on this network.
- Assumes [none] → the box assumes nothing; `Problem.WellFormed`, every pair a person and an
  object of the problem, is a hypothesis of the promise parts.
-/

@[expose] public section

namespace AlgoDesign.Flows.Matching

open AlgoDesign.Graphs

/-- **A matching problem**: how many people, how many objects, and the acceptable pairs, each a
person and an object. -/
structure Problem where
  /-- The people are `0 … people − 1`. -/
  people : ℕ
  /-- The objects are `0 … objects − 1`. -/
  objects : ℕ
  /-- The acceptable pairs: person `e.1` accepts object `e.2`. -/
  pairs : List (ℕ × ℕ)
deriving DecidableEq, Repr

namespace Problem

variable (P : Problem)

/-- Every acceptable pair is a person and an object of the problem. -/
def WellFormed : Prop := ∀ e ∈ P.pairs, e.1 < P.people ∧ e.2 < P.objects

/-- **The matching network**: one unit from the source to every person, on every acceptable pair,
and from every object to the sink. -/
def network : Network where
  g := ⟨P.people + P.objects + 2,
    (List.range P.people).map (fun p => (0, 1 + p)) ++
      P.pairs.map (fun e => (1 + e.1, 1 + P.people + e.2)) ++
      (List.range P.objects).map (fun o => (1 + P.people + o, 1 + P.people + P.objects))⟩
  cap := List.replicate (P.people + P.pairs.length + P.objects) 1
  source := 0
  sink := 1 + P.people + P.objects

end Problem

/-- **The pairs whose arrows carry the unit** under the flow `f`, in input order. -/
def carried (P : Problem) (f : Flow) : List (ℕ × ℕ) :=
  ((List.range P.pairs.length).filter fun j => 0 < f.on (P.people + j)).map
    fun j => P.pairs.getD j (0, 0)

/-- **A matching**: acceptable pairs, each person in at most one and each object in at most one. -/
def IsMatching (P : Problem) (M : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M, e ∈ P.pairs) ∧ (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup

/-- **A cover**: people and objects, none listed twice, with every acceptable pair incident to one
of them. -/
def IsCover (P : Problem) (people objects : List ℕ) : Prop :=
  people.Nodup ∧ objects.Nodup ∧ (∀ p ∈ people, p < P.people) ∧
    (∀ o ∈ objects, o < P.objects) ∧ ∀ e ∈ P.pairs, e.1 ∈ people ∨ e.2 ∈ objects

/-- A group of people, and the objects beside them. -/
structure Group where
  /-- The people of the group. -/
  people : List ℕ
  /-- The objects beside them. -/
  objects : List ℕ
deriving DecidableEq, Repr

/-- **A blocked group**: some people, none listed twice, beside exactly the objects they accept
between them, and fewer of those than there are people. -/
def IsBlocked (P : Problem) (g : Group) : Prop :=
  g.people.Nodup ∧ (∀ p ∈ g.people, p < P.people) ∧ g.objects.Nodup ∧
    (∀ o, o ∈ g.objects ↔ ∃ p ∈ g.people, (p, o) ∈ P.pairs) ∧
    g.objects.length < g.people.length

/-! ## A flow's state -/

/-- **A flow on a problem's matching network**, the state the rounds change. -/
structure State where
  /-- The problem. -/
  prob : Problem
  /-- The amount on each arrow of its matching network. -/
  flow : Flow

/-- Box invariant 1: those of max flow, on this network. -/
def FlowRespected (st : State) : Prop := Flows.Valid ⟨st.prob.network, st.flow⟩

/-! ## The answer -/

/-- **The answer**: the matched pairs, a cover, and a blocked group when someone stays unmatched. -/
structure Answer where
  /-- The matched pairs, each a person and an object. -/
  pairs : List (ℕ × ℕ)
  /-- The cover's people. -/
  coverPeople : List ℕ
  /-- The cover's objects. -/
  coverObjects : List ℕ
  /-- A blocked group, when someone stays unmatched. -/
  blocked : Option Group
deriving DecidableEq, Repr

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `Matching.lean` proves the library's procedures meet it
(`Matching.contract`). -/

/-- The procedures the box speaks of: the answer, and the paths each round of max flow added. -/
structure Ops where
  /-- The answer: the pairs, a cover and, when someone stays unmatched, a blocked group. -/
  maxMatching : Problem → Answer
  /-- The paths each round added, in order; rounds that added nothing are not listed. -/
  rounds : Problem → List (List Augmentation)
  /-- The design's invariants, on a flow's state. -/
  Valid : State → Prop
  /-- An integer flow is a matching: the pairs are those whose arrows carry the unit in
  the flow the rounds sent, from the zero flow. -/
  walks : ∀ P, (maxMatching P).pairs =
    carried P ((rounds P).foldl applyAll (Flow.zero P.network))
  /-- The zero flow keeps the invariants. -/
  startValid : ∀ P : Problem, P.WellFormed → Valid ⟨P, Flow.zero P.network⟩
  /-- Every round keeps the invariants. -/
  roundsKeep : ∀ P : Problem, P.WellFormed → ∀ k ≤ (rounds P).length,
    Valid ⟨P, ((rounds P).take k).foldl applyAll (Flow.zero P.network)⟩
  /-- Every path the rounds added was augmenting on the matching network when its turn came, its
  amount fitting every arrow on it, and carried at least one unit. -/
  augments : ∀ P : Problem, P.WellFormed →
    FitInTurn P.network (Flow.zero P.network) (rounds P).flatten ∧
      ∀ x ∈ (rounds P).flatten, 1 ≤ x.amount

/-- **A maximum matching**: a matching, and no matching is larger. -/
def Ops.MaximumMatching (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → IsMatching P (o.maxMatching P).pairs ∧
    ∀ M, IsMatching P M → M.length ≤ (o.maxMatching P).pairs.length

/-- **Beside it a cover: as many people and objects as there are pairs, with every acceptable
pair incident to one of them.** -/
def Ops.CoverAsLarge (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed →
    IsCover P (o.maxMatching P).coverPeople (o.maxMatching P).coverObjects ∧
      (o.maxMatching P).coverPeople.length + (o.maxMatching P).coverObjects.length =
        (o.maxMatching P).pairs.length

/-- **If some person stays unmatched, a blocked group: some people who together accept fewer
objects than there are of them.** -/
def Ops.BlockedGroupWhenShort (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → (o.maxMatching P).pairs.length < P.people →
    ∃ g, (o.maxMatching P).blocked = some g ∧ IsBlocked P g

/-! ## The cost -/

/-- **At most one step per person**: max flow adds at most as many paths as there are people. -/
def Ops.StepsAtMostPeople (o : Ops) : Prop :=
  ∀ P : Problem, P.WellFormed → (o.rounds P).flatten.length ≤ P.people

/-- **A legal flow on the matching network**: the box's one invariant. -/
def Valid (st : State) : Prop := FlowRespected st

/-- **The matching contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Match as many people as possible with objects they accept, at most one each, and show
  -- what stops a larger matching.
  /-- Promise: a maximum matching, a cover as large, and a blocked group when someone is left. -/
  promise :
    o.MaximumMatching ∧        -- a maximum matching
    o.CoverAsLarge ∧           -- a cover as large, every pair incident to it
    o.BlockedGroupWhenShort    -- if some person stays unmatched, a blocked group
  -- Idea: Reduction to max flow (The design 7.1): one unit of capacity from a source to every
  -- person, on every acceptable pair, and from every object to a sink. An integer flow is a
  -- matching.
  /-- Invariants: the box's one. -/
  invariants : ∀ st, o.Valid st ↔
    FlowRespected st           -- 1. those of max flow, on this network
  /-- Cost: at most one step per person. -/
  cost : o.StepsAtMostPeople   -- "as max flow" is argued

end AlgoDesign.Flows.Matching
