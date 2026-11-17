/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Spec

/-!
# Assignment: the specification

Sources: the Flow chapter, "Splitting the rent so nobody envies"; Ahuja, Magnanti and Orlin,
*Network Flows* (1993), §12.4 (one person at a time, p. 471); Kleinberg and Tardos, *Algorithm
Design*, §7.13, (7.65), p. 409 (a chosen pair stays exact); Kuhn, "The Hungarian method for the
assignment problem" (1955).

> **Goal:** Give every person exactly one object and every object to one person at the least total
> cost, and prove that no assignment costs less.
>
> **Promise:** A least-cost assignment, and beside it a label on every person and every object: on
> every pair the two labels add up to at most the pair's cost, and on every chosen pair exactly
> to it. Adding the labels up proves that no assignment costs less. Read as prices, every person's
> object is their favorite after price.
>
> **Idea:** Reduction to min-cost flow (The design 7.3): the cheapest path rule, one
> person at a time, on the matching network; heights become the labels.
>
> **Invariants:**
>
> 1. The people placed so far hold different objects, at the least total cost for them.
> 2. After every step the labels fit every pair and are exact on the chosen ones.
>
> **Cost:** One best-first search per person; on a full table the work grows like the cube of the
> number of people.
>
> **Assumes:** As many objects as people.

A problem (`Problem`) is a table of costs, one row per person and one column per object. An
assignment gives person `i` the object `obj[i]`. The people are added one at a time, in row order;
a state (`State`) holds the objects of the people added so far and the labels of every person and
every object.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Assignment.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `Ops.assign`, a field of `Ops`: an assignment and the labels.
- Promise [proved] → four parts: `Ops.LeastCost`, `Ops.LabelsFit`, `Ops.ExactOnChosen`,
  `Ops.FavoriteAfterPrice`. "Adding the labels up proves that no assignment costs less" is why the
  first follows from the next two (`least_of_labels`, in `Assignment.lean`). Not in the box: the
  invariants hold before the first person, `Ops.startValid`, and after every person,
  `Ops.stepsKeep`; the answer is the state after the last person, `Ops.walks`.
- Idea [argued] → no theorem links the assignment to min-cost flow, so the reduction and the
  heights becoming the labels are argued. What is proved is the procedure: one search per person
  on changed costs `cost − label of the person − label of the object`, from the new person to the
  nearest free object, the earlier people moved along its path; afterwards the labels move by the
  distances found (`Assignment/Steps.lean`).
- Invariants [proved] → `Valid`:
  1 [proved] `CheapestForThesePeople`: the people added so far hold different objects, and no
  other such choice for them costs less; that this is the cheapest flow's invariants 1 and 2 on
  the matching network is argued.
  2 [proved] `LabelsFitAndExact`: the labels fit every pair of a person added so far, and are
  exact on the chosen pairs; that this is the cheapest flow's invariant 3, its heights read on
  both sides, is argued.
  Not in the box: `WellFormed`, one label per person and per object.
- Cost [argued] → `Ops.OneSearchPerPerson`: one more person per step, which follows from
  `Ops.adds`; one search per person is argued from the procedure, whose step runs the search once
  (`step`, `Assignment/Steps.lean`), and the cube of the number of people on a full table from the
  search's array scan.
- Assumes [proved] → `Problem.Square`, a hypothesis of the promise parts and of `Ops.startValid`.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-- **An assignment problem**: the cost of giving each person each object, one row per person. -/
structure Problem where
  /-- The costs, row `i` for person `i`, column `j` for object `j`. -/
  cost : List (List ℤ)
deriving DecidableEq, Repr

namespace Problem

variable (P : Problem)

/-- The number of people. -/
def n : ℕ := P.cost.length

/-- **As many objects as people**: every row has one cost per person. -/
def Square : Prop := ∀ row ∈ P.cost, row.length = P.n

/-- The cost of giving person `i` object `j`. -/
def costAt (i j : ℕ) : ℤ := (P.cost.getD i []).getD j 0

end Problem

/-- **An assignment of the people `0 … k − 1`**: each holds an object of the table, and no two hold
the same one. -/
def IsAssignmentOf (P : Problem) (obj : List ℕ) : Prop := (∀ j ∈ obj, j < P.n) ∧ obj.Nodup

/-- The cost of an assignment: each person's cost for their object, summed. -/
def assignmentCost (P : Problem) (obj : List ℕ) : ℤ :=
  ((List.range obj.length).map fun i => P.costAt i (obj.getD i 0)).sum

/-- Labels, one per person or one per object. -/
abbrev Labels := List ℤ

/-- The label of `i`. -/
def Labels.at (l : Labels) (i : ℕ) : ℤ := l.getD i 0

/-! ## The state of the steps -/

/-- **The people added so far, their objects, and the labels**, the state the steps change. -/
structure State where
  /-- The problem. -/
  prob : Problem
  /-- The objects of the people added so far, person `i` holding `obj[i]`. -/
  obj : List ℕ
  /-- The label of every person. -/
  personLabel : Labels
  /-- The label of every object. -/
  objectLabel : Labels

/-- Box invariant 1 (argued: the cheapest flow's invariants on this network): the people added so
far hold different objects, and no other choice of different objects for them costs less. -/
def CheapestForThesePeople (st : State) : Prop :=
  IsAssignmentOf st.prob st.obj ∧
    ∀ o, o.length = st.obj.length → IsAssignmentOf st.prob o →
      assignmentCost st.prob st.obj ≤ assignmentCost st.prob o

/-- Box invariant 2: after every step the labels fit every pair and are exact on the chosen ones;
a pair is a person added so far and any object. -/
def LabelsFitAndExact (st : State) : Prop :=
  (∀ i < st.obj.length, ∀ j < st.prob.n,
      st.personLabel.at i + st.objectLabel.at j ≤ st.prob.costAt i j) ∧
    ∀ i < st.obj.length,
      st.personLabel.at i + st.objectLabel.at (st.obj.getD i 0) = st.prob.costAt i (st.obj.getD i 0)

/-- Not in the box: one label per person and one per object. -/
def WellFormed (st : State) : Prop :=
  st.personLabel.length = st.prob.n ∧ st.objectLabel.length = st.prob.n

/-! ## The answer -/

/-- **The answer**: every person's object, and the labels of every person and every object. -/
structure Answer where
  /-- Person `i` gets object `obj[i]`. -/
  obj : List ℕ
  /-- The label of every person. -/
  personLabel : Labels
  /-- The label of every object. -/
  objectLabel : Labels

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `Assignment.lean` proves the library's procedures meet it
(`Assignment.contract`). -/

/-- The procedures the box speaks of: the answer, and the state after the first `k` people. -/
structure Ops where
  /-- The answer: an assignment and the labels. -/
  assign : Problem → Answer
  /-- The state after the first `k` people have been added. -/
  after : Problem → ℕ → State
  /-- The design's invariants, on a state of the steps. -/
  Valid : State → Prop
  /-- The answer is the state after the last person. -/
  walks : ∀ P, (after P P.n).obj = (assign P).obj ∧
    (after P P.n).personLabel = (assign P).personLabel ∧
      (after P P.n).objectLabel = (assign P).objectLabel
  /-- The state after `k` people has added exactly `k`. -/
  adds : ∀ P : Problem, P.Square → ∀ k ≤ P.n, (after P k).prob = P ∧ (after P k).obj.length = k
  /-- Before the first person the invariants hold. -/
  startValid : ∀ P : Problem, P.Square → Valid (after P 0)
  /-- After every person the invariants hold. -/
  stepsKeep : ∀ P : Problem, P.Square → ∀ k ≤ P.n, Valid (after P k)

/-- **A least-cost assignment**: every person gets a different object, and no assignment costs
less. -/
def Ops.LeastCost (o : Ops) : Prop :=
  ∀ P : Problem, P.Square →
    IsAssignmentOf P (o.assign P).obj ∧ (o.assign P).obj.length = P.n ∧
      ∀ σ, σ.length = P.n → IsAssignmentOf P σ →
        assignmentCost P (o.assign P).obj ≤ assignmentCost P σ

/-- **On every pair the two labels add up to at most the pair's cost.** -/
def Ops.LabelsFit (o : Ops) : Prop :=
  ∀ P : Problem, P.Square → ∀ i < P.n, ∀ j < P.n,
    (o.assign P).personLabel.at i + (o.assign P).objectLabel.at j ≤ P.costAt i j

/-- **On every chosen pair exactly to it.** -/
def Ops.ExactOnChosen (o : Ops) : Prop :=
  ∀ P : Problem, P.Square → ∀ i < P.n,
    (o.assign P).personLabel.at i + (o.assign P).objectLabel.at ((o.assign P).obj.getD i 0) =
      P.costAt i ((o.assign P).obj.getD i 0)

/-- **Read as prices, every person's object is their favorite after price**: with each object's
price the negative of its label, no object costs a person less, price included, than their own. -/
def Ops.FavoriteAfterPrice (o : Ops) : Prop :=
  ∀ P : Problem, P.Square → ∀ i < P.n, ∀ j < P.n,
    P.costAt i ((o.assign P).obj.getD i 0) -
        (o.assign P).objectLabel.at ((o.assign P).obj.getD i 0) ≤
      P.costAt i j - (o.assign P).objectLabel.at j

/-! ## The cost -/

/-- **One best-first search per person**: the steps add the people one at a time, so the answer is
reached after as many steps as there are people. -/
def Ops.OneSearchPerPerson (o : Ops) : Prop :=
  ∀ P : Problem, P.Square → ∀ k < P.n, (o.after P (k + 1)).obj.length = (o.after P k).obj.length + 1

/-- **A legal state of the steps**: the box's two invariants. -/
def Valid (st : State) : Prop :=
  CheapestForThesePeople st ∧ LabelsFitAndExact st

/-- **The assignment's contract**, the part of the design Lean checks, one field per box field and
one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Give every person exactly one object and every object to one person at the least total
  -- cost, and prove that no assignment costs less.
  /-- Promise: a least-cost assignment, labels that fit and are exact, and the prices' reading. -/
  promise :
    o.LeastCost ∧              -- a least-cost assignment
    o.LabelsFit ∧              -- on every pair the labels add up to at most its cost
    o.ExactOnChosen ∧          -- on every chosen pair exactly to it
    o.FavoriteAfterPrice      -- read as prices, every person's object is their favorite
  -- Idea: Reduction to min-cost flow (The design 7.3): the cheapest path rule, one person
  -- at a time, on the matching network; heights become the labels.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    CheapestForThesePeople st ∧   -- 1. people placed so far hold different objects, at least cost
    LabelsFitAndExact st          -- 2. the labels fit every pair and are exact on the chosen ones
  /-- Cost: one best-first search per person. -/
  cost : o.OneSearchPerPerson     -- the cube of the number of people on a full table is argued
  -- Assumes: As many objects as people.

end AlgoDesign.Flows.Assignment
