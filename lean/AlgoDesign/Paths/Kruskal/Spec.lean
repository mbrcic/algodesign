/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.LinkNetwork

/-!
# Cheapest spanning forest: the specification

Sources: the Paths chapter, "After the big snow"; Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms* (4th ed.), §21.2, `MST-KRUSKAL` (p. 594), for the walk over the
links sorted by cost, and Theorem 21.1 (p. 587), the cut property with ties allowed: a cheapest
link across a cut that no kept link crosses keeps the kept links part of some cheapest spanning
tree.

> **Goal:** Join every vertex with the least total link cost.
>
> **Promise:** The chosen links join every two vertices the graph joins, close no cycle, and no
> other such set of links has a smaller total.
>
> **Idea:** Greedy-exchange. Take the links cheapest first, and keep a link unless it closes a
> cycle.
>
> **Invariants:**
>
> 1. The links kept so far are part of some minimum such set.
> 2. Two vertices are in one union-find group (@dsg-m5-union-find) exactly when the kept links join
>    them.
>
> **Cost:** Sorting the links, then a nearly constant union-find step per link.

The walk runs on a `LinkNetwork`, over an order of its link ids. A set of links is a list of link
ids (`LinkNetwork.Joins`, `LinkNetwork.ClosesNoCycle`), so two links between the same vertices may
cost differently, and a loop or a doubled link is an ordinary input.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Kruskal.contract` proves the library's procedures, `ops`, meet it.

- Goal [required] → the answer, `kruskal`, a field of `Ops`: the kept link ids, in the order kept.
- Promise [proved] → three parts: `Ops.JoinsWhatGraphJoins`, `Ops.ClosesNoCycle`,
  `Ops.NoCheaperForest`. On a graph in several pieces the chosen links are a spanning forest, one
  tree per piece. Not in the box: the invariants hold along the walk, `Ops.stepKeeps`, from its
  start in every order that takes the links cheapest first, `Ops.emptyValid`, whatever it does
  with equal costs; the walk starts from its network and keeps it, `Ops.carries` and
  `Ops.keepsNetwork`; its order takes the links cheapest first, `Ops.orderCheapestFirst`.
- Idea [mentioned] → taking the next link and keeping it when the Graphs chapter's union-find merges
  its two ends is `Ops.step`; a link whose ends are already in one group closes a cycle, and the
  merge answers no. The library's order sorts the link ids by cost, equal costs by id; the walk
  stops once one group is left, since every later link has both ends in it.
- Invariants [proved] → `Valid`:
  1 [proved] `PartOfCheapest`.
  2 [proved] `GroupsAreKeptJoins`.
  Not in the box: `WellFormed`, which the steps keep together with `Valid`,
  `Ops.stepKeepsWellFormed`, from the start, `Ops.emptyWellFormed`; its pieces are
  `UnionFindReady`, `KeptClosesNoCycle`, `RestCheapestFirst`, `PassedAreJoined`.
- Cost [argued] → `Ops.OneStepPerLink`: `State.tried`, the links the walk (`runSteps`) gives to the
  union-find, each at most once and at most one per link, proved; the sort, and the nearly constant
  cost of a union-find step over a long run, argued: Cormen, Leiserson, Rivest and Stein, §19.4,
  Theorem 19.14.
- Assumes [none] → the box assumes nothing; any integer costs, zero and negative included.
-/

@[expose] public section

namespace AlgoDesign.Paths.Kruskal

open AlgoDesign.Graphs LinkNetwork

/-! ## The walk's state -/

/-- **The state of the walk.** -/
structure State where
  /-- The network the walk runs on. -/
  net : LinkNetwork
  /-- The link ids still to take, in order. -/
  rest : List ℕ
  /-- The kept link ids, in the order kept. -/
  kept : List ℕ
  /-- The link ids given to the union-find, in order. -/
  tried : List ℕ
  /-- The union-find over the vertices, its groups joined by the kept links. -/
  uf : UnionFind

/-- **The links are taken cheapest first**: every link id once, and no link before a cheaper
one. -/
def CheapestFirst (N : LinkNetwork) (ord : List ℕ) : Prop :=
  ord.Perm (List.range N.g.links.length) ∧ ord.Pairwise fun i j => N.linkCost i ≤ N.linkCost j

/-- Box invariant 1: the links kept so far are part of some minimum such set. -/
def PartOfCheapest (st : State) : Prop :=
  ∃ T, st.net.CheapestForest T ∧ ∀ i ∈ st.kept, i ∈ T

/-- Box invariant 2: two vertices are in one union-find group exactly when the kept links join
them. -/
def GroupsAreKeptJoins (st : State) : Prop :=
  ∀ u < st.net.g.n, ∀ v < st.net.g.n, (st.uf.Same u v ↔ st.net.Joins st.kept u v)

/-- Not in the box: the union-find is legal and well formed, over the graph's vertices. -/
def UnionFindReady (st : State) : Prop :=
  st.uf.Valid ∧ st.uf.WellFormed ∧ st.uf.n = st.net.g.n

/-- Not in the box: the kept links are links of the graph and close no cycle. -/
def KeptClosesNoCycle (st : State) : Prop :=
  (∀ i ∈ st.kept, i < st.net.g.links.length) ∧ st.net.ClosesNoCycle st.kept

/-- Not in the box: the links still to take are links of the graph, cheapest first. -/
def RestCheapestFirst (st : State) : Prop :=
  (∀ i ∈ st.rest, i < st.net.g.links.length) ∧
    st.rest.Pairwise fun i j => st.net.linkCost i ≤ st.net.linkCost j

/-- Not in the box: the kept links join the two ends of every link already taken. -/
def PassedAreJoined (st : State) : Prop :=
  ∀ i < st.net.g.links.length, i ∉ st.rest →
    st.net.Joins st.kept (st.net.ends i).1 (st.net.ends i).2

/-- **A well-formed walk state**: the conditions the walk needs beyond the box, which its steps
keep together with `Valid`. -/
def WellFormed (st : State) : Prop :=
  UnionFindReady st ∧ KeptClosesNoCycle st ∧ RestCheapestFirst st ∧ PassedAreJoined st

/-- Take steps while links are left and more than one group is, at most `f` of them. -/
def runSteps (step : State → State) : ℕ → State → State
  | 0, st => st
  | f + 1, st => if st.rest = [] ∨ st.uf.count = 1 then st else runSteps step f (step st)

/-! ## The contract, the part Lean checks

`Ops` names the procedures the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `Kruskal.lean` proves the library's procedures meet it
(`Kruskal.contract`). -/

/-- The procedures the box speaks of: the order the links are taken in, the walk's start and step,
and the whole walk, read off the state its steps reach. -/
structure Ops where
  /-- The order the links are taken in. -/
  order : LinkNetwork → List ℕ
  /-- The start: no link kept, every vertex a group of its own, the links to take in the given
  order. -/
  start : LinkNetwork → List ℕ → State
  /-- One step: take the next link, and keep it when the union-find merges its two ends. -/
  step : LinkNetwork → State → State
  /-- The walk: the kept link ids, in the order kept. -/
  kruskal : LinkNetwork → List ℕ
  /-- The design's invariants, on the walk's state. -/
  Valid : State → Prop
  /-- The answer is read off the state the steps reach from the start, at most one step per link,
  so the invariants and the cost are of the walk that answers. -/
  walks : ∀ N, kruskal N =
    (runSteps (step N) N.g.links.length (start N (order N))).kept
  /-- The order takes the links cheapest first. -/
  orderCheapestFirst : ∀ N, CheapestFirst N (order N)
  /-- The start carries the network it is given. -/
  carries : ∀ N ord, (start N ord).net = N
  /-- A step keeps the walk's network. -/
  keepsNetwork : ∀ N st, (step N st).net = st.net
  /-- On a well-formed network, from any order that takes the links cheapest first, the start
  keeps the invariants. -/
  emptyValid : ∀ N : LinkNetwork, N.WellFormed → ∀ ord, CheapestFirst N ord →
    Valid (start N ord)
  /-- On a well-formed network, from any order that takes the links cheapest first, the start is
  well formed. -/
  emptyWellFormed : ∀ N : LinkNetwork, N.WellFormed → ∀ ord, CheapestFirst N ord →
    WellFormed (start N ord)
  /-- Every step with a link left keeps the invariants. -/
  stepKeeps : ∀ N : LinkNetwork, N.WellFormed → ∀ st, st.net = N → Valid st → WellFormed st →
    st.rest ≠ [] → Valid (step N st)
  /-- Every step with a link left keeps the walk well formed. -/
  stepKeepsWellFormed : ∀ N : LinkNetwork, N.WellFormed → ∀ st, st.net = N → Valid st →
    WellFormed st → st.rest ≠ [] → WellFormed (step N st)

/-- The state the walk ends in. -/
abbrev Ops.final (o : Ops) (N : LinkNetwork) : State :=
  runSteps (o.step N) N.g.links.length (o.start N (o.order N))

/-- **The chosen links join every two vertices the graph joins**, on a well-formed network. -/
def Ops.JoinsWhatGraphJoins (o : Ops) : Prop :=
  ∀ N : LinkNetwork, N.WellFormed → N.JoinsWhatGraphJoins (o.kruskal N)

/-- **The chosen links are links of the graph and close no cycle**, on a well-formed network. -/
def Ops.ClosesNoCycle (o : Ops) : Prop :=
  ∀ N : LinkNetwork, N.WellFormed →
    (∀ i ∈ o.kruskal N, i < N.g.links.length) ∧ N.ClosesNoCycle (o.kruskal N)

/-- **No other such set of links has a smaller total**, on a well-formed network: no spanning
forest costs less than the chosen links. -/
def Ops.NoCheaperForest (o : Ops) : Prop :=
  ∀ N : LinkNetwork, N.WellFormed → ∀ F, N.IsSpanningForest F → N.total (o.kruskal N) ≤ N.total F

/-! ## The cost -/

/-- **One union-find step per link**: over the walk, each link given to the union-find at most
once. -/
def Ops.OneStepPerLink (o : Ops) : Prop :=
  ∀ N : LinkNetwork, (o.final N).tried.Nodup ∧ (o.final N).tried.length ≤ N.g.links.length

/-- **A legal state of the walk**: the box's two invariants. -/
def Valid (st : State) : Prop :=
  PartOfCheapest st ∧ GroupsAreKeptJoins st

/-- **The cheapest spanning forest's contract**, the part of the design Lean checks, one field per
box field and one conjunct per box line. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Join every vertex with the least total link cost.
  /-- Promise: everything the graph joins, no cycle, no cheaper such set. -/
  promise :
    o.JoinsWhatGraphJoins ∧  -- the chosen links join every two vertices the graph joins
    o.ClosesNoCycle ∧        -- they close no cycle
    o.NoCheaperForest        -- no other such set of links has a smaller total
  -- Idea: Greedy-exchange. Take the links cheapest first, and keep a link unless it closes a
  -- cycle.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ st, o.Valid st ↔
    PartOfCheapest st ∧      -- 1. the links kept so far are part of some minimum such set
    GroupsAreKeptJoins st    -- 2. one union-find group exactly when the kept links join them
  /-- Cost: each link given to the union-find at most once. -/
  cost : o.OneStepPerLink  -- over the walk; the sort and the near-constant step are argued

end AlgoDesign.Paths.Kruskal
