/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Point

/-!
# The graph index: the specification

Sources: the Geometry chapter, the graph index; Malkov and Yashunin, *Efficient and robust
approximate nearest neighbor search using Hierarchical Navigable Small World graphs* (2020),
Algorithms 1, 2, 4 and 5; Toussaint (1980), the relative neighborhood graph.

> **Goal:** answer "a place like this one" fast, at a recall you choose, among millions of places
> in hundreds of dimensions.
>
> **Promise:** up to $k$ stored points, nearest first, each measured exactly. They may not be the
> true nearest. Recall, measured on the data, says how often they are.
>
> **Idea:** link every new place to a few near neighbors that point in different directions, and
> link them back. Then walk, always stepping toward the query and keeping a short list of
> the best seen.
>
> **Invariants:**
>
> 1. Every place has at most a fixed number of neighbors.
> 2. A place picks its neighbors nearest first, skipping any candidate that is closer to one
>    already picked than to the place.
> 3. With layers, every place on a layer is on every layer below it, and each layer up keeps a
>    random few of the one below.
>
> **Cost:** per query, a few neighbors' distances for each step of a short walk; memory, a fixed
> number of links per place.
>
> **Assumes:** that walking downhill through the neighbors leads to the nearest. On some data it
> stops at a point that is not, a wrong answer that recall measures.

Words: a place is a node, its point `points[v]`; a neighbor is a link; the short list of the
best seen is the beam.

The box, field by field. `Contract`, last in this file, is the part Lean checks; `HNSW.contract`
proves the library's operations, `HNSW.ops`, meet it.

- Goal [measured] → the picking rule, the search's last step and the insertion, each a field of
  `Ops`; the walk itself is `SearchSpec`, proved, outside `Ops`; "fast, at a recall you choose"
  measured on GloVe, M = 16, a beam of 200 while building, all 10,000 questions, the beam width the
  dial.
- Promise [measured] → the last step, `Promise`, on a beam of stored nodes, each once [proved]; the
  walk that fills the beam, `SearchSpec`, proved of the library's search; "recall, measured on the
  data" [measured], on GloVe, M = 16, a beam of 200 while building, all 10,000 questions. No recall
  level is promised.
- Idea [mentioned] → invariant 2's picking and the insertion's back-links; the walk, steps that
  never move away from the query.
- Invariants [tested] → `Valid` on the stored graph, then the picking step:
  1 [proved] `DegreeBounded`.
  2 [proved] on a picking step, not the stored graph: `PicksDiverse`, required of the picking rule.
  3 [tested] `NestedLayers`, proved kept by every build; "a random few" tested of the layer draw.
  Not in the box: `NoSelfLinks`, `NoRepeatedLinks`, `EntryOnTop`, `OneNodePerPoint`
- Cost [measured] → distances per query measured on GloVe, M = 16, a beam of 200 while building, all
  10,000 questions; memory, `LinksPerPlaceAtMost`, links per place [proved].
- Assumes [measured] → recall against the scan, on GloVe, M = 16, a beam of 200 while building, all
  10,000 questions. No search guarantee is claimed: none exists for this variant.

The graph is stored as its points, and `links[v][l]`, node `v`'s neighbor
list on layer `l`, for each layer `v` is on, so a node is on layers
`0, …, (links[v]).length - 1` and the first half of invariant 3 holds by the representation. What
can fail is stated by `NestedLayers`: every node is on layer 0, and every link on a layer reaches
a node on that layer. The flat graph is the same structure with every node on layer 0 only.
-/

@[expose] public section

namespace AlgoDesign.Geometry

/-- An HNSW graph over the points `points`, node `v` being the point `points[v]`, with the caps it
was made with: `links[v][l]` is node `v`'s neighbors on layer `l`, for every layer `v` is on,
layer 0 first; the search starts at `entry`, `none` when there are no nodes. -/
structure HNSW (d : ℕ) (α : Type) where
  /-- How many neighbors a list above layer 0 may hold. -/
  m : ℕ
  /-- How many neighbors a list on layer 0 may hold. -/
  m0 : ℕ
  /-- The stored points, node `v` being `points[v]`. -/
  points : List (Point d α)
  /-- Per node, per layer it is on, its neighbors there. -/
  links : List (List (List ℕ))
  /-- Where every search starts. -/
  entry : Option ℕ
deriving DecidableEq

namespace HNSW

variable {d : ℕ} {α : Type}

/-- The number of nodes. -/
def size (g : HNSW d α) : ℕ := g.links.length

/-- How many layers node `v` is on: layers `0, …, layers v - 1`. -/
def layers (g : HNSW d α) (v : ℕ) : ℕ := (g.links.getD v []).length

/-- Node `v`'s neighbors on layer `l` (none off the graph). -/
def neighbors (g : HNSW d α) (v l : ℕ) : List ℕ := (g.links.getD v []).getD l []

/-- Node `v` is a node of the graph and is on layer `l`. -/
def OnLayer (g : HNSW d α) (v l : ℕ) : Prop := v < g.size ∧ l < g.layers v

/-- The graph with no nodes, at caps `m` (above layer 0) and `m0` (on it). -/
def empty (m m0 : ℕ) : HNSW d α := ⟨m, m0, [], [], none⟩

/-- How many neighbors a list on layer `l` may hold: `m0` on layer 0, `m` above it. -/
def cap (m m0 l : ℕ) : ℕ := if l = 0 then m0 else m

/-- Box invariant 1: every place has at most a fixed number of neighbors. Every list on layer 0
holds at most `m0` neighbors, every list above it at most `m`. -/
def DegreeBounded (g : HNSW d α) : Prop :=
  ∀ v < g.size, ∀ l < g.layers v, (g.neighbors v l).length ≤ cap g.m g.m0 l

/-- Box invariant 3: with layers, every place on a layer is on every layer below it, and each
layer up keeps a random few of the one below. A node is on layers `0, …, layers v - 1`, so the
first half holds by the representation; what can fail is that every node is on layer 0, and that
every link on a layer reaches a node on that layer (so it too is on every layer below). The
random few is the layer draw's, not a property of one graph. -/
def NestedLayers (g : HNSW d α) : Prop :=
  (∀ v < g.size, 0 < g.layers v) ∧
    ∀ v < g.size, ∀ l < g.layers v, ∀ u ∈ g.neighbors v l, g.OnLayer u l

/-- Not in the box: no node is its own neighbor. -/
def NoSelfLinks (g : HNSW d α) : Prop :=
  ∀ v < g.size, ∀ l < g.layers v, v ∉ g.neighbors v l

/-- Not in the box: no list names a neighbor twice. -/
def NoRepeatedLinks (g : HNSW d α) : Prop :=
  ∀ v < g.size, ∀ l < g.layers v, (g.neighbors v l).Nodup

/-- Not in the box: the entry point is a node on the top layer, no node on
more layers than it is; `none` exactly when there are no nodes. -/
def EntryOnTop (g : HNSW d α) : Prop :=
  match g.entry with
  | none => g.size = 0
  | some e => e < g.size ∧ ∀ v < g.size, g.layers v ≤ g.layers e

/-- Not in the box: one node per stored point, so every node is a point. -/
def OneNodePerPoint (g : HNSW d α) : Prop := g.points.length = g.size

section Ring

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- What the picking rule keeps from the candidates `cs`, given the neighbors `sofar` already
picked: each candidate in turn is picked when fewer than `m` are picked and none of those is
strictly nearer to it than `base` is (a tie keeps it); `picked` lists the picks, in order. -/
def PicksFrom (m : ℕ) (base : Point d α) :
    List (Point d α) → List (Point d α) → List (Point d α) → Prop
  | _, [], picked => picked = []
  | sofar, c :: cs, picked =>
    if sofar.length < m ∧ ∀ n ∈ sofar, sqDist base c ≤ sqDist n c then
      match picked with
      | [] => False
      | p :: ps => p = c ∧ PicksFrom m base (sofar ++ [c]) cs ps
    else PicksFrom m base sofar cs picked

/-- One picking step: the cap `m`, the place `base` whose list is picked, its candidates, and
what was picked. -/
structure Picking (d : ℕ) (α : Type) where
  /-- At most this many are picked. -/
  m : ℕ
  /-- The place whose neighbors are picked. -/
  base : Point d α
  /-- The candidates, in the order offered. -/
  candidates : List (Point d α)
  /-- What was picked, in order. -/
  picked : List (Point d α)

/-- Box invariant 2: a place picks its neighbors nearest first, skipping any candidate that is
closer to one already picked than to the place. The candidates come nearest to `base` first, and
`picked` is what that rule keeps of them, at most `m`, a tie with a neighbor already picked
keeping the candidate. -/
def PicksDiverse (p : Picking d α) : Prop :=
  p.candidates.Pairwise (fun a b => sqDist p.base a ≤ sqDist p.base b) ∧
    PicksFrom p.m p.base [] p.candidates p.picked


/-- The order the search reports in: by squared distance, then by id. -/
def ByDistance (a b : Neighbor α) : Prop :=
  a.sqDist < b.sqDist ∨ (a.sqDist = b.sqDist ∧ a.id ≤ b.id)

/-- The box's promise: up to `k` stored points, nearest first, each measured exactly. `ans` answers
the query `q` from the `beam` the walk ended with, over the stored points `pts`: it holds `k` of the
beam's nodes (all of them if fewer), each once, each a stored point with its exact squared distance
to `q`, in `ByDistance` order, and no stored node of the beam left out (its id not reported) comes
before one reported. Its domain, which `Contract.promise` states first: a beam of stored nodes, each
once. The same shape as LSH's `MeasuredExactly` over other candidates. -/
def Promise (pts : List (Point d α)) (q : Point d α) (k : ℕ) (beam : List ℕ)
    (ans : List (Neighbor α)) : Prop :=
  ans.length = min k beam.length ∧
  (ans.map Neighbor.id).Nodup ∧
  (∀ a ∈ ans, a.id ∈ beam ∧
    ∃ h : a.id < pts.length, a.sqDist = sqDist pts[a.id] q) ∧
  ans.Pairwise ByDistance ∧
  ∀ a ∈ ans, ∀ i ∈ beam, i ∉ ans.map Neighbor.id → ∀ h : i < pts.length,
    ByDistance a ⟨sqDist pts[i] q, i⟩

/-- One layer's candidates for an insertion: the layer, and the nodes the layer search found
on it. -/
structure Candidates where
  /-- The layer. -/
  layer : ℕ
  /-- The nodes found on that layer, the new node's picks to choose from. -/
  nodes : List ℕ
deriving DecidableEq

/-- What an insertion asks of its candidates, given the new node's top layer `top`: one list per
layer, each on a layer of the new node, without repeats, of stored nodes on that layer. The
layer search returns such lists. -/
def CandidatesOk (g : HNSW d α) (top : ℕ) (cands : List Candidates) : Prop :=
  (cands.map Candidates.layer).Nodup ∧
    ∀ c ∈ cands, c.layer ≤ top ∧ c.nodes.Nodup ∧ ∀ u ∈ c.nodes, g.OnLayer u c.layer

/-- The graphs built by the insertion `ins` from an empty graph, one point at a time, each with
candidates the layer search could return. -/
inductive Builds (ins : HNSW d α → Point d α → ℕ → List Candidates → HNSW d α) :
    HNSW d α → Prop where
  /-- An empty graph, at any caps. -/
  | empty (m m0 : ℕ) : Builds ins (empty m m0)
  /-- One more point, a node on layers `0, …, top`, with candidates `cands`. -/
  | insert {g : HNSW d α} (p : Point d α) (top : ℕ) (cands : List Candidates) :
      Builds ins g → CandidatesOk g top cands → Builds ins (ins g p top cands)

/-- Box cost, memory, in links: a fixed number of links per place. Node `v` stores at most `m0`
links on layer 0 and `m` on each layer above, so at most `m0 + m · (layers v - 1)` in all. -/
def LinksPerPlaceAtMost (g : HNSW d α) : Prop :=
  ∀ v < g.size, ((List.range (g.layers v)).map fun l => (g.neighbors v l).length).sum ≤
    g.m0 + g.m * (g.layers v - 1)

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe. `GraphIndex.lean`, the
file that imports the whole structure, proves the library's operations meet it (`HNSW.contract`).
-/

/-- The operations the box speaks of: the picking rule, the search's last step, the insertion, and
the invariant. -/
structure Ops (d : ℕ) (α : Type) where
  /-- The picking rule: at most `m` neighbors for `base` from candidates nearest first. -/
  select : ℕ → Point d α → List (Point d α) → List (Point d α)
  /-- The search's last step: the answer to `q` from the beam, over the stored points. -/
  finish : List (Point d α) → Point d α → ℕ → List ℕ → List (Neighbor α)
  /-- Insertion, at the graph's caps: the next point, its top layer, and its candidates per
  layer. -/
  insert : HNSW d α → Point d α → ℕ → List Candidates → HNSW d α
  /-- The design's invariants. -/
  Valid : HNSW d α → Prop

/-- Promise: on a beam of stored nodes, each once, up to `k` of its points, nearest first, each
a stored point measured exactly. -/
def Ops.AnswersFromBeam (o : Ops d α) : Prop :=
  ∀ pts (q : Point d α) k beam, beam.Nodup → (∀ i ∈ beam, i < pts.length) →
    Promise pts q k beam (o.finish pts q k beam)

/-- Not in the box: insertion stores the point and keeps caps and `Valid`; picking, invariant 2. -/
def Ops.KeepsInvariants (o : Ops d α) : Prop :=
  (∀ g p top cands, (o.insert g p top cands).points = g.points ++ [p]) ∧  -- the point stored
  (∀ g p top cands,
    (o.insert g p top cands).m = g.m ∧ (o.insert g p top cands).m0 = g.m0) ∧  -- the caps kept
  (∀ m m0, o.Valid (empty m m0 : HNSW d α)) ∧                      -- an empty graph is valid
  (∀ g p top cands, g.m ≤ g.m0 → o.Valid g → CandidatesOk g top cands →
    o.Valid (o.insert g p top cands)) ∧                            -- insertion keeps it, m ≤ m0
  (∀ g, Builds o.insert g → g.m ≤ g.m0 → o.Valid g) ∧              -- every graph built is valid
  ∀ m (base : Point d α) cs, cs.Pairwise (fun a b => sqDist base a ≤ sqDist base b) →
    PicksDiverse ⟨m, base, cs, o.select m base cs⟩      -- invariant 2, candidates nearest first

/-- **Proved:** the search's walk. On a valid graph, the search for the `k` nearest to
`q` with a beam of width `ef` answers what the last step, `finish`, answers on some beam of
stored nodes, each once; the beam is not empty when `k` is positive and the graph has nodes, and
it holds at most `max ef k` nodes: whatever path the walk takes, it ends with the step
`Contract.promise` is about. The library's search, `HNSW.search`, meets it: `searchSpec`. `Ops`
names no search, so `Contract` does not include it. -/
def SearchSpec (o : Ops d α)
    (search : HNSW d α → Point d α → ℕ → ℕ → List (Neighbor α)) : Prop :=
  ∀ g q k ef, o.Valid g → ∃ beam : List ℕ, beam.Nodup ∧ (∀ i ∈ beam, i < g.size) ∧
    (0 < k → 0 < g.size → beam ≠ []) ∧ beam.length ≤ max ef k ∧
    search g q k ef = o.finish g.points q k beam

end Ring

/-- **The stored graph's invariant**, one piece per box line about it: `DegreeBounded` (1) and
`NestedLayers` (3); then `NoSelfLinks`, `NoRepeatedLinks`, `EntryOnTop` and `OneNodePerPoint`,
not in the box. Box invariant 2 is about the picking step, not the stored graph:
`Picking.Valid`. -/
def Valid (g : HNSW d α) : Prop :=
  DegreeBounded g ∧ NestedLayers g ∧ NoSelfLinks g ∧ NoRepeatedLinks g ∧ EntryOnTop g ∧
    OneNodePerPoint g

/-- **The graph index's contract**, the part of the design Lean checks, one field per box field
and one conjunct per box line. -/
structure Contract [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] (o : Ops d α) : Prop where
  -- Goal: answer "a place like this one" fast, at a recall you choose, among millions of places
  -- in hundreds of dimensions.
  /-- Promise: up to `k` stored points, nearest first, each measured exactly. -/
  promise :  -- they may not be the true nearest; recall, measured on the data, says how often
    o.AnswersFromBeam ∧  -- up to k stored points, nearest first, each measured exactly
    o.KeepsInvariants    -- not in the box: insertion stores and keeps `Valid`; picking, invariant 2
  -- Idea: link every new place to a few near neighbors that point in different directions, and
  -- link them back. Then walk, always stepping toward the query and keeping a short list of
  -- the best seen.
  /-- Invariants: the box's three, in box order, then pieces not in the box. -/
  invariants : ∀ g, o.Valid g ↔
    DegreeBounded g ∧    -- 1. every place has at most a fixed number of neighbors
    -- 2. a place picks its neighbors nearest first, skipping any candidate closer to one already
    --    picked: on a picking step, not the graph, `PicksDiverse`, in `KeepsInvariants`
    NestedLayers g ∧     -- 3. every place on a layer is on every layer below; a random few: tested
    NoSelfLinks g ∧      -- not in the box: no node is its own neighbor
    NoRepeatedLinks g ∧  -- not in the box: no list names a neighbor twice
    EntryOnTop g ∧       -- not in the box: the entry point is on the top layer
    OneNodePerPoint g    -- not in the box: one node per stored point
  /-- Cost: memory, a fixed number of links per place. -/
  cost :
    ∀ g, o.Valid g → LinksPerPlaceAtMost g  -- memory: links per place
    -- per query, a few neighbors' distances for each step of a short walk: measured on GloVe
  -- Assumes: that walking downhill through the neighbors leads to the nearest. On some data it
  -- stops at a point that is not, a wrong answer that recall measures.

end HNSW

end AlgoDesign.Geometry
