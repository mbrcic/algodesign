/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Reach

/-!
# Bridges, cut vertices and blocks: the specification

Sources: the Graphs chapter, "Single failures"; Drozdek, *Data Structures and Algorithms in C++*
(4th ed.), §8.6.1, pp. 416–418, the walk with an edge stack; Hopcroft and Tarjan, *Efficient
algorithms for graph manipulation*, CACM 16 (1973); Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms* (4th ed.), Problem 20-2, p. 583; Diestel, *Graph Theory* (5th ed.),
§3.1, pp. 64–66, the block-cut forest.

> **Goal:** Find every link and every vertex whose failure alone splits a network, and which of them
> stand between any two vertices.
>
> **Promise:** A link or vertex is reported exactly when its failure alone splits the network. For
> any two connected vertices, the answer lists exactly the vertices that stand between them.
>
> **Idea:** DFS timestamps and low-link, on links that go both ways. If the part of the walk below a
> vertex has no way back above it, the vertex separates that part from the rest. With no way back
> even to the vertex, the link to that part is a bridge.
>
> **Invariants:**
>
> 1. A finished vertex's climb-back number is the earliest entry number the part of the walk below
>    it can reach, without the link it arrived by.
> 2. The link stack holds the explored links whose block has not come off yet, and every block that
>    has come off is whole.
>
> **Cost:** One look at every vertex and every link.
>
> **Assumes:** Only one link or vertex fails at a time. Two failures can split a network that this
> reports as having no weak point.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Blocks.contract` proves the library's operations, `ops`, meet it.

- Goal [required] → the walk's report, `blocks`, and the separators, `separators`, fields of
  `Ops`.
- Promise [proved] → two parts: (a) `Ops.ReportsFailures`, read by deletion (`IsBridge`,
  `IsCutVertex`); (b) `Ops.ListsSeparators` (`Separates`), a vertex standing between two others
  read as its failure alone cutting them apart.
- Idea [mentioned] → the bridge test, the cut test and the root rule (the vertex where the walk
  starts separates only when the walk goes down from it more than once) are proved of the finished
  walk, outside the contract; the walk itself executes them.
- Invariants [proved] → `Valid` on the walk state, one piece per box line:
  1 `ClimbBackIsEarliest`, 2 `StackHoldsOpenLinks`.
  Not in the box: the invariants hold along the walk, `Ops.stepKeeps`; the walk starts from its
  graph and keeps it, `Ops.carries` and `Ops.keepsGraph`, and the report is read off it,
  `Ops.walks`; a doubled link is two links with one pair of ends, a cycle of two, so never a
  bridge, and a loop is in no block (`SameBlock`, the book's extension of blocks to doubled
  links); the reported blocks are the network's, `BlocksAgree`, outside the contract.
- Cost [mentioned] → `Ops.OneLookEach`: the walk is over within `2 n + 2 m` steps, proved; a
  step's time, mentioned.
- Assumes [mentioned] → one failure at a time: the definitions delete one link or one vertex.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

open Relation

/-! ## Pieces

Whether two vertices are in one piece is decided by a search: on a well-formed graph, by sweeps over
the vertices `0 .. n - 1` (`Scc.mem_reachFrom_iff`); otherwise by the search over every vertex a
link touches, on the links read both ways. -/

/-- **The number of pieces**: each piece counted at its smallest vertex, the vertex in one piece
with no smaller vertex. -/
def pieces (g : Graph) : ℕ :=
  ((List.range g.n).filter fun v => decide (∀ u < v, ¬ g.Connected u v)).length

/-! ## Deleting a link, a vertex -/

/-- The graph without link `e`; the links after it move down one id, which no piece notices. -/
def deleteLink (g : Graph) (e : ℕ) : Graph := ⟨g.n, g.links.eraseIdx e⟩

/-- The graph with vertex `w`'s links deleted: `w` is left alone, a piece of its own. -/
def isolate (g : Graph) (w : ℕ) : Graph := ⟨g.n, g.links.filter fun l => l.1 ≠ w ∧ l.2 ≠ w⟩

/-- **A bridge**: deleting link `e` leaves more pieces. -/
def IsBridge (g : Graph) (e : ℕ) : Prop := e < g.links.length ∧ pieces g < pieces (deleteLink g e)

/-- **A cut vertex**: deleting vertex `v` with its links leaves more pieces among the other
vertices. `isolate g v` keeps `v` as a piece of its own, so the other vertices make one piece
fewer. -/
def IsCutVertex (g : Graph) (v : ℕ) : Prop := v < g.n ∧ pieces g < pieces (isolate g v) - 1

/-- **`w` separates `u` from `v`**: `w` is neither of them, `u` and `v` are in one piece, and they
are not once `w` and its links are deleted. -/
def Separates (g : Graph) (w u v : ℕ) : Prop :=
  w ≠ u ∧ w ≠ v ∧ g.Connected u v ∧ ¬ (isolate g w).Connected u v

/-! ## Cycles and blocks -/

/-- Link `i` joins `a` and `b`, either way round. -/
def Joins (g : Graph) (i a b : ℕ) : Prop := g.links[i]? = some (a, b) ∨ g.links[i]? = some (b, a)

/-- Link `i` is not a loop: its two ends differ. -/
def NonLoop (g : Graph) (i : ℕ) : Prop := ∃ l ∈ g.links[i]?, l.1 ≠ l.2

/-- A walk from `x` given by its steps, each a link and the vertex it leads to. -/
def Trail (g : Graph) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | x, (f, y) :: rest => Joins g f x y ∧ Trail g y rest

/-- Where the steps from `x` end. -/
def endOf (x : ℕ) (steps : List (ℕ × ℕ)) : ℕ := (x :: steps.map Prod.snd).getLast (by simp)

/-- **A cycle through `e` holding `f`**: `e` joins `a` to a different vertex `b`, and a path leads
from `b` back to `a` through distinct vertices, without `e`, using `f`. -/
def OnCycleWith (g : Graph) (e f : ℕ) : Prop :=
  ∃ a b, g.links[e]? = some (a, b) ∧ a ≠ b ∧ ∃ steps, Trail g b steps ∧
    (b :: steps.map Prod.snd).Nodup ∧ endOf b steps = a ∧ e ∉ steps.map Prod.fst ∧
    f ∈ steps.map Prod.fst

/-- **One block**: two links that are not loops, the same or on one cycle through distinct
vertices. -/
def SameBlock (g : Graph) (e f : ℕ) : Prop :=
  NonLoop g e ∧ NonLoop g f ∧ (e = f ∨ OnCycleWith g e f)

/-- **An isolated vertex**: every link at it is a loop. It is a block of its own, with no
links. -/
def IsolatedVertex (g : Graph) (v : ℕ) : Prop :=
  v < g.n ∧ ∀ l ∈ g.links, (l.1 = v ∨ l.2 = v) → l.1 = l.2

/-! ## The answer -/

/-- What the walk reports. -/
structure Report where
  /-- The bridges' link ids, increasing. -/
  bridges : List ℕ
  /-- The cut vertices, increasing. -/
  cutVertices : List ℕ
  /-- Each link's block, `none` for a loop. -/
  blockOfLink : List (Option ℕ)
  /-- Each block's links, in the order the edge stack gave them up. -/
  blocks : List (List ℕ)
  /-- Each block's vertices, increasing. -/
  blockVertices : List (List ℕ)
deriving DecidableEq, Repr

/-! ## The walk's state

What the invariants read: the graph walked, the walk's own fields, and four it carries only for
them. The walk itself, its start and its step, comes with the walk's procedure. -/

/-- A frame of the walk's path. -/
structure Frame where
  /-- The vertex. -/
  vertex : ℕ
  /-- The link it was entered by; `none` for a root. -/
  arrival : Option ℕ
  /-- The next position in its row. -/
  pos : ℕ
deriving DecidableEq, Repr

/-- **The walk**: the graph walked, its own fields, then four it carries for its invariants. -/
structure Walk where
  /-- The graph being walked. -/
  g : Graph
  /-- The number of vertices entered so far. -/
  time : ℕ
  /-- Each vertex's entry number, from 1; `0` if not entered. -/
  entry : ℕ → ℕ
  /-- Each vertex's climb-back number. -/
  low : ℕ → ℕ
  /-- The frames of the current path, the current vertex first. -/
  path : List Frame
  /-- The edge stack, top first. -/
  edges : List ℕ
  /-- The cut vertices found. -/
  cut : ℕ → Bool
  /-- The bridges, in the order found. -/
  bridges : List ℕ
  /-- The blocks emitted, each with its links in the order popped. -/
  blocks : List (List ℕ)
  /-- Each emitted block's vertices, increasing. -/
  vertices : List (List ℕ)
  /-- The current root's children. -/
  children : ℕ
  /-- The outer loop's next root. -/
  next : ℕ
  /-- The link each vertex was entered by; `none` for a root or a vertex not entered. Read only by
  the invariants. -/
  arrival : ℕ → Option ℕ
  /-- The vertex each vertex was entered from. Read only by the invariants. -/
  up : ℕ → ℕ
  /-- Whether each vertex has finished. Read only by the invariants. -/
  finished : ℕ → Bool
  /-- How many entries of each vertex's row the walk has taken. Read only by the invariants. -/
  taken : ℕ → ℕ

/-- What a walk has found, as the answer reports it: bridges and cut vertices increasing, each
link's block (`none` for a loop), the blocks in the order emitted with their vertices. -/
def report (g : Graph) (w : Walk) : Report :=
  ⟨(List.range g.links.length).filter (· ∈ w.bridges), (List.range g.n).filter w.cut,
    (List.range g.links.length).map fun i => w.blocks.findIdx? (i ∈ ·), w.blocks, w.vertices⟩

namespace Walk

variable {g : Graph}

/-- The entries of `x`'s row the walk has taken. -/
def looked (w : Walk) (x : ℕ) : List (ℕ × ℕ) := (g.adj x).take (w.taken x)

/-- `x` and the vertices above it in the walk's tree, at most `k + 1` of them. -/
def chain (w : Walk) : ℕ → ℕ → List ℕ
  | 0, x => [x]
  | k + 1, x => x :: match w.arrival x with
    | some _ => chain w k (w.up x)
    | none => []

/-- **`v`'s explored subtree** holds `x`: `x` is `v`, or `x` lies under a finished child of
`v`. -/
def Explored (w : Walk) (v x : ℕ) : Prop :=
  x = v ∨ ∃ y ∈ chain w g.n x, w.finished y ∧ w.arrival y ≠ none ∧ w.up y = v

instance (w : Walk) (v x : ℕ) : Decidable (Explored (g := g) w v x) := by
  unfold Explored; infer_instance

/-- The earliest entry number `v`'s explored subtree reaches by one taken row entry, never the
link the vertex taking it arrived by; at most `v`'s own entry number. -/
def climb (w : Walk) (v : ℕ) : ℕ :=
  ((List.range g.n).filter fun x => decide (Explored (g := g) w v x)).foldr
    (fun x m => ((looked (g := g) w x).filter fun s => w.arrival x ≠ some s.2).foldr
      (fun s m => min (w.entry s.1) m) m)
    (w.entry v)

/-- A link the walk has taken from one of its ends, not a loop. -/
def Taken (w : Walk) (f : ℕ) : Prop :=
  NonLoop g f ∧ ∃ x < g.n, ∃ s ∈ looked (g := g) w x, s.2 = f

end Walk

/-- The walk has finished: no path, and the outer loop past every vertex. -/
def Done {g : Graph} (w : Walk) : Prop := w.path = [] ∧ w.next = g.n

/-! ## The invariants, on the walk's state -/

section Pieces

open Walk

/-- Box invariant 1: a finished vertex's climb-back number is the earliest entry number the part
of the walk below it can reach, without the link it arrived by. The formal statement holds for
every entered vertex, with the part below it taken as the vertex and its finished children's
parts, which is the whole part once the vertex finishes. It also adds how that
part reaches: through tree links and at most one link that is not on the walk's path, never the
very link the vertex arrived by. So it is narrower than the box line read literally: what the
part reaches through two or more links off the path does not count. -/
def ClimbBackIsEarliest (w : Walk) : Prop :=
  ∀ v < w.g.n, w.entry v ≠ 0 → w.low v = climb (g := w.g) w v

/-- Box invariant 2: the link stack holds the explored links whose block has not come off yet,
and every block that has come off is whole. The formal statement adds that the stack holds exactly
those links, each once; that whole means a whole block of the network; and that a finished block
without links is an isolated vertex. -/
def StackHoldsOpenLinks (w : Walk) : Prop :=
  w.edges.Nodup ∧
  (∀ f < w.g.links.length, f ∈ w.edges ↔ Taken (g := w.g) w f ∧ f ∉ w.blocks.flatten) ∧
  (∀ b ∈ w.blocks, ∀ e ∈ b, ∀ f < w.g.links.length, f ∈ b ↔ SameBlock w.g e f) ∧
  ∀ k < w.blocks.length, w.blocks.getD k [] = [] →
    (w.vertices.getD k []).length = 1 ∧ ∀ v ∈ w.vertices.getD k [], IsolatedVertex w.g v

end Pieces

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, in the box's shape: the
promise in a few named pieces, each spelled out below, the invariants, the cost. -/

/-- The operations the box speaks of: the walk's start and step, the report read off the walk,
and the separators of two vertices. -/
structure Ops where
  /-- The walk's start. -/
  start : Graph → Walk
  /-- One step of the walk. -/
  step : Graph → Walk → Walk
  /-- The walk: bridges, cut vertices and blocks. -/
  blocks : Graph → Report
  /-- The separators of two vertices, read off the block-cut forest; `none` across pieces. -/
  separators : Graph → ℕ → ℕ → Option (List ℕ)
  /-- The design's invariants, on the walk's state. -/
  Valid : Walk → Prop
  /-- The report is read off the state the walk reaches in `2 n + 2 m` steps, so the invariants
  and the cost are of the walk that answers. -/
  walks : ∀ g, blocks g = report g ((step g)^[2 * g.n + 2 * g.links.length] (start g))
  /-- The start carries the graph it is given. -/
  carries : ∀ g, (start g).g = g
  /-- A step keeps the walk's graph. -/
  keepsGraph : ∀ g w, (step g w).g = w.g
  /-- Every state of the walk on a well-formed graph keeps the invariants. -/
  stepKeeps : ∀ g : Graph, g.WellFormed → ∀ k, Valid ((step g)^[k] (start g))

/-! ## The promise, piece by piece -/

/-- **(a) A link or a vertex is reported exactly when removing it alone leaves more pieces.** -/
def Ops.ReportsFailures (o : Ops) : Prop :=
  ∀ g : Graph, g.WellFormed →
    (∀ e, e ∈ (o.blocks g).bridges ↔ IsBridge g e) ∧
    ∀ v, v ∈ (o.blocks g).cutVertices ↔ IsCutVertex g v

/-- **(b) For two vertices in one piece, the cut vertices on their path in the block-cut forest
are exactly the vertices whose failure alone separates them.** Not in the box: two vertices in
different pieces get `none`. -/
def Ops.ListsSeparators (o : Ops) : Prop :=
  ∀ g : Graph, g.WellFormed → ∀ u < g.n, ∀ v < g.n,
    (g.Connected u v → ∃ l, o.separators g u v = some l ∧ ∀ w, w ∈ l ↔ Separates g w u v) ∧
    (¬ g.Connected u v → o.separators g u v = none)

/-! ## The cost -/

/-- **One look at every vertex and every link**: the walk is over within `2 n + 2 m` steps, each
vertex passed and finished once, each row entry looked at once. -/
def Ops.OneLookEach (o : Ops) : Prop :=
  ∀ g : Graph, g.WellFormed →
    Done (g := g) ((o.step g)^[2 * g.n + 2 * g.links.length] (o.start g))

/-- **A legal walk**: the box's two invariants. -/
def Valid (w : Walk) : Prop :=
  ClimbBackIsEarliest w ∧ StackHoldsOpenLinks w

/-- **The single failures' contract**, the part of the design Lean checks, one field per box
field. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Find every link and every vertex whose failure alone splits a network, and which of
  -- them stand between any two vertices.
  /-- Promise: (a) every single failure that splits, (b) the separators of two vertices. -/
  promise :
    o.ReportsFailures ∧  -- (a) a link or vertex reported exactly when removing it alone splits
    o.ListsSeparators    -- (b) cut vertices on the forest path: exactly those that alone separate
  -- Idea: DFS timestamps and low-link, on links that go both ways. If the part of the walk below a
  -- vertex has no way back above it, the vertex separates that part from the rest. With no way
  -- back even to the vertex, the link to that part is a bridge.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ w, o.Valid w ↔
    ClimbBackIsEarliest w ∧  -- 1. each climb-back number is the earliest the part below can reach
    StackHoldsOpenLinks w    -- 2. the stack holds the open links; every block come off is whole
  /-- Cost: one look at every vertex and link. -/
  cost : o.OneLookEach  -- one look at every vertex and every link
    -- the time of a step [mentioned]
  -- Assumes: Only one link or vertex fails at a time. Two failures can split a network that this
  -- reports as having no weak point.

end AlgoDesign.Graphs.Blocks
