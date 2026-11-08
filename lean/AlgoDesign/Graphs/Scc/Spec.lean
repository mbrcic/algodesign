/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Reach

/-!
# Strong components: the specification

Sources: the Graphs chapter, "Knots"; Tarjan and Zwick, *Finding strong components using
depth-first search*, European Journal of Combinatorics 119 (2024), arXiv 2201.07197v3: Algorithm
T (Fig. 2, p. 12), Lemmas 3.1–3.9 (pp. 6–9), the condensation (§3.3, p. 10), Implementation V
(§6.1, p. 20); Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §20.5,
p. 577, for Kosaraju–Sharir.

> **Goal:** Find the groups of vertices that all reach each other, and the order between the groups.
>
> **Promise:** Every vertex is in exactly one group, and two vertices share a group exactly when
> each reaches the other. A vertex reaches another exactly when its group reaches the other's group,
> and the graph of groups has no cycle.
>
> **Idea:** DFS timestamps and low-link. One depth-first walk numbers the vertices as it meets them.
> A vertex that cannot get back to anyone met before it leads a group, and its group comes out
> together.
>
> **Invariants:**
>
> 1. The open list holds the finished vertices whose group has not come out yet.
> 2. Each vertex's climb-back number is an entry number it can get back to within its group.
> 3. Every group that has come out is whole.
>
> **Cost:** One look at every vertex and every arrow, and a few numbers per vertex.
>
> **Assumes:** The arrows do not change during the walk. If they do, the groups can be wrong.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`Scc.contract` proves the library's operations, `ops`, meet it.

- Goal [required] → the groups, `Ops.components`, and the order between them, `Ops.condenses`.
- Promise [proved] → three parts: `Ops.Groups`, `Ops.GroupsReach`, `Ops.GroupsAcyclic`.
- Idea [mentioned] → `algorithmT` walks Fig. 2 as Implementation V, with p. 12's stop when done
  (proved to take out one whole group, `AlgorithmT.Inv.mem_stopGroup_iff`); the group a leader
  takes out is the leader with every vertex still on the open list that the walk met after it;
  groups come out sinks first and are numbered `k - 1 - e`, so the ids are topological; each
  shrinks to one vertex in the condensation.
- Invariants [proved] → `Valid` on the walk state, one piece per box line:
  1 `FollowersInFinishOrder`, 2 `ClimbBackIsEarliest`, 3 `DoneIffGroupOut`, from Tarjan and
  Zwick's Fig. 2 and Lemmas 3.8 and 3.9.
  Not in the box: the invariants hold along the walk, `Ops.stepKeeps`; the walk starts from its
  graph and keeps it, `Ops.carries` and `Ops.keepsGraph`, and the components are read off it,
  `Ops.walks`, one member list per group, `Ops.lists`; the checker, `check`, and
  Kosaraju–Sharir, `kosarajuSharir` [argued], outside the contract.
- Cost [mentioned] → `Ops.OneLookEach`: the walk is over within `3 n + m` steps, proved; the time
  of a step and the few numbers per vertex, mentioned.
- Assumes [mentioned] → a `Digraph` is a value, so nothing changes it during a walk.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

open Digraph

/-! ## Groups -/

/-- The group of vertex `v`, read off a list of groups by vertex. -/
def gid (c : List ℕ) (v : ℕ) : ℕ := c.getD v 0

/-- The number of groups a list of groups by vertex uses: one more than its largest id. -/
def numGroups (c : List ℕ) : ℕ := c.foldr (fun i k => max (i + 1) k) 0

/-- **A partition into numbered groups**: one group id per vertex, and every id below the number
of groups used by some vertex, so the ids are `0 .. k - 1`. -/
def IsPartition (g : Digraph) (c : List ℕ) : Prop :=
  c.length = g.n ∧ ∀ i < numGroups c, i ∈ c

/-- **The strong components**: a partition in which two vertices share a group exactly when each
reaches the other. -/
def IsSccPartition (g : Digraph) (c : List ℕ) : Prop :=
  IsPartition g c ∧ ∀ u < g.n, ∀ v < g.n, (gid c u = gid c v ↔ Mutual g u v)

/-- The arrows between different groups, each read as an arrow between their groups, duplicates
kept. -/
def quotientArrows (g : Digraph) (c : List ℕ) : List (ℕ × ℕ) :=
  (g.arrows.filter fun a => gid c a.1 ≠ gid c a.2).map fun a => (gid c a.1, gid c a.2)

/-- **The graph of groups**, derived from the original arrows: one vertex per group, an arrow
between two different groups whenever some arrow joins their members, each such arrow once. It
is computed from the graph and the grouping, never supplied. -/
def quotient (g : Digraph) (c : List ℕ) : Digraph := ⟨numGroups c, (quotientArrows g c).dedup⟩

/-- The graph of groups has no cycle: no arrow of it can be followed back. -/
def QuotientAcyclic (g : Digraph) (c : List ℕ) : Prop :=
  ∀ a ∈ (quotient g c).arrows, ¬ (quotient g c).Reaches a.2 a.1

/-- **Ids in topological order**: every arrow of the graph of groups goes from a smaller id to a
larger one. -/
def IdsTopological (g : Digraph) (c : List ℕ) : Prop :=
  ∀ a ∈ (quotient g c).arrows, a.1 < a.2

/-! ## The answer: groups by vertex, and members by group -/

/-- The strong components as the library answers them: each vertex's group, and each group's
members, groups in id order. -/
structure Components where
  /-- The group of each vertex. -/
  groupOf : List ℕ
  /-- The members of each group, groups in id order. -/
  groups : List (List ℕ)
deriving DecidableEq, Repr

/-! ## Algorithm T's walk state

What the invariants read: the graph walked, the walk's own fields, and three it carries only for
them. The walk itself, its start and its step, comes with Algorithm T. -/

/-- **Algorithm T's walk**: the graph walked, the walk's own fields, then three it carries for its
invariants. -/
structure Walk where
  /-- The graph being walked. -/
  g : Digraph
  /-- The number of vertices entered so far. -/
  time : ℕ
  /-- Each vertex's low value: `0` unvisited, then its climb-back number, then `done` once its
  group is out. -/
  low : ℕ → ℕ
  /-- Whether a vertex may still lead its group: true on entry, false once its low value falls. -/
  lead : ℕ → Bool
  /-- The frames of the current path, (vertex, next row position), the current vertex first. -/
  path : List (ℕ × ℕ)
  /-- The followers stack `F`, top first; the guard is at the bottom. -/
  followers : List ℕ
  /-- The groups emitted so far, in emission order, each with its members in postorder. -/
  groups : List (List ℕ)
  /-- The emission index of each vertex's group, once it is out. -/
  emitted : ℕ → ℕ
  /-- The outer loop's next root. -/
  next : ℕ
  /-- Each vertex's entry number, from 1; `0` if not entered. Read only by the invariants. -/
  pre : ℕ → ℕ
  /-- The vertices in the order they finished. Read only by the invariants. -/
  finished : List ℕ
  /-- The arrows the walk has come back over, in order, as (from, to). Read only by the
  invariants. -/
  retreats : List (ℕ × ℕ)

namespace AlgorithmT

variable (g : Digraph)

/-- The value marking a vertex done: above every entry number. -/
def done : ℕ := g.n + 1

/-- The guard at the bottom of `F`: a vertex that is never entered, so its low value stays `0`
and the popping loop stops on it. -/
def guard : ℕ := g.n

/-- **The answer a walk gives**: group ids `k - 1 - e` for the group emitted `e`-th of `k`,
members in postorder, groups listed in id order. -/
def read (w : Walk) : Components :=
  ⟨(List.range g.n).map fun v => w.groups.length - 1 - w.emitted v, w.groups.reverse⟩

variable {g}

/-- The leader of `v`'s strong component, its first-entered member, has finished. -/
def LeaderOut (w : Walk) (v : ℕ) : Prop :=
  ∃ u < g.n, Mutual g u v ∧ u ∈ w.finished ∧ ∀ x < g.n, Mutual g x v → w.pre x = 0 ∨
    w.pre u ≤ w.pre x

/-- The least entry number reachable from `v` along the paths `retreatReach` collects. -/
def climbBack (w : Walk) (v : ℕ) : ℕ :=
  ((retreatReach g w.retreats w.retreats.length).getD v []).foldr
    (fun x m => min (w.pre x) m) (w.pre v)

end AlgorithmT

/-- **The walk is over**: no current vertex, and the outer loop has passed every vertex. -/
def Over (g : Digraph) (w : Walk) : Prop := w.path = [] ∧ g.n ≤ w.next

/-! ## The invariants, on the walk's state -/

section Pieces

open AlgorithmT

/-- Box invariant 1: the open list holds the finished vertices whose group has not come out
yet. The formal statement adds that it holds exactly those, in the order they finished. On the
walk's state (Fig. 2's postvisit, p. 12): `F`, above the guard, holds exactly the finished vertices
whose group is not yet out, most recently finished on top. -/
def FollowersInFinishOrder (w : Walk) : Prop :=
  w.followers = (w.finished.filter fun v => v ∉ w.groups.flatten).reverse ++ [guard w.g]

/-- Box invariant 2: each vertex's climb-back number is an entry number it can get back to within
its group. The formal statement says the number is the earliest such one, which is stronger than
the box line. It reads only arrows the walk has already come back over, and only from the
vertex's entry until its leader finishes. On the
walk's state (Lemma 3.8, p. 8): from its entry until its leader finishes, a vertex's low value is
the least entry number it reaches along a retreating path inside its strong component, every arrow
of which the walk has come back over. That is narrower still: each arrow of the path must have
been come back over after every arrow ahead of it on the path (p. 7); along arrows come back over
in another order, a vertex can sometimes get back further than its low value. -/
def ClimbBackIsEarliest (w : Walk) : Prop :=
  ∀ v < w.g.n, w.pre v ≠ 0 → ¬ LeaderOut (g := w.g) w v → w.low v = climbBack (g := w.g) w v

/-- Box invariant 3: every group that has come out is whole. The formal statement adds that a
vertex is marked out exactly when its group is out. On the walk's state (Lemma 3.9, p. 9): a vertex
is marked out (its low value `done`) exactly when the leader of its strong component has finished,
which is exactly when its group is out; and each group out is a whole strong component. -/
def DoneIffGroupOut (w : Walk) : Prop :=
  (∀ v < w.g.n, (w.low v = done w.g ↔ LeaderOut (g := w.g) w v) ∧
    (v ∈ w.groups.flatten ↔ LeaderOut (g := w.g) w v)) ∧
  ∀ m ∈ w.groups, ∀ u ∈ m, ∀ x < w.g.n, (x ∈ m ↔ Mutual w.g x u)

end Pieces

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, in the box's shape: the
promise in a few named pieces, each spelled out below, the invariants, the cost. -/

/-- The operations the box speaks of: Algorithm T's start and step, the strong components read
off the walk, and the graph of groups. -/
structure Ops where
  /-- The walk's start. -/
  start : Digraph → Walk
  /-- One step of the walk. -/
  step : Digraph → Walk → Walk
  /-- The strong components of a graph. -/
  components : Digraph → Components
  /-- The graph of groups, from a graph and its components. -/
  condensation : Digraph → Components → Digraph
  /-- The design's invariants, on the walk's state. -/
  Valid : Walk → Prop
  /-- The components are read off the state the walk reaches in `3 n + m` steps, so the
  invariants and the cost are of the walk that answers. -/
  walks : ∀ g, components g =
    AlgorithmT.read g ((step g)^[3 * g.n + g.arrows.length] (start g))
  /-- The start carries the graph it is given. -/
  carries : ∀ g, (start g).g = g
  /-- A step keeps the walk's graph. -/
  keepsGraph : ∀ g w, (step g w).g = w.g
  /-- Every state of the walk on a well-formed graph keeps the invariants. -/
  stepKeeps : ∀ g : Digraph, g.WellFormed → ∀ k, Valid ((step g)^[k] (start g))
  /-- One member list per group, and group `i`'s list holds, each once, exactly the vertices whose
  group is `i`. -/
  lists : ∀ g : Digraph, g.WellFormed →
    (components g).groups.length = numGroups (components g).groupOf ∧
    ∀ i (hi : i < (components g).groups.length), (components g).groups[i].Nodup ∧
      ∀ v, v ∈ (components g).groups[i] ↔ v < g.n ∧ gid (components g).groupOf v = i
  /-- The order between the groups, which the box's Goal asks for, owed beside the boxed Promise.
  The groups are numbered so that every arrow of the graph of groups goes from a smaller id to a
  larger one, and the condensation builds that graph from the original arrows between different
  groups, one vertex per group and each of its arrows once. -/
  condenses : ∀ g : Digraph, g.WellFormed →
    IdsTopological g (components g).groupOf ∧
    (condensation g (components g)).n = numGroups (components g).groupOf ∧
    (condensation g (components g)).arrows.Nodup ∧
    ∀ a, a ∈ (condensation g (components g)).arrows ↔
      a ∈ (quotient g (components g).groupOf).arrows

/-! ## The promise, piece by piece -/

/-- **Every vertex in exactly one group; two vertices share a group exactly when each reaches the
other.** -/
def Ops.Groups (o : Ops) : Prop :=
  ∀ g : Digraph, g.WellFormed → IsSccPartition g (o.components g).groupOf

/-- **One vertex reaches another exactly when its group reaches the other's group.** -/
def Ops.GroupsReach (o : Ops) : Prop :=
  ∀ g : Digraph, g.WellFormed → ∀ u < g.n, ∀ v < g.n,
    (g.Reaches u v ↔ (quotient g (o.components g).groupOf).Reaches
      (gid (o.components g).groupOf u) (gid (o.components g).groupOf v))

/-- **The graph of groups, built from the original arrows between different groups, has no
cycle.** -/
def Ops.GroupsAcyclic (o : Ops) : Prop :=
  ∀ g : Digraph, g.WellFormed → QuotientAcyclic g (o.components g).groupOf

/-! ## The cost -/

/-- **One look at every vertex and every arrow**: the walk is over within `3 n + m` steps, each
vertex entered, finished and passed once, each arrow looked at once. -/
def Ops.OneLookEach (o : Ops) : Prop :=
  ∀ g : Digraph, g.WellFormed → Over g ((o.step g)^[3 * g.n + g.arrows.length] (o.start g))

/-- **A legal walk**: the box's three invariants. -/
def Valid (w : Walk) : Prop :=
  FollowersInFinishOrder w ∧ ClimbBackIsEarliest w ∧ DoneIffGroupOut w

/-- **The strong components' contract**, the part of the design Lean checks, one field per box
field. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Find the groups of vertices that all reach each other, and the order between the
  -- groups.
  /-- Promise: the groups, their reach, the graph of groups without a cycle. -/
  promise :
    o.Groups ∧           -- one group per vertex; two share one exactly when each reaches the other
    o.GroupsReach ∧      -- one vertex reaches another exactly when its group reaches the other's
    o.GroupsAcyclic      -- the graph of groups, from the original arrows, has no cycle
  -- Idea: DFS timestamps and low-link. One depth-first walk numbers the vertices as it meets them.
  -- A vertex that cannot get back to anyone met before it leads a group, and its group comes out
  -- together.
  /-- Invariants: the box's three, in box order. -/
  invariants : ∀ w, o.Valid w ↔
    FollowersInFinishOrder w ∧  -- 1. the open list holds the finished vertices not yet out
    ClimbBackIsEarliest w ∧     -- 2. each climb-back number is the earliest it can get back to
    DoneIffGroupOut w           -- 3. every group that has come out is whole
  /-- Cost: one look at every vertex and arrow. -/
  cost : o.OneLookEach  -- one look at every vertex and every arrow
    -- a few numbers per vertex [mentioned]
  -- Assumes: The arrows do not change during the walk. If they do, the groups can be wrong.

end AlgoDesign.Graphs.Scc
