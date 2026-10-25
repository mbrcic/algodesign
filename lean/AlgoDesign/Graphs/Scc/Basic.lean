/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Decide

/-! # Strong components: member lists, postorder, the checker

What the library's answers carry beyond the grouping: member lists that agree with it, and each
group's members in postorder against a reference depth-first walk; and the chapter's checker for a
grouping computed elsewhere. -/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

open Digraph

/-- The member lists say what `groupOf` says: one list per group, no member twice, and each
vertex listed in its own group and nowhere else. -/
def MembersAgree (g : Digraph) (r : Components) : Prop :=
  r.groups.length = numGroups r.groupOf ∧
    (∀ i (hi : i < r.groups.length), r.groups[i].Nodup ∧
      ∀ v ∈ r.groups[i], v < g.n ∧ gid r.groupOf v = i) ∧
    ∀ v < g.n, v ∈ r.groups.getD (gid r.groupOf v) []

instance (g : Digraph) (r : Components) : Decidable (MembersAgree g r) := by
  unfold MembersAgree; infer_instance

/-! ## Postorder

The order vertices finish in one depth-first walk: roots `0` upward, each row walked in its order,
a vertex entered the first time an arrow (or the outer loop) meets it. Kosaraju–Sharir's first pass
is this walk, and Algorithm T walks the same way, so its members come out in this order. -/

/-- A depth-first walk with explicit frames: which vertices are entered, the frames (vertex, next
row position) with the current vertex on top, and the vertices in the order entered and finished. -/
structure Dfs where
  /-- Entered already. -/
  seen : ℕ → Bool
  /-- The frames, current one first. -/
  stack : List (ℕ × ℕ)
  /-- The vertices in the order they were entered. -/
  entered : List ℕ
  /-- The vertices in the order they finished. -/
  finished : List ℕ

namespace Dfs

/-- Nothing entered. -/
def init : Dfs := ⟨fun _ => false, [], [], []⟩

/-- One step: look at the current vertex's next arrow, entering its head if new; or, at the end of
the row, finish the vertex. -/
def step (rows : ℕ → List (ℕ × ℕ)) (s : Dfs) : Dfs :=
  match s.stack with
  | [] => s
  | (v, i) :: rest =>
    match (rows v)[i]? with
    | some (w, _) =>
      if s.seen w then { s with stack := (v, i + 1) :: rest }
      else
        { s with seen := Function.update s.seen w true, stack := (w, 0) :: (v, i + 1) :: rest
                 entered := s.entered ++ [w] }
    | none => { s with stack := rest, finished := s.finished ++ [v] }

/-- `fuel` steps. -/
def run (rows : ℕ → List (ℕ × ℕ)) : ℕ → Dfs → Dfs
  | 0, s => s
  | k + 1, s => run rows k (step rows s)

/-- A walk from `r` if `r` is new, for `fuel` steps. -/
def visit (rows : ℕ → List (ℕ × ℕ)) (fuel : ℕ) (s : Dfs) (r : ℕ) : Dfs :=
  if s.seen r then s
  else run rows fuel
    { s with seen := Function.update s.seen r true, stack := [(r, 0)], entered := s.entered ++ [r] }

end Dfs

/-- Enough steps for any one walk on `g`: each vertex is entered and finished once, and each
arrow looked at once. -/
def fuel (g : Digraph) : ℕ := 2 * g.n + g.arrows.length + 1

/-- **Postorder**: the vertices in the order they finish in the depth-first walk with roots `0`
upward. -/
def finishOrder (g : Digraph) : List ℕ :=
  ((List.range g.n).foldl (Dfs.visit g.out (fuel g)) Dfs.init).finished

/-- Each group's members are listed in postorder. -/
def MembersInPostorder (g : Digraph) (r : Components) : Prop :=
  ∀ m ∈ r.groups, m.Sublist (finishOrder g)

instance (g : Digraph) (r : Components) : Decidable (MembersInPostorder g r) := by
  unfold MembersInPostorder; infer_instance

/-! ## The checker

Three checks on a grouping it did not compute, in order; the first that fails is named. -/

/-- The checks, by name. -/
inductive Failure where
  /-- Some vertex has no group, or some id below the number of groups is unused. -/
  | partition
  /-- Some group is not strongly connected. -/
  | notStronglyConnected
  /-- The graph of groups, derived from the arrows, has a cycle. -/
  | quotientCycle
deriving DecidableEq, Repr

/-- Check 1: every vertex in exactly one group, ids `0 .. k - 1` all used. -/
def checkPartition (g : Digraph) (c : List ℕ) : Bool :=
  c.length == g.n && (List.range (numGroups c)).all fun i => i ∈ c

/-- Steps of `next` that stay inside group `i`. -/
def inside (c : List ℕ) (i : ℕ) (next : ℕ → List ℕ) (v : ℕ) : List ℕ :=
  (next v).filter fun w => gid c w = i

/-- Check 2: each group strongly connected. From its first member, a forward search on `out` and
a backward search on `into`, both staying inside the group, reach every member. -/
def checkStrong (g : Digraph) (c : List ℕ) : Bool :=
  (List.range (numGroups c)).all fun i =>
    let fwd := reachFrom g.n (inside c i (forward g)) (c.idxOf i)
    let bwd := reachFrom g.n (inside c i (backward g)) (c.idxOf i)
    (List.range g.n).all fun v => gid c v ≠ i || (v ∈ fwd && v ∈ bwd)

/-- Check 3: the graph of groups, derived from the original arrows, has no cycle: no arrow of it
from `a` to `b` has `a` reachable back from `b`. -/
def checkAcyclic (g : Digraph) (c : List ℕ) : Bool :=
  let q := quotient g c
  q.arrows.all fun a => a.1 ∉ reachFrom q.n (forward q) a.2

/-- **The checker**: `none` if all three checks pass, else the first that fails. -/
def check (g : Digraph) (c : List ℕ) : Option Failure :=
  if !checkPartition g c then some .partition
  else if !checkStrong g c then some .notStronglyConnected
  else if !checkAcyclic g c then some .quotientCycle
  else none

end AlgoDesign.Graphs.Scc
