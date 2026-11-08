/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Nearest
public import Cslib.Algorithms.Lean.TimeM

/-!
# The design project's contract: an index for "places like this one"

Source: the Geometry chapter's design project, "design an index for 'places like this one' that
computes at most half the scan's distances while keeping recall@10 ≥ 0.9 under a memory cap". The
box's top half is the problem, and it is fixed before any candidate exists. In the chapter the
reader writes this top half; the one below is the bench's:

> **Goal:** find the places most like this one among many, without measuring them all.
>
> **Promise:** up to ten stored places, each once, nearest first, each with its exact distance;
> at least nine in ten of the true ten nearest, on places nobody tuned for.
>
> **Cost:** distances and inner products computed per query, at most half the scan's one per
> stored place; memory within a cap.
>
> **Assumes:** places in a hundred dimensions that lie near a few directions, in clusters, some
> crowded and some sparse; the cap as many numbers as the stored coordinates.

The box, field by field. `Contract`, last in this file, is the part Lean checks; the scan, the
plainest candidate, meets it (`reference_contract`).

- Goal [mentioned] → the places most like this one, without measuring them all: `Ops`'s build and
  query.
- Promise [measured] → "up to ten stored places, each once, nearest first, each with its exact
  distance" [required]: `Contract.promise`, in two parts, `Ops.UpToKStoredOnce` and
  `Ops.NearestFirstExact`, on every list of points the index is built from. "At least nine in
  ten of the true ten nearest" [measured]: `recallAt`, held by the bench on places nobody tuned
  for.
- Idea [none] → the box has none: the candidate's own.
- Invariants [none] → the box has none: the candidate's own.
- Cost [measured] → distances and inner products per query, and memory, counted by the bench
  through accessors the candidate does not control.
- Assumes [measured] → the bench's two corpus families, clustered and skewed, and its cap, not
  stated here.

An answer is a list of `Neighbor`s: each a squared distance and the id of a stored
point, its number in the input, counting from 0. Ids, not points, so that "each once" means each
stored place once, even when two places are equal.
-/

@[expose] public section

namespace AlgoDesign.Geometry.Workbench

open Cslib.Algorithms.Lean

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- An answer: points, each a squared distance from the query and an id. That the ids are stored
ones is the promise `Stored`. -/
abbrev Answer (α : Type) := List (Neighbor α)

/-- Promise: at most `k` points answered. -/
def UpToK (k : ℕ) (ans : Answer α) : Prop := ans.length ≤ k

/-- Promise: every point answered is a stored one. -/
def Stored (ps : List (Point d α)) (ans : Answer α) : Prop :=
  ∀ a ∈ ans, a.id < ps.length

/-- Promise: each point answered once. -/
def EachOnce (ans : Answer α) : Prop := (ans.map Neighbor.id).Nodup

/-- Promise: nearest first, the distances never decreasing. -/
def NearestFirst (ans : Answer α) : Prop := (ans.map Neighbor.sqDist).Pairwise (· ≤ ·)

/-- Promise: each distance answered is the point's exact squared distance from the query, the
point a stored one. With `UpToK`, `EachOnce` and `NearestFirst`, the form of the answer LSH's
`MeasuredExactly` and the graph index's `Promise` also ask. -/
def ExactDistance (ps : List (Point d α)) (q : Point d α) (ans : Answer α) : Prop :=
  ∀ a ∈ ans, ∃ h : a.id < ps.length, a.sqDist = sqDist ps[a.id] q

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, its promise in two
parts. `Workbench.lean` proves the scan meets it (`reference_contract`). -/

/-- The operations the box speaks of, on a candidate's states `S`: build over a list of points,
then ask for the `k` nearest to a query; and the query counted, a tick per distance computed. -/
structure Ops (d : ℕ) (α S : Type) where
  /-- Build the index over the points, each with its id, its number counting from 0. -/
  build : List (Point d α) → S
  /-- The `k` nearest the index finds to a query. -/
  query : ℕ → Point d α → S → Answer α
  /-- The query, counting one tick per distance it computes. -/
  queryM : ℕ → Point d α → S → TimeM ℕ (Answer α)
  /-- The counted query answers as the query does, so the cost is of the query. -/
  counted : ∀ k q s, (queryM k q s).ret = query k q s

variable {S : Type}

/-- Promise: up to `k` stored places, each once, on every list of points the index is built
from. -/
def Ops.UpToKStoredOnce (o : Ops d α S) : Prop :=
  (∀ ps k q, UpToK k (o.query k q (o.build ps))) ∧    -- up to k
  (∀ ps k q, Stored ps (o.query k q (o.build ps))) ∧  -- stored places
  (∀ ps k q, EachOnce (o.query k q (o.build ps)))     -- each once

/-- Promise: nearest first, each with its exact distance, on every list of points the index is
built from. -/
def Ops.NearestFirstExact (o : Ops d α S) : Prop :=
  (∀ ps k q, NearestFirst (o.query k q (o.build ps))) ∧       -- nearest first
  (∀ ps k q, ExactDistance ps q (o.query k q (o.build ps)))  -- each with its exact distance

/-- **The design project's contract**, the part of it Lean checks: on every list of points, for
every `k` and query, the answer holds at most `k` stored points, each once, nearest first, each
with its exact squared distance. Recall and cost are not here: they are measured on the bench,
outside the candidate's control. -/
structure Contract (o : Ops d α S) : Prop where
  -- Goal: find the places most like this one among many, without measuring them all.
  /-- Promise: up to `k` stored places, each once, nearest first, exact; recall is measured. -/
  promise :
    o.UpToKStoredOnce ∧  -- up to k stored places, each once
    o.NearestFirstExact  -- nearest first, each with its exact distance
  -- Idea: none in the box; the candidate's own.
  -- Invariants: none in the box; the candidate's own.
  -- Cost: distances and inner products computed per query, at most half the scan's one per
  -- stored place; memory within a cap. Measured by the bench, not stated here.
  -- Assumes: places in a hundred dimensions that lie near a few directions, in clusters, some
  -- crowded and some sparse; the cap as many numbers as the stored coordinates.

end AlgoDesign.Geometry.Workbench
