/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Digraph
public import Mathlib.Data.Finset.Basic

/-!
# The design project's contract: a dependency analyzer

Source: the Graphs chapter's design project. The box's top half is the problem, and it is fixed
before any candidate exists:

> **Goal:** tell a team, from its tasks and what each waits for, which tasks can start now, which
> will be able to later, and which never will.
>
> **Promise:** every task not yet done is in exactly one of four lists: ready now (everything it
> waits for is done); later (not ready now, and nothing before it is in a knot); in a knot (it
> waits on itself, directly or through other unfinished tasks); blocked (not in a knot, but it
> waits, through other unfinished tasks, on a task that is). Asked why a task is blocked, it gives
> a chain of real waits from a task in a knot to that task.
>
> **Cost:** time to produce the four lists, and memory, both measured on the bench.
>
> **Assumes:** about 100,000 tasks with a few prerequisites each. Which tasks are already done is
> part of the input.

The box, field by field. `Contract`, last in this file, is the part Lean checks.

- Goal [mentioned] → the four lists, read off what the candidate builds from the tasks.
- Promise [required] → `Contract.promise`, one part per clause: `Ops.EachOnce`, `Ops.ReadyNow`,
  `Ops.LaterOnes`, `Ops.Knotted`, `Ops.BlockedOnes`, `Ops.Explains`.
  Not in the box: `Ops.buildValid`, and `Ops.Explains`'s nothing for a task not blocked.
- Idea [none] → the box has none: the candidate's own.
- Invariants [none] → the box has none: the candidate's own `Ops.Valid`.
- Cost [measured] → time and memory, measured by the bench.
- Assumes [measured] → the workload, in the bench; not stated here.

Words: an arrow `(a, b)` means `a` before `b`, so `b` waits for `a`; the tasks are the vertices
`0 … n - 1`; the tasks not in `done` are unfinished, and only arrows between two unfinished tasks
still hold anyone up.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Workbench

open Digraph

/-- The arrows still holding anyone up: those between two unfinished tasks. -/
def pending (g : Digraph) (done : Finset ℕ) : Digraph :=
  ⟨g.n, g.arrows.filter fun a => a.1 ∉ done ∧ a.2 ∉ done⟩

/-- A task not yet done. -/
def Unfinished (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop := v < g.n ∧ v ∉ done

/-- **Ready now**: unfinished, and everything it waits for is done. -/
def Ready (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop :=
  Unfinished g done v ∧ ∀ a, g.Arrow a v → a ∈ done

/-- **In a knot**: unfinished, and it waits on itself, directly or through other unfinished
tasks. -/
def InKnot (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop :=
  Unfinished g done v ∧ ∃ w, (pending g done).Arrow w v ∧ (pending g done).Reaches v w

/-- **Later**: unfinished, not ready now, and nothing before it is in a knot. -/
def Later (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop :=
  Unfinished g done v ∧ ¬ Ready g done v ∧
    ∀ k, (pending g done).Reaches k v → ¬ InKnot g done k

/-- **Blocked**: not in a knot, but it waits, through other unfinished tasks, on a task that
is. -/
def Blocked (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop :=
  Unfinished g done v ∧ ¬ InKnot g done v ∧
    ∃ k, InKnot g done k ∧ (pending g done).Reaches k v

/-- **A chain of real waits** from a task in a knot to `v`: it starts in a knot, ends at `v`, and
each step is an arrow between two unfinished tasks. -/
def WaitChain (g : Digraph) (done : Finset ℕ) (v : ℕ) (p : List ℕ) : Prop :=
  (∃ k, p.head? = some k ∧ InKnot g done k) ∧ p.getLast? = some v ∧
    p.IsChain (pending g done).Arrow

/-- A candidate design: what it builds from the tasks, the arrows and the tasks already done; the
four lists it reads off; its answer to "why is this task blocked?"; and the invariants it claims
(`Valid`). -/
structure Ops (S : Type) where
  /-- What the candidate builds from the tasks and the tasks already done. -/
  build : Digraph → Finset ℕ → S
  /-- The tasks that can start now. -/
  ready : S → List ℕ
  /-- The tasks that will be able to start later. -/
  later : S → List ℕ
  /-- The tasks in a knot. -/
  knot : S → List ℕ
  /-- The tasks blocked behind a knot. -/
  blocked : S → List ℕ
  /-- Why a task is blocked: a chain of waits, or nothing. -/
  why : S → ℕ → Option (List ℕ)
  /-- The candidate's invariants: the bottom half of its box. Lean checks only that `Valid` holds;
  whether it says anything is for the reader and the bench: `fun _ => True` would pass. -/
  Valid : S → Prop
  /-- The candidate's own invariants hold of everything it builds. -/
  buildValid : ∀ g done, g.WellFormed → Valid (build g done)

variable {S : Type}

/-- Promise: every task not yet done is in exactly one of the four lists, and no list holds
anything else. -/
def Ops.EachOnce (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed →
    let all := o.ready (o.build g done) ++ o.later (o.build g done) ++
      o.knot (o.build g done) ++ o.blocked (o.build g done)
    (∀ v, Unfinished g done v → all.count v = 1) ∧  -- each unfinished task once
    ∀ v ∈ all, Unfinished g done v                   -- nothing else

/-- Promise: ready now, everything it waits for is done. -/
def Ops.ReadyNow (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed → ∀ v, v ∈ o.ready (o.build g done) ↔ Ready g done v

/-- Promise: later, not ready now, and nothing before it is in a knot. -/
def Ops.LaterOnes (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed → ∀ v, v ∈ o.later (o.build g done) ↔ Later g done v

/-- Promise: in a knot, it waits on itself, directly or through other unfinished tasks. -/
def Ops.Knotted (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed → ∀ v, v ∈ o.knot (o.build g done) ↔ InKnot g done v

/-- Promise: blocked, not in a knot, but it waits, through other unfinished tasks, on a task that
is. -/
def Ops.BlockedOnes (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed → ∀ v, v ∈ o.blocked (o.build g done) ↔ Blocked g done v

/-- Promise: asked why a task is blocked, it gives a chain of real waits from a task in a knot to
that task. Not in the box: asked about any other task, nothing, so a candidate never offers a chain
where none exists. -/
def Ops.Explains (o : Ops S) : Prop :=
  ∀ g done, g.WellFormed → ∀ v,
    (Blocked g done v → ∃ p, o.why (o.build g done) v = some p ∧ WaitChain g done v p) ∧
    (¬ Blocked g done v → o.why (o.build g done) v = none)

/-- **The design project's contract**, the part of it Lean checks; the box quoted at the top of
this file says how each claim is checked. It is the box's top half, which the human wrote: every
candidate owes all of it. The bottom half (idea, invariants) is the candidate's: its own `Valid`,
which must hold of everything it builds. Cost is not here: it is measured on the bench. -/
structure Contract (o : Ops S) : Prop where
  -- Goal: tell a team, from its tasks and what each waits for, which tasks can start now, which
  -- will be able to later, and which never will.
  /-- Promise: four lists, each unfinished task in one, and why a task is blocked. -/
  promise :
    o.EachOnce ∧         -- every task not yet done is in exactly one of four lists
    o.ReadyNow ∧         -- ready now: everything it waits for is done
    o.LaterOnes ∧        -- later: not ready now, and nothing before it is in a knot
    o.Knotted ∧          -- in a knot: it waits on itself, directly or through others
    o.BlockedOnes ∧      -- blocked: not in a knot, but waits on a task that is
    o.Explains           -- why blocked: a chain of real waits from a knot; else nothing
  -- Idea: none in the box; the candidate's own.
  -- Invariants: none in the box; the candidate's own `Valid`.
  -- Cost: time to produce the four lists, and memory, measured by the bench, not stated here.
  -- Assumes: about 100,000 tasks with a few prerequisites each. Which tasks are already done is
  -- part of the input.

end AlgoDesign.Graphs.Workbench
