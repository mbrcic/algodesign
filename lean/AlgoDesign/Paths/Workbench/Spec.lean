/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation

/-!
# The design project's contract: a trip planner with a battery

Source: the Paths chapter's design project. The box's top half is the problem, and it is fixed
before any candidate exists:

> **Goal:** Give a delivery rider the quickest trip from one place to another on a battery bike, a
> trip that never runs the battery flat.
>
> **Promise:** If some trip from the start to the goal never takes the battery below empty, it
> gives one, as the places in order with the charging stops, and no such trip is quicker. A trip
> may arrive with the battery at empty. If there is none, it says so.
>
> **Cost:** time to answer one trip, counted as every street and every socket it looks at, read
> from the town or from anything the planner keeps of the town, and memory, both measured on the
> bench. What the bench cannot count is checked by reading the code.
>
> **Assumes:** a town of about 10,000 places and 30,000 one-way streets, at most one from one place
> to another. The battery has up to 100 levels and starts full. Each street costs minutes (never
> below nothing) and energy (below nothing downhill). A ride that would charge past full ends at
> full. A socket adds one level for a fixed number of minutes.

The box, field by field. `Contract`, last in this file, is the part Lean checks.

- Goal [mentioned] → the trip `Ops.plan` gives from the start to the goal.
- Promise [required] → `Contract.promise`, three parts: `Ops.RealTrip`, a trip it gives is one;
  `Ops.NoneQuicker`, no such trip is quicker; `Ops.SaysNone`, it gives one exactly when there is
  one. "It gives one" is the half of `Ops.SaysNone`'s ↔ from left to right, and "if there is
  none, it says so" the half from right to left.
  Not in the box: `Town.WellFormed`'s other two pieces (every street joins two places of the
  town, every socket is at one), and `Ops.buildValid`.
- Idea [none] → the box has none: the candidate's own.
- Invariants [none] → the box has none: the candidate's own `Ops.Valid`.
- Cost [measured] → time to answer one trip, counted as every street and every socket it looks
  at, read from the town or from anything the planner keeps of the town, and memory, both
  measured on the bench; what the bench cannot count is checked by reading the code.
- Assumes [measured] → the town's size and the battery's levels, in the bench; not stated here.
  At most one street from one place to another is `Town.WellFormed`'s second piece, a hypothesis
  of every promise part, so the places in order name the streets. The rest is in the
  definitions: a street's minutes are a natural number, so never negative; its energy an
  integer, negative downhill; a ride and a charge end at most at full (`Town.next`); a
  charging stop adds one level for `Town.chargeMinutes` (`Town.next`, `Town.stepMinutes`); a trip
  starts full (`Town.startAt`).

Words: the places are `0 … places - 1`; the battery's levels run from `0`, empty, to `full`. A
trip is its steps, each a ride along the street to a place or a charging stop, and the level
after each step follows from them (`Town.passes`). Running flat is a level below empty; a level
of exactly empty is not flat. The level is read where each step ends.
-/

@[expose] public section

namespace AlgoDesign.Paths.Workbench

/-- A one-way street: the place it leaves, the place it leads to, its minutes and its energy. -/
structure Street where
  /-- The place the street leaves. -/
  source : ℕ
  /-- The place the street leads to. -/
  target : ℕ
  /-- The minutes the ride takes. -/
  minutes : ℕ
  /-- The battery levels the ride takes; negative downhill, where the ride charges. -/
  energy : ℤ
deriving DecidableEq, Repr

/-- A town: its places, its streets, the places with a socket, the battery's full level, and the
minutes a socket takes to add one level. -/
structure Town where
  /-- The number of places, `0 … places - 1`. -/
  places : ℕ
  /-- The one-way streets. -/
  streets : List Street
  /-- The places with a socket. -/
  sockets : List ℕ
  /-- The battery's full level; empty is `0`. -/
  full : ℕ
  /-- The minutes a socket takes to add one level. -/
  chargeMinutes : ℕ
deriving DecidableEq, Repr

/-- A step of a trip: a ride along the street to a place, or a charging stop at a socket. -/
inductive Step where
  /-- Ride along the street to this place. -/
  | ride (place : ℕ)
  /-- Stop and charge one level at the socket where the bike stands. -/
  | charge
deriving DecidableEq, Repr

/-- Where the bike stands, and its battery level; a level below `0` has run flat. -/
structure State where
  /-- The place. -/
  place : ℕ
  /-- The battery level. -/
  level : ℤ
deriving DecidableEq, Repr

namespace Town

variable (T : Town)

/-- Every street joins two places of the town, at most one street leads from one place to
another, and every socket is at a place of the town. -/
def WellFormed : Prop :=
  (∀ s ∈ T.streets, s.source < T.places ∧ s.target < T.places) ∧
    (T.streets.map fun s => (s.source, s.target)).Nodup ∧
    ∀ p ∈ T.sockets, p < T.places

/-- The street from `p` to `q`, if the town has one. -/
def street (p q : ℕ) : Option Street :=
  T.streets.find? fun s => s.source = p ∧ s.target = q

/-- One step from `x`. A ride along the street to a place takes the street's energy, and a ride
that would charge past full ends at full. A charging stop at a socket adds one level, and at full
stays full. `none` when there is no such street, or no socket where the bike stands. -/
def next (x : State) : Step → Option State
  | .ride q => (T.street x.place q).map fun s => ⟨q, min T.full (x.level - s.energy)⟩
  | .charge => if x.place ∈ T.sockets then some ⟨x.place, min T.full (x.level + 1)⟩ else none

/-- The minutes one step from `x` takes: its street's, or a socket's. -/
def stepMinutes (x : State) : Step → ℕ
  | .ride q => ((T.street x.place q).map Street.minutes).getD 0
  | .charge => T.chargeMinutes

/-- The states a trip passes from `x`: `x`, then the state after each step; `none` when a step
cannot be taken. -/
def passes (x : State) : List Step → Option (List State)
  | [] => some [x]
  | st :: r => (T.next x st).bind fun y => (passes y r).map (x :: ·)

/-- The minutes a trip from `x` takes: its steps' minutes, added up. -/
def minutesFrom (x : State) : List Step → ℕ
  | [] => 0
  | st :: r => T.stepMinutes x st + ((T.next x st).map fun y => minutesFrom y r).getD 0

/-- A trip starts at its start place with the battery full. -/
def startAt (s : ℕ) : State := ⟨s, T.full⟩

/-- **A trip from `s` to `g`**: every ride is along a street of the town, every charging stop is
at a socket, and the last place is `g`. -/
def IsTrip (s g : ℕ) (t : List Step) : Prop :=
  ∃ xs ∈ T.passes (T.startAt s) t, xs.getLast?.map State.place = some g

/-- **It never runs the battery flat**: after every step the level is not below empty. -/
def NeverFlat (s : ℕ) (t : List Step) : Prop :=
  ∀ xs ∈ T.passes (T.startAt s) t, ∀ x ∈ xs, 0 ≤ x.level

/-- **Its minutes**: the minutes of every ride and every charging stop, added up. -/
def tripMinutes (s : ℕ) (t : List Step) : ℕ := T.minutesFrom (T.startAt s) t

end Town

/-- A candidate design: what it builds from the town, the trip it gives from a start to a goal or
nothing, and the invariants it claims (`Valid`). -/
structure Ops (S : Type) where
  /-- What the candidate builds from the town. -/
  build : Town → S
  /-- The trip it gives from the start to the goal, as its steps, or nothing. -/
  plan : S → ℕ → ℕ → Option (List Step)
  /-- The candidate's invariants, the bottom half of its box; `fun _ => True` would pass. -/
  Valid : S → Prop
  /-- The candidate's own invariants hold of everything it builds. -/
  buildValid : ∀ T, T.WellFormed → Valid (build T)

variable {S : Type}

/-- Promise: a trip it gives goes from the start to the goal and never runs the battery flat. -/
def Ops.RealTrip (o : Ops S) : Prop :=
  ∀ T, T.WellFormed → ∀ s g, s < T.places → g < T.places → ∀ t,
    o.plan (o.build T) s g = some t → T.IsTrip s g t ∧ T.NeverFlat s t

/-- Promise: no trip from the start to the goal that never runs the battery flat is quicker than
the one it gives. -/
def Ops.NoneQuicker (o : Ops S) : Prop :=
  ∀ T, T.WellFormed → ∀ s g, s < T.places → g < T.places → ∀ t,
    o.plan (o.build T) s g = some t →
      ∀ u, T.IsTrip s g u → T.NeverFlat s u → T.tripMinutes s t ≤ T.tripMinutes s u

/-- Promise: it says there is none exactly when no trip from the start to the goal never runs the
battery flat. -/
def Ops.SaysNone (o : Ops S) : Prop :=
  ∀ T, T.WellFormed → ∀ s g, s < T.places → g < T.places →
    (o.plan (o.build T) s g = none ↔ ¬ ∃ t, T.IsTrip s g t ∧ T.NeverFlat s t)

/-- **The design project's contract**, the part of it Lean checks; the box quoted at the top of
this file says how each claim is checked. It is the box's top half, which the human wrote: every
candidate owes all of it. The bottom half (idea, invariants) is the candidate's: its own `Valid`,
which must hold of everything it builds. Cost is not here: it is measured on the bench. -/
structure Contract (o : Ops S) : Prop where
  -- Goal: Give a delivery rider the quickest trip from one place to another on a battery bike, a
  -- trip that never runs the battery flat.
  /-- Promise: a real trip that never runs flat, none quicker; none exactly when there is none. -/
  promise :
    o.RealTrip ∧     -- a trip it gives goes to the goal, never flat; arriving at empty is not flat
    o.NoneQuicker ∧  -- and no such trip is quicker
    o.SaysNone       -- it gives one exactly when one exists
  -- Idea: none in the box; the candidate's own.
  -- Invariants: none in the box; the candidate's own `Valid`.
  -- Cost: time to answer one trip, counted as every street and every socket it looks at, read
  -- from the town or from anything the planner keeps of the town, and memory, measured by the
  -- bench, not stated here. What the bench cannot count is checked by reading the code.
  -- Assumes: a town of about 10,000 places and 30,000 one-way streets, at most one from one place
  -- to another. The battery has up to 100 levels and starts full. Each street costs minutes (never
  -- below nothing) and energy (below nothing downhill). A ride that would charge past full ends at
  -- full. A socket adds one level for a fixed number of minutes.

end AlgoDesign.Paths.Workbench
