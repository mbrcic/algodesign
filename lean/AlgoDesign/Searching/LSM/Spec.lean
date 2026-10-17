/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Order.Defs.LinearOrder

/-!
# LSM-tree: the specification

Sources: the Search chapter, "I'll pay it back later"; O'Neil, Cheng, Gawlick and O'Neil, *The
Log-Structured Merge-Tree (LSM-Tree)* [@oneil1996log].

> **Goal:** take writes as fast as they arrive, with every key still findable.
>
> **Promise:** a map. Write stores a key's value; delete removes it. A read gets the newest value
> written, or nothing if the key was never written or its newest write was a delete.
>
> **Idea:** pay in installments: store at once, and put off the sorting into merges.
>
> **Invariants:**
>
> 1. Every batch written to disk is sorted, and never changed afterwards.
> 2. Only a few batches pile up. Batches on disk sit in levels, each allowed several times the data
>    of the one above: the top level holds at most a set number of batches, each lower level at most
>    one, and each level stays within its size budget.
>
> **Cost:** a write is one insert in memory, rewritten several times on its way down; a read may
> check memory and every level.
>
> **Assumes:** merging keeps up with the writes. Otherwise unmerged batches pile up until new writes
> have to wait.

Words: a batch is a run; memory is the memtable; the top level is level 0.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`LSM.contract` proves the library's operations, `LSM.ops`, meet it.

- Goal [required] → write, delete and the counted read, each a field of `Ops`.
- Promise [proved] → `Contract`, one law per sentence of the box, read through `Store.get`; and,
  not in the box, every operation keeps the invariants, `Ops.KeepsInvariants`.
- Idea [mentioned] → `Store.write` sorts one entry into the memtable; the merges come later.
- Invariants [proved] → `Store.Valid`, one piece per box line: 1 `Store.RunsSorted`,
  2 `Store.FewBatches`; "never changed afterwards" by construction, a run is a value.
  Not in the box: `Store.RunsNonEmpty`, `Store.OldestRunClean`, `Store.ShapeUsable`, the last
  three conjuncts of `Store.Valid`.
- Cost [argued] → a read's runs proved; a write's rewrites argued, `WriteRewrites`.
- Assumes [mentioned] → merge rate against write rate, which Lean, with no time in its model,
  cannot state; the library merges inside the write that fills the memtable.

-/

@[expose] public section

namespace AlgoDesign.Searching

/-- One immutable batch of writes: each key with a live value or a tombstone (`none`), which
records a deletion and still shadows older runs. -/
abbrev Run (α β : Type) := List (α × Option β)

namespace Run

variable {α β : Type} [LinearOrder α]

/-- Keys strictly increasing within the run. -/
def Sorted (r : Run α β) : Prop := r.Pairwise (fun p q => p.1 < q.1)

/-- Look up `a` in one run: `none` if the run does not mention `a`, `some none` for a tombstone. -/
def lookup (a : α) : Run α β → Option (Option β)
  | [] => none
  | (k, v) :: rest => if k = a then some v else lookup a rest

/-- A run with no tombstone. -/
def Clean (r : Run α β) : Prop := ∀ p ∈ r, p.2 ≠ none

end Run

namespace LSM

variable {α β : Type} [LinearOrder α]

/-! ## The store -/

/-- The three numbers that decide the layering. -/
structure Shape where
  /-- How many entries the memtable holds before it is flushed. -/
  capacity : Nat
  /-- How much bigger each level may be than the one above it. -/
  ratio : Nat
  /-- How many sealed flushes level 0 holds before they are merged into level 1. -/
  level0Runs : Nat
deriving DecidableEq, Repr

/-- How many entries level `i` may hold before it is pushed down: `capacity · ratio ^ i`. -/
def Shape.budget (sh : Shape) (i : Nat) : Nat := sh.capacity * sh.ratio ^ i

/-- A usable shape: capacity at least 1, ratio at least 2, level 0 at least one run. -/
def Shape.Usable (sh : Shape) : Prop := 1 ≤ sh.capacity ∧ 2 ≤ sh.ratio ∧ 1 ≤ sh.level0Runs

/-- The library's store: the shape it was built at, the memtable, a sorted run of the newest
writes, and the levels, level 0 first, each a list of runs newest first. -/
structure Store (α β : Type) where
  /-- The three numbers that decide the layering, chosen when the store is made. -/
  shape : Shape
  /-- The newest writes, in key order, one entry per key. -/
  memtable : Run α β
  /-- Level 0 first; each level's runs newest first. -/
  levels : List (List (Run α β))

namespace Store

/-- The runs on disk, newest first: level 0's, then each deeper level's. -/
@[simp] abbrev diskRuns (s : Store α β) : List (Run α β) := s.levels.flatten

/-- The store's runs, newest first: the memtable, then the runs on disk. -/
def runs (s : Store α β) : List (Run α β) := s.memtable :: s.diskRuns

/-- **The box's promise**, the store's meaning: a read gets the newest value written, or nothing
if the key was never written or its newest write was a delete. The first run, newest first, that
mentions the key answers; a tombstone answers nothing. -/
def get (a : α) (s : Store α β) : Option β := (s.runs.findSome? (Run.lookup a)).join

/-- Level 0's runs, newest first. -/
@[simp] abbrev level0 (s : Store α β) : List (Run α β) := s.levels.headD []

/-- The levels below level 0, level 1 first. -/
@[simp] abbrev deeper (s : Store α β) : List (List (Run α β)) := s.levels.tail

/-- From level `i` down, every level but the deepest within its budget: its run holds at most
`budget i` entries. -/
def WithinBudgetFrom (sh : Shape) : Nat → List (List (Run α β)) → Prop
  | _, [] => True
  | _, [_] => True
  | i, l :: m :: rest =>
      (∀ r ∈ l.head?, r.length ≤ sh.budget i) ∧ WithinBudgetFrom sh (i + 1) (m :: rest)

/-- Box invariant 1: every batch written to disk is sorted, and never changed afterwards. The
memtable, the batch a flush writes, and every run on the levels sorted. "Never changed
afterwards" holds by construction: runs are values, and a merge writes a new run. -/
def RunsSorted (s : Store α β) : Prop :=
  Run.Sorted s.memtable ∧ ∀ r ∈ s.diskRuns, Run.Sorted r

/-- Box invariant 2, first half: the top level holds at most a set number of batches, each lower
level at most one. Level 0 holds at most `level0Runs` runs, every deeper level at most one. -/
def FewRuns (s : Store α β) : Prop :=
  (level0 s).length ≤ s.shape.level0Runs ∧ ∀ l ∈ deeper s, l.length ≤ 1

/-- Box invariant 2, second half: each level within its size budget. Every level from 1 down but
the deepest, which takes whatever is pushed into it. -/
def LevelsWithinBudget (s : Store α β) : Prop :=
  WithinBudgetFrom s.shape 1 (deeper s)

/-- Box invariant 2: only a few batches pile up. The top level holds at most a set number of
batches, each lower level at most one, and each level stays within its size budget. "Each allowed
several times the data of the one above" is the shape's: `Shape.Usable`. -/
def FewBatches (s : Store α β) : Prop := FewRuns s ∧ LevelsWithinBudget s

/-- Not in the box: no run on disk is empty. -/
def RunsNonEmpty (s : Store α β) : Prop := ∀ r ∈ s.diskRuns, r ≠ []

/-- Not in the box: the oldest run below level 0 holds no tombstone. -/
def OldestRunClean (s : Store α β) : Prop := ∀ r ∈ (deeper s).flatten.getLast?, Run.Clean r

/-- Not in the box: the store's shape is usable (`Shape.Usable`): the
memtable holds at least one entry, each level is at least twice the one above, and level 0 holds
at least one run. The cascade needs the first two to finish, and a full compaction the third to
leave its one run in level 0. -/
def ShapeUsable (s : Store α β) : Prop := s.shape.Usable

end Store

/-! ## The contract, the part Lean checks

The promise is a map, key to newest value, not the search tree's set, so the contract is the
LSM's own. `LSM.lean`, the file that imports the whole structure, proves the library's operations
meet it (`LSM.contract`). -/

open Cslib.Algorithms.Lean

/-- The operations the box speaks of: an empty store at a chosen shape, write, delete, the
invariant, and a read that counts the runs it checks. -/
structure Ops (α β : Type) [LinearOrder α] where
  /-- The empty store at a shape. -/
  empty : Shape → Store α β
  /-- Store a key's value. -/
  write : α → β → Store α β → Store α β
  /-- Remove a key. -/
  delete : α → Store α β → Store α β
  /-- The invariant. -/
  Valid : Store α β → Prop
  /-- Get, counting the runs it checks, the memtable among them. -/
  getM : α → Store α β → TimeM ℕ (Option β)
  /-- The counted read answers as `Store.get`, so the cost is of the read. -/
  counted : ∀ a s, (getM a s).ret = Store.get a s

/-- The key's newest value, or nothing, read by `Store.get`. -/
def Ops.get (_o : Ops α β) : α → Store α β → Option β := Store.get

/-- Promise: write stores a key's value; a read of any other key gets what it got. -/
def Ops.WriteStores (o : Ops α β) : Prop :=
  (∀ a b s, o.Valid s → o.get a (o.write a b s) = some b) ∧   -- write stores a key's value
  (∀ a b c s, o.Valid s → c ≠ a →
    o.get c (o.write a b s) = o.get c s)                      -- every other key as it was

/-- Promise: delete removes it; a read of any other key gets what it got. -/
def Ops.DeleteRemoves (o : Ops α β) : Prop :=
  (∀ a s, o.Valid s → o.get a (o.delete a s) = none) ∧        -- delete removes it
  (∀ a c s, o.Valid s → c ≠ a →
    o.get c (o.delete a s) = o.get c s)                       -- every other key as it was

/-- Promise: a read gets nothing if the key was never written. -/
def Ops.NeverWrittenIsNothing (o : Ops α β) : Prop :=
  ∀ sh a, o.get a (o.empty sh) = none                         -- never written: nothing

/-- Not in the box: every operation keeps the invariants. -/
def Ops.KeepsInvariants (o : Ops α β) : Prop :=
  (∀ sh, sh.Usable → o.Valid (o.empty sh)) ∧                 -- a valid empty store
  (∀ a b s, o.Valid s → o.Valid (o.write a b s)) ∧            -- write keeps the invariants
  (∀ a s, o.Valid s → o.Valid (o.delete a s))                 -- delete keeps them

/-- The store's invariant, one piece per box line: `RunsSorted` (1) and `FewBatches` (2); then
`RunsNonEmpty`, `OldestRunClean` and `ShapeUsable`, not in the box. The box's promise is
`get`'s meaning. -/
def Store.Valid (s : Store α β) : Prop :=
  RunsSorted s ∧ FewBatches s ∧ RunsNonEmpty s ∧ OldestRunClean s ∧ ShapeUsable s

/-- **The LSM's contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. The cost counts the runs the counting read counts itself. -/
structure Contract (o : Ops α β) : Prop where
  -- Goal: take writes as fast as they arrive, with every key still findable.
  /-- Promise: a map. -/
  promise :
    o.WriteStores ∧            -- write stores a key's value
    o.DeleteRemoves ∧          -- delete removes it
    o.NeverWrittenIsNothing ∧  -- nothing if the key was never written
    o.KeepsInvariants          -- not in the box: every operation keeps the invariants
  -- Idea: pay in installments: store at once, and put off the sorting into merges.
  /-- Invariants: the box's two, in box order. -/
  invariants : ∀ s, o.Valid s ↔
    Store.RunsSorted s ∧      -- 1. every batch on disk is sorted, never changed afterwards
    Store.FewBatches s ∧      -- 2. only a few batches pile up, each level within its budget
    Store.RunsNonEmpty s ∧    -- not in the box: no run on disk is empty
    Store.OldestRunClean s ∧  -- not in the box: the oldest run holds no tombstone
    Store.ShapeUsable s       -- not in the box: the shape is usable
  /-- Cost: a read may check memory and every level. -/
  cost :
    -- a read: the memtable, level 0's runs and one run per deeper level, counted in runs
    ∀ a s, o.Valid s → (o.getM a s).time ≤ 1 + s.shape.level0Runs + (Store.deeper s).length
    -- a write: one insert in memory, rewritten several times on its way down: argued,
    -- `WriteRewrites`, beside the read's cost
  -- Assumes: merging keeps up with the writes. Otherwise unmerged batches pile up until new writes
  -- have to wait.

end LSM

end AlgoDesign.Searching
