/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.Range
public import Mathlib.Logic.Relation
public import Cslib.Init
public import Cslib.Algorithms.Lean.TimeM

/-!
# Union-find: the specification

Sources: the Graphs chapter, "Merges"; Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms* (4th ed.), §19.3, `FIND-SET` (p. 530); Weiss, *Data Structures and Algorithm Analysis
in C++* (4th ed.), §8.5, `unionSets` (Fig. 8.14, p. 359) for the union: both roots found first,
no merge when they are the same, and on equal ranks the second root goes under the first.

> **Goal:** Answer "are these two joined yet?" while links keep arriving.
>
> **Promise:** Items start alone. A merge joins exactly the two groups it names, and a lookup
> changes no group. Two items get the same lookup answer exactly when they are in the same group.
> The structure also counts the groups.
>
> **Idea:** Union by rank and path compression. Each group is a tree whose root stands for it. A
> merge hangs the lower-ranked root under the other, and a lookup points everything it walked
> through straight at the root.
>
> **Invariants:**
>
> 1. Following parents up from any item ends at its group's root.
> 2. Ranks rise toward the root, and a root of rank $r$ has at least $2^r$ items.
>
> **Cost:** A lookup walks at most $\log_2 n$ links, and over a long run each operation costs nearly
> a constant.
>
> **Assumes:** The items are known in advance, and groups only merge. A removed link still counts as
> joined.

The box, field by field. `Contract`, last in this file, is the part Lean checks;
`UnionFind.contract` proves the library's operations, `ops`, meet it.

- Goal [required] → the question "are these two joined yet?", `joined`, a field of `Ops`.
- Promise [proved] → four parts: `Ops.StartsAlone`, `Ops.MergeJoins`, `Ops.LookupTells`,
  `Ops.CountsGroups`. Which item stands for a group is not promised. Not in the box:
  `Ops.keeps` and `Ops.keepsWellFormed`, every operation keeping `Valid` and `WellFormed`;
  `Ops.emptyValid` and `Ops.emptyWellFormed`, the start valid and well formed; `Ops.keepsItems`,
  every operation keeping the items.
- Idea [mentioned] → the lower-ranked root under the other, on equal ranks the second under the
  first, is `union`; a lookup pointing its walk at the root is in `FindSpec`, what `find` owes,
  outside the contract.
- Invariants [proved] → `Valid`:
  1 [proved] `UpwardEndsAtRoot`.
  2 [proved] `RanksRiseUpward` and `RootRankBoundsSize`, a root's items being those in its tree;
  no tree deeper than log₂ of its size.
  Not in the box: `WellFormed`, which the operations keep together with `Valid`; its one piece
  is `CountIsRoots`, the group count the promise reports.
- Cost [argued] → `Ops.Within`: a lookup walks at most `log₂ n` links, proved, counting links;
  a long run costs nearly a constant per operation, argued: Tarjan, JACM 22 (1975); CLRS 4th ed.,
  §19.4, Theorem 19.14.
- Assumes [mentioned] → the items are fixed by `init n`; no operation splits a group.
-/

@[expose] public section

namespace AlgoDesign.Graphs

/-- A union-find over the items `0, …, n - 1`: each item's parent (a root is its own parent), each
item's rank, and the number of groups. Entries at `n` and beyond are never read. -/
structure UnionFind where
  /-- The number of items, fixed at the start. -/
  n : ℕ
  /-- The link upward from each item; a root links to itself. -/
  parent : ℕ → ℕ
  /-- Each item's rank. -/
  rank : ℕ → ℕ
  /-- The number of groups. -/
  count : ℕ

namespace UnionFind

/-- Is `r` a root, its own parent? -/
def IsRoot (u : UnionFind) (r : ℕ) : Prop := u.parent r = r

/-- Where following the links upward from `i` leads after `n` steps: the root of `i`'s group, on
a valid structure, since no path upward is that long and a root links to itself. -/
def root (u : UnionFind) (i : ℕ) : ℕ := u.parent^[u.n] i

/-- Are `i` and `j` in one group? -/
def Same (u : UnionFind) (i j : ℕ) : Prop := u.root i = u.root j

/-- Box invariant 1: following parents up from any item ends at its group's root. Every
link stays among the items, and `n` steps up reach an item that is its own parent. -/
def UpwardEndsAtRoot (u : UnionFind) : Prop :=
  ∀ i < u.n, u.parent i < u.n ∧ u.IsRoot (u.root i)

/-- Box invariant 2, first half: ranks rise toward the root. An item that is not a root has a
smaller rank than its parent. -/
def RanksRiseUpward (u : UnionFind) : Prop :=
  ∀ i < u.n, u.parent i ≠ i → u.rank i < u.rank (u.parent i)

/-- Box invariant 2, second half: a root of rank `r` has at least `2 ^ r` items, those in its
tree. -/
def RootRankBoundsSize (u : UnionFind) : Prop :=
  ∀ r < u.n, u.IsRoot r → 2 ^ u.rank r ≤ (List.range u.n).countP (fun i => u.root i = r)

/-- The group count is the number of roots, which the promise's group count reads. -/
def CountIsRoots (u : UnionFind) : Prop :=
  u.count = (List.range u.n).countP (fun r => u.parent r = r)

/-- **A well-formed union-find**: the condition the representation needs beyond the box, which the
operations keep together with `Valid`. -/
def WellFormed (u : UnionFind) : Prop :=
  CountIsRoots u

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per box field
and one conjunct per box line. `UnionFind.lean`, the file that imports the whole structure, proves
the library's operations meet it (`UnionFind.contract`). -/

open Cslib.Algorithms.Lean

/-- The operations the box speaks of, the design's invariants, and a lookup that counts the links
it walks. -/
structure Ops where
  /-- Every item alone. -/
  init : ℕ → UnionFind
  /-- Lookup: the structure after it, and the answer. -/
  find : UnionFind → ℕ → UnionFind × ℕ
  /-- Merge: the structure after it, and whether two groups became one. -/
  union : UnionFind → ℕ → ℕ → UnionFind × Bool
  /-- "Are these two joined yet?": the structure after it, and the answer. -/
  joined : UnionFind → ℕ → ℕ → UnionFind × Bool
  /-- The number of groups. -/
  count : UnionFind → ℕ
  /-- The design's invariants. -/
  Valid : UnionFind → Prop
  /-- Lookup, counting the links walked. -/
  findM : UnionFind → ℕ → TimeM ℕ (UnionFind × ℕ)
  /-- The counted lookup answers as the lookup does, so the cost is of the lookup. -/
  counted : ∀ u x, (findM u x).ret = find u x
  /-- The start is legal. -/
  emptyValid : ∀ n, Valid (init n)
  /-- The start is well formed. -/
  emptyWellFormed : ∀ n, WellFormed (init n)
  /-- A merge, a lookup and the question keep the invariants. -/
  keeps : ∀ u, Valid u → WellFormed u → ∀ x < u.n, ∀ y < u.n,
    Valid (union u x y).1 ∧ Valid (find u x).1 ∧ Valid (joined u x y).1
  /-- A merge, a lookup and the question keep the structure well formed. -/
  keepsWellFormed : ∀ u, Valid u → WellFormed u → ∀ x < u.n, ∀ y < u.n,
    WellFormed (union u x y).1 ∧ WellFormed (find u x).1 ∧ WellFormed (joined u x y).1
  /-- A merge, a lookup and the question keep the items. -/
  keepsItems : ∀ u, Valid u → WellFormed u → ∀ x < u.n, ∀ y < u.n,
    (union u x y).1.n = u.n ∧ (find u x).1.n = u.n ∧ (joined u x y).1.n = u.n

/-! ## The promise, piece by piece -/

/-- **It starts with every item alone**: the items are `0, …, n - 1`, each its own root. -/
def Ops.StartsAlone (o : Ops) : Prop :=
  ∀ n, (o.init n).n = n ∧ ∀ i < n, (o.init n).IsRoot i

/-- **A merge joins exactly the two named groups and changes no other; two items already together
merge nothing**, and the answer says whether two groups became one. -/
def Ops.MergeJoins (o : Ops) : Prop :=
  ∀ u, o.Valid u → WellFormed u → ∀ x < u.n, ∀ y < u.n,
    (∀ i < u.n, ∀ j < u.n, ((o.union u x y).1.Same i j ↔
      u.Same i j ∨ (u.Same i x ∧ u.Same j y) ∨ (u.Same i y ∧ u.Same j x))) ∧
    ((o.union u x y).2 = true ↔ ¬ u.Same x y)

/-- **Two items give the same lookup answer exactly when they are in one group, and a lookup never
changes who is together.** So "are these two joined yet?" answers yes exactly when the two are in
one group, and asking changes no one's group. -/
def Ops.LookupTells (o : Ops) : Prop :=
  ∀ u, o.Valid u → WellFormed u → ∀ x < u.n, ∀ y < u.n,
    ((o.find u x).2 = (o.find u y).2 ↔ u.Same x y) ∧
    (∀ i < u.n, ∀ j < u.n, (o.find u x).1.Same i j ↔ u.Same i j) ∧
    ((o.joined u x y).2 = true ↔ u.Same x y) ∧
    ∀ i < u.n, ∀ j < u.n, (o.joined u x y).1.Same i j ↔ u.Same i j

/-- **It reports the number of groups**: one per root. -/
def Ops.CountsGroups (o : Ops) : Prop :=
  ∀ u, o.Valid u → WellFormed u → o.count u = (List.range u.n).countP fun r => u.parent r = r

/-! ## The cost -/

/-- **A lookup walks at most `bound n` links**: the counted lookup takes at most `bound n` steps,
one per link walked up, on every valid, well-formed structure of `n` items. -/
def Ops.Within (o : Ops) (counted : UnionFind → ℕ → TimeM ℕ (UnionFind × ℕ)) (bound : ℕ → ℕ) :
    Prop :=
  ∀ u, o.Valid u → WellFormed u → ∀ x < u.n, (counted u x).time ≤ bound u.n

/-- **A legal union-find**: box invariants 1 and 2. -/
def Valid (u : UnionFind) : Prop :=
  UpwardEndsAtRoot u ∧ RanksRiseUpward u ∧ RootRankBoundsSize u

/-- **The union-find's contract**, the part of the design Lean checks, one field per box field and
one conjunct per box line. The cost counts the links a lookup walks up; the repointing is free. -/
structure Contract (o : Ops) : Prop where
  -- Goal: Answer "are these two joined yet?" while links keep arriving.
  /-- Promise: every item alone at first; merges join groups; lookups tell; the count. -/
  promise :
    o.StartsAlone ∧     -- it starts with every item alone
    o.MergeJoins ∧      -- a merge joins exactly the two named groups and changes no other
    o.LookupTells ∧     -- two items give the same lookup answer exactly when in one group
    o.CountsGroups      -- it also reports the number of groups
  -- Idea: Union by rank and path compression. Each group is a tree whose root stands for it. A
  -- merge hangs the lower-ranked root under the other, and a lookup points everything it walked
  -- through straight at the root.
  /-- Invariants: the box's lines 1 and 2. -/
  invariants : ∀ u, o.Valid u ↔
    UpwardEndsAtRoot u ∧     -- 1. following parents up from any item ends at its group's root
    RanksRiseUpward u ∧      -- 2. ranks rise toward the root,
    RootRankBoundsSize u     --    and a root of rank r has at least 2^r items (in its tree)
  /-- Cost: a lookup walks at most `log₂ n` links. -/
  cost : o.Within o.findM Nat.log2  -- a lookup walks at most log₂ n links
    -- a long run nearly a constant per operation, `O(m α(n))`: argued, Cormen, Leiserson, Rivest
    -- and Stein, §19.4, Theorem 19.14
  -- Assumes: The items are known in advance, and groups only merge. A removed link still counts
  -- as joined.

end UnionFind

end AlgoDesign.Graphs
