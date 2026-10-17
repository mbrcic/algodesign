/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Scan
public import Cslib.Algorithms.Lean.TimeM

/-!
# LSH: the specification

Sources: the Geometry chapter, LSH; Charikar, *Similarity Estimation Techniques from Rounding
Algorithms* (2002), §3 (SimHash); Datar, Immorlica, Indyk and Mirrokni, *Locality-Sensitive
Hashing Scheme Based on p-Stable Distributions* (2004), §3.2; Leskovec, Rajaraman and Ullman,
*Mining of Massive Datasets*, Ch. 3 (keys of several hash values, several tables).

> **Goal:** find a place like this one among millions, in hundreds of dimensions, without checking
> them all.
>
> **Promise:** the nearest of the candidates, measured exactly. Whatever the places, one at angle
> $\theta$ from you becomes a candidate with probability $1 - (1 - (1 - \theta/\pi)^K)^L$.
>
> **Idea:** hash so that near points tend to collide. A random cut through the origin gives one
> bit, which side you are on; several bits make a key; several tables give second chances.
>
> **Invariants:**
>
> 1. Every stored point sits in the bucket its key names, in every table.
> 2. A shared bucket only makes a point a candidate, and every candidate is measured exactly before
>    one is reported.
>
> **Cost:** per query, a key per table plus an exact distance per candidate; memory, one entry per
> point per table.
>
> **Assumes:** the cuts are drawn at random, independently of the places. If the true nearest
> collides in no table, the answer is a farther point, a wrong answer that recall measures.

Words: a place is a `Point`; a key is a table's hash of a point; a candidate is a stored point
sharing a bucket with the query in some table.

The box, field by field. `Contract`, last in this file, is the part Lean checks; `LSH.contract`
proves the library's operations, `LSH.ops`, meet it, for any hash family.

- Goal [measured] → a build over the points and the queries, each a field of `Ops`; "among
  millions, in hundreds of dimensions, without checking them all" measured on GloVe, eight bits a
  key and 64 tables, the first 1,000 questions.
- Promise [tested] → "the nearest of the candidates, measured exactly" [proved]; the probability
  of becoming a candidate [tested], over the random cuts, which this Lean does not state.
- Idea [mentioned] → the two hash families, `simBit` and `pStableKey`; one shared key in one table
  makes a candidate.
- Invariants [proved] → `Valid` on the stored index, then a query's answer:
  1 [proved] `InItsBucket`.
  2 [proved] on a query's answer, not the stored index: `MeasuredExactly`, in the promise.
  Not in the box: `OneBucketPerKey`, `EachPointOncePerTable`
- Cost [proved] → `QueryTicksKeysPlusCandidates`, ticks per nearest query;
  `EntriesOnePerPointPerTable`, entries in memory.
- Assumes [measured] → the cuts drawn at random, the world's; the true nearest is the answer
  whenever it collides in some table [proved], `nearest_eq_scanNearest`; recall [measured], on
  GloVe, eight bits a key and 64 tables, the first 1,000 questions.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- A bucket: a key, and the ids of the points stored under it. -/
structure Bucket (κ : Type) where
  /-- The key. -/
  key : κ
  /-- The ids of the points stored under the key, in insertion order. -/
  ids : List ℕ
deriving DecidableEq

/-- One table: its hash function, and its buckets, each a key with the ids of the points stored
under it. -/
structure Table (d : ℕ) (α κ : Type) where
  /-- The table's hash function: a point's key. -/
  hash : Point d α → κ
  /-- The buckets, each a key and the ids stored under it. -/
  buckets : List (Bucket κ)

/-- An LSH index: the stored points and the tables. -/
structure Index (d : ℕ) (α κ : Type) where
  /-- The stored points; a point's id is its number in this list, counting from 0. -/
  points : List (Point d α)
  /-- One table per hash function. -/
  tables : List (Table d α κ)

/-- The ids stored in the first bucket with key `key`, or none. -/
def bucketOf (key : κ) : List (Bucket κ) → List ℕ
  | [] => []
  | b :: rest => if b.key = key then b.ids else bucketOf key rest

/-- Every id a table stores, bucket after bucket. -/
def Table.entries (t : Table d α κ) : List ℕ := t.buckets.flatMap Bucket.ids

/-- A query's candidates: the ids, ascending and each once, stored in its own bucket in some
table. One key per table is computed, and one bucket read. -/
def Index.candidates (x : Index d α κ) (q : Point d α) : List ℕ :=
  ((x.tables.flatMap fun t => bucketOf (t.hash q) t.buckets).insertionSort (· ≤ ·)).dedup

/-- Box invariant 1: every stored point sits in the bucket its key names, in every table. In
every table, every stored id names a stored point whose key is its bucket's, and every stored
point is found in the bucket its key names. The bucket a key names is the first with that key;
`OneBucketPerKey` makes it the only one. -/
def InItsBucket (x : Index d α κ) : Prop :=
  ∀ t ∈ x.tables,
    (∀ b ∈ t.buckets, ∀ i ∈ b.ids,
      ∃ h : i < x.points.length, t.hash x.points[i] = b.key) ∧
    ∀ (i : ℕ) (h : i < x.points.length), i ∈ bucketOf (t.hash x.points[i]) t.buckets

/-- Not in the box: in every table, one bucket per key, and no bucket empty. -/
def OneBucketPerKey (x : Index d α κ) : Prop :=
  ∀ t ∈ x.tables, (t.buckets.map Bucket.key).Nodup ∧ ∀ b ∈ t.buckets, b.ids ≠ []

/-- Not in the box: every stored point is stored exactly once in every table. -/
def EachPointOncePerTable (x : Index d α κ) : Prop :=
  ∀ t ∈ x.tables, ∀ i < x.points.length, t.entries.count i = 1

/-- A query's answer with what it answers: the index asked (the structure), the query point, how
many points were asked for, and the ids reported. -/
structure Answer (d : ℕ) (α κ : Type) where
  /-- The index the query read. -/
  index : Index d α κ
  /-- The query point. -/
  query : Point d α
  /-- How many points were asked for. -/
  k : ℕ
  /-- The ids reported. -/
  result : List ℕ

/-- The candidates the answer is drawn from: the query's, in its index. -/
@[simp] abbrev Answer.candidates (a : Answer d α κ) : List ℕ := a.index.candidates a.query

/-- Box invariant 2: a shared bucket only makes a point a candidate, and every candidate is measured
exactly before one is reported. Every candidate names a stored point, so it can be measured; the
answer holds `min k` of the candidates, each once, and none is farther from the query than a
candidate left out: they are, among the candidates, those of least exact distance. A piece on a
query's answer, not the stored index. -/
def MeasuredExactly (a : Answer d α κ) : Prop :=
  (∀ c ∈ a.candidates, c < a.index.points.length) ∧
    a.result.Nodup ∧ a.result.length = min a.k a.candidates.length ∧
    (∀ r ∈ a.result, r ∈ a.candidates) ∧
    ∀ r ∈ a.result, ∀ c ∈ a.candidates, c ∉ a.result →
      ∀ (hr : r < a.index.points.length) (hc : c < a.index.points.length),
        sqDist a.index.points[r] a.query ≤ sqDist a.index.points[c] a.query

/-- Cost, per nearest query, in ticks: a counted query `m` on `x` and `q` takes one tick per table,
for the key it computes, and one per candidate, for its exact distance. -/
def QueryTicksKeysPlusCandidates (x : Index d α κ) (q : Point d α)
    (m : Cslib.Algorithms.Lean.TimeM ℕ (Option ℕ)) : Prop :=
  m.time = x.tables.length + (x.candidates q).length

/-- Cost, memory, in entries: every table stores one entry per point, as many ids as points. -/
def EntriesOnePerPointPerTable (x : Index d α κ) : Prop :=
  ∀ t ∈ x.tables, t.entries.length = x.points.length

/-! ## The contract, the part Lean checks

`Ops` names the operations the box speaks of; `Contract` is what they owe, one field per claim.
`LSH.lean`, the file that imports the whole structure, proves the library's operations meet it
(`LSH.contract`). -/

/-- The operations the box speaks of: the build, the query for the nearest point and for the `k`
nearest, the invariant, and the nearest query that counts its steps. -/
structure Ops (d : ℕ) (α κ : Type) where
  /-- Hash every point into one table per hash function. -/
  build : List (Point d α → κ) → List (Point d α) → Index d α κ
  /-- The nearest candidate, if any. -/
  nearest : Index d α κ → Point d α → Option ℕ
  /-- The `k` nearest candidates. -/
  kNearest : Index d α κ → Point d α → ℕ → List ℕ
  /-- The design's invariants. -/
  Valid : Index d α κ → Prop
  /-- The query for the nearest, counting a tick per key computed and per candidate measured. -/
  nearestM : Index d α κ → Point d α → Cslib.Algorithms.Lean.TimeM ℕ (Option ℕ)
  /-- The counted query answers as the query does, so the cost is of the query. -/
  counted : ∀ x q, (nearestM x q).ret = nearest x q

/-- Promise: the nearest of the candidates, measured exactly, and the `k` nearest, on a valid
index. -/
def Ops.NearestOfCandidates (o : Ops d α κ) : Prop :=
  (∀ x q, o.Valid x → MeasuredExactly ⟨x, q, 1, (o.nearest x q).toList⟩) ∧  -- the nearest
  (∀ x q k, o.Valid x → MeasuredExactly ⟨x, q, k, o.kNearest x q k⟩)        -- the k nearest

/-- Not in the box: every index the build makes holds the points and hashes given, and is valid. -/
def Ops.KeepsInvariants (o : Ops d α κ) : Prop :=
  (∀ hs pts, (o.build hs pts).points = pts ∧
    (o.build hs pts).tables.map Table.hash = hs) ∧  -- the points, one table per hash, in order
  ∀ hs pts, o.Valid (o.build hs pts)                -- every index it makes is valid

/-- **The LSH index's invariant**: `InItsBucket`, the box's line 1, then `OneBucketPerKey` and
`EachPointOncePerTable`, not in the box. Box line 2 is about a query's answer, not the
stored index: `MeasuredExactly`, on an `Answer`. -/
def Valid (x : Index d α κ) : Prop :=
  InItsBucket x ∧ OneBucketPerKey x ∧ EachPointOncePerTable x

/-- **The LSH contract**, the part of the design Lean checks, one field per box field and one
conjunct per box line. Costs count the steps the counting query counts itself. -/
structure Contract (o : Ops d α κ) : Prop where
  -- Goal: find a place like this one among millions, in hundreds of dimensions, without checking
  -- them all.
  /-- Promise: the nearest of the candidates, measured exactly. -/
  promise :  -- at angle θ, a candidate with probability 1 - (1 - (1 - θ/π)^K)^L: tested
    o.NearestOfCandidates ∧  -- the nearest of the candidates, measured exactly
    o.KeepsInvariants        -- not in the box: the build stores the points; every index is valid
  -- Idea: hash so that near points tend to collide. A random cut through the origin gives one
  -- bit, which side you are on; several bits make a key; several tables give second chances.
  /-- Invariants: the box's two, in box order, then pieces not in the box. -/
  invariants : ∀ x, o.Valid x ↔
    InItsBucket x ∧            -- 1. every stored point sits in the bucket its key names
    -- 2. a shared bucket only makes a point a candidate, every candidate measured exactly: on a
    --    query's answer, not the index, `MeasuredExactly`, in the promise
    OneBucketPerKey x ∧        -- not in the box: one bucket per key, none empty
    EachPointOncePerTable x    -- not in the box: every point once in every table
  /-- Cost: a key per table plus a distance per candidate; memory, an entry per point per table. -/
  cost :
    (∀ x q, QueryTicksKeysPlusCandidates x q (o.nearestM x q)) ∧  -- per nearest query: ticks
    (∀ x, o.Valid x → EntriesOnePerPointPerTable x)               -- memory: entries
  -- Assumes: the cuts are drawn at random, independently of the places. If the true nearest
  -- collides in no table, the answer is a farther point, a wrong answer that recall measures.

end LSH

end AlgoDesign.Geometry
