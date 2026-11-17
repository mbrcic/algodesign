/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.LSH.Query

/-!
# LSH: the query, counted

`nearestM` is `nearest` with its steps counted through `Cslib.Algorithms.Lean.TimeM`: one tick
per table, for the key it computes and the bucket it reads (`readM`), and one per candidate handed
to the exact ranking (`measureM`). `ret_nearestM`: it answers as `nearest` does. `time_nearestM`:
a key per table plus an exact distance per candidate, the box's cost.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- Read `q`'s bucket in every table: one tick per table, for its key. -/
def readM (q : Point d α) : List (Table d α κ) → TimeM ℕ (List ℕ)
  | [] => pure []
  | t :: ts => do
      tick 1
      let rest ← readM q ts
      pure (bucketOf (t.hash q) t.buckets ++ rest)

/-- Hand each candidate's point to the exact ranking: one tick per candidate. -/
def measureM (pts : List (Point d α)) : List ℕ → TimeM ℕ (List (Point d α))
  | [] => pure []
  | c :: cs => do
      tick 1
      let rest ← measureM pts cs
      pure (pts[c]! :: rest)

/-- **The counted query**: the candidates read from the stored buckets, each measured once, and
the nearest of them, the one stored first on ties. -/
def nearestM (x : Index d α κ) (q : Point d α) : TimeM ℕ (Option ℕ) := do
  let found ← readM q x.tables
  let cs := (found.insertionSort (· ≤ ·)).dedup
  let measured ← measureM x.points cs
  pure ((scanNearest measured q).map (cs[·]!))

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
theorem ret_readM (q : Point d α) (ts : List (Table d α κ)) :
    (readM q ts).ret = ts.flatMap fun t => bucketOf (t.hash q) t.buckets := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [readM, ih]

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
theorem time_readM (q : Point d α) (ts : List (Table d α κ)) : (readM q ts).time = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [readM, ih]; omega

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem ret_measureM (pts : List (Point d α)) (cs : List ℕ) :
    (measureM pts cs).ret = cs.map (pts[·]!) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [measureM, ih]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem time_measureM (pts : List (Point d α)) (cs : List ℕ) :
    (measureM pts cs).time = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [measureM, ih]; omega

omit [IsStrictOrderedRing α] in
/-- **The counted query answers as the query does.** -/
theorem ret_nearestM (x : Index d α κ) (q : Point d α) : (nearestM x q).ret = nearest x q := by
  simp [nearestM, nearest, Index.candidates, ret_readM, ret_measureM]

omit [IsStrictOrderedRing α] in
/-- **A key per table plus an exact distance per candidate**, in ticks. -/
theorem time_nearestM (x : Index d α κ) (q : Point d α) :
    QueryTicksKeysPlusCandidates x q (nearestM x q) := by
  simp [QueryTicksKeysPlusCandidates, nearestM, Index.candidates, time_readM, time_measureM,
    ret_readM]

end LSH

end AlgoDesign.Geometry
