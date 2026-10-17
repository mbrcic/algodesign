import AlgoDesign
import Mathlib.Tactic

/-! Regression checks for the geometry specifications. Run with
`lake env lean -DwarningAsError=true AlgoDesignTests/Geometry.lean`. -/
namespace AlgoDesignTests
open AlgoDesign.Geometry

/-- Points in the plane, written as pairs. -/
def p2 (x y : ℤ) : Point 2 ℤ := ![x, y]

-- empty set: no answer
example : scanNearest ([] : List (Point 2 ℤ)) (p2 0 0) = none := by decide
-- the query is stored: distance 0, that index
example : scanNearest [p2 5 5, p2 1 1, p2 9 0] (p2 1 1) = some 1 := by decide
-- a tie between indices 0 and 2 (both at squared distance 1): the lower index wins
example : scanNearest [p2 1 0, p2 4 4, p2 (-1) 0] (p2 0 0) = some 0 := by decide
-- duplicates: the first copy wins
example : scanNearest [p2 3 3, p2 2 2, p2 2 2] (p2 2 2) = some 1 := by decide

-- orientation: left, right, collinear, all equal
example : orient ((0 : ℤ), 0) (1, 0) (0, 1) = 1 := by decide
example : orient ((0 : ℤ), 0) (1, 0) (0, -1) = -1 := by decide
example : orient ((0 : ℤ), 0) (1, 1) (3, 3) = 0 := by decide
example : orient ((2 : ℤ), 2) (2, 2) (2, 2) = 0 := by decide

-- the 1D range tree: leaves 1 3 5 7, split keys = left maxima (lower median)
open RangeTree1D in
def rt : RangeTree1D ℤ := .node 3 (.node 1 (.leaf 1) (.leaf 3)) (.node 5 (.leaf 5) (.leaf 7))
-- endpoints equal to keys are reported
example : RangeTree1D.query 3 5 rt = [3, 5] := by decide
-- lo > hi: empty
example : RangeTree1D.query 6 4 rt = [] := by decide
-- a key equal to the split key and to lo is reported
example : RangeTree1D.query 3 3 rt = [3] := by decide
-- the whole range: every leaf, in order
example : RangeTree1D.query 0 9 rt = [1, 3, 5, 7] := by decide
-- repeated keys: every copy is reported, though copies of the split key sit on both sides
def rtDup : RangeTree1D ℤ := .node 3 (.node 1 (.leaf 1) (.leaf 3)) (.node 3 (.leaf 3) (.leaf 5))
example : RangeTree1D.query 3 3 rtDup = [3, 3] := by decide
example :
    RangeTree1D.query 1 1 (.node 1 (.node 1 (.leaf 1) (.leaf 1)) (.node 1 (.leaf 1) (.leaf 1)))
    = [1, 1, 1, 1] := by decide

-- the build splits at the lower median: 3 of [1, 3, 5, 7], and 3 of [1, 3, 5]
example : RangeTree1D.build [(1 : ℤ), 3, 5, 7] (by simp) = rt := by
  simp [rt, RangeTree1D.build, RangeTree1D.half]
example : RangeTree1D.build [(1 : ℤ), 3, 5] (by simp) =
    .node 3 (.node 1 (.leaf 1) (.leaf 3)) (.leaf 5) := by
  simp [RangeTree1D.build, RangeTree1D.half]
-- the build with repeated keys gives the tree above, whose query reports both copies
example : RangeTree1D.build [(1 : ℤ), 3, 3, 5] (by simp) = rtDup := by
  simp [rtDup, RangeTree1D.build, RangeTree1D.half]
-- the build the contract names sorts first: keys in any order give the same tree, no keys none
example : RangeTree1D.ofList [(5 : ℤ), 1, 7, 3] = some rt := by
  simp +decide [rt, RangeTree1D.ofList, RangeTree1D.sortKeys, RangeTree1D.build, RangeTree1D.half]
example : RangeTree1D.ofList ([] : List ℤ) = none := by simp [RangeTree1D.ofList]
-- the contract, at the integers
example : RangeTree1D.Contract (RangeTree1D.ops : RangeTree1D.Ops ℤ) := RangeTree1D.contract
-- both box invariants hold of these trees; a split below its left side breaks only the first,
-- three keys on the right of one only the second
example : RangeTree1D.Valid rt ∧ RangeTree1D.Valid rtDup := by decide
example : ¬ RangeTree1D.KeysSeparate (.node 2 (.leaf 3) (.leaf 3) : RangeTree1D ℤ) ∧
    RangeTree1D.SplitsHalve (.node 2 (.leaf 3) (.leaf 3) : RangeTree1D ℤ) := by decide
example :
    RangeTree1D.KeysSeparate (.node 1 (.leaf 1) (.node 2 (.leaf 2) (.leaf 3)) : RangeTree1D ℤ) ∧
    ¬ RangeTree1D.SplitsHalve (.node 1 (.leaf 1) (.node 2 (.leaf 2) (.leaf 3)) : RangeTree1D ℤ) :=
  by decide
-- the counted query answers as the query does, within `2 ⌈log₂ 4⌉ + k + 1` ticks
example : (RangeTree1D.queryM 3 5 rt).ret = [3, 5] ∧ (RangeTree1D.queryM 3 5 rt).time = 6 :=
  by decide
example : (RangeTree1D.queryM 3 3 rtDup).ret = [3, 3] ∧ (RangeTree1D.queryM 6 4 rt).ret = [] :=
  by decide

-- the 2D tree over (1,5), (1,2), (1,2), (3,3), sorted by x: x = 1 sits on both sides of the root
-- every inner node holds its associated tree: the points below it by y, split at the lower median
def rt2 : RangeTree2D ℤ :=
  .node 1
    (.node (p2 1 2) (.node (p2 1 2) (.leaf (p2 1 2)) (.leaf (p2 1 2)))
      (.node (p2 3 3) (.leaf (p2 3 3)) (.leaf (p2 1 5))))
    (.node 1 (.node (p2 1 2) (.leaf (p2 1 2)) (.leaf (p2 1 5))) (.leaf (p2 1 5)) (.leaf (p2 1 2)))
    (.node 1 (.node (p2 1 2) (.leaf (p2 1 2)) (.leaf (p2 3 3))) (.leaf (p2 1 2)) (.leaf (p2 3 3)))
example : RangeTree2D.query (p2 0 2) (p2 2 4) (some rt2) = [p2 1 2, p2 1 2] := by decide
example : RangeTree2D.query (p2 1 0) (p2 3 9) (some rt2) = [p2 1 5, p2 1 2, p2 1 2, p2 3 3] :=
  by decide
-- an inverted rectangle answers nothing
example : RangeTree2D.query (p2 3 9) (p2 0 0) (some rt2) = [] := by decide
-- the promise, at the integers, on the build of those points in another order
example : (RangeTree2D.query (p2 0 2) (p2 2 4)
    (RangeTree2D.build [p2 1 5, p2 3 3, p2 1 2, p2 1 2])).Perm [p2 1 2, p2 1 2] :=
  (RangeTree2D.query_build _ _ _).trans (by decide)
-- the counted walk the Rust and the Python run: right subtrees before the path below, 7 ticks
example : (RangeTree2D.queryM (p2 1 0) (p2 3 9) (some rt2)).ret =
    [p2 1 2, p2 1 5, p2 1 2, p2 3 3] ∧ (RangeTree2D.queryM (p2 1 0) (p2 3 9) (some rt2)).time = 7 :=
  by decide
example : (RangeTree2D.queryM (p2 3 9) (p2 0 0) (some rt2)).ret = [] := by decide

-- the k-d tree, dBCKO's form: points in leaves. The root splits on x at 2; the point (2, 1) has
-- x equal to the split and sits on the left, and (2, 3) also has x = 2 and sits on the right
def kd : KDTree 2 ℤ :=
  .node 0 2 (.node 1 1 (.leaf (p2 2 1)) (.leaf (p2 1 5)))
    (.node 1 0 (.leaf (p2 3 0)) (.leaf (p2 2 3)))
-- every cut separates the points below it
example : KDTree.CutsSeparate kd := by decide
-- a box whose left edge is the split reports the points on it, on both sides
example : KDTree.rangeQuery (p2 2 0) (p2 4 4) kd = [p2 2 1, p2 3 0, p2 2 3] := by decide
-- a box left of the split still reaches the right side's point on the split
example : KDTree.rangeQuery (p2 0 0) (p2 2 3) kd = [p2 2 1, p2 2 3] := by decide
-- every cut also splits its points in half: the tree is valid
example : KDTree.CutsHalve kd := by decide
example : KDTree.Valid kd := by decide
-- a point past its cut: the halves are even, but the cut does not separate them
def kdPastCut : KDTree 2 ℤ := .node 0 0 (.leaf (p2 2 1)) (.leaf (p2 1 5))
example : ¬ KDTree.CutsSeparate kdPastCut ∧ KDTree.CutsHalve kdPastCut := by decide
-- three points with one on the left (the `n / 2` split): the cuts separate, but the left side
-- holds fewer than `⌈3/2⌉`
def kdUneven : KDTree 2 ℤ :=
  .node 0 0 (.leaf (p2 0 0)) (.node 0 1 (.leaf (p2 1 0)) (.leaf (p2 2 0)))
example : KDTree.CutsSeparate kdUneven ∧ ¬ KDTree.CutsHalve kdUneven := by decide

-- the build: axis x at the root, the first ⌈3/2⌉ = 2 points by x go left, split at the last one's
-- x; then axis y below
example : KDTree.build [p2 3 0, p2 1 5, p2 2 1] (by simp) =
    .node 0 2 (.node 1 1 (.leaf (p2 2 1)) (.leaf (p2 1 5))) (.leaf (p2 3 0)) := by
  simp +decide [KDTree.build, KDTree.buildAt, KDTree.sortAlong, p2, Fin.ofNat]
-- no points: no tree, so no answer
example : KDTree.ofList ([] : List (Point 2 ℤ)) = none := by simp [KDTree.ofList]
-- asked for no neighbors, the search measures nothing and answers nothing
example :
    (KDTree.BestFirst.search 0 (p2 3 0) kd).measured = [] ∧ KDTree.kNearest 0 (p2 3 0) kd = [] := by
  decide
-- the two nearest (3, 0), nearest first
example :
    KDTree.kNearest 2 (p2 3 0) kd = [p2 3 0, p2 2 1] ∧
      KDTree.nearest (p2 3 0) kd = some (p2 3 0) := by
  decide

-- the contract, at the integers
example : KDTree.Contract (KDTree.ops : KDTree.Ops 2 ℤ) := KDTree.contract
-- best-first search for the point nearest (3, 0): the root's left side is never opened
open KDTree.BestFirst in
example : (search 1 (p2 3 0) kd).measured = [p2 2 3, p2 3 0] := by decide
open KDTree.BestFirst in
example : kthBest 1 (p2 3 0) (search 1 (p2 3 0) kd) = some 0 := by decide
open KDTree.BestFirst in
example : Valid ⟨kd, p2 3 0, search 1 (p2 3 0) kd⟩ ∧ Stopped 1 (p2 3 0) (search 1 (p2 3 0) kd) :=
  by decide
-- a tie: (0, 0) and (2, 0) are both at squared distance 1 from (1, 0). After the right leaf, the
-- left region waits with bound 1, equal to the best: a stop at `≥` would skip (0, 0); the strict
-- stop opens it
def kdTie : KDTree 2 ℤ := .node 0 0 (.leaf (p2 0 0)) (.leaf (p2 2 0))
open KDTree.BestFirst in
example : (run 1 (p2 1 0) 2 (start kdTie)).measured = [p2 2 0] ∧
    (run 1 (p2 1 0) 2 (start kdTie)).queue.map Region.bound = [1] ∧
    kthBest 1 (p2 1 0) (run 1 (p2 1 0) 2 (start kdTie)) = some 1 := by decide
open KDTree.BestFirst in
example : (search 1 (p2 1 0) kdTie).measured = [p2 2 0, p2 0 0] := by decide
-- the two nearest (3, 0): itself and (2, 1), from opposite sides of the root's cut
open KDTree.BestFirst in
example : (dists (p2 3 0) (search 2 (p2 3 0) kd).measured).take 2 = [0, 2] ∧
    (dists (p2 3 0) (KDTree.points kd)).take 2 = [0, 2] := by decide
-- the two nearest (2, 2): (2, 1) and (2, 3), tied at 1, one on each side of the root's cut
open KDTree.BestFirst in
example : (dists (p2 2 2) (search 2 (p2 2 2) kd).measured).take 2 =
    (dists (p2 2 2) (KDTree.points kd)).take 2 ∧
    (dists (p2 2 2) (KDTree.points kd)).take 2 = [1, 1] := by decide
-- a state that skips a closer point: (0, 0) waits in a region whose bound, 4, is more than its
-- squared distance, 1. Every point is accounted for; the region's bound is what is wrong
open KDTree.BestFirst in
def skips : State 2 ℤ := ⟨[p2 2 0], [⟨![-2, 0], .leaf (p2 0 0)⟩]⟩
open KDTree.BestFirst in
example : ¬ NothingCloserSkipped ⟨kdTie, p2 1 0, skips⟩ ∧ EachPointOnce ⟨kdTie, p2 1 0, skips⟩ := by
  decide
-- a root cut that does not separate, (0, 0) left of a split at -1: the search's start fails only
-- QueuedCutsSeparate
def kdBroken : KDTree 2 ℤ := .node 0 (-1) (.leaf (p2 0 0)) (.leaf (p2 2 0))
open KDTree.BestFirst in
example : ¬ QueuedCutsSeparate ⟨kdBroken, p2 1 0, start kdBroken⟩ ∧
    NothingCloserSkipped ⟨kdBroken, p2 1 0, start kdBroken⟩ ∧
    OffsetsBound ⟨kdBroken, p2 1 0, start kdBroken⟩ ∧
    EachPointOnce ⟨kdBroken, p2 1 0, start kdBroken⟩ := by decide

-- LSH, one table, the axis directions: a key is the point's quadrant
def lshTables : List (Point 2 ℤ → List Bool) := [simKey [p2 1 0, p2 0 1]]
def lshPts : List (Point 2 ℤ) := [p2 5 5, p2 (-1) 1, p2 10 10]
-- the true nearest neighbor collides: LSH is exact
example : LSH.lshQuery lshTables lshPts (p2 4 4) = some 0 := by decide
example : scanNearest lshPts (p2 4 4) = some 0 := by decide
-- the honest half: the true nearest (index 1, a different quadrant) does not collide, so LSH
-- returns a farther point
example : scanNearest lshPts (p2 1 1) = some 1 := by decide
example : LSH.lshQuery lshTables lshPts (p2 1 1) = some 0 := by decide
-- a SimHash bit asks which side
example : simBit (p2 1 0) (p2 (-3) 7) = false := by decide

-- the stored index: one table, keys are quadrants. (5,5) and (10,10) share the bucket
-- [true, true], in insertion order; (-1,1) has its own
def lshIdx : LSH.Index 2 ℤ (List Bool) := LSH.build lshTables lshPts
example :
    lshIdx.tables.map LSH.Table.buckets = [[⟨[true, true], [0, 2]⟩, ⟨[false, true], [1]⟩]] := by
  decide
example : LSH.Valid lshIdx := by decide
-- the stored-bucket query gives the on-the-fly answers, the honest miss included
example : LSH.nearest lshIdx (p2 4 4) = some 0 ∧ LSH.nearest lshIdx (p2 1 1) = some 0 := by decide
example : LSH.kNearest lshIdx (p2 9 9) 3 = [2, 0] := by decide
-- an index over no points is valid and answers nothing
example : LSH.Valid (LSH.build lshTables ([] : List (Point 2 ℤ))) ∧
    LSH.nearest (LSH.build lshTables ([] : List (Point 2 ℤ))) (p2 1 1) = none := by decide
-- each defect breaks its own piece: a point in another key's bucket, an id past the points
-- and a point missing break InItsBucket; a point stored twice breaks only EachPointOncePerTable;
-- an empty bucket, and a key with two buckets, only OneBucketPerKey
def lshWith (bs : List (LSH.Bucket (List Bool))) : LSH.Index 2 ℤ (List Bool) :=
  ⟨lshPts, [⟨simKey [p2 1 0, p2 0 1], bs⟩]⟩
example : ¬ LSH.InItsBucket (lshWith [⟨[true, true], [0]⟩, ⟨[false, true], [1, 2]⟩]) := by decide
example : ¬ LSH.InItsBucket (lshWith [⟨[true, true], [0, 2, 3]⟩, ⟨[false, true], [1]⟩]) := by
  decide
example : ¬ LSH.InItsBucket (lshWith [⟨[true, true], [0]⟩, ⟨[false, true], [1]⟩]) := by decide
example : LSH.InItsBucket (lshWith [⟨[true, true], [0, 2, 0]⟩, ⟨[false, true], [1]⟩]) ∧
    LSH.OneBucketPerKey (lshWith [⟨[true, true], [0, 2, 0]⟩, ⟨[false, true], [1]⟩]) ∧
    ¬ LSH.EachPointOncePerTable (lshWith [⟨[true, true], [0, 2, 0]⟩, ⟨[false, true], [1]⟩]) := by
  decide
def lshEmptyBucket : LSH.Index 2 ℤ (List Bool) :=
  lshWith [⟨[true, true], [0, 2]⟩, ⟨[false, true], [1]⟩, ⟨[false, false], []⟩]
def lshTwoBuckets : LSH.Index 2 ℤ (List Bool) :=
  lshWith [⟨[true, true], [0, 2]⟩, ⟨[false, true], [1]⟩, ⟨[true, true], []⟩]
example : LSH.InItsBucket lshEmptyBucket ∧ LSH.EachPointOncePerTable lshEmptyBucket ∧
    ¬ LSH.OneBucketPerKey lshEmptyBucket := by decide
example : LSH.InItsBucket lshTwoBuckets ∧ LSH.EachPointOncePerTable lshTwoBuckets ∧
    ¬ LSH.OneBucketPerKey lshTwoBuckets := by decide
-- MeasuredExactly: the right answer holds; a farther candidate, a repeat, a short answer and a
-- non-candidate each break it
example : LSH.MeasuredExactly ⟨lshIdx, p2 9 9, 1, [2]⟩ := by decide
example : ¬ LSH.MeasuredExactly ⟨lshIdx, p2 9 9, 1, [0]⟩ := by decide
example : ¬ LSH.MeasuredExactly ⟨lshIdx, p2 9 9, 2, [2, 2]⟩ := by decide
example : ¬ LSH.MeasuredExactly ⟨lshIdx, p2 9 9, 2, [2]⟩ := by decide
example : ¬ LSH.MeasuredExactly ⟨lshIdx, p2 9 9, 1, [1]⟩ := by decide
-- a candidate past the points cannot be measured: the answer that is right on the stored points
-- still fails
def lshPast : LSH.Index 2 ℤ (List Bool) := lshWith [⟨[true, true], [0, 2, 3]⟩, ⟨[false, true], [1]⟩]
example : ¬ LSH.MeasuredExactly ⟨lshPast, p2 9 9, 1, [2]⟩ := by decide
-- NearestFirst: the k nearest hold it; the same ids, farthest first, break it
example : LSH.NearestFirst ⟨lshIdx, p2 9 9, 2, LSH.kNearest lshIdx (p2 9 9) 2⟩ ∧
    ¬ LSH.NearestFirst ⟨lshIdx, p2 9 9, 2, (LSH.kNearest lshIdx (p2 9 9) 2).reverse⟩ := by
  decide
-- the counted query: one tick per table and one per candidate, and the query's answer
example :
    (LSH.nearestM lshIdx (p2 9 9)).time = 3 ∧ (LSH.nearestM lshIdx (p2 9 9)).ret = some 2 := by
  decide
-- the box, at the integers
example : LSH.Contract (LSH.ops : LSH.Ops 2 ℤ (List Bool)) := LSH.contract

-- the graph's pruning rule keeps diverse neighbors. Candidates nearest-first: (1, 0) at 1,
-- (0, 2) at 4, (2, 0) at 4. (0, 2) is kept: it is nearer the base than the kept (1, 0) (4 < 5).
-- (2, 0) is dropped although M = 3 leaves room: the kept (1, 0) is nearer to it (1 < 4)
example : HNSW.selectNeighbors 3 (p2 0 0) [] [p2 1 0, p2 0 2, p2 2 0] = [p2 1 0, p2 0 2] := by
  decide
-- at most M are kept
example : HNSW.selectNeighbors 1 (p2 0 0) [] [p2 1 0, p2 0 2, p2 2 0] = [p2 1 0] := by decide
-- a tie: (1, 2) is as far from the kept (2, 0) as from the base (5 and 5). No kept neighbor is
-- strictly nearer to it, so it is kept, as hnswlib does
example : HNSW.selectNeighbors 2 (p2 0 0) [] [p2 2 0, p2 1 2] = [p2 2 0, p2 1 2] := by decide
-- the greedy step moves to the neighbor nearest the query, and stays put if none is nearer
example : HNSW.greedyStep (p2 5 5) (p2 0 0) [p2 1 0, p2 4 4, p2 3 3] = p2 4 4 := by decide
example : HNSW.greedyStep (p2 0 0) (p2 0 0) [p2 1 0, p2 4 4] = p2 0 0 := by decide

-- the stored graph: node 0 on layers 0 and 1, nodes 1 and 2 on layer 0, entry 0 (on top), one
-- node per point
def hnswG : HNSW 2 ℤ :=
  ⟨1, 2, [p2 0 0, p2 1 0, p2 0 1], [[[1, 2], []], [[0, 2]], [[0, 1]]], some 0⟩
example : HNSW.Valid hnswG := by decide
-- the empty graph (no entry) and one node alone
example : HNSW.Valid (HNSW.empty 1 2 : HNSW 2 ℤ) := by decide
example : HNSW.Valid (⟨1, 2, [p2 0 0], [[[]]], some 0⟩ : HNSW 2 ℤ) := by decide
-- each piece fails alone: a layer-0 list over m0 = 1
example : ¬ HNSW.DegreeBounded { hnswG with m0 := 1 } ∧ HNSW.NestedLayers hnswG := by decide
-- a link on layer 1 to node 1, which is only on layer 0
example : ¬ HNSW.NestedLayers { hnswG with links := [[[1, 2], [1]], [[0, 2]], [[0, 1]]] } := by
  decide
-- a node on no layer
example : ¬ HNSW.NestedLayers (⟨1, 2, [p2 0 0, p2 1 0], [[[]], []], some 0⟩ : HNSW 2 ℤ) := by
  decide
-- the entry below the top layer, and an entry on an empty graph: only EntryOnTop fails
example : ¬ HNSW.EntryOnTop { hnswG with entry := some 1 } ∧
    HNSW.NestedLayers { hnswG with entry := some 1 } := by decide
example : ¬ HNSW.EntryOnTop (⟨1, 2, [], [], some 0⟩ : HNSW 2 ℤ) := by decide
example : ¬ HNSW.NoSelfLinks (⟨1, 2, [p2 0 0], [[[0]]], some 0⟩ : HNSW 2 ℤ) ∧
    HNSW.NestedLayers (⟨1, 2, [p2 0 0], [[[0]]], some 0⟩ : HNSW 2 ℤ) := by decide
example : ¬ HNSW.NoRepeatedLinks
    (⟨1, 2, [p2 0 0, p2 1 0], [[[1, 1]], [[0]]], some 0⟩ : HNSW 2 ℤ) := by decide
-- a point with no node, and a node with no point: only OneNodePerPoint fails
example : ¬ HNSW.OneNodePerPoint { hnswG with points := [p2 0 0, p2 1 0] } ∧
    HNSW.DegreeBounded { hnswG with points := [p2 0 0, p2 1 0] } := by decide
example : ¬ HNSW.OneNodePerPoint { hnswG with points := hnswG.points ++ [p2 7 7] } := by decide
-- the picking step: the rule's picks are diverse, ties kept; dropping the tie is not
example : HNSW.PicksDiverse ⟨2, p2 0 0, [p2 2 0, p2 1 2], [p2 2 0, p2 1 2]⟩ := by decide
example : ¬ HNSW.PicksDiverse ⟨2, p2 0 0, [p2 2 0, p2 1 2], [p2 2 0]⟩ := by decide
example : HNSW.PicksDiverse ⟨3, p2 0 0, [p2 1 0, p2 0 2, p2 2 0], [p2 1 0, p2 0 2]⟩ := by decide
-- candidates out of distance order are not a picking step
example : ¬ HNSW.PicksDiverse ⟨3, p2 0 0, [p2 0 2, p2 1 0], [p2 0 2, p2 1 0]⟩ := by decide
-- no candidates, no picks; m = 0, no picks
example : HNSW.PicksDiverse ⟨2, p2 0 0, [], []⟩ := by decide
example : HNSW.PicksDiverse ⟨0, p2 0 0, [p2 1 0], []⟩ := by decide
-- the search's last step: the beam [2, 0, 1] at q = (0, 0) over (3, 0), (1, 0), (1, 0); the tie
-- at 1 goes to the lower node; k = 2 keeps two, k = 5 all three
example : HNSW.finish [p2 3 0, p2 1 0, p2 1 0] (p2 0 0) 2 [2, 0, 1] = [⟨1, 1⟩, ⟨1, 2⟩] := by
  decide
example :
    HNSW.finish [p2 3 0, p2 1 0, p2 1 0] (p2 0 0) 5 [2, 0, 1] = [⟨1, 1⟩, ⟨1, 2⟩, ⟨9, 0⟩] := by
  decide
example : HNSW.finish [p2 3 0] (p2 0 0) 0 [0] = [] := by decide
-- the promise's domain is a beam of stored nodes, each once: off it, the answer measures no
-- stored point, and a beam that names a node twice answers it twice
example : HNSW.Promise [p2 3 0] (p2 0 0) 1 [0] (HNSW.finish [p2 3 0] (p2 0 0) 1 [0]) ∧
    ¬ HNSW.Promise [p2 3 0] (p2 0 0) 1 [5] (HNSW.finish [p2 3 0] (p2 0 0) 1 [5]) := by
  unfold HNSW.Promise; decide
example : HNSW.finish [p2 3 0] (p2 0 0) 2 [0, 0] = [⟨9, 0⟩, ⟨9, 0⟩] ∧
    ¬ HNSW.Promise [p2 3 0] (p2 0 0) 2 [0, 0] (HNSW.finish [p2 3 0] (p2 0 0) 2 [0, 0]) := by
  unfold HNSW.Promise; decide
-- insertion, as the Rust runs it: m = 1, m0 = 2. Node 0 on layers 0-1; node 1 picks 0; node 2
-- picks 0, the nearer of its two candidates; node 3 arrives on three layers, picks 1 (tied with
-- 2, the lower index first) on layer 0 and 0 on layer 1, and becomes the entry; node 4 picks 0,
-- whose layer-0 list goes over m0 = 2 and is re-picked, dropping 4 again
def hnsw1 : HNSW 2 ℤ := HNSW.insert (HNSW.empty 1 2) (p2 0 0) 1 []
def hnsw2 : HNSW 2 ℤ := HNSW.insert hnsw1 (p2 1 0) 0 [⟨0, [0]⟩]
def hnsw3 : HNSW 2 ℤ := HNSW.insert hnsw2 (p2 0 1) 0 [⟨0, [0, 1]⟩]
def hnsw4 : HNSW 2 ℤ := HNSW.insert hnsw3 (p2 5 5) 2 [⟨0, [1, 2, 0]⟩, ⟨1, [0]⟩]
def hnsw5 : HNSW 2 ℤ := HNSW.insert hnsw4 (p2 0 (-1)) 0 [⟨0, [0]⟩]
example : hnsw3.links = [[[1, 2], []], [[0]], [[0]]] ∧ hnsw3.entry = some 0 := by decide
example : hnsw4.links = [[[1, 2], [3]], [[0, 3]], [[0]], [[1], [0], []]] ∧ hnsw4.entry = some 3 :=
  by decide
example : hnsw5.links = [[[1, 2], [3]], [[0, 3]], [[0]], [[1], [0], []], [[0]]] ∧
    hnsw5.entry = some 3 := by decide
example : hnsw5.points = [p2 0 0, p2 1 0, p2 0 1, p2 5 5, p2 0 (-1)] := by decide
example : HNSW.Valid hnsw5 ∧ HNSW.LinksPerPlaceAtMost hnsw5 := by decide
-- the memory bound is tight at node 0: 2 links on layer 0, 1 on layer 1
example : ¬ HNSW.LinksPerPlaceAtMost { hnsw5 with m0 := 1 } := by decide
-- why `m ≤ m0` is a hypothesis of `valid_insert`: at m = 2, m0 = 1, a node picks two neighbors
-- on layer 0, more than m0 lets a layer-0 list hold, from candidates the layer search could
-- return
def hnswWide1 : HNSW 2 ℤ := HNSW.insert (HNSW.empty 2 1) (p2 0 0) 0 []
def hnswWide2 : HNSW 2 ℤ := HNSW.insert hnswWide1 (p2 2 0) 0 [⟨0, [0]⟩]
def hnswWide3 : HNSW 2 ℤ := HNSW.insert hnswWide2 (p2 1 1) 0 [⟨0, [0, 1]⟩]
example : HNSW.Valid hnswWide2 ∧ HNSW.CandidatesOk hnswWide2 0 [⟨0, [0, 1]⟩] := by
  unfold HNSW.CandidatesOk; decide
example : ¬ HNSW.Valid hnswWide3 ∧ ¬ HNSW.DegreeBounded hnswWide3 := by decide

-- LSH: a stored query collides with itself and is returned
example : LSH.lshQuery lshTables lshPts (p2 10 10) = some 2 := by decide
-- LSH over no points: no answer
example : LSH.lshQuery lshTables ([] : List (Point 2 ℤ)) (p2 1 1) = none := by decide

-- the stronger statements exist with these shapes
example (tables : List (Point 2 ℤ → List Bool)) (pts : List (Point 2 ℤ)) (q : Point 2 ℤ) (n : ℕ)
    (hn : scanNearest pts q = some n) (hc : n ∈ LSH.candidates tables pts q) :
    LSH.lshQuery tables pts q = some n := LSH.lshQuery_eq_scanNearest hn hc
example (M : ℕ) (base : Point 2 ℤ) (cs : List (Point 2 ℤ)) :
    (HNSW.selectNeighbors M base [] cs).Pairwise (fun k c => sqDist base c ≤ sqDist k c) :=
  HNSW.selectNeighbors_diverse M base cs
example (pts : List (Point 2 ℤ)) (q : Point 2 ℤ) (k : ℕ) (beam : List ℕ) (hnd : beam.Nodup)
    (hb : ∀ i ∈ beam, i < pts.length) :
    HNSW.Promise pts q k beam (HNSW.finish pts q k beam) :=
  HNSW.promise_finish pts q k beam hnd hb
example : HNSW.Contract (HNSW.ops : HNSW.Ops 2 ℤ) := HNSW.contract
example (g : HNSW 2 ℤ) (h : HNSW.Built g) (hm : g.m ≤ g.m0) : HNSW.Valid g := HNSW.valid_build h hm
-- box invariant 3 of the k-d search from two of the pieces not in the box
example (r : KDTree.BestFirst.Run 2 ℤ) (ho : KDTree.BestFirst.OffsetsBound r)
    (he : KDTree.BestFirst.EachPointOnce r) : KDTree.BestFirst.NothingCloserSkipped r :=
  KDTree.BestFirst.nothingCloserSkipped_of_offsetsBound_eachPointOnce ho he
example (q x : Point 2 ℤ) (s : ℤ) (hq : s ≤ q 0) (hx : x 0 ≤ s) : (q 0 - s) ^ 2 ≤ sqDist x q :=
  far_side_bound_left q x 0 s hq hx

-- p-stable LSH, the grid on a line: direction (1, 0), offset 0, width 2. (3, 0) and (2, 5) share
-- cell 1; (4, 0) is in cell 2
example : pStableKey (![1, 0] : Point 2 ℚ) 0 2 ![3, 0] = 1 := by
  norm_num [pStableKey, dot, Fin.sum_univ_two, Int.floor_eq_iff]
example : pStableKey (![1, 0] : Point 2 ℚ) 0 2 ![2, 5] = 1 := by
  norm_num [pStableKey, dot, Fin.sum_univ_two, Int.floor_eq_iff]
example : pStableKey (![1, 0] : Point 2 ℚ) 0 2 ![4, 0] = 2 := by
  norm_num [pStableKey, dot, Fin.sum_univ_two, Int.floor_eq_iff]
-- the theorems hold for real coordinates, not only integer ones
example (p q : Point 3 ℝ) (i : Fin 3) : (p i - q i) ^ 2 ≤ sqDist p q := sq_axis_le_sqDist p q i

-- the design project's contract: the scan as a candidate, and recall@k
section Workbench
open Workbench
/-- Four points, two of them equal (indices 1 and 3), both at squared distance 1 from the origin. -/
def wps : List (Point 2 ℤ) := [p2 3 0, p2 1 0, p2 0 2, p2 1 0]
example : reference.query 2 (p2 0 0) (reference.build wps) = [⟨1, 1⟩, ⟨1, 3⟩] := by decide
example : (reference.queryM 2 (p2 0 0) (reference.build wps)).time = 4 := by decide
example : reference.query 9 (p2 0 0) (reference.build ([] : List (Point 2 ℤ))) = [] := by decide
-- equal points are distinct indices: either order of the two copies has recall 1
example : recallAt 2 wps (p2 0 0) [⟨1, 3⟩, ⟨1, 1⟩] = 1 := by decide +kernel
example : recallAt 2 wps (p2 0 0) [⟨1, 1⟩, ⟨9, 0⟩] = 1 / 2 := by decide +kernel
example : recallAt 2 wps (p2 0 0) [] = 0 := by decide +kernel
-- a tie at the k-th distance counts whichever point is answered
example : recallAt 2 [p2 1 0, p2 0 1, p2 (-1) 0] (p2 0 0) [⟨1, 2⟩, ⟨1, 1⟩] = 1 := by decide +kernel
-- nothing wanted: no points, or k = 0
example : recallAt 3 ([] : List (Point 2 ℤ)) (p2 0 0) [] = 1 := by decide +kernel
example : recallAt 0 wps (p2 0 0) [] = 1 := by decide +kernel
-- each piece of the contract, holding and failing
example : UpToK 2 [(⟨1, 1⟩ : Neighbor ℤ), ⟨1, 3⟩] ∧ ¬ UpToK 1 [(⟨1, 1⟩ : Neighbor ℤ), ⟨1, 3⟩] := by
  decide
example : Stored wps [⟨1, 3⟩] ∧ ¬ Stored wps [⟨0, 4⟩] := by decide
example : EachOnce [(⟨1, 1⟩ : Neighbor ℤ), ⟨1, 3⟩] ∧
    ¬ EachOnce [(⟨1, 1⟩ : Neighbor ℤ), ⟨1, 1⟩] := by decide
example : NearestFirst [(⟨1, 1⟩ : Neighbor ℤ), ⟨4, 2⟩] ∧
    ¬ NearestFirst [(⟨4, 2⟩ : Neighbor ℤ), ⟨1, 1⟩] := by decide
example : ExactDistance wps (p2 0 0) [⟨1, 1⟩] ∧ ¬ ExactDistance wps (p2 0 0) [⟨2, 1⟩] := by decide
-- an index past the points has no distance: one that would read the origin is not exact
example : ¬ ExactDistance wps (p2 0 0) [⟨0, 7⟩] := by decide
-- the contract, at the integers
example : Contract (reference : Ops 2 ℤ (List (Point 2 ℤ))) := reference_contract
end Workbench

end AlgoDesignTests
