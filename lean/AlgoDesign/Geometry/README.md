# Lean geometry and high-dimensional search

These modules accompany the Geometry chapter of *Modern Algorithm Design*. They follow the layout
of `lean/AlgoDesign/Searching/`: each structure is a folder whose `Spec.lean` quotes its design box
and states the contract — the structure, its invariant `Valid` in the structure's own namespace,
and what the operations owe — and holds no algorithm. The other files of the folder hold the
algorithms and the theorems that they meet the contract, `Cost.lean` the `TimeM` counts, and a thin
umbrella `X.lean` imports the whole folder and proves `contract`. Small modules stay single files.

Coordinates are in any ordered commutative ring (the reals, the rationals, the integers), so each
theorem is about the chapter's real points; distances are squared, so no square roots appear.
Tests compute at `ℤ`. The Rust and the Python work over `f64`, whose rounding is a representation
difference, not a different algorithm.

| Module | Specification | Algorithm files | Correctness | `Valid` | Cost |
|---|---|---|---|---|---|
| `Point` | `Point`, `sqDist` | (the definitions) | `sqDist_comm`, `sqDist_nonneg`, `sq_axis_le_sqDist` | — | none |
| `Scan` | the least squared distance, lowest index on ties | `scanNearest` (one pass, strict `<`) | `scanNearest_isSome_iff`, `scanNearest_mem`, `scanNearest_le`, `scanNearest_lowest` | `ScanInv`, the running scan's | none |
| `Orientation` | collinearity (`∃ k m`, scaled multiples) | `orient` (2×2 determinant) | `orient_swap`, `orient_cycle`, `orient_self_left`, `orient_eq_zero_iff` (for `a ≠ b`) | — | none |
| `Nearest` | the scan's promise: `Nearest.Answers` over a stored list, `Nearest.Promise` for every build; `InRectangle`, `dists` | (the contract) | `Nearest.Promise.build_nil` | — | none |
| `RangeTree/` | `RangeTree1D.Valid` (`KeysSeparate ∧ SplitsHalve`), `InStrip`, `RangeTree1D.Contract`; `RangeTree2D` and `RangeTree2D.Query2DSpec` | `Build` (`ofList`: sort, then split at the lower median), `Query`, `Cost`, `Query2D` (the 2D build and query), `Cost2D` (the 2D walk the Rust and the Python run, counted) | `RangeTree1D.contract` (umbrella), `query_eq_filter`, `RangeTree2D.query_build`, `RangeTree2D.queryM_spec`, `leaves_ofList`, `valid_ofList`, `keysSeparate_build`, `splitsHalve_build`, `ret_queryM` | — | `time_queryM_le`: `2 ⌈log₂ n⌉ + k + 1` ticks; 2D: `RangeTree2D.time_queryM_le`, `4 ⌈log₂ n⌉ (⌈log₂ n⌉ + 1) + k + 1` ticks |
| `KDTree/` | `KDTree.Valid` (`CutsSeparate ∧ CutsHalve`), `KDTree.Contract` (on `Nearest.Promise`) | `Build`, `Prune`, `Range`, `Search` (best-first search, `kNearest`, `nearest`) | `KDTree.contract` (umbrella), `KDTree.answers_of_valid`, `valid_build`, `points_build`, `rangeQuery_perm_filter`, `BestFirst.search_nearest`, `BestFirst.search_kNearest_eq_scan`, `head?_dists` | `BestFirst.Valid` on a `BestFirst.Run` (`NothingCloserSkipped ∧ QueuedCutsSeparate ∧ OffsetsBound ∧ EachPointOnce`; `valid_start`, `valid_visit`, `nothingCloserSkipped_of_offsetsBound_eachPointOnce`) | none (measured) |
| `LSH/` | `LSH.Valid` (`InItsBucket`), `LSH.WellFormed` (`OneBucketPerKey ∧ EachPointOncePerTable`), `MeasuredExactly` on an `Answer`, `LSH.Contract` | `Families`, `Rerank` (`LSH.candidates`, `LSH.lshQuery`, on the fly), `Build`, `Query` (`nearest`, `kNearest`, `NearestFirst`), `Cost` | `LSH.contract` (umbrella), `LSH.valid_build`, `LSH.measuredExactly_nearest`, `LSH.measuredExactly_kNearest`, `LSH.nearestFirst_kNearest`, `LSH.nearest_eq_lshQuery`, `LSH.nearest_eq_scanNearest`, `LSH.lshQuery_eq_scanNearest`, `simBit_eq_orient`, `pStableKey_eq` | — | `LSH.time_nearestM`: a key per table plus a distance per candidate; `LSH.entries_length` |
| `GraphIndex/` | `HNSW.Valid` on a graph carrying its caps and points (`DegreeBounded ∧ NestedLayers`), `HNSW.WellFormed` (`NoSelfLinks ∧ NoRepeatedLinks ∧ EntryOnTop ∧ OneNodePerPoint`), `PicksDiverse` on a `Picking`, `HNSW.Promise`, `HNSW.Contract`, `HNSW.Ops.WalksToBeam` (proved, `HNSW.searchSpec`; a separate Lean–Rust check also checks the walk and its last step on the Rust's searches) | `Select` (`HNSW.selectNeighbors`), `Greedy` (`HNSW.greedyStep`), `Finish` (`HNSW.finish`), `Search` (`HNSW.search`, `HNSW.searchLayer`), `Insert` (`HNSW.insert`), `Cost` | `HNSW.contract` and `HNSW.searchSpec` (umbrella), `HNSW.search_eq_finish`, `HNSW.valid_insert`, `HNSW.valid_build`, `HNSW.points_insert`, `HNSW.picksDiverse_selectNeighbors`, `HNSW.picks_insert`, `HNSW.promise_finish`, `HNSW.greedyStep_le`, `HNSW.searchLayer_one` | — | `HNSW.linksPerPointAtMost_of_valid` (memory) |
| `Workbench/` | the design project's contract: `UpToK`, `Stored`, `EachOnce`, `NearestFirst`, `ExactDistance`, `recallAt`, `Workbench.Contract` | `Workbench.lean` (the scan as a candidate, `reference`) | `reference_contract`, `reference_recall`, `recall_eq_one_of_scan` | — | `time_referenceM`: one tick per stored point |

The hypotheses the theorems carry are stated in each `Spec.lean`: `m ≤ m0` and `CandidatesOk` for
`HNSW.valid_insert`, candidates nearest first for `HNSW.picksDiverse_selectNeighbors`, a beam of
stored nodes, each once, for `HNSW.promise_finish`, and `0 < w` for the p-stable family.

No module states a search guarantee for the graph index: none exists for the variant the library
ships. `HNSW.greedyStep_le` says a step never moves away from the query, not that the walk reaches
the nearest neighbor; `HNSW.searchLayer_one` proves that the layer search with a beam of one, the
descent's step, is the greedy walk, ties included.

## Where each box line is proved

Each boxed structure's `Spec.lean` ends with its `Valid` and its `Contract`, and its umbrella
proves the library meets it (`RangeTree1D.contract`, `KDTree.contract`, `LSH.contract`,
`HNSW.contract`; the design project's `reference_contract`). The `Decidable` instances of each
invariant are in the folder's `Decide.lean`. The theorems behind them:

- **Range tree.** Promise: `query_eq_filter` (`Query.lean`), on a valid tree the stored keys
  inside `[lo, hi]` (`InStrip`), in order and with multiplicity; `leaves_ofList` (`Build.lean`),
  the build stores exactly the keys it was given, sorted, and `ofList_eq_none`, nothing from no
  keys. Invariants: `keysSeparate_build`, `splitsHalve_build`, `valid_ofList` (`Build.lean`).
  Cost: `queryM` (`Cost.lean`) is dBCKO's walk to the split node and down its two sides, one tick
  per node on those paths and one per point reported; `time_queryM_le`, at most
  `2 ⌈log₂ n⌉ + k + 1` ticks, from `height_le_clog` (invariant 2 keeps the tree `⌈log₂ n⌉`
  tall); `ret_queryM`, the counted query answers as the query does on a tree whose keys
  separate. The Idea's "each subtree can carry its own tree on the other coordinate" is the 2D
  range tree, `RangeTree2D` (`Query2D.lean`), which the Rust and the Python ship: its query's
  obligation `RangeTree2D.Query2DSpec`, proved of the Lean build and query by
  `RangeTree2D.query_build` (`Query2D.lean`), and of the walk the Rust and the Python run,
  counted, by `RangeTree2D.queryM_spec`; its cost, `O(log² n + k)`, is
  `RangeTree2D.time_queryM_le` (`Cost2D.lean`), at most `4 ⌈log₂ n⌉ (⌈log₂ n⌉ + 1) + k + 1`
  ticks, each node on the walk's two paths paying for one query of its associated tree. The
  Rust's property test of the 2D query against a filter of the points and a separate Rust–Python
  check of 2D query answers hold the Rust
  and the Python to it. The points are in the leaves; each inner node holds a split
  key, the lower median of the keys below it. Repeated keys are allowed: copies of a split key
  may sit on both sides, and the query still reports every copy. The build sorts the keys first,
  as the Rust's `RangeTree1D::new` does, so it takes them in any order.
- **k-d tree.** Promise: the scan's, `Nearest.Promise`, on every tree the build makes, and the
  same answers on every valid tree, built or not (`KDTree.answers_of_valid`): the nearest point
  answered is a stored point at the least squared distance, the first of the scan's ranking
  `dists`; the $k$ nearest are, in order, the $k$ least squared distances; the rectangle query
  reports exactly the stored points inside, as a permutation of the input's filter; built over no
  points, the tree answers nothing (`Nearest.Promise.build_nil`). Behind it:
  `BestFirst.search_nearest`, `BestFirst.search_kNearest_eq_scan` (`Search.lean`),
  `rangeQuery_perm_filter` (`Range.lean`), `head?_dists` (`Search.lean`). What the Lean does not
  state is tested: the tie rule (the Rust and the Python answer with ids and break ties by the
  lowest; the Lean leaf holds a point, not an id), and leaves of more than one point (the Rust's
  default bucket is 8; the Lean leaf holds one), by the Rust's tests
  `best_first_is_the_scan` and `best_first_is_the_scan_on_real_coordinates` and a separate
  Lean–Rust check of nearest points at buckets 1 and 8. Invariants: `valid_build` (`Build.lean`),
  which also gives
  `points_build`; invariant 3, `BestFirst.NothingCloserSkipped` on a run of the search
  (`BestFirst.Run`: the tree, the query and the running state), is kept by `BestFirst.valid_start`,
  `BestFirst.valid_visit` and `BestFirst.valid_run` (`Search.lean`), inside the run's
  `BestFirst.Valid` (`Search.lean`) with three pieces not in the box,
  `BestFirst.QueuedCutsSeparate`, `BestFirst.OffsetsBound` and `BestFirst.EachPointOnce`; the last
  two alone give invariant 3, `BestFirst.nothingCloserSkipped_of_offsetsBound_eachPointOnce`.
  Invariant 1 also gives `rangeQuery_eq_filter` (`Range.lean`); the pruning facts
  `far_side_bound`, `far_side_bound_left` and `boxSqDist_le` (`Prune.lean`) need no invariant.
  Cost: measured, the k-d tree's leaf-size measurement in the chapter; Lean states no cost for
  the k-d tree. Assumes: the collapse curve in the chapter varies the dimension the
  points are stated in (uniform data, whose real dimension is that, and GloVe projected), not
  their real dimension on its own; "slower, never wrong" is the answer theorems above, in every
  dimension from one up (`d ≠ 0`, which the build needs for an axis to cut). The points are
  stored in the leaves, one per leaf: the tree the Rust and the Python build with a bucket of 1.
  Each inner node holds an axis and a split value, the cut; the points on the left have that
  coordinate `≤` the split, and those on the right `≥` it. The build cycles the axis with the
  depth and splits at the lower median of the points below; `CutsHalve` states the halving the
  lower median gives, and the axis cycle is how the build chooses, not something the box asks of
  a tree, so `Valid` does not hold it. dBCKO assume no two points share a coordinate and remove
  the assumption with composite numbers (§5.5); here the invariant allows repeats, and every query
  still finds a point whose coordinate equals the split. Asked for no neighbors ($k = 0$), the
  search measures nothing, as the Rust and the Python answer nothing.
- **LSH.** Every statement holds for any hash family. Goal: a query reads one stored bucket per
  table and measures only the candidates it finds there (`LSH.nearest`); "among millions, in
  hundreds of dimensions" is the LSH measurement on GloVe-100 (1 183 514 points) in
  the chapter, the share of the data a query measures beside its recall. Promise:
  `MeasuredExactly` at one answer, `LSH.measuredExactly_nearest`, and at `k`,
  `LSH.measuredExactly_kNearest`; when the true nearest is a candidate the answer is the scan's on
  every valid index, `LSH.nearest_eq_scanNearest`, its lowest-index tie rule included; the build
  stores the points, `LSH.build_stores`. On a valid index the stored-bucket query is the on-the-fly
  re-rank of `Rerank.lean` (`LSH.nearest_eq_lshQuery`), so `lshQuery_le_candidates`,
  `lshQuery_exact_of_collision` and `lshQuery_eq_scanNearest` carry over. The probability
  `1 − (1 − (1 − θ/π)^K)^L` is over the random cuts, which this Lean, having no measure theory,
  does not state; a seeded statistical test of the Rust holds the one-cut
  rate `1 − θ/π` it is built from, and the rest follows from the cuts being drawn independently.
  Idea: `simBit`, `simKey` (`Families.lean`), and `simBit_eq_orient`, in the plane the bit is the
  orientation test; the p-stable family, the grid on a line, is `pStableKey` with `pStableKey_eq`
  (one cell, shadows less than a cell apart). Invariants: every index the build makes is valid,
  `LSH.valid_build`; `OneBucketPerKey` holds of the Rust's and the Python's maps for free.
  Cost: `LSH.nearestM` ticks once per table, for the key it computes, and once per candidate it
  hands to the exact ranking (`LSH.time_nearestM`), and answers as `LSH.nearest` does
  (`LSH.ret_nearestM`); one entry per point per table, `LSH.entries_length`; the candidate counts
  and build memory of real runs are in the chapter's LSH measurements. Assumes: what
  randomness buys, that near points collide more often (`1 − θ/π` for SimHash, Datar et al.'s
  rate for p-stable), is held by seeded statistical tests of the Rust's collision rates; "the
  answer is a farther point" is never nearer than the scan's answer, `scanNearest_le`; recall is
  the recall@10 the chapter measures for LSH. The model: an index holds the points
  and, per table, its hash function and its buckets, each a key with the indices of the points
  stored under it, in insertion order; `Build.lean` fills one, `Query.lean` reads candidates from
  the stored buckets and ranks them exactly.
- **Graph index.** Promise: the last step, `promise_finish` (`Finish.lean`): on a beam of stored
  nodes, each once, `HNSW.finish` returns `min k` of the beam's points, each once, each a stored
  point with its exact squared distance, sorted nearest first (ties by index), with nothing left
  out nearer than what is reported. The walk that fills the beam: `Ops.WalksToBeam`, proved of
  `HNSW.search` (`Search.lean`, the greedy descent and then the layer search on layer 0, as the
  Rust runs it) by `searchSpec` (`GraphIndex.lean`). Insertion: `points_insert`, `caps_insert`.
  Idea: `greedyStep` never moves away (`greedyStep_le`, `Greedy.lean`), and the beam at width 1
  moves as greedy steps do (`searchLayer_one`, `Search.lean`). Invariants: `valid_empty`,
  `valid_insert` and `valid_build` (`Insert.lean`), at caps with `m ≤ m0`, for any candidates the
  layer search returns that are stored nodes on their layer (`CandidatesOk`); the picking rule
  meets invariant 2, `picksDiverse_selectNeighbors` (`Select.lean`), with
  `selectNeighbors_diverse`, `selectNeighbors_length_le`, `selectNeighbors_subset`,
  `selectNeighbors_head`; the insertion runs it on indices (`selectIds_map`) on every new node's
  list and on every list a back-link overfills. A back-link added while a list has room is not a
  picking, so invariant 2 is a check on the picking step, `Picking.Valid` (`Select.lean`), not on
  the stored graph. "Each layer up keeps a random few of the one below" is tested: the layer draw
  `⌊−ln u · m_L⌋`, `m_L = 1/ln M`, puts a node above layer 0 with probability `1/M`
  (`hnsw::tests::levels_thin_out_by_m`). Cost: per query, the HNSW table in
  the chapter; memory, `linksPerPointAtMost_of_valid` (`Cost.lean`), at most
  `m0 + m · (layers - 1)` links per node on every `Valid` graph. Assumes: recall against the scan,
  `hnsw::tests::recall_against_the_scan` and the HNSW table in the chapter.
- **Design project.** Promise: `reference_contract`, the scan meets the contract; recall:
  `recallAt` (`Workbench.lean`) defines the share against the scan's distances `dists`; the
  threshold and the places nobody tuned for are the bench's
  (`python/algodesign/geometry/workbench.py`, hidden seeds); `recall_eq_one_of_scan`, an answer
  keeping the contract whose distances are the scan's has recall 1, and `reference_recall`. Cost: the ticks are the operation's own count, so a
  wrapper that counts nothing meets any bound on them (as `SearchTree.Within` says); the number to
  beat is proved, one tick per stored point, `time_referenceM`. An answer is a list of
  `Neighbor`s, each a squared distance and the id of a stored point, so "each once" means each
  stored place once, even when two places are equal.
