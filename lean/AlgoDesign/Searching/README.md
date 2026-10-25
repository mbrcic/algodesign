# Lean data-structure formalizations

These modules accompany the Search chapter of *Modern Algorithm Design*. They consume CSLib's
public APIs, including `Cslib.Algorithms.Lean.TimeM`, and live in the independent `AlgoDesign`
namespace.

A cost bound and an operation-correctness theorem guarantee different things; each docstring
says which one it states.

## Development checks

From `lean/` run `lake build`, `lake env lean CheckAxioms.lean`, and
`lake env lean -DwarningAsError=true` on each chapter's regression file,
`AlgoDesignTests/Searching.lean`, `AlgoDesignTests/Strings.lean`,
`AlgoDesignTests/Geometry.lean` and `AlgoDesignTests/Graphs.lean`. The axiom check
rejects proof admissions and nonstandard axioms in every declaration an `AlgoDesign`
module defines, and in their dependencies. Unproved goals stay out of the exported API.
The regression files record specification counterexamples and boundary cases.

## Layout

A structure with a specification and several operations to prove against it is a folder behind a
thin umbrella, and no file passes Mathlib's 1500-line limit: `BTree.lean` only imports
`BTree/*.lean`, so `import AlgoDesign.Searching.BTree` imports the whole structure. Small cohesive modules
(`BinarySearch`, `SequentialSearch`, `RangeQuery`) stay single files.
`Spec.lean` is what an implementation must meet — the type, what it holds, the invariant and its
parts, and for the boxed trees the contract (`Ops`, `Contract`) — and holds no algorithm. The boxed
trees' per-operation obligations (`InsertSpec`, `DeleteSpec`) sit with their operation, as the
steps their `Promise` is assembled from; the unboxed treap keeps its obligations in `Spec.lean`.
It is named for what the book teaches, that the specification comes first and the implementation
must meet it. Each
operation's file (`Search.lean`, `Insert.lean`, `Delete.lean`, …) holds the algorithm and the
theorem that it meets its obligation, `Basic.lean` the lemmas several of them share,
`Cost.lean` the `TimeM` counts, and `Decide.lean` the `Decidable` instances of `Valid` and its
pieces. `lean/AlgoDesign/Strings/` follows the same convention.

## Where each box line is proved

Each boxed tree's `Spec.lean` ends with its `Contract`, and its umbrella proves the library meets
it (`BST.contract`, `LLRB.contract`, `BTree.contract`, `LSM.contract`). The theorems behind them:

- **BST.** Promise: `SearchTree.Promise.of_mem` from `sorted_insert`, `sorted_delete`
  (`Insert.lean`, `Delete.lean`); the order queries `ceiling?_correct`, `ceiling?_eq_none`
  (`Search.lean`); `sorted_deleteHibbard` for Hibbard's delete. Cost: `time_searchM_le_height`,
  `time_insertM_le_height` (`Cost.lean`) and `BST.within_size`; delete's comparisons argued,
  `DeleteCost` (`Delete.lean`). Random order: `internalPathLength_eq` (`Analysis.lean`).
- **LLRB.** Promise: from `valid_insert` (`Insert.lean`), `valid_deleteTop`, `mem_deleteTop_iff`
  (`Delete.lean`), `sorted_toList` (`Search.lean`). Cost: `height_le_two_log` (`Balance.lean`),
  `time_searchM_le_two_log`, `time_insertM_le_two_log` (`Cost.lean`),
  `time_deleteTopRot_le_height` (`Rotations.lean`); delete's comparisons argued, `DeleteCost`
  (`Delete.lean`), and with it the shared target, `LLRB.logarithmic_of_deleteCost`. One shape per
  2-3 tree: `T23.toLlrb_injective`, `T23.exists_twoThree_of_llrbColors`
  (`TwoThree/Encoding.lean`).
- **B-tree.** Promise: from `insertSpec` (`Insert.lean`), `deleteSpec` (`Delete.lean`),
  `sorted_toList` (`Search.lean`); `occupancy_bounds`, `two_mul_pow_height_le_size_succ`
  (`Balance.lean`). Cost: `time_searchM_le_log`, `time_deleteM_le_log` (`Cost.lean`),
  `time_insertM_le_log` (`Insert.lean`); reads and writes apart, `searchIO_le_log`,
  `insertIO_le_log`, `deleteIO_le_log` (`IO.lean`); the lower bound, `decisionTree_depth_ge`
  (`Cost.lean`); the shared target, `BTree.logarithmic`.
- **LSM-tree.** Promise: `Store.get_empty`, `Store.get_write_self`, `Store.get_write_other`,
  `Store.get_delete_self`, `Store.get_delete_other` (`Flush.lean`); `Store.valid_empty`,
  `Store.wellFormed_empty`, `Store.valid_write`, `Store.valid_delete`, and every store the API
  builds is valid and well formed, with its memtable within capacity, `Store.valid_of_reachable` (`Invariant.lean`). Flush and full compaction, outside the box:
  `Store.preservesGet_flush`, `Store.preservesGet_compactFully`, `Store.valid_flush`,
  `Store.valid_compactFully`, `Store.memtable_flush`, `Store.compactFully_one_run`, and the shape
  kept, `Store.shape_write`, `Store.shape_flush`, `Store.shape_compactFully` (`Flush.lean`,
  `Invariant.lean`). Cost: `Store.time_getM_le` (`Cost.lean`); a write's rewrites argued,
  `WriteRewrites` (`Cost.lean`).
