# Lean string algorithms

These modules accompany the Strings chapter of *Modern Algorithm Design*. They follow the layout of
`lean/AlgoDesign/Searching/`: each structure or algorithm is a folder whose `Spec.lean` states the
contract — the inputs, what they mean, the invariant `Valid` in the structure's or algorithm's own
namespace, and what the operations owe — and holds no algorithm. The other files of the folder
hold the algorithms and the theorems that they meet the contract, `Cost.lean` the `TimeM` counts,
and a thin umbrella `X.lean` imports the whole folder. The table lists, per folder, what each file
holds and the main theorems.

| Folder | Specification (`Spec.lean`) | Algorithm files | Correctness | Running state (`Valid`) | Cost |
|---|---|---|---|---|---|
| `RabinKarp/` | `fingerprint`, `candidateCount`, `RabinKarp.Scan`, `RabinKarp.Valid`, `RabinKarp.Contract` | `Decide`, `Search` (`WindowRule`, `Scan.first`, `Scan.next`), `Collision` (`RarelyEqual`), `Expected` | `RabinKarp.contract` (umbrella), `rabinKarpSearch_eq_occurrenceList`, `rabinKarpSearch_pairwise_lt` (increasing order, beyond the promise), `rabinKarpSearch_eq_run`, `RabinKarp.mem_run`, `rarelyEqual_fingerprint`, `collision_fraction_le`, `avg_falseAlarms_le` | `RabinKarp.Valid` on a `Scan` (`NumberMatchesWindow ∧ FoundSoFarExact`; `valid_first`, `valid_roll`, `run_roll`, `found_append_run`) | `Cost`: `time_rabinKarpSearchM`, `WindowRule.time_rollM_le` (one slide in a fixed number of steps); `Expected`: `avg_time_rabinKarpSearchM_le` |
| `Trie/` | `Trie.Valid` (`DistinctLetters ∧ NoDeadBranches`), `Trie.Contract` | `Insert` (`InsertSpec`), `Remove`, `Query` | `Trie.contract` (umbrella), `get_insert`, `get_remove`, `keysWithPrefix_perm`, `longestPrefix_eq_some_iff` | — | `Cost`: `Trie.time_getM_le`, `Trie.time_insertM`, `Trie.time_removeM_le`, `Trie.nodeCount_le` |
| `Patricia/` | `Patricia.Valid` (`DistinctFirstLetters ∧ BranchesUnlessWordEnds ∧ NoEmptyBranches`), `Patricia.Contract` | `Insert` (`InsertSpec`), `Compress`, `Build`, `Remove`, `Sorted`, `Query` | `Patricia.contract` (umbrella), `get_ofTrie`, `get_remove`, `valid_remove`, `keysWithPrefix_perm`; sorted child order, not in `Valid`: `SortedHeads`, `get_sortTree`, `insertSpec_insertSorted` | — | `Cost`: `Patricia.time_getM_le`, `Patricia.nodeCount_le` |
| `SuffixArray/` | `SuffixArray` (`text`, `positions`), `SuffixArray.Valid`, `SuffixArray.Contract` | `Decide`, `Basic`, `Build` (`Doubling`), `Search` (`Bisect`), `LCP` (`lcpEntry`, `Kasai`) | `SuffixArray.contract` (umbrella), `valid_suffixArray`, `suffixArrayEarly_eq`, `search_eq_filter`, `mem_search_iff`, `time_searchM_le`, `kasai_eq` | `Doubling.Valid`, `Bisect.Valid`, `Kasai.Valid` | none |
| `BWT/` | `Transform` (`text`, `letters`), `BWT.Valid`, `Terminated`, `BWT.Contract` | `Decide`, `Rotations`, `Invert` (`LFWalk`, `RowInTable`) | `BWT.contract` (umbrella); the rejection of a text without one final `$` is tested, the Rust's `bwt::try_encode` and the Python's `bwt.encode`; `bwt_eq_rotations`, `invertBwt_bwt`, `saOf_bwtOfSa`, `valid_bwtOfSa` | `LFWalk.Valid` on an `LFWalk.Walk` | none |
| `RankSelect/` | `rank`, `select`, `occ`, `Directory.Valid` | `Basic`, `Directory` | `rank_select`, `select_eq_some_iff`, `occ_eq_rank`, `rankTwoLevel_eq`, `occTwoLevel_eq` | the directory's build loop keeps `Directory.Valid` | none |
| `FMIndex/` | `FMIndex`, `FMIndex.text` (without its `$`), `FMIndex.Valid`, `FMIndex.Contract` (both boxes, on `Occurrences.Promise`), `BackwardSearch.Stretch`, `BackwardSearch.StretchHoldsMatches`; `FMIndex` holds the parts the Rust `FmIndex` and the Python `FMIndex` keep, and `alphabetOf` is the Rust's `Alphabet::of` | `Decide`, `Search` (`matchCount`, `lexBelow`, `BackwardSearch.Valid`), `Sampled` (`SampledLocate.Walk`), `Alphabet`, `Parts`, `Sufficient` | `FMIndex.contract` (umbrella), `FMIndex.build_sample` (umbrella: the build keeps the interval asked for), `backwardSearch_spec`, `fmCount_eq`, `fmLocate_perm`, `fmExtract_eq`, `locateSampled_eq`, `FMIndex.valid_build`, `positionOf_of_valid`, `backwardSearch_spec_of_valid`, `FMIndex.count_of_valid`, `FMIndex.locate_perm_of_valid`, `keptPositionsCorrect_iff` | `BackwardSearch.Valid` on a `Stretch`, `SampledLocate.Valid` on a `Walk` | `Cost`: `time_backwardSearchM`; `Sampled`: `time_locateSampledM_le`; `Sufficient`: `FMIndex.time_locateM_le` |
| `Records/` | `Records.Valid`, `Corpus.WellFormed`, `FindSpec`, `QuoteSpec` | `Quote`, `Corpus` | `recordBounds_contains`, `findObligation`, `quoteObligation` | — | none |

`WordMap.lean` is the trie's promise, the one contract the trie and Patricia boxes share ("Promise:
the trie's"), as `Searching/SearchTree.lean` is the search tree's: each umbrella proves its `Contract`,
promise included (`Trie.contract`, `Patricia.contract`).

The hypotheses the theorems carry are stated in each `Spec.lean`: `Terminated t s` (a sentinel
that is the text's last and smallest character) for the BWT and the FM-index, `s ∉ p.dropLast`
(the sentinel only as the pattern's last character) for backward search on the text with its `$`, `0 < m` for Rabin–Karp,
and `0 < B`, `0 < k` for the rank directory.
