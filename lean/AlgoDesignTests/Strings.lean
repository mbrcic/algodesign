import AlgoDesign
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Regression checks for the Strings chapter's public specifications. Run with
`lake env lean -DwarningAsError=true AlgoDesignTests/Strings.lean`. -/
namespace AlgoDesignTests
open AlgoDesign.Searching

open AlgoDesign.Strings in
-- base 10, modulus 13: the chapter's trace parameters, where 40259 and 65947 both have
-- fingerprint 11.
example : rabinKarpSearch 10 13 [4,0,2,5,9,2,1,9,6,5,9,4,7] [0,2,5,9] = [1] := by decide
open AlgoDesign.Strings in
example : rabinKarpSearch 10 13 [6,5,9,4,7] [5,9] = occurrenceList [6,5,9,4,7] [5,9] := by decide

-- The chapter's hand trace, digit for digit: text 1767640259219659478, pattern 40259, base 10,
-- mod 13. The occurrence at position 5 is found by rolling, and the window 65947 at position 13
-- is a false alarm that verification rejects.
private def bookTrace : List Nat := [1,7,6,7,6,4,0,2,5,9,2,1,9,6,5,9,4,7,8]
open AlgoDesign.Strings in
example : highPower 10 13 5 = 3 := by decide
open AlgoDesign.Strings in
-- The window 40259 has value 11; sliding to 02592 gives (11 - 4·3)·10 + 2 ≡ 5.
example : rollHash 10 13 (highPower 10 13 5) 11 4 2 = 5 := by decide
open AlgoDesign.Strings in
example : fingerprint 10 13 [4,0,2,5,9] = 11 ∧ fingerprint 10 13 [6,5,9,4,7] = 11 := by decide
open AlgoDesign.Strings in
-- The value the search carries into position 13, rolled thirteen times from the first window:
-- the collision the scan meets there is the one the chapter shows.
example : (List.range 13).foldl (fun h i => rollHash 10 13 (highPower 10 13 5) h
    bookTrace[i]! bookTrace[i + 5]!) (fingerprint 10 13 (bookTrace.take 5)) = 11 := by decide
open AlgoDesign.Strings in
example : rabinKarpSearch 10 13 bookTrace [4,0,2,5,9] = [5] := by decide
open AlgoDesign.Strings in
-- The regression the rolling lemma guards: the same scan run with the leaving character weighted
-- `base ^ k` instead of `base ^ (k - 1)` misses the true occurrence at 5.
example : scan 10 13 (10 ^ 5 % 13) 5 (fingerprint 10 13 [4,0,2,5,9]) [4,0,2,5,9] 0
    (fingerprint 10 13 (bookTrace.take 5)) bookTrace = [] := by decide
open AlgoDesign.Strings in
-- The empty pattern occurs at every shift 0 … n, as in the Rust's `naive::search`.
example : rabinKarpSearch 10 13 [1,2] [] = [0,1,2] ∧ occurrenceList [1,2] [] = [0,1,2] := by decide

-- Tries: the key is the path. Two words sharing a prefix coexist, a prefix of a stored key is
-- not itself stored, and `words` lists exactly the value-carrying nodes.
open AlgoDesign.Strings in
example : (Trie.insert (Trie.insert Trie.empty [1,2] 7) [1,3] 9).get [1,2] = some 7 := by decide
open AlgoDesign.Strings in
example : (Trie.insert Trie.empty [1,2] 7).get [1] = (none : Option Nat) := by decide
open AlgoDesign.Strings in
example : (Trie.insert (Trie.insert Trie.empty [1] 1) [1,2] 2).words.length = 2 := by decide

-- The chapter's five words (she, shells, sea, shore, seashore), inserted in its order, and its
-- `keys_with_prefix` examples: `sh` gives she, shells and shore; `se` gives sea and seashore; `x`
-- fails at the first letter. The answers come out in byte order, a key before every longer key it
-- begins, whatever order the words arrived in.
open AlgoDesign.Strings in
private def fiveWords : Trie Nat :=
  [([115,104,101], 0), ([115,104,101,108,108,115], 1), ([115,101,97], 2),
    ([115,104,111,114,101], 3), ([115,101,97,115,104,111,114,101], 4)].foldl
    (fun t p => Trie.insert t p.1 p.2) Trie.empty
open AlgoDesign.Strings in
example : Trie.keysWithPrefix fiveWords [115,104] =
    [[115,104,101], [115,104,101,108,108,115], [115,104,111,114,101]] := by decide
open AlgoDesign.Strings in
example : Trie.keysWithPrefix fiveWords [115,101] =
    [[115,101,97], [115,101,97,115,104,111,114,101]] := by decide
open AlgoDesign.Strings in
example : Trie.keysWithPrefix fiveWords [120] = [] := by decide
open AlgoDesign.Strings in
example : Trie.keysWithPrefix fiveWords [] = [[115,101,97], [115,101,97,115,104,111,114,101],
    [115,104,101], [115,104,101,108,108,115], [115,104,111,114,101]] := by decide
-- `get` is lookup in the stored map: `sea` is stored with 2, `sh` with nothing.
open AlgoDesign.Strings in
example : Trie.get fiveWords [115,101,97] = some 2 ∧ ([115,101,97], 2) ∈ Trie.toList fiveWords ∧
    Trie.get fiveWords [115,104] = none := by decide
open AlgoDesign.Strings in
example : Trie.keysWithPrefix fiveWords [115,104] =
    [[115,104,101], [115,104,101,108,108,115], [115,104,111,114,101]] ∧
    (Trie.keysWithPrefix fiveWords [115,104]).Perm
      ((Trie.words fiveWords).filter ([115,104].isPrefixOf ·)) :=
  ⟨by decide, Trie.keysWithPrefix_perm _ (by
    simp only [fiveWords, List.foldl]
    repeat apply Trie.distinctLetters_insert
    exact Trie.distinctLetters_empty) _⟩
-- `longest_prefix` on the trie: `shell` is not stored, `she` is the longest stored word it
-- begins with; `seashores` gets `seashore`; `x` gets nothing.
open AlgoDesign.Strings in
example : Trie.longestPrefix fiveWords [115,104,101,108,108] = some [115,104,101] ∧
    Trie.longestPrefix fiveWords [115,101,97,115,104,111,114,101,115] =
      some [115,101,97,115,104,111,114,101] ∧
    Trie.longestPrefix fiveWords [120] = none := by decide
-- `DistinctLetters` is needed by `longestPrefix_eq_some_iff`/`_none_iff` too: the walk takes the
-- first child under 1, which holds nothing, while the second stores [1].
open AlgoDesign.Strings in
example : Trie.longestPrefix (.node none [(1, .node none []), (1, .node (some 0) [])]) [1] = none ∧
    [1] ∈ Trie.words (.node none [(1, .node none []), (1, .node (some 0) [])]) := by decide
-- `DistinctLetters` is needed by both: two children under one symbol, and `get` reads the first
-- while the stored map holds the second too; the prefix query lists the key twice.
open AlgoDesign.Strings in
example : Trie.get (.node none [(1, .node (some 0) []), (1, .node (some 1) [])]) [1] = some 0 ∧
    ([1], 1) ∈ Trie.toList (.node none [(1, .node (some 0) []), (1, .node (some 1) [])]) ∧
    Trie.keysWithPrefix (.node none [(1, .node (some 0) []), (1, .node (some 1) [])]) [] =
      [[1], [1]] := by decide

-- Patricia trees: compression is a representation change. The two words survive it, in order.
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2)).words.length = 2
    := by decide
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2)).words
      = [[1,2,3], [1,2,4]] := by decide
-- What the key list alone cannot show: the shared prefix is now one edge. The two trie nodes for
-- symbols 1 and 2 are gone, and their symbols live in the label `[1,2]`. Note also the shape the
-- root exemption in `BranchesUnlessWordEnds` exists for -- the root here is valueless with exactly
-- one child, and there is no edge above it to merge that child into.
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2))
      = .node none [([1,2], .node none [([3], .node (some 1) []), ([4], .node (some 2) [])])] :=
  rfl

-- Lookup through compression. A stored key is found across the merged edge `[1,2]`; the shared
-- prefix `[1,2]` is not itself a key; and `[1,3]` begins with that edge's first symbol but not its
-- whole label, so `get` answers `none` at the root without descending.
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2)).get [1,2,4]
      = some 2 := by decide
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2)).get [1,2]
      = none := by decide
open AlgoDesign.Strings in
example :
    (Patricia.ofTrie (Trie.insert (Trie.insert Trie.empty [1,2,3] 1) [1,2,4] 2)).get [1,3]
      = none := by decide

-- Patricia insert: `insert` splits an edge at the first mismatch, as the Rust does. The
-- second key diverges from the edge [1,2,3] after [1,2], so a fresh branching node sits there.
open AlgoDesign.Strings in
example : Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2,4] 2
    = .node none [([1,2], .node none [([3], .node (some 1) []), ([4], .node (some 2) [])])] := rfl
-- A key ending inside an edge: the fresh node at the split holds the value itself.
open AlgoDesign.Strings in
example : Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2] 9
    = .node none [([1,2], .node (some 9) [([3], .node (some 1) [])])] := rfl
-- Removal. Removing [1,2,3] leaves the branching node [1,2] valueless with one child, so it is
-- merged into that child (the Rust's `absorb_only_child(parent)`); removing [1,2], a target with
-- one child, merges the target instead; an absent key changes nothing.
open AlgoDesign.Strings in
example : Patricia.remove (Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2,4] 2)
      [1,2,3] = .node none [([1,2,4], .node (some 2) [])] := rfl
open AlgoDesign.Strings in
example : Patricia.remove (Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2] 9)
      [1,2] = .node none [([1,2,3], .node (some 1) [])] := rfl
open AlgoDesign.Strings in
example : Patricia.remove (Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2,4] 2)
      [1,2] = Patricia.insert (Patricia.insert (.node none []) [1,2,3] 1) [1,2,4] 2 := rfl
-- The trie cuts the unshared suffix of the path and stops at the node that still branches.
open AlgoDesign.Strings in
example : Trie.remove (Trie.insert (Trie.insert Trie.empty [1,2,3] 7) [1,4] 8) [1,2,3]
    = Trie.insert Trie.empty [1,4] 8 := rfl
-- The Rust test's word set (she, shells, sea, shore, seashore), then "shell", which ends exactly
-- at the "ll"/"s" boundary inside an edge. Every key keeps its value.
open AlgoDesign.Strings in
private def shells : Patricia Nat :=
  [([115,104,101], 0), ([115,104,101,108,108,115], 1), ([115,101,97], 2),
    ([115,104,111,114,101], 3), ([115,101,97,115,104,111,114,101], 4),
    ([115,104,101,108,108], 99)].foldl (fun t p => Patricia.insert t p.1 p.2) (.node none [])
open AlgoDesign.Strings in
example : shells.get [115,104,101,108,108,115] = some 1 ∧
    shells.get [115,104,101,108,108] = some 99 ∧ shells.get [115,104,101] = some 0 ∧
    shells.get [115,101,97,115,104,111,114,101] = some 4 ∧ shells.get [115,104] = none := by
  decide
open AlgoDesign.Strings in
example : Patricia.Valid shells := Patricia.valid_insert _ _ (Patricia.valid_insert _ _
  (Patricia.valid_insert _ _ (Patricia.valid_insert _ _ (Patricia.valid_insert _ _
    (Patricia.valid_insert _ _ Patricia.valid_empty)))))
-- `keys_with_prefix` on the chapter's five words squeezed. `sh` is a whole branch; `seas` and
-- `sho` end inside a label, and the whole label below them is read; `seax` leaves a label partway
-- along and gets nothing.
open AlgoDesign.Strings in
private def fivePat : Patricia Nat :=
  [([115,104,101], 0), ([115,104,101,108,108,115], 1), ([115,101,97], 2),
    ([115,104,111,114,101], 3), ([115,101,97,115,104,111,114,101], 4)].foldl
    (fun t p => Patricia.insert t p.1 p.2) (.node none [])
open AlgoDesign.Strings in
example : Patricia.keysWithPrefix fivePat [115,104] =
    [[115,104,101], [115,104,101,108,108,115], [115,104,111,114,101]] ∧
    Patricia.keysWithPrefix fivePat [115,101] = [[115,101,97], [115,101,97,115,104,111,114,101]] ∧
    Patricia.keysWithPrefix fivePat [120] = [] := by decide
open AlgoDesign.Strings in
example : Patricia.keysWithPrefix fivePat [115,101,97,115] = [[115,101,97,115,104,111,114,101]] ∧
    Patricia.keysWithPrefix fivePat [115,104,111] = [[115,104,111,114,101]] ∧
    Patricia.keysWithPrefix fivePat [115,101,97,120] = [] := by decide
open AlgoDesign.Strings in
example : (Patricia.keysWithPrefix fivePat [115,104]).Perm
    ((Patricia.words fivePat).filter ([115,104].isPrefixOf ·)) :=
  Patricia.keysWithPrefix_perm _ (by
    simp only [fivePat, List.foldl]
    repeat apply Patricia.valid_insert
    exact Patricia.valid_empty) _
-- `Valid` is needed: with two sibling labels beginning with 1 the descent commits to the first,
-- and the stored key [1,2] is missing from the answer.
open AlgoDesign.Strings in
example : Patricia.keysWithPrefix (.node none [([1], .node none []), ([1,2], .node (some 0) [])])
    [1,2] = [] := by decide

-- The appendix's router: prefixes 1100, 110010 and 1110, as bits. 11001011 walks 11, 00 (a
-- mark), 10 (a mark), and stops: the more specific 110010. 11000111 walks 11, 00, finds no branch
-- for the next 0, and gets 1100. An address beginning 0 gets nothing, the default route.
open AlgoDesign.Strings in
private def routes : Patricia Nat :=
  [([1,1,0,0], 0), ([1,1,0,0,1,0], 1), ([1,1,1,0], 2)].foldl
    (fun t p => Patricia.insert t p.1 p.2) (.node none [])
open AlgoDesign.Strings in
example : routes = .node none [([1,1], .node none [([0,0], .node (some 0) [([1,0], .node (some 1)
    [])]), ([1,0], .node (some 2) [])])] := rfl
open AlgoDesign.Strings in
example : Patricia.longestPrefix routes [1,1,0,0,1,0,1,1] = some [1,1,0,0,1,0] ∧
    Patricia.longestPrefix routes [1,1,0,0,0,1,1,1] = some [1,1,0,0] ∧
    Patricia.longestPrefix routes [0,1,1,0] = none := by decide
-- A key that ends inside a label matches nothing below it; the empty key, once stored, is the
-- answer whenever nothing longer matches.
open AlgoDesign.Strings in
example : Patricia.longestPrefix routes [1,1,0] = none ∧
    Patricia.longestPrefix (Patricia.insert routes [] 9) [0] = some [] := by decide
-- `longestPrefix_eq_some_iff` applied to the router's table.
open AlgoDesign.Strings in
example : Patricia.longestPrefix routes [1,1,0,0,1,0,1,1] = some [1,1,0,0,1,0] ↔
    [1,1,0,0,1,0] ∈ routes.words ∧ [1,1,0,0,1,0] <+: [1,1,0,0,1,0,1,1] ∧
      ∀ q' ∈ routes.words, q' <+: [1,1,0,0,1,0,1,1] → q'.length ≤ [1,1,0,0,1,0].length :=
  Patricia.longestPrefix_eq_some_iff _ (by
    simp only [routes, List.foldl]
    repeat apply Patricia.valid_insert
    exact Patricia.valid_empty) _ _
-- `Valid` is needed for the key-set statement: two sibling labels beginning with 1, and the walk
-- commits to the first, so the stored key [1,2] is never reached.
open AlgoDesign.Strings in
example : [1,2] ∈ Patricia.words (.node none [([1], .node none []), ([1,2], .node (some 0) [])]) ∧
    Patricia.longestPrefix (.node none [([1], .node none []), ([1,2], .node (some 0) [])]) [1,2] =
      none := by decide

-- `Valid`'s conjuncts one at a time. `DistinctFirstLetters` broken alone (box lines 3 and 4 hold):
-- labels 1 and 12 share a head, the walk commits to the first, and the stored 12 is missed by both
-- queries.
open AlgoDesign.Strings in
example : Patricia.BranchesUnlessWordEnds
      (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])] : Patricia Nat) ∧
    Patricia.NoEmptyBranches
      (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])] : Patricia Nat) ∧
    ¬ Patricia.DistinctFirstLetters
      (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])] : Patricia Nat) := by
  decide
open AlgoDesign.Strings in
example : Patricia.longestPrefix (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])])
      [1,2] = some [1] ∧
    Patricia.keysWithPrefix (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])])
      [1,2] = [] ∧
    [1,2] ∈ Patricia.words (.node none [([1], .node (some 1) []), ([1,2], .node (some 0) [])]) := by
  decide
-- `NoEmptyBranches` broken (`DistinctFirstLetters` holds): an empty label begins with nothing, so
-- the walk passes it over, and the stored 5 below it is missed by both queries.
open AlgoDesign.Strings in
example :
    let t : Patricia Nat := .node none [([], .node none [([5], .node (some 0) [])])]
    ¬ Patricia.NoEmptyBranches t ∧ Patricia.DistinctFirstLetters t := by
  decide
open AlgoDesign.Strings in
example :
    Patricia.longestPrefix (.node none [([], .node none [([5], .node (some 0) [])])]) [5] = none ∧
    Patricia.keysWithPrefix (.node none [([], .node none [([5], .node (some 0) [])])]) [5] = [] ∧
    [5] ∈ Patricia.words (.node none [([], .node none [([5], .node (some 0) [])])]) := by decide

-- Patricia trees, the two constructions. The Rust test's word set (she, shells, sea, shore,
-- seashore), then "shell", inserted by splitting edges, is exactly the compression of the trie
-- the same inserts build: labels, values and child order. Were `insert` to file children in any
-- other order than `Trie.insert` does, or split where compression would not merge, this would fail.
open AlgoDesign.Strings in
private def shellsKvs : List (List Nat × Nat) :=
  [([115,104,101], 0), ([115,104,101,108,108,115], 1), ([115,101,97], 2),
    ([115,104,111,114,101], 3), ([115,101,97,115,104,111,114,101], 4), ([115,104,101,108,108], 99)]
open AlgoDesign.Strings in
example : Patricia.ofList shellsKvs
    = Patricia.ofTrie (shellsKvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty) := rfl
open AlgoDesign.Strings in
example : Patricia.ofList shellsKvs
    = .node none [([115], .node none [
        ([104], .node none [
          ([101], .node (some 0) [([108,108], .node (some 99) [([115], .node (some 1) [])])]),
          ([111,114,101], .node (some 3) [])]),
        ([101,97], .node (some 2) [([115,104,111,114,101], .node (some 4) [])])])] := rfl
-- The Rust's insert keeps each child list sorted by first byte: under "s", "ea" (101) now comes
-- before "h" (104), the one place this key set's creation order is not sorted. Everything else is
-- the same tree, as `ofListSorted_eq_ofTrie` says. A Rust-order insert that stopped sorting fails
-- here; one that sorted differently fails the equation with `sortTree` below.
open AlgoDesign.Strings in
example : Patricia.ofListSorted shellsKvs
    = .node none [([115], .node none [
        ([101,97], .node (some 2) [([115,104,111,114,101], .node (some 4) [])]),
        ([104], .node none [
          ([101], .node (some 0) [([108,108], .node (some 99) [([115], .node (some 1) [])])]),
          ([111,114,101], .node (some 3) [])])])] := rfl
open AlgoDesign.Strings in
example : Patricia.ofListSorted shellsKvs = Patricia.sortTree (Patricia.ofList shellsKvs) := rfl
-- A new leaf edge goes to its sorted place, and a split node's two children are sorted: [2] and
-- [3] in both cases, whichever arrived first. The creation-order insert keeps arrival order.
open AlgoDesign.Strings in
example : Patricia.ofListSorted [([3], 0), ([1], 1), ([2], 2)]
    = .node none [([1], .node (some 1) []), ([2], .node (some 2) []), ([3], .node (some 0) [])] :=
  rfl
open AlgoDesign.Strings in
example : Patricia.ofList [([3], 0), ([1], 1), ([2], 2)]
    = .node none [([3], .node (some 0) []), ([1], .node (some 1) []), ([2], .node (some 2) [])] :=
  rfl
open AlgoDesign.Strings in
example : Patricia.ofListSorted [([1,3], 0), ([1,2], 1)]
    = .node none [([1], .node none [([2], .node (some 1) []), ([3], .node (some 0) [])])] := rfl
open AlgoDesign.Strings in
example : Patricia.ofList [([1,3], 0), ([1,2], 1)]
    = .node none [([1], .node none [([3], .node (some 0) []), ([2], .node (some 1) [])])] := rfl
-- `words` under `insert`: the new key joins, nothing leaves, and on a tree built from empty the
-- order is the trie's.
open AlgoDesign.Strings in
example : (Patricia.ofList shellsKvs).words
    = [[115,104,101], [115,104,101,108,108], [115,104,101,108,108,115], [115,104,111,114,101],
        [115,101,97], [115,101,97,115,104,111,114,101]] := by decide
-- Why `insert_ofTrie` asks for `NoDeadBranches`: under a valueless trie leaf, compression merges
-- the edge the new key makes, while `insert` hangs it below the old edge, leaving a chain.
open AlgoDesign.Strings in
example : Patricia.insert (Patricia.ofTrie (.node none [(1, .node none [])] : Trie Unit)) [1, 2] ()
    = .node none [([1], .node none [([2], .node (some ()) [])])] := rfl
open AlgoDesign.Strings in
example : Patricia.ofTrie (Trie.insert (.node none [(1, .node none [])] : Trie Unit) [1, 2] ())
    = .node none [([1, 2], .node (some ()) [])] := rfl
open AlgoDesign.Strings in
example : ¬ Trie.NoDeadBranches (.node none [(1, .node none [])] : Trie Unit) := by
  simp [Trie.NoDeadBranches, Trie.NoDeadBranchesChildren, Trie.NoDeadBranchesNode]
-- `ofTrie` of a trie built by insertions keeps box lines 3 and 4, checked on the tree itself rather
-- than through `branchesUnlessWordEnds_ofTrie` and `noEmptyBranches_ofTrie`: every node below the
-- root holds a value or branches, and every branch carries a letter.
open AlgoDesign.Strings in
example : Patricia.BranchesUnlessWordEnds
      (Patricia.ofTrie (shellsKvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty)) ∧
    Patricia.NoEmptyBranches
    (Patricia.ofTrie (shellsKvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty)) := by
  have h : Patricia.ofTrie (shellsKvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty)
      = .node none [([115], .node none [
        ([104], .node none [
          ([101], .node (some 0) [([108,108], .node (some 99) [([115], .node (some 1) [])])]),
          ([111,114,101], .node (some 3) [])]),
        ([101,97], .node (some 2) [([115,104,111,114,101], .node (some 4) [])])])] := rfl
  rw [h]
  decide
-- The Rust's insert answers lookups as `insert` does. On the shells word set built in the Rust's
-- order, every stored key is found with its value, a key ending inside an edge ("sh") and a key
-- past a leaf ("shores") are not, and inserting "sea" again overwrites only "sea".
open AlgoDesign.Strings in
example : (Patricia.ofListSorted shellsKvs).get [115,104,101] = some 0 ∧
    (Patricia.ofListSorted shellsKvs).get [115,104,101,108,108,115] = some 1 ∧
    (Patricia.ofListSorted shellsKvs).get [115,101,97] = some 2 ∧
    (Patricia.ofListSorted shellsKvs).get [115,104,111,114,101] = some 3 ∧
    (Patricia.ofListSorted shellsKvs).get [115,101,97,115,104,111,114,101] = some 4 ∧
    (Patricia.ofListSorted shellsKvs).get [115,104,101,108,108] = some 99 ∧
    (Patricia.ofListSorted shellsKvs).get [115,104] = none ∧
    (Patricia.ofListSorted shellsKvs).get [115,104,111,114,101,115] = none := by decide
open AlgoDesign.Strings in
example : (Patricia.insertSorted (Patricia.ofListSorted shellsKvs) [115,101,97] 7).get
      [115,101,97] = some 7 ∧
    (Patricia.insertSorted (Patricia.ofListSorted shellsKvs) [115,101,97] 7).get
      [115,101,97,115,104,111,114,101] = some 4 ∧
    (Patricia.insertSorted (Patricia.ofListSorted shellsKvs) [115,101,97] 7).get
      [115,104,101] = some 0 := by decide
-- A new edge filed in front of a sibling, and a split whose new leaf sorts first: both words stay
-- reachable, and so does everything already there.
open AlgoDesign.Strings in
example : (Patricia.ofListSorted [([3], 0), ([1], 1), ([2], 2)]).get [1] = some 1 ∧
    (Patricia.ofListSorted [([3], 0), ([1], 1), ([2], 2)]).get [2] = some 2 ∧
    (Patricia.ofListSorted [([3], 0), ([1], 1), ([2], 2)]).get [3] = some 0 := by decide
open AlgoDesign.Strings in
example : (Patricia.ofListSorted [([1,3], 0), ([1,2], 1)]).get [1,2] = some 1 ∧
    (Patricia.ofListSorted [([1,3], 0), ([1,2], 1)]).get [1,3] = some 0 ∧
    (Patricia.ofListSorted [([1,3], 0), ([1,2], 1)]).get [1] = none := by decide
-- Why `InsertSpec` for the Rust's insert needs a sorted tree. Under an unsorted child list
-- [2] before [1, 5], inserting [1] files a new edge in front of [2] and so in front of [1, 5],
-- which `get` then never reaches: the old key [1, 5] is lost. On the sort of that tree it is not.
open AlgoDesign.Strings in
example : (Patricia.insertSorted
      (.node none [([2], .node (some 0) []), ([1, 5], .node (some 1) [])] : Patricia Nat)
      [1] 9).get [1, 5] = none := by decide
open AlgoDesign.Strings in
example : (Patricia.insertSorted (Patricia.sortTree
      (.node none [([2], .node (some 0) []), ([1, 5], .node (some 1) [])] : Patricia Nat))
      [1] 9).get [1, 5] = some 1 := by decide


-- Suffix arrays: the doubling invariant, on the `banana` the chapter traces by hand. Encode
-- 'banana' as 0 = a, 1 = b, 2 = n. Sorted suffixes: a, ana, anana, banana, na, nana -- so the
-- suffix array is [5,3,1,0,4,2].
open AlgoDesign.Strings in
example : SuffixArray.Valid ⟨[1,0,2,0,2,0], [5,3,1,0,4,2]⟩ := by decide
-- The identity permutation is not it: `banana` does not precede `anana`.
open AlgoDesign.Strings in
example : ¬ SuffixArray.Valid ⟨[1,0,2,0,2,0], [0,1,2,3,4,5]⟩ := by decide

-- Round 0 of the doubling, concretely: each position tagged by its own character. This is
-- `Doubling.valid_initial` on one text.
open AlgoDesign.Strings in
example : Doubling.Valid [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0 := by decide
-- Round 1 sorts by the first two characters: a < an = an < ba < na = na. The invariant says
-- nothing finer, and the ties between positions 1 and 3, and 2 and 4, are exactly that.
open AlgoDesign.Strings in
example : Doubling.Valid [1,0,2,0,2,0] [2,1,3,1,3,0] 1 := by decide
-- And round 1's tags are what one doubling round produces from round 0's -- `refineTags`
-- tagging each position by how many pair keys are strictly smaller. This is
-- `Doubling.valid_succ` at `k = 0` on one text: character order in, order on pairs of
-- characters out.
open AlgoDesign.Strings in
example : Doubling.Valid [1,0,2,0,2,0]
    (refineTags [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0) 1 := by decide
-- The dense tagging the definition picks is [3,1,4,1,4,0]: the ties at 1/3 and 2/4 are the same
-- ties [2,1,3,1,3,0] carries, differently numbered. The invariant does not distinguish them.
open AlgoDesign.Strings in
example : refineTags [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0 = [3,1,4,1,4,0] := by decide
-- The second component's shift by one is load-bearing, not decoration. Position 5 is the last,
-- so nothing sits one character on from it, and its key's second slot is the reserved 0 --
-- distinct from the key of a position whose neighbour genuinely tags 0.
open AlgoDesign.Strings in
example : pairKey [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0 5 = (0, 0) := by decide
open AlgoDesign.Strings in
example : pairKey [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0 4 = (2, 1) := by decide
-- Two rounds reach a window of four, which on `banana` is already suffix order.
open AlgoDesign.Strings in
example : Doubling.Valid [1,0,2,0,2,0]
    (refineTags [1,0,2,0,2,0] (refineTags [1,0,2,0,2,0] (initialTags [1,0,2,0,2,0]) 0) 1) 2
  := by decide

-- The same tags do *not* satisfy the invariant for a window of four: `ana` and `anana` are
-- already separated at that width, and equal tags claim they are not.
open AlgoDesign.Strings in
example : ¬ Doubling.Valid [1,0,2,0,2,0] [2,1,3,1,3,0] 2 := by decide
-- Once the window reaches eight, past the text's six characters, the tags are the inverse
-- suffix array and the invariant is suffix order -- which is `valid_of_doubling`.
open AlgoDesign.Strings in
example : Doubling.Valid [1,0,2,0,2,0] [3,2,5,1,4,0] 3 := by decide
open AlgoDesign.Strings in
example : SuffixArray.Valid ⟨[1,0,2,0,2,0], [5,3,1,0,4,2]⟩ :=
  valid_of_doubling [1,0,2,0,2,0] [3,2,5,1,4,0] [5,3,1,0,4,2] 3
    (by decide) (by decide) (by decide) (by decide)

-- And the construction that does all of that by itself: `t.length` rounds of doubling, read off
-- in tag order. On `banana` that is the array the hand trace above arrived at.
open AlgoDesign.Strings in
example : suffixArray [1,0,2,0,2,0] = [5,3,1,0,4,2] := by decide
open AlgoDesign.Strings in
example : SuffixArray.Valid ⟨[1,0,2,0,2,0], suffixArray [1,0,2,0,2,0]⟩ := by decide
-- The same claim as a theorem rather than a computation, on every text at once.
open AlgoDesign.Strings in
example : SuffixArray.Valid ⟨[1,0,2,0,2,0], suffixArray [1,0,2,0,2,0]⟩ :=
  valid_suffixArray [1,0,2,0,2,0]
-- The chapter's `abaa` witness, with 0 = a and 1 = b. No sentinel is appended, so this is suffix
-- order, not rotation order: 'a' < 'aa' < 'abaa' < 'baa'.
open AlgoDesign.Strings in
example : suffixArray [0,1,0,0] = [3,2,0,1] := by decide
-- Six rounds is more fuel than `banana` needs -- three already reach a window of eight -- and the
-- extra rounds change nothing, because a round with nothing left to separate is the identity on
-- the order. This is why a single structural bound can stand in for the loop's real exit test,
-- and `suffixArrayEarly_eq` proves the real test returns the same array.
open AlgoDesign.Strings in
example : doublingRounds [1,0,2,0,2,0] 6 = doublingRounds [1,0,2,0,2,0] 3 := by decide
-- The Rust's loop stops as soon as every tag is distinct. On `banana` that is after two rounds:
-- the windows of four (bana, anan, nana, ana, na, a) already differ, although a window of four
-- does not yet cover six characters. A loop without the distinct-tags test would run a third
-- round, to a window of eight; `suffixArray` runs six.
open AlgoDesign.Strings in
example : earlyRounds [1,0,2,0,2,0] = 2 := by decide
-- Distinct bytes need no doubling round at all: round 0's tags are the bytes, already
-- distinct (the Rust's `distinct_bytes_need_no_doubling_round`, on "abcdef" and "fedcba").
open AlgoDesign.Strings in
example : earlyRounds [0,1,2,3,4,5] = 0 ∧ suffixArrayEarly [0,1,2,3,4,5] = [0,1,2,3,4,5] := by
  decide
open AlgoDesign.Strings in
example : earlyRounds [5,4,3,2,1,0] = 0 ∧ suffixArrayEarly [5,4,3,2,1,0] = [5,4,3,2,1,0] := by
  decide
-- And stopping early changes nothing: the array is the one the full loop builds.
open AlgoDesign.Strings in
example : suffixArrayEarly [1,0,2,0,2,0] = [5,3,1,0,4,2] := by decide
open AlgoDesign.Strings in
example : suffixArrayEarly [0,1,0,0] = suffixArray [0,1,0,0] := by decide
-- Where the exit fires on `banana`: round 1's tags still tie (`an` twice, `na` twice), round 2's
-- are distinct. Distinct counting tags are the inverse suffix array, so a third round would
-- return them unchanged -- the "nothing left to separate" the exit reads off `top == n`.
open AlgoDesign.Strings in
example : ¬ (doublingRounds [1,0,2,0,2,0] 1).Nodup ∧ (doublingRounds [1,0,2,0,2,0] 2).Nodup ∧
    doublingRounds [1,0,2,0,2,0] 3 = doublingRounds [1,0,2,0,2,0] 2 := by decide
-- A run of equal characters is where the window test and the distinct test fire together: at a
-- window of four on a four-character text, not one round sooner.
open AlgoDesign.Strings in
example : earlyRounds [0,0,0,0] = 2 ∧ ¬ (doublingRounds [0,0,0,0] 1).Nodup := by decide

-- The empty text has an empty suffix array, and the fuel is zero: the loop never turns.
open AlgoDesign.Strings in
example : suffixArray [] = [] := by decide

-- The chapter's search, on `banana$` ($ = 36, a = 97, b = 98, n = 110) and its array
-- 6 5 3 1 0 4 2. For `ana` the top edge is row 2 and the bottom edge row 4, the rows the
-- chapter's two halvings stop at, so the block is rows 2 and 3, positions 3 and 1.
open AlgoDesign.Strings in
example : suffixArray [98,97,110,97,110,97,36] = [6,5,3,1,0,4,2] := by decide
open AlgoDesign.Strings in
example : bisect (fun i => decide ((suffix [98,97,110,97,110,97,36] i).take 3 < [97,110,97]))
      [6,5,3,1,0,4,2] 7 0 7 = 2 ∧
    bisect (fun i => decide ((suffix [98,97,110,97,110,97,36] i).take 3 ≤ [97,110,97]))
      [6,5,3,1,0,4,2] 7 0 7 = 4 := by decide
open AlgoDesign.Strings in
example : search [98,97,110,97,110,97,36] [6,5,3,1,0,4,2] [97,110,97] = [3,1] := by decide
-- The empty pattern is at every position, end included: 7 first, then every row.
open AlgoDesign.Strings in
example : search [98,97,110,97,110,97,36] [6,5,3,1,0,4,2] [] = [7,6,5,3,1,0,4,2] := by decide
-- An absent pattern, and a pattern running past the end of the text (`a$` then more).
open AlgoDesign.Strings in
example : search [98,97,110,97,110,97,36] [6,5,3,1,0,4,2] [120] = [] ∧
    search [98,97,110,97,110,97,36] [6,5,3,1,0,4,2] [97,36,97] = [] := by decide
-- `search_eq_filter` applied: the answer is the filter its statement names.
open AlgoDesign.Strings in
example : search [98,97,110,97,110,97,36] (suffixArray [98,97,110,97,110,97,36]) [110,97] =
    ([98,97,110,97,110,97,36].length :: suffixArray [98,97,110,97,110,97,36]).filter
      (fun i => [110,97].isPrefixOf (suffix [98,97,110,97,110,97,36] i)) :=
  search_eq_filter (valid_suffixArray _) _
-- `SuffixArray.Valid` is needed: on the unsorted identity permutation, `a` (97) occurs at 1, 3
-- and 5 only, but the halving brackets every row; and `na` (110 97) occurs at 2 and 4, but the
-- halving steps past both.
open AlgoDesign.Strings in
example : ¬ SuffixArray.Valid ⟨[98,97,110,97,110,97,36], [0,1,2,3,4,5,6]⟩ ∧
    search [98,97,110,97,110,97,36] [0,1,2,3,4,5,6] [97] = [0,1,2,3,4,5,6] ∧
    search [98,97,110,97,110,97,36] [0,1,2,3,4,5,6] [110,97] = [] := by decide

-- A suffix's place in the array is a count: the i-th smallest suffix is the one with exactly i
-- suffixes below it. 'banana' (position 0) has a, ana and anana below it and lands at index 3;
-- 'a' (position 5) has nothing below it and lands at index 0 -- which is where [5,3,1,0,4,2]
-- puts them. `saPos_eq_count` says this of every row at once.
open AlgoDesign.Strings in
example : saPos [1,0,2,0,2,0] 0 = 3 := by decide
open AlgoDesign.Strings in
example : saPos [1,0,2,0,2,0] 5 = 0 := by decide
open AlgoDesign.Strings in
example : ∀ r, r < 6 → saPos [1,0,2,0,2,0] [5,3,1,0,4,2][r]! = r := by decide
-- Positions 1 and 3 both carry an 'a', so their suffixes compare as their successors do:
-- 'anana' against 'ana' is 'nana' against 'na'. Spelled with `List.le` rather than `≤`, because
-- this file imports all of Mathlib and `≤` on `List Nat` would resolve to Mathlib's order
-- instance instead of the core one `SuffixArray/Spec.lean` states suffix order with. The two are
-- the same relation reached by a different path, but they are not definitionally equal.
open AlgoDesign.Strings in
example : List.le (suffix [1,0,2,0,2,0] 1) (suffix [1,0,2,0,2,0] 3)
    ↔ List.le (suffix [1,0,2,0,2,0] 2) (suffix [1,0,2,0,2,0] 4) :=
  suffix_le_cons_iff [1,0,2,0,2,0] 1 3 (by decide) (by decide) (by decide)

-- The LCP array of `banana`, predecessor-direction and with no sentinel, exactly as
-- `rust/crates/algodesign/src/strings/lcp.rs` computes it. Suffix order is a, ana, anana, banana,
-- na, nana: 'a' has no predecessor so entry 0 is 0; 'ana' shares 'a' with it; 'anana' shares 'ana'
-- with 'ana'; 'banana' shares nothing with 'anana'; 'na' shares nothing with 'banana'; 'nana'
-- shares 'na' with 'na'.
open AlgoDesign.Strings in
example : kasai [1,0,2,0,2,0] [5,3,1,0,4,2] = [0,1,3,0,0,2] := by decide
-- Entry by entry, from the definition rather than from the scan -- the same six numbers.
open AlgoDesign.Strings in
example : (List.range 6).map (lcpEntry [1,0,2,0,2,0] [5,3,1,0,4,2]) = [0,1,3,0,0,2] := by decide
-- The same claim as a theorem rather than a computation, on the array the doubling loop builds.
-- `kasai_eq` says the two agree on every text, not just on the ones tried here.
open AlgoDesign.Strings in
example : kasai [1,0,2,0,2,0] (suffixArray [1,0,2,0,2,0])
    = (List.range (suffixArray [1,0,2,0,2,0]).length).map
      (lcpEntry [1,0,2,0,2,0] (suffixArray [1,0,2,0,2,0])) :=
  kasai_eq _ _ (valid_suffixArray _)
-- The LCP array's use: the longest repeated substring. In `banana` the largest entry is 3, first
-- reached at row 2 ('anana'), so the answer is 'ana' -- its two occurrences overlap. In
-- 'mississippi' (i=0, m=1, p=2, s=3) it is 'issi'. With nothing repeated every entry is 0, and
-- the answer is empty.
open AlgoDesign.Strings in
example : longestRepeat [1,0,2,0,2,0] [5,3,1,0,4,2] = [0,2,0] := by decide
open AlgoDesign.Strings in
example : longestRepeat [1,0,3,3,0,3,3,0,2,2,0] [10,7,4,1,0,9,8,6,3,5,2] = [0,3,3,0] := by
  decide
open AlgoDesign.Strings in
example : longestRepeat [0,1,2,3] [0,1,2,3] = [] := by decide
-- The two edges the property test in the Rust cannot reach. An empty text has no entries at all;
-- a one-character text has one entry, and it is 0, because the only suffix has no predecessor.
open AlgoDesign.Strings in
example : kasai [] [] = ([] : List Nat) := by decide
open AlgoDesign.Strings in
example : kasai [7] [0] = [0] := by decide
-- The input the carry is sharpest on: every character equal, so the suffixes sort
-- shortest-to-longest and each shares its whole self with its successor. The scan never walks a
-- comparison back down -- it resumes at h each time, which is what the entries 0,1,2,3 record.
open AlgoDesign.Strings in
example : kasai [0,0,0,0] (suffixArray [0,0,0,0]) = [0,1,2,3] := by decide

-- The Burrows–Wheeler transform permutes, it does not compress. 'banana$' with $ = 0, a = 1, b = 2,
-- n = 3: the
-- sorted rotation matrix reads $banana / a$banan / ana$ban / anana$b / banana$ / na$bana / nana$ba,
-- so the last column is 'annb$aa'. Seven characters in, seven characters out -- and the two runs
-- of doubled letters are the whole point: they are what the next stage compresses, and they were
-- not there before.
open AlgoDesign.Strings in
example : bwtOfSorted [2,1,3,1,3,1,0] = [1,3,3,2,0,1,1] := by decide
-- The output is a rearrangement of the input, with nothing added and nothing dropped.
open AlgoDesign.Strings in
example : (bwtOfSorted [2,1,3,1,3,1,0]).Perm [2,1,3,1,3,1,0] := by decide
-- The two edge cases a length or multiset claim could plausibly fail on. An empty text has no
-- rotations at all, so there is no last column to read; and a text whose rotations repeat --
-- 'abab' has each row twice -- keeps both copies, because the matrix is indexed by position, not
-- by row content. Deduplicating there would shorten the output and break the theorem.
open AlgoDesign.Strings in
example : bwtOfSorted ([] : List Nat) = [] := by decide
open AlgoDesign.Strings in
example : (rotations [1,2,1,2]).length = 4 ∧ ((rotations [1,2,1,2]).dedup).length = 2 := by decide
open AlgoDesign.Strings in
example : bwtOfSorted [1,2,1,2] = [2,2,1,1] := by decide
open AlgoDesign.Strings in
example : (bwtOfSorted [1,2,1,2]).length = 4 := by decide

-- The sentinel, and what it is for. 'banana$' carries one: $ = 0 sits last and is strictly below
-- every character before it. A text whose $ occurs anywhere but last does not -- which is what
-- the Rust refuses to transform.
open AlgoDesign.Strings in
example : Terminated [2,1,3,1,3,1,0] 0 := by decide
open AlgoDesign.Strings in
example : ¬ Terminated [0,1,0,0] 0 := by decide
-- Under it the two routes agree: the single array scan the Rust runs returns the string the
-- chapter's rotation matrix draws. Once by computation on 'banana$', once as the theorem.
open AlgoDesign.Strings in
example : bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])
    = bwtOfSorted [2,1,3,1,3,1,0] := by decide
open AlgoDesign.Strings in
example : bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])
    = bwtOfSorted [2,1,3,1,3,1,0] :=
  bwt_eq_rotations _ 0 (by decide) _ (valid_suffixArray _)
-- `Terminated` is load-bearing, not decoration. 'abaa' has no sentinel, and there the two routes
-- return different strings: its rotations sort [2,3,0,1] and its suffixes [3,2,0,1], so the last
-- columns the two orders read off disagree in their first two characters.
open AlgoDesign.Strings in
example : bwtOfSa [0,1,0,0] (suffixArray [0,1,0,0]) = [0,1,0,0] := by decide
open AlgoDesign.Strings in
example : bwtOfSorted [0,1,0,0] = [1,0,0,0] := by decide
open AlgoDesign.Strings in
example : bwtOfSa [0,1,0,0] (suffixArray [0,1,0,0]) ≠ bwtOfSorted [0,1,0,0] := by decide

-- And what the transform turns on: the last column alone rebuilds the text. The walk starts at
-- the row whose last character is the $ -- row four of 'annb$aa' -- and each LF step reads off the
-- character before the one it just read: $, a, n, a, n, a, b, which is 'banana$' backwards. Once
-- by computation, once as the theorem.
open AlgoDesign.Strings in
example : invertBwt (bwtOfSorted [2,1,3,1,3,1,0]) = [2,1,3,1,3,1,0] := by decide
open AlgoDesign.Strings in
example : invertBwt (bwtOfSorted [2,1,3,1,3,1,0]) = [2,1,3,1,3,1,0] :=
  invertBwt_bwt _ 0 (by decide)
-- The step the walk takes, on the same string: row four of the last column carries the $, which
-- stands at position six of the text, and that position's suffix is row zero of the array. That
-- identity, for every row of every terminated text, is `lf_spec`.
open AlgoDesign.Strings in
example : lf (bwtOfSorted [2,1,3,1,3,1,0]) 4 = 0 := by decide
open AlgoDesign.Strings in
example : (suffixArray [2,1,3,1,3,1,0])[lf (bwtOfSorted [2,1,3,1,3,1,0]) 4]! = 6 := by decide
open AlgoDesign.Strings in
example : (suffixArray [1,0])[lf (bwtOfSa [1,0] (suffixArray [1,0])) 0]!
    = ((suffixArray [1,0])[0]! + [1,0].length - 1) % [1,0].length :=
  lf_spec _ 0 (by decide) _ (valid_suffixArray _) 0 (by decide)
-- Without a sentinel the round trip is not one. 'abab' comes back rotated by a position, and
-- 'abaa' comes back as a different string again -- so `Terminated` is a hypothesis, not a manner
-- of speaking.
open AlgoDesign.Strings in
example : invertBwt (bwtOfSorted [1,2,1,2]) = [2,1,2,1] := by decide
open AlgoDesign.Strings in
example : invertBwt (bwtOfSorted [0,1,0,0]) ≠ [0,1,0,0] := by decide

-- Rank and select: one counting primitive, three questions. `rank` counts set bits before a
-- position:
-- [1,0,1,1] has two of them in its first three bits.
open AlgoDesign.Strings in
example : rank [true, false, true, true] 3 = 2 := by decide
-- `select` runs it backwards -- the bit of index one, counting from zero, sits at position two.
open AlgoDesign.Strings in
example : select [true, false, true, true] 1 = some 2 := by decide
-- And over a larger alphabet the same count is `occ`: three 1s among the first four symbols.
open AlgoDesign.Strings in
example : occ [1,2,1,1,3] 1 4 = 3 := by decide
-- The edge the two-level structure has to get right: `select` is total, and answers `none`
-- rather than a junk position when the bit asked for does not exist -- past the population
-- count, in a vector with no set bits, and in the empty vector.
open AlgoDesign.Strings in
example : select [true, false, true, true] 3 = none := by decide
open AlgoDesign.Strings in
example : select [false, false] 0 = none := by decide
open AlgoDesign.Strings in
example : select ([] : List Bool) 0 = none := by decide
-- `rank` saturates past the end instead of failing: it is the whole vector's population count.
open AlgoDesign.Strings in
example : rank [true, false] 100 = 1 := by decide
-- The sharing the Rust depends on, on one concrete vector: the symbol count over {0,1} and the
-- bit count are the same number, which is `occ_eq_rank`.
open AlgoDesign.Strings in
example : occ [1,0,1,1] 1 3 = rank [true, false, true, true] 3 := by decide
open AlgoDesign.Strings in
example :
    occ ([true, false, true, true].map fun x => if x then 1 else 0) 1 3
      = rank [true, false, true, true] 3 := by decide

-- The FM-index: backward search counts occurrences out of the last column and the C
-- array, and never indexes the text. 'banana$' once more, with $ = 0, a = 1, b = 2, n = 3:
-- 'ana' twice, 'ban' once, and a character the text does not carry never.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [1,3,1] = 2 := by decide
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [2,1,3] = 1 := by decide
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [4] = 0 := by decide
-- The proved obligation on that text: a terminated text, and a pattern that does not carry the
-- sentinel before its last character. `fmCount_eq` builds its own suffix array.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [1,3,1]
    = ((List.range [2,1,3,1,3,1,0].length).filter
      (fun i => decide ([1,3,1] <+: suffix [2,1,3,1,3,1,0] i))).length :=
  fmCount_eq _ 0 (by decide) _ (by decide)
-- Why that last hypothesis is there. The last column is read off *rotations*, so backward
-- search walks the text cyclically: '$banana' begins with '$b' although no suffix of 'banana$'
-- does, and the search reports the match. The count below is the wrap, pinned as a regression --
-- the theorems exclude a pattern carrying the sentinel before its end rather than pretending it
-- cannot happen.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [0,2] = 1 := by decide
open AlgoDesign.Strings in
example : ((List.range 7).filter
    (fun i => decide ([0,2] <+: suffix [2,1,3,1,3,1,0] i))).length = 0 := by decide
-- Locate: the rows of the interval, read off the suffix array. 'ana' sits at positions 1 and 3,
-- and comes back in suffix order, which is why the theorem is a permutation and not an equality.
open AlgoDesign.Strings in
example : fmLocate [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) [1,3,1] = [3,1] := by decide
open AlgoDesign.Strings in
example : (fmLocate [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) [1,3,1]).Perm
    ((List.range [2,1,3,1,3,1,0].length).filter
      (fun i => decide ([1,3,1] <+: suffix [2,1,3,1,3,1,0] i))) :=
  fmLocate_perm _ 0 (by decide) _ (valid_suffixArray _) _ (by decide)
-- An end-anchored query is legitimate: `na$` occurs once in `banana$`, at position 4, and backward
-- search finds it (the Rust's `the_sentinel_is_a_legitimate_last_pattern_byte`). So do `a$`, `$`
-- alone, and `b$` in `ab$`. Each count agrees with the definition, counted by hand.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [3,1,0] = 1 ∧
    ((List.range 7).filter
      (fun i => decide ([3,1,0] <+: suffix [2,1,3,1,3,1,0] i))).length = 1 := by
  decide
open AlgoDesign.Strings in
example : fmLocate [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) [3,1,0] = [4] := by decide
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [1,0] = 1 ∧ fmCount [2,1,3,1,3,1,0] [0] = 1 := by decide
open AlgoDesign.Strings in
example : fmCount [1,2,0] [2,0] = 1 ∧
    ((List.range 3).filter (fun i => decide ([2,0] <+: suffix [1,2,0] i))).length = 1 := by decide
-- And the theorems reach them: the hypothesis is `s ∉ p.dropLast`, which `na$` and `$` meet.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [3,1,0]
    = ((List.range [2,1,3,1,3,1,0].length).filter
      (fun i => decide ([3,1,0] <+: suffix [2,1,3,1,3,1,0] i))).length :=
  fmCount_eq _ 0 (by decide) _ (by decide)
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [0]
    = ((List.range [2,1,3,1,3,1,0].length).filter
      (fun i => decide ([0] <+: suffix [2,1,3,1,3,1,0] i))).length :=
  fmCount_eq _ 0 (by decide) _ (by decide)
-- Extract: three characters from position 1 of 'banana$', read off the last column by walking
-- LF from the row of position 4. A range ending at the text's end starts from the row of
-- position 0 and yields the sentinel, the Rust's wrap-around branch.
open AlgoDesign.Strings in
example : fmExtract (bwtOfSorted [2,1,3,1,3,1,0]) (saPos [2,1,3,1,3,1,0] 4) 3 = [1,3,1] := by
  decide
open AlgoDesign.Strings in
example : fmExtract (bwtOfSorted [2,1,3,1,3,1,0]) (saPos [2,1,3,1,3,1,0] 0) 2 = [1,0] := by
  decide
open AlgoDesign.Strings in
example : fmExtract (bwtOfSorted [2,1,3,1,3,1,0]) (saPos [2,1,3,1,3,1,0] (7 % 7)) 2
    = ([2,1,3,1,3,1,0].drop 5).take 2 :=
  fmExtract_bwtOfSorted _ 0 (by decide) 5 2 (by decide)
-- The two-level directory at blocks of 2 and superblocks of 2 blocks, built by the Rust's loop:
-- block counts [1, 2, 0], superblock totals [0, 3], relative block counts [0, 1, 0]. A real
-- table, not `rank` written into one -- and `rankTwoLevel_eq` says its answers are `rank`'s,
-- saturation past the end included.
open AlgoDesign.Strings in
example : directory 2 2 [true, false, true, true, false] = ⟨[0, 3], [0, 1, 0], 3⟩ := by decide
open AlgoDesign.Strings in
example : (List.range 8).map (rankTwoLevel 2 2 [true, false, true, true, false])
    = [0, 1, 1, 2, 3, 3, 3, 3] := by decide
-- `occ` of 'a' in 'banana$' through the same directory, every branch of `ByteIndex::occ`.
open AlgoDesign.Strings in
example : (List.range 8).map (occTwoLevel 2 2 [2,1,3,1,3,1,0] 1) = [0,0,1,1,2,2,3,3] := by
  decide
-- Sampled locate at rate 3 on 'banana$': marked rows hold positions 6, 3 and 0; every other row
-- walks LF back to one of them. The answers are the suffix array, row by row.
open AlgoDesign.Strings in
example : (List.range 7).map (locateSampled [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) 3)
    = [6,5,3,1,0,4,2].map some := by decide
open AlgoDesign.Strings in
example : locateSampled [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) 3 3 = some 1 :=
  locateSampled_eq _ 0 (by decide) _ (valid_suffixArray _) 3 (by decide) 3 (by decide)
-- Costs, in LF steps, at rate 3 on 'banana$': a hit's walk takes `sa[r] mod 3` steps
-- (`time_locateSampledM`). Extraction follows the Rust's start rule; these are the two values
-- `extract_starts_at_the_first_sample_past_the_range` pins with `LF_STEPS`: `extract(4, 1)` starts
-- at position 6 and `extract(5, 2)` at position 7, the row of position 0; two steps each.
open AlgoDesign.Strings in
example : (List.range 7).map
    (fun r => (locateSampledM [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) 3 r).time)
    = [0,2,0,1,0,1,2] := by decide
open AlgoDesign.Strings in
example : (extractSampledM (bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])) 7 3 4 1
      (saPos [2,1,3,1,3,1,0] 6)).ret = [3] ∧
    (extractSampledM (bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])) 7 3 4 1
      (saPos [2,1,3,1,3,1,0] 6)).time = 2 ∧
    (extractSampledM (bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])) 7 3 5 2
      (saPos [2,1,3,1,3,1,0] 0)).ret = [1,0] ∧
    (extractSampledM (bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0])) 7 3 5 2
      (saPos [2,1,3,1,3,1,0] 0)).time = 2 := by decide
-- Counting 'ana' is three backward steps, whatever the text.
open AlgoDesign.Strings in
example : (backwardSearchM (bwtOfSorted [2,1,3,1,3,1,0]) (cLess [2,1,3,1,3,1,0]) [1,3,1]).ret
      = backwardSearch (bwtOfSorted [2,1,3,1,3,1,0]) (cLess [2,1,3,1,3,1,0]) [1,3,1] ∧
    (backwardSearchM (bwtOfSorted [2,1,3,1,3,1,0]) (cLess [2,1,3,1,3,1,0]) [1,3,1]).time = 3 := by
  decide
-- Rabin–Karp on CLRS's parameters (10, 13): 10 windows of [3,1,4,1,5,2,6,7,3,9,9,2,1] for the
-- pattern [1,4,1,5], each one fingerprint comparison, plus 4 per fingerprint hit.
open AlgoDesign.Strings in
example : (rabinKarpSearchM 10 13 [3,1,4,1,5,2,6,7,3,9,9,2,1] [1,4,1,5]).time
    = 10 + 4 * candidateCount 10 13 [3,1,4,1,5,2,6,7,3,9,9,2,1] [1,4,1,5] := by decide
-- A trie lookup of a present key walks exactly its length; a stored prefix's path is walked too.
open AlgoDesign.Strings in
example :
    (Trie.getM (Trie.insert (Trie.insert Trie.empty [1,2,3] 7) [1,4] 8) [1,2,3]).ret = some 7 ∧
    (Trie.getM (Trie.insert (Trie.insert Trie.empty [1,2,3] 7) [1,4] 8) [1,2,3]).time = 3 ∧
    (Trie.getM (Trie.insert (Trie.insert Trie.empty [1,2,3] 7) [1,4] 8) [1,2]).ret = none ∧
    (Trie.getM (Trie.insert (Trie.insert Trie.empty [1,2,3] 7) [1,4] 8) [1,2]).time = 2 := by
  decide
-- The effective alphabet of 'banana$' over 256 byte values, and the dense C array the Rust's
-- constructor accumulates over it: `cDense_eq_cLess` says entry `d` is `cLess` of symbol `d`.
open AlgoDesign.Strings in
example : alphabetOf 256 [2,1,3,1,3,1,0] = [0,1,2,3] ∧
    cDense [2,1,3,1,3,1,0] [0,1,2,3] = [0,1,4,5] := by decide
open AlgoDesign.Strings in
example : (List.range 7).map (lfDense 4 (bwtOfSorted [2,1,3,1,3,1,0]))
    = (List.range 7).map (lf (bwtOfSorted [2,1,3,1,3,1,0])) := by decide
open AlgoDesign.Strings in
example : (fmLocate [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) [3,1,0]).Perm
    ((List.range [2,1,3,1,3,1,0].length).filter
      (fun i => decide ([3,1,0] <+: suffix [2,1,3,1,3,1,0] i))) :=
  fmLocate_perm _ 0 (by decide) _ (valid_suffixArray _) _ (by decide)
-- The line the hypothesis still draws: a sentinel *before* the end wraps (`$b` counts once, and
-- no suffix begins with it), and `[0,2].dropLast = [0]` carries it.
open AlgoDesign.Strings in
example : fmCount [2,1,3,1,3,1,0] [0,2] = 1 ∧ (0 : Nat) ∈ ([0,2] : List Nat).dropLast := by decide

-- Records: from a hit to the whole quote. Three records
-- start at 0, 4 and 9. A hit at position 6 is inside the second one, and `recordBounds` hands
-- back its half-open span.
open AlgoDesign.Strings in
example : recordOf [true,false,false,false,true,false,false,false,false,true,false] 6 = 1
    := by decide
open AlgoDesign.Strings in
example : recordBounds [true,false,false,false,true,false,false,false,false,true,false] 1
    = (4, 9) := by decide
-- The final record has no next start, so its end is the end of the text rather than a `select`
-- result -- the `getD b.length` branch, which is the one an off-by-one would hide in.
open AlgoDesign.Strings in
example : recordBounds [true,false,false,false,true,false,false,false,false,true,false] 2
    = (9, 11) := by decide
-- Containment, on that vector, for the opening word of a record, its middle, and its last
-- position: one theorem, three remembered fragments.
open AlgoDesign.Strings in
example : ∀ i, i < 11 →
    (recordBounds [true,false,false,false,true,false,false,false,false,true,false]
        (recordOf [true,false,false,false,true,false,false,false,false,true,false] i)).1 ≤ i ∧
      i < (recordBounds [true,false,false,false,true,false,false,false,false,true,false]
        (recordOf [true,false,false,false,true,false,false,false,false,true,false] i)).2 := by
  decide
-- `hstart` is load-bearing, not decoration. With no record starting at position 0 the text
-- before the first start is folded into record 0 by `recordOf`'s truncating subtraction, and
-- record 0 starts at position 2 -- *after* the hit at position 0. The lower bound is false here,
-- and `recordBounds_contains` is inapplicable because `[false,false,true][0]! = false`.
open AlgoDesign.Strings in
example : recordOf [false,false,true] 0 = 0 := by decide
open AlgoDesign.Strings in
example : ¬ (recordBounds [false,false,true] (recordOf [false,false,true] 0)).1 ≤ 0 := by decide
-- And `hi` is what the *upper* bound needs: past the end of the text, the last record still
-- starts before the hit, but it certainly does not end after it.
open AlgoDesign.Strings in
example : (recordBounds [true,false,true] (recordOf [true,false,true] 99)).1 ≤ 99 := by decide
open AlgoDesign.Strings in
example : ¬ 99 < (recordBounds [true,false,true] (recordOf [true,false,true] 99)).2 := by decide
-- So each half carries only its own hypothesis, and each is its own theorem: the lower half
-- holds past the end of the text (no `hi`), the upper half where no record starts at 0 (no
-- `hstart`).
open AlgoDesign.Strings in
example : (recordBounds [true,false,true] (recordOf [true,false,true] 99)).1 ≤ 99 :=
  lower_le_of_recordOf _ 99 (by decide)
open AlgoDesign.Strings in
example : 0 < (recordBounds [false,false,true] (recordOf [false,false,true] 0)).2 :=
  lt_snd_of_recordOf _ 0 (by decide)
-- Deduplication: two hits with no record start between them name one quote. Positions 5 and 8
-- are both inside record 1, so a search over two remembered fragments reports one result.
open AlgoDesign.Strings in
example :
    recordOf [true,false,false,false,true,false,false,false,false,true,false] 8
      = recordOf [true,false,false,false,true,false,false,false,false,true,false] 5 :=
  recordOf_eq_of_no_start_between _ 5 8 (by omega) (by
    intro k h1 h2; interval_cases k <;> rfl)

-- `Trie.Valid`: `DistinctLetters` and `NoDeadBranches`. The empty trie has it; a dead branch and
-- two children under one symbol each break it.
open AlgoDesign.Strings in
example : Trie.Valid (Trie.empty : Trie Unit) := Trie.valid_empty
open AlgoDesign.Strings in
-- a dead branch: valueless and childless below the root
example : ¬ Trie.Valid (.node none [(1, .node none [])] : Trie Unit) := by
  simp [Trie.Valid, Trie.NoDeadBranches, Trie.NoDeadBranchesChildren, Trie.NoDeadBranchesNode]
open AlgoDesign.Strings in
-- two children under one symbol
example : ¬ Trie.Valid (.node none [(1, .node (some ()) []), (1, .node (some ()) [])] :
    Trie Unit) := by
  simp [Trie.Valid, Trie.DistinctLetters]

-- `Patricia.Valid`: `DistinctFirstLetters`, `BranchesUnlessWordEnds` and `NoEmptyBranches`. A
-- valueless leaf below the root keeps `NoEmptyBranches` but breaks `BranchesUnlessWordEnds`, so
-- it is the case separating the two; two sibling labels with one head break
-- `DistinctFirstLetters`; an empty label breaks `NoEmptyBranches` alone.
open AlgoDesign.Strings in
example : Patricia.Valid (.node none [] : Patricia Unit) := Patricia.valid_empty
open AlgoDesign.Strings in
example : Patricia.DistinctFirstLetters (.node none [([1], .node none [])] : Patricia Unit) ∧
    ¬ Patricia.BranchesUnlessWordEnds (.node none [([1], .node none [])] : Patricia Unit) ∧
    Patricia.NoEmptyBranches (.node none [([1], .node none [])] : Patricia Unit) := by
  decide
open AlgoDesign.Strings in
example :
    let t : Patricia Unit := .node none [([], .node (some ()) []), ([1], .node (some ()) [])]
    Patricia.DistinctFirstLetters t ∧ Patricia.BranchesUnlessWordEnds t ∧
      ¬ Patricia.NoEmptyBranches t := by
  decide
open AlgoDesign.Strings in
example : ¬ Patricia.Valid
    (.node none [([1, 2], .node (some ()) []), ([1, 3], .node (some ()) [])] : Patricia Unit) := by
  simp [Patricia.Valid, Patricia.DistinctFirstLetters]

-- `SortedHeads`: the Rust's child order, strictly ascending by first symbol.
open AlgoDesign.Strings in
example : Patricia.SortedHeads
    (.node none [([1], .node (some ()) []), ([2], .node (some ()) [])] : Patricia Unit) := by
  simp [Patricia.SortedHeads, Patricia.SortedHeadsAux, Patricia.headSym]
open AlgoDesign.Strings in
example : ¬ Patricia.SortedHeads
    (.node none [([2], .node (some ()) []), ([1], .node (some ()) [])] : Patricia Unit) := by
  simp [Patricia.SortedHeads, Patricia.headSym]
-- The Rust's construction lands in `Valid` and in `SortedHeads`, whatever the arrival order.
open AlgoDesign.Strings in
example : Patricia.Valid (Patricia.ofListSorted [([2], ()), ([1], ())])
    ∧ Patricia.SortedHeads (Patricia.ofListSorted [([2], ()), ([1], ())]) := by
  have h : Patricia.ofListSorted [([2], ()), ([1], ())]
      = .node none [([1], .node (some ()) []), ([2], .node (some ()) [])] := rfl
  rw [h]
  exact ⟨by decide, by
    simp [Patricia.SortedHeads, Patricia.SortedHeadsAux, Patricia.headSym]⟩

-- `FMIndex.Valid` on `banana$` with sampling rate 2: the index the build stores is valid;
-- bumping a `C` entry, flipping a mark, or a second sentinel in the column each break it, and so
-- does swapping two stored values, which only `PositionsKept`'s last part,
-- `KeptPositionsCorrect`, sees.
open AlgoDesign.Strings in
example : (FMIndex.build [2,1,3,1,3,1,0] 2).Valid := by
  decide
-- The parts themselves: L = `annb$aa`, C over the alphabet `$abn`, marks at the even positions.
open AlgoDesign.Strings in
example : bwtOfSa [2,1,3,1,3,1,0] (suffixArray [2,1,3,1,3,1,0]) = [1,3,3,2,0,1,1]
    ∧ cDense [1,3,3,2,0,1,1] (alphabetOf 256 [1,3,3,2,0,1,1]) = [0,1,4,5]
    ∧ saMarks (suffixArray [2,1,3,1,3,1,0]) 2 = [true,false,false,false,true,true,true]
    ∧ saValues (suffixArray [2,1,3,1,3,1,0]) 2 = [6,0,4,2] := by decide
open AlgoDesign.Strings in
example : FMIndex.Valid ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
    [6,0,4,2], [4,6,5,0], 2⟩ := by decide
open AlgoDesign.Strings in
example : ¬ FMIndex.Valid ⟨[1,3,3,2,0,1,1], [0,2,4,5], [true,false,false,false,true,true,true],
    [6,0,4,2], [4,6,5,0], 2⟩ := by decide
open AlgoDesign.Strings in
example : ¬ FMIndex.Valid ⟨[1,3,3,2,0,1,1], [0,1,4,5], [false,false,false,false,true,true,true],
    [6,0,4,2], [4,6,5,0], 2⟩ := by decide
-- The stored values swapped: still the multiples of 2, one per mark, but no longer each at its
-- own row, so `PositionsKept` fails, through `KeptPositionsCorrect`.
open AlgoDesign.Strings in
example : ¬ FMIndex.PositionsKept ⟨[1,3,3,2,0,1,1], [0,1,4,5],
      [true,false,false,false,true,true,true],
      [0,6,4,2], [4,6,5,0], 2⟩
    ∧ ¬ FMIndex.KeptPositionsCorrect ⟨[1,3,3,2,0,1,1], [0,1,4,5],
      [true,false,false,false,true,true,true], [0,6,4,2], [4,6,5,0], 2⟩ := by
  decide
open AlgoDesign.Strings in
example : ¬ FMIndex.Valid ⟨[1,3,3,2,0,0,1], [0,2,4,5], [true,false,false,false,true,true,true],
    [6,0,4,2], [4,6,5,0], 2⟩ := by decide
-- `n` stored as `259`, past the bytes: every other piece still holds (`C` is over the bytes
-- `$ab`), and only `LettersAreBytes` breaks `FMIndex.Valid`.
open AlgoDesign.Strings in
example : FMIndex.PositionsKept ⟨[1,259,259,2,0,1,1], [0,1,4],
      [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩
    ∧ FMIndex.SentinelOnce ⟨[1,259,259,2,0,1,1], [0,1,4], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩
    ∧ FMIndex.SmallerLettersCounted ⟨[1,259,259,2,0,1,1], [0,1,4],
      [true,false,false,false,true,true,true], [6,0,4,2], [4,6,5,0], 2⟩
    ∧ FMIndex.WalkVisitsEveryRow ⟨[1,259,259,2,0,1,1], [0,1,4],
      [true,false,false,false,true,true,true], [6,0,4,2], [4,6,5,0], 2⟩
    ∧ FMIndex.KeptRowsListed ⟨[1,259,259,2,0,1,1], [0,1,4], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩
    ∧ ¬ FMIndex.LettersAreBytes ⟨[1,259,259,2,0,1,1], [0,1,4],
      [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩
    ∧ ¬ FMIndex.Valid ⟨[1,259,259,2,0,1,1], [0,1,4], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ := by decide
-- The box's operations on `banana$`'s index: `ana` (`[1,3,1]`) occurs twice; the stretch holds
-- rows 2 and 3, which locate reads as positions 3 and 1.
open AlgoDesign.Strings in
example : FMIndex.count ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ [1,3,1] = 2
    ∧ FMIndex.locate ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ [1,3,1] = [3, 1] := by decide
-- The text the index answers about is `banana`, without its `$`: a fragment with `$` in it occurs
-- nowhere, ending in it or not; at rate `0`, `RateAtLeastOne` breaks.
open AlgoDesign.Strings in
example : FMIndex.text ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ = [2,1,3,1,3,1]
    ∧ FMIndex.count ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ [1,0] = 0
    ∧ FMIndex.locate ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ [1,0] = []
    ∧ FMIndex.count ⟨[1,3,3,2,0,1,1], [0,1,4,5], [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 2⟩ [] = 7 := by decide
open AlgoDesign.Strings in
example : ¬ FMIndex.RateAtLeastOne ⟨[1,3,3,2,0,1,1], [0,1,4,5],
      [true,false,false,false,true,true,true],
      [6,0,4,2], [4,6,5,0], 0⟩ := by decide

-- `FirstRecordAtStart`: the empty corpus (`[false]`, no starts) has it vacuously; a vector whose
-- first start is past position 0 does not.
open AlgoDesign.Strings in
example : Records.FirstRecordAtStart [false] := by decide
open AlgoDesign.Strings in
example : Records.FirstRecordAtStart [true, false, true] := by decide
open AlgoDesign.Strings in
example : ¬ Records.FirstRecordAtStart [false, false, true] := by decide

-- The corpus. Three records, 23, 34 and 232, joined by the separator 1 and closed by the
-- sentinel 0, with a start bit at 0, 3 and 6.
open AlgoDesign.Strings in
example : Corpus.text 1 0 [[2,3],[3,4],[2,3,2]] = [2,3,1,3,4,1,2,3,2,0] ∧
    Corpus.starts [[2,3],[3,4],[2,3,2]] =
      [true,false,false,true,false,false,true,false,false,false] := by decide
-- `find`: 23 is in records 0 and 2 (twice in neither, once each), 3 is in all three, and each
-- record comes back once, in order. 313 holds the separator and is refused, though the joined
-- text contains it across records 0 and 1.
open AlgoDesign.Strings in
example : Corpus.find 1 0 [[2,3],[3,4],[2,3,2]] [2,3] = [0,2] ∧
    Corpus.find 1 0 [[2,3],[3,4],[2,3,2]] [3] = [0,1,2] ∧
    Corpus.find 1 0 [[2,3],[3,4],[2,3,2]] [3,1,3] = [] ∧
    Corpus.find 1 0 [[2,3],[3,4],[2,3,2]] [] = [0,1,2] := by decide
-- `FindSpec`'s equation, which `findObligation` proves, checked by evaluation on this corpus
-- for fragments that hit one record, several, none, a reserved byte, and the empty fragment.
open AlgoDesign.Strings in
example : ∀ p ∈ [[2,3],[3],[3,4],[3,2],[3,1,3],[],[4,1],[2,3,2],[5],[0]],
    Corpus.find 1 0 [[2,3],[3,4],[2,3,2]] p =
      (List.range 3).filter (fun id => decide (p <:+: [[2,3],[3,4],[2,3,2]][id]!)) := by decide
-- The chapter's records figure: "call me ishmael", "it is a truth" and "all happy families",
-- joined. A hit for "truth" at 24 falls in quote 1, whose bounds are 16 and 30. (`Corpus.find`
-- itself over these 49 positions is too slow for the kernel; the small corpus above runs it.)
open AlgoDesign.Strings in
example : (Corpus.text 1 0 [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]]).extract 24 29 =
      [116,114,117,116,104] ∧
    recordOf (Corpus.starts [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]]) 24 = 1 ∧
    recordBounds (Corpus.starts [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]]) 1 = (16, 30) := by
  decide
-- The test corpus is `Corpus.WellFormed`, so `FindObligation` is not vacuous on it; and
-- `QuoteSpec` holds there: each record's bounds, less the closing byte, give the record
-- whole.
open AlgoDesign.Strings in
example : Corpus.WellFormed 1 0 [[2,3],[3,4],[2,3,2]] := by decide
open AlgoDesign.Strings in
example : Corpus.QuoteSpec [[2,3],[3,4],[2,3,2]] (Corpus.text 1 0 [[2,3],[3,4],[2,3,2]])
    (recordBounds (Corpus.starts [[2,3],[3,4],[2,3,2]])) := by
  intro id hid
  simp at hid
  interval_cases id <;> decide +revert
-- And the two theorems applied there: the well-formedness `decide` settles is all `find` asks;
-- quoting asks nothing.
open AlgoDesign.Strings in
example : Corpus.FindSpec [[2,3],[3,4],[2,3,2]] (Corpus.find 1 0 [[2,3],[3,4],[2,3,2]]) :=
  Corpus.findObligation 1 0 _ (by decide)
open AlgoDesign.Strings in
example : Corpus.QuoteSpec [[2,3],[3,4],[2,3,2]] (Corpus.text 1 0 [[2,3],[3,4],[2,3,2]])
    (recordBounds (Corpus.starts [[2,3],[3,4],[2,3,2]])) :=
  Corpus.quoteObligation 1 0 _
-- `Corpus.WellFormed` is needed: a record holding the separator 1. The fragment 21 is in the
-- record, but `find` refuses it, so `FindSpec` fails for `find` on this corpus.
open AlgoDesign.Strings in
example : ¬ Corpus.WellFormed 1 0 [[2,1,3]] ∧ Corpus.find 1 0 [[2,1,3]] [2,1] = [] ∧
    [2,1] <:+: [2,1,3] := by decide
open AlgoDesign.Strings in
example : ¬ Corpus.FindSpec [[2,1,3]] (Corpus.find 1 0 [[2,1,3]]) := fun h => by
  have := h [2,1]
  revert this
  decide
-- `QuoteSpec` on the records figure: each of the three quotes comes back whole.
open AlgoDesign.Strings in
example : Corpus.QuoteSpec [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]]
    (Corpus.text 1 0 [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]])
    (recordBounds (Corpus.starts [[99,97,108,108,32,109,101,32,105,115,104,109,97,101,108],
      [105,116,32,105,115,32,97,32,116,114,117,116,104],
      [97,108,108,32,104,97,112,112,121,32,102,97,109,105,108,105,101,115]])) := by
  intro id hid
  simp at hid
  interval_cases id <;> decide +revert
-- The empty corpus answers nothing.
open AlgoDesign.Strings in
example : Corpus.find 1 0 [] [2] = [] ∧ Corpus.find 1 0 [] [] = [] := by decide

end AlgoDesignTests

/-! ## Each piece of a `Valid` decides on its own

Every `Valid` is a conjunction of named pieces, each decidable, so a failing example names the
invariant it breaks. -/

-- Box invariant 2 of the suffix array fails alone on a permutation out of order.
open AlgoDesign.Strings in
example : SuffixArray.EachPositionOnce ⟨[1,0,2,0,2,0], [3,5,1,0,4,2]⟩ ∧
    ¬ SuffixArray.SuffixesSorted ⟨[1,0,2,0,2,0], [3,5,1,0,4,2]⟩ := by decide
-- Box invariant 1 fails alone on a sorted list that repeats a position.
open AlgoDesign.Strings in
example : ¬ SuffixArray.EachPositionOnce ⟨[1,0,2,0,2,0], [5,3,3,0,4,2]⟩ := by decide
-- The BWT of `banana$` meets both box invariants and the assumption; the first column breaks
-- invariant 2 but is still a permutation; a text without `$` breaks the assumption alone.
open AlgoDesign.Strings in
example : BWT.Valid ⟨[2,1,3,1,3,1,0], bwtOfSorted [2,1,3,1,3,1,0]⟩ := by decide
open AlgoDesign.Strings in
example : BWT.SameLetters ⟨[2,1,3,1,3,1,0], [0,1,1,1,2,3,3]⟩ ∧
    ¬ BWT.LetterBeforeEachSuffix ⟨[2,1,3,1,3,1,0], [0,1,1,1,2,3,3]⟩ := by decide
open AlgoDesign.Strings in
example : BWT.SameLetters ⟨[2,1], [2,1]⟩ ∧ BWT.LetterBeforeEachSuffix ⟨[2,1], [2,1]⟩ ∧
    ¬ BWT.SentinelOnce ⟨[2,1], [2,1]⟩ := by decide
-- The boundary texts: the empty text stores nothing, and `[0]`'s one letter is its own `$`.
open AlgoDesign.Strings in
example : BWT.LetterBeforeEachSuffix ⟨[], []⟩ ∧ BWT.LetterBeforeEachSuffix ⟨[0], [0]⟩ ∧
    ¬ BWT.LetterBeforeEachSuffix ⟨[0], []⟩ := by decide
-- The library's operations: the suffixes of `banana$` come back from its letters alone.
open AlgoDesign.Strings in
example : BWT.ops.suffixes (BWT.ops.transform [2,1,3,1,3,1,0]) = [6,5,3,1,0,4,2] ∧
    BWT.ops.invert (BWT.ops.transform [2,1,3,1,3,1,0]) = [2,1,3,1,3,1,0] := by decide
-- Backward search's state after reading `a` in `banana$`: rows 1 to 3; one row short breaks box
-- invariant 1.
open AlgoDesign.Strings in
example : BackwardSearch.Valid
      ⟨⟨[2,1,3,1,3,1,0], suffixArray [2,1,3,1,3,1,0]⟩, [1], [1], 1, 4, List.suffix_refl _⟩ ∧
    ¬ BackwardSearch.StretchHoldsMatches
      ⟨⟨[2,1,3,1,3,1,0], suffixArray [2,1,3,1,3,1,0]⟩, [1], [1], 1, 3, List.suffix_refl _⟩ :=
  by decide
-- The trie and Patricia pieces decide through their proved mirrors.
open AlgoDesign.Strings in
example : Trie.Valid (Trie.empty : Trie Nat) := by decide
open AlgoDesign.Strings in
example : Patricia.DistinctFirstLetters (.node none [([], .node none [([5], .node (some 0) [])])] :
    Patricia Nat) ∧
    ¬ Patricia.NoEmptyBranches (.node none [([], .node none [([5], .node (some 0) [])])] :
      Patricia Nat) := by
  decide
-- The corpus pieces: a record holding the separator breaks `SeparatorOutsideRecords` alone.
open AlgoDesign.Strings in
example : Corpus.SentinelBelowSeparator 1 0 ∧ Corpus.SentinelBelowRecords 0 [[2,1,3]] ∧
    ¬ Corpus.SeparatorOutsideRecords 1 [[2,1,3]] := by decide
-- Rabin–Karp's state at the book's trace parameters: the first window of `3 1 4` carries its
-- fingerprint.
open AlgoDesign.Strings in
example : RabinKarp.Valid (RabinKarp.Scan.first 10 13 [3, 1, 4] [3, 1]) ∧
    (RabinKarp.Scan.first 10 13 [3, 1, 4] [3, 1]).number = fingerprint 10 13 [3, 1] ∧
    ¬ RabinKarp.NumberMatchesWindow
      { RabinKarp.Scan.first 10 13 [3, 1, 4] [3, 1] with number := fingerprint 10 13 [1, 4] } := by
  decide
-- And `FoundSoFarExact` fails alone on a state that has not reported the occurrence it passed.
open AlgoDesign.Strings in
example : ¬ RabinKarp.FoundSoFarExact
    ⟨[3, 1, 4], [3, 1], 10, 13, 1, [1, 4], fingerprint 10 13 [1, 4], [], rfl, by decide⟩ ∧
    RabinKarp.NumberMatchesWindow
    ⟨[3, 1, 4], [3, 1], 10, 13, 1, [1, 4], fingerprint 10 13 [1, 4], [], rfl, by decide⟩ := by
  decide

/-! ## The contracts reject the naive candidates

Each candidate below gets something wrong that its `Contract` turns away: a Rabin–Karp whose scan
keeps a stale number fails the promise; a trie or Patricia tree that files each word as one child
under a code of it fails the promise, read through the structure's own `get`; an FM-index whose
search is right only on the indexes it builds fails the promise on a valid index built at
another interval. -/

section Contracts

open AlgoDesign.Strings

/-- A Rabin–Karp that never updates its number: every window carries the first window's number, so
a window is a candidate only when the first window's number equals the pattern's, then checked
letter by letter. -/
private def staleRabinKarp : RabinKarp.Ops where
  base := 10
  modulus := 13
  finder :=
    { build := id, text := id, Valid := fun _ => True
      search := fun t p => (occurrenceList t p).filter
        fun _ => decide (fingerprint 10 13 (t.take p.length) = fingerprint 10 13 p) }
  Valid := RabinKarp.Valid
  searchM t p := ⟨(occurrenceList t p).filter
    fun _ => decide (fingerprint 10 13 (t.take p.length) = fingerprint 10 13 p), 0⟩
  counted _ _ := rfl

/-- In `[3, 1, 4]` the pattern `[1, 4]` occurs at 1, but the first window's number, `31 mod 13`,
is not the pattern's, `14 mod 13`, so the stale scan misses it. -/
example : ¬ RabinKarp.Contract staleRabinKarp := by
  intro h
  have := h.promise.every [3, 1, 4] trivial [1, 4] 1 (by decide)
  revert this
  decide

/-- A code of a word, one number per word. -/
private def wordCode (w : List Nat) : Nat := w.foldl (fun acc c => acc * 1000 + c + 1) 0

/-- A trie that files each word as one child of the root, under its code. -/
private def codedTrie : Trie.Ops Nat where
  empty := Trie.empty
  insert w a t := Trie.insert t [wordCode w] a
  remove w t := Trie.remove t [wordCode w]
  keysWithPrefix _ _ := []
  Valid := Trie.Valid
  getM w t := ⟨Trie.get t w, 1⟩
  insertM w a t := ⟨Trie.insert t [wordCode w] a, 1⟩
  removeM w t := ⟨Trie.remove t [wordCode w], 1⟩
  counted _ _ := ⟨rfl, fun _ => rfl, rfl⟩

example : ¬ Trie.Contract codedTrie := by
  intro h
  have := h.promise.insert_stores [1, 2] 5 Trie.empty h.promise.valid_empty
  revert this
  decide

/-- A Patricia tree that files each word as one child of the root, under its code. -/
private def codedPatricia : Patricia.Ops Nat where
  empty := Patricia.empty
  insert w a t := Patricia.insert t [wordCode w] a
  remove w t := Patricia.remove t [wordCode w]
  keysWithPrefix _ _ := []
  Valid := Patricia.Valid
  getM w t := ⟨Patricia.get t w, 1⟩
  counted _ _ := rfl

example : ¬ Patricia.Contract codedPatricia := by
  intro h
  have := h.promise.insert_stores [1, 2] 5 Patricia.empty h.promise.valid_empty
  revert this
  decide

/-- An FM-index whose search is right only at the sampling rate it builds with. -/
private def builtOnlyFM : FMIndex.Ops where
  build u := FMIndex.build (u ++ [0]) 2
  search ix p := if ix.sample = 2 then FMIndex.locate ix p else []
  Valid := FMIndex.Valid
  count := FMIndex.count
  countM := FMIndex.countM
  locateM ix p := ⟨if ix.sample = 2 then FMIndex.locate ix p else [], 0⟩
  counted ix p := ⟨FMIndex.ret_countM ix p, rfl⟩

/-- Built at interval 3, the index of `[2, 1, 3, 1, 3, 1]` is valid, and `[1, 3]` occurs at 1, but
the candidate's search answers nothing there. -/
example : ¬ FMIndex.Contract builtOnlyFM := by
  intro h
  have hv : FMIndex.Valid (FMIndex.build [2, 1, 3, 1, 3, 1, 0] 3) :=
    FMIndex.valid_build (by decide) (by decide) (valid_suffixArray _) (by decide)
  have := h.promise.2.every _ hv [1, 3] 1 (by decide)
  revert this
  decide

end Contracts
