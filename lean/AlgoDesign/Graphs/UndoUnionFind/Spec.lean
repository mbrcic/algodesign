/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Basic

/-!
# Union-find with undo: the specification

No design box exists for undo. The specification's source is the Graphs chapter's appendix
"Taking a merge back", whose rule is quoted here; its source is Westbrook and Tarjan, *SIAM J.
Comput.* 18(1), 1989, p. 3, crediting Mannila and Ukkonen:

> Keep the rank rule and drop path compression. Then a merge changes one parent and perhaps one
> rank, and a log of those changes, one entry per `union` call, an empty one when nothing merged,
> lets the last call be undone exactly.

The appendix's `undo` listing pops the newest entry: the root that went under is a root again, a
risen rank falls back, and the group count rises by one; an empty entry takes one undo step and
changes nothing.

The merge's guard and tie rule are the union-find's (`UnionFind/Spec.lean`): both roots found
first, `x`'s then `y`'s; the same root merges nothing and answers no; the root of lower rank goes
under the other; on equal ranks the second root goes under the first, whose rank rises by one.
On an empty log, `undo` does nothing and answers no: the library's choice, not the source's.

The rule, clause by clause, each held by a theorem about the library's operations (`init`,
`find`, `union`, `joined`, `count`, `undo` and the counting `findM`) in `UndoUnionFind.lean`,
which imports the whole structure.

- "Union by rank" [proved] → `merge_logs`: the merge keeps the union-find's own promise,
  `UnionSpec`, guard and tie rule included, by `merge_spec` (`UndoUnionFind/Basic.lean`).
- "without path compression" [proved] → by type: `find` and `joined` hand back only an answer,
  never a structure, so a lookup changes nothing. A merge compresses nothing either:
  `merge_logs` makes `unmerge` of its entry give back the structure before it, and
  `unmerge` resets one link and one rank. `lookup_tells`: `find` answers the root.
  Without compression no lookup ever shortens a path, so its worst case is the tree's depth, at
  most `log₂ n` links: `time_findM_le_log` (`UndoUnionFind/Cost.lean`), from the union-find's
  `depth_le_log`.
- "a log whose entries record the root that stopped being a root and whether the other root's
  rank rose" [proved] → the entry `some (c, rose)`; `unmerge` below says what it means, and
  `merge_logs`: each `union` call adds one entry, and taking that entry back with `unmerge`
  gives the structure before the call. What the entry holds: `merge_entry`
  (`UndoUnionFind/Basic.lean`).
- "rollback pops entries" [proved] → `undo_takes_back`: `undo` right after `union` gives
  back the state before it, structure and log, and answers yes. Over a whole run,
  `rollback_unions` (`UndoUnionFind/Promise.lean`): rolling back walks through every earlier
  state, last first; and `rolls_back`: after a run of merges and any number of undos, the
  lookups and `joined` say exactly who the merges still in the log joined.
- "One entry per `union` call, an empty one when nothing merged" [proved] → `merge_logs`,
  and `undo_takes_back` for a merge of two items already together: one `undo` takes back that
  call alone.
- "a rollback restores the group count" [proved] → `undo_takes_back` restores the whole
  structure, its count included; `counts_groups`: the count answers the number of roots, one per
  group.
- Empty log [proved] → `undo_takes_back`: `undo` does nothing and answers no.
- Invariants [proved] → `Valid`: the union-find's `Valid` and `WellFormed`, and `RollbacksLegal`,
  every structure the log rolls back to is legal and well formed; kept by `init`, `union` and
  `undo` (`keeps_invariants`). The union-find's `Valid` and `WellFormed` alone are not kept by
  `undo`: an entry that no merge wrote, taken back,
  leaves a count that is not the number of roots (an example in the tests). `RollbacksLegal` is
  the library's choice of invariant for the log.
- Cost [proved] → `time_findM_le_log`: one lookup walks at most `log₂ n` links; `findM` counts
  one step per link and answers as `find` does, `ret_findM`. A merge writes at most one
  link and one rank and an undo takes them back [mentioned]: the operations' shape, not a claim.
-/

@[expose] public section

namespace AlgoDesign.Graphs

/-- A union-find with a log of its merges, newest first. An entry `some (c, rose)` is a merge
that put root `c` under another root, `rose` saying whether that root's rank rose; `none` is a
`union` call that merged nothing. -/
structure UndoUnionFind where
  /-- The union-find: links, ranks, the group count. -/
  uf : UnionFind
  /-- One entry per `union` call, newest first. -/
  log : List (Option (ℕ × Bool))

namespace UndoUnionFind

/-- **Taking back one entry**: what the entry means. `some (c, rose)`: `c` is a root again, its
old parent's rank drops by one if it rose, and there is one group more. `none`: nothing. -/
def unmerge (u : UnionFind) : Option (ℕ × Bool) → UnionFind
  | none => u
  | some (c, rose) =>
    { u with parent := Function.update u.parent c c,
             rank := if rose then Function.update u.rank (u.parent c) (u.rank (u.parent c) - 1)
               else u.rank,
             count := u.count + 1 }

/-- **Every structure the log rolls back to is legal**: taking back the newest entry gives a
legal, well-formed union-find, and so on down the log. -/
def RollbacksLegal : UnionFind → List (Option (ℕ × Bool)) → Prop
  | _, [] => True
  | u, e :: log =>
    ((unmerge u e).Valid ∧ (unmerge u e).WellFormed) ∧ RollbacksLegal (unmerge u e) log

/-- **A legal union-find with undo**: the union-find is legal and well formed, and so is every
structure its log rolls back to. -/
def Valid (s : UndoUnionFind) : Prop :=
  (s.uf.Valid ∧ s.uf.WellFormed) ∧ RollbacksLegal s.uf s.log

end UndoUnionFind

end AlgoDesign.Graphs
