/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UndoUnionFind.Basic
public import AlgoDesign.Graphs.UnionFind.Cost

/-!
# Union-find with undo: the cost of a lookup

`findM` walks up from `x` to its root, counting one step per link, through
`Cslib.Algorithms.Lean.TimeM`. It answers as `find` does (`ret_findM`). Nothing shortens a path,
so every lookup is a worst case: the walk is the item's depth, at most `log₂ n` links on a legal
structure (`time_findM_le_log`), by the union-find's `depth_le_log`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UndoUnionFind

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-- Walk up from `x`, at most `fuel` links, stopping at a root and counting one step per link. -/
def walkM : ℕ → (ℕ → ℕ) → ℕ → TimeM ℕ ℕ
  | 0, _, x => pure x
  | f + 1, p, x =>
    if p x = x then pure x
    else do
      tick 1
      walkM f p (p x)

/-- **Lookup, counting the links walked.** -/
def findM (s : UndoUnionFind) (x : ℕ) : TimeM ℕ ℕ := walkM s.uf.n s.uf.parent x

/-- The walk lands where `fuel` links up from `x` lead. -/
theorem ret_walkM (fuel : ℕ) (p : ℕ → ℕ) (x : ℕ) : (walkM fuel p x).ret = p^[fuel] x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ f ih =>
    simp only [walkM]
    split_ifs with hx
    · simp [Function.iterate_fixed hx]
    · simp [ih]

/-- **The counted lookup answers as the lookup does.** -/
theorem ret_findM (s : UndoUnionFind) (x : ℕ) : (findM s x).ret = s.find x :=
  ret_walkM _ _ _

/-- The walk counts at most `k` links when `k` links up from `x` reach a root. -/
theorem time_walkM_le (fuel : ℕ) (p : ℕ → ℕ) {x k : ℕ} (hk : p (p^[k] x) = p^[k] x) :
    (walkM fuel p x).time ≤ k := by
  induction fuel generalizing x k with
  | zero => simp [walkM]
  | succ f ih =>
    simp only [walkM]
    split_ifs with hx
    · simp
    · cases k with
      | zero => exact absurd hk hx
      | succ k =>
        rw [Function.iterate_succ_apply] at hk
        simp only [time_bind, time_tick]
        have := ih (x := p x) hk
        omega

/-- **One lookup walks at most `log₂ n` links**, on a legal structure: nothing shortens a path,
and no path is longer than `log₂ n` (`UnionFind.depth_le_log`). -/
theorem time_findM_le_log {s : UndoUnionFind} (hv : s.uf.Valid) {x : ℕ} (hx : x < s.uf.n) :
    (findM s x).time ≤ Nat.log2 s.uf.n := by
  have hroot : s.uf.IsRoot (s.uf.parent^[Nat.log2 s.uf.n] x) := by
    rw [UnionFind.depth_le_log hv hx]; exact (hv.1 x hx).2
  exact time_walkM_le _ _ hroot

end AlgoDesign.Graphs.UndoUnionFind
