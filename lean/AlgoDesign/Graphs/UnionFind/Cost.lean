/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.UnionFind.Find

/-!
# Union-find: depth and the cost of a lookup

Box invariant 2 bounds the depth: ranks rise strictly along a path upward, so a path of `k` links
ends at a root of rank at least `k`, whose tree holds at least `2 ^ k` items. So every item reaches
its root within `log₂` of its tree's size (`depth_le_log_size`), and so within `log₂ n`
(`depth_le_log`).

`findM` is `find` counting one step per link walked, through `Cslib.Algorithms.Lean.TimeM`; the
repointing on the way back is free. It answers as `find` does (`ret_findM`) and, on a valid
structure, walks at most `log₂ n` links (`time_findM_le_log`).

A long run of operations costs nearly a constant per operation, `O(m α(n))` for `m` operations
(Cormen, Leiserson, Rivest and Stein, §19.4, Theorem 19.14; Weiss, §8.6). That bound is argued from
the sources, not proved here: its proof is a potential-function argument over whole sequences of
operations, a long proof of a textbook bound.
-/

@[expose] public section

namespace AlgoDesign.Graphs.UnionFind

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-! ## Depth -/

variable {u : UnionFind}

/-- Along a path upward that has not met a root, the rank grows by at least one per link. -/
theorem le_rank_iterate (hv : u.Valid) {i : ℕ} (hi : i < u.n) {k : ℕ}
    (hk : ¬ u.IsRoot (u.parent^[k] i)) : k ≤ u.rank (u.parent^[k] i) := by
  have hlt : ∀ j < u.n, u.parent j < u.n := fun j hj => (hv.1 j hj).1
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk' : ¬ u.IsRoot (u.parent^[k] i) := fun h =>
      hk (by rw [Function.iterate_succ_apply', h]; exact h)
    have := rank_lt_iterate hlt hv.2.1 hi (k := k + 1) (Nat.lt_add_one k) hk
    have := ih hk'
    omega

/-- **Depth within the tree's size**: if `i`'s tree has fewer than `2 ^ (L + 1)` items, then `L`
links up from `i` reach its root. -/
theorem iterate_eq_root_of_size_lt (hv : u.Valid) {i : ℕ} (hi : i < u.n) {L : ℕ}
    (hL : (List.range u.n).countP (fun j => u.root j = u.root i) < 2 ^ (L + 1)) :
    u.parent^[L] i = u.root i := by
  have hlt : ∀ j < u.n, u.parent j < u.n := fun j hj => (hv.1 j hj).1
  by_cases hroot : u.IsRoot (u.parent^[L] i)
  · exact iterate_eq_root hv.1 hi hroot
  · exfalso
    have h1 := le_rank_iterate hv hi hroot
    have h2 := hv.2.1 _ (iterate_lt hlt hi L) hroot
    have h3 := rank_le_iterate hlt hv.2.1 (iterate_lt hlt hi (L + 1)) u.n
    rw [← Function.iterate_add_apply, iterate_eq_root_of_le hv.1 hi (k := u.n + (L + 1)) (by omega),
      Function.iterate_succ_apply'] at h3
    have hsize : 2 ^ u.rank (u.root i) ≤
        (List.range u.n).countP (fun j => u.root j = u.root i) :=
      hv.2.2 _ (iterate_lt hlt hi u.n) (hv.1 i hi).2
    have : 2 ^ (L + 1) ≤ 2 ^ u.rank (u.root i) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- **No path is longer than `log₂` of its tree's size.** -/
theorem depth_le_log_size (hv : u.Valid) {i : ℕ} (hi : i < u.n) :
    u.parent^[Nat.log2 ((List.range u.n).countP (fun j => u.root j = u.root i))] i = u.root i :=
  iterate_eq_root_of_size_lt hv hi Nat.lt_log2_self

/-- **No path is longer than `log₂ n`**: every item reaches its root within `log₂ n` links. -/
theorem depth_le_log (hv : u.Valid) {i : ℕ} (hi : i < u.n) :
    u.parent^[Nat.log2 u.n] i = u.root i := by
  refine iterate_eq_root_of_size_lt hv hi (lt_of_le_of_lt ?_ Nat.lt_log2_self)
  exact (List.countP_le_length).trans (List.length_range).le

/-! ## The counted lookup -/

/-- The walk behind `findM`: `findAux`, with one step counted per link walked up. -/
def findAuxM : ℕ → (ℕ → ℕ) → ℕ → TimeM ℕ ((ℕ → ℕ) × ℕ)
  | 0, p, x => pure (p, x)
  | f + 1, p, x =>
    if p x = x then pure (p, x)
    else do
      tick 1
      let pr ← findAuxM f p (p x)
      pure (Function.update pr.1 x pr.2, pr.2)

/-- **Lookup, counting the links walked.** -/
def findM (u : UnionFind) (x : ℕ) : TimeM ℕ (UnionFind × ℕ) := do
  let pr ← findAuxM u.n u.parent x
  pure ({ u with parent := pr.1 }, pr.2)

theorem ret_findAuxM (fuel : ℕ) (p : ℕ → ℕ) (x : ℕ) :
    (findAuxM fuel p x).ret = findAux fuel p x := by
  induction fuel generalizing x with
  | zero => rfl
  | succ f ih =>
    simp only [findAuxM, findAux]
    split_ifs
    · rfl
    · simp [ih]

/-- **The counted lookup answers as the lookup does.** -/
theorem ret_findM (u : UnionFind) (x : ℕ) : (findM u x).ret = u.find x := by
  simp [findM, find, ret_findAuxM]

/-- The walk counts at most `k` links when `k` links up from `x` reach a root. -/
theorem time_findAuxM_le (fuel : ℕ) (p : ℕ → ℕ) {x k : ℕ} (hk : p (p^[k] x) = p^[k] x) :
    (findAuxM fuel p x).time ≤ k := by
  induction fuel generalizing x k with
  | zero => simp [findAuxM]
  | succ f ih =>
    simp only [findAuxM]
    split_ifs with hx
    · simp
    · cases k with
      | zero => exact absurd hk hx
      | succ k =>
        rw [Function.iterate_succ_apply] at hk
        simp only [time_bind, time_tick, time_pure]
        have := ih (x := p x) hk
        omega

/-- **A lookup walks at most `log₂ n` links**, on a valid structure. -/
theorem time_findM_le_log (hv : u.Valid) {x : ℕ} (hx : x < u.n) :
    (findM u x).time ≤ Nat.log2 u.n := by
  have hroot : u.IsRoot (u.parent^[Nat.log2 u.n] x) := by
    rw [depth_le_log hv hx]; exact (hv.1 x hx).2
  simpa [findM] using time_findAuxM_le u.n u.parent hroot

/-- In `twoDeep`, looking up 0 walks its two links, as many as `log₂ 4`. -/
example : (findM twoDeep 0).time = 2 ∧ Nat.log2 twoDeep.n = 2 := by decide

end AlgoDesign.Graphs.UnionFind
