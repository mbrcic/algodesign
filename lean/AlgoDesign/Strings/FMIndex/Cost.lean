/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import AlgoDesign.Strings.FMIndex.Search

/-!
# FM-index: the cost of counting

`backwardSearchM` returns `backwardSearch`'s interval after exactly `m` steps for a pattern of
length `m`. The costs of locating and extracting are in `Sampled.lean`.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- `backwardSearch` with one tick per backward step (two `occ` reads), with no early exit. -/
def backwardSearchM (bwt : List Nat) (cLess : Nat → Nat) :
    List Nat → Cslib.Algorithms.Lean.TimeM ℕ (Nat × Nat)
  | [] => ⟨(0, bwt.length), 0⟩
  | c :: p =>
      let r := backwardSearchM bwt cLess p
      ⟨backwardStep bwt cLess c r.ret.1 r.ret.2, r.time + 1⟩

/-- Cost erasure: the timed search returns `backwardSearch`'s interval. -/
theorem ret_backwardSearchM (bwt : List Nat) (cLess : Nat → Nat) (p : List Nat) :
    (backwardSearchM bwt cLess p).ret = backwardSearch bwt cLess p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
      simp only [backwardSearchM, ih]
      rfl

/-- Counting costs exactly `m` backward steps for a pattern of length `m`, whatever the text. -/
theorem time_backwardSearchM (bwt : List Nat) (cLess : Nat → Nat) (p : List Nat) :
    (backwardSearchM bwt cLess p).time = p.length := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [backwardSearchM, ih]

end AlgoDesign.Strings
