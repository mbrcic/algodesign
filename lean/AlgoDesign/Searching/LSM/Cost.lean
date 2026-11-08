/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Invariant

/-!
# LSM-tree: cost of a read

Runs counted through `Cslib.Algorithms.Lean.TimeM`, one tick per run a read checks, the memtable
among them, as `lsm.rs`'s `lookup` does: the memtable, then each run newest first, stopping at the
first that mentions the key. `Store.getM` erases to `Store.get` (`Store.ret_getM`), and on a store
whose batches are few it checks at most the memtable, level 0's runs and one run per deeper level
(`Store.time_getM_le`). The work inside a run is not counted. A write's cost, its rewrites on the
way down, is argued, `WriteRewrites`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LSM

variable {α β : Type} [LinearOrder α]

/-- `lookup`, counting the runs it checks: one tick per run, newest first, until one mentions
`a`. -/
def lookupM (a : α) : List (Run α β) → TimeM ℕ (Option (Option β))
  | [] => pure none
  | r :: rs => do
      tick 1
      match Run.lookup a r with
      | some v => pure (some v)
      | none => lookupM a rs

theorem ret_lookupM (a : α) (t : List (Run α β)) : (lookupM a t).ret = lookup a t := by
  induction t with
  | nil => rfl
  | cons r rs ih =>
      simp only [lookupM, lookup, ret_bind]
      split <;> simp_all

theorem time_lookupM_le (a : α) (t : List (Run α β)) : (lookupM a t).time ≤ t.length := by
  induction t with
  | nil => simp [lookupM]
  | cons r rs ih =>
      simp only [lookupM, time_bind, time_tick, List.length_cons]
      split
      · simp
      · omega

namespace Store

/-- `get`, counting the runs it checks, the memtable among them. Rust: `Lsm::get`. -/
def getM (a : α) (s : Store α β) : TimeM ℕ (Option β) := Option.join <$> lookupM a s.runs

theorem ret_getM (a : α) (s : Store α β) : (getM a s).ret = get a s := by
  simp [getM, get_eq, LSM.get, ret_lookupM]

omit [LinearOrder α] in
theorem sum_length_le {ls : List (List (Run α β))} (h : ∀ l ∈ ls, l.length ≤ 1) :
    ls.flatten.length ≤ ls.length := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      have := h l (by simp)
      have := ih (fun l' hl' => h l' (by simp [hl']))
      omega

omit [LinearOrder α] in
/-- A store whose batches are few holds at most the memtable, `level0Runs` runs on level 0 and one
run per deeper level. -/
theorem length_runs_le {s : Store α β} (h : FewRuns s) :
    s.runs.length ≤ 1 + s.shape.level0Runs + (deeper s).length := by
  obtain ⟨h0, h1⟩ := h
  have hd := sum_length_le h1
  have hflat := headD_append_flatten_tail s.levels
  have : s.runs.length = 1 + (s.levels.headD []).length + s.levels.tail.flatten.length := by
    simp only [runs, List.length_cons, ← hflat, List.length_append]
    omega
  simp only [level0, deeper] at h0 hd ⊢
  omega

/-- **A read checks at most the memtable, level 0's runs and one run per deeper level.** -/
theorem time_getM_le {s : Store α β} (h : FewRuns s) (a : α) :
    (getM a s).time ≤ 1 + s.shape.level0Runs + (deeper s).length := by
  simpa [getM] using Nat.le_trans (time_lookupM_le a s.runs) (length_runs_le h)

end Store

/-- One write (`some b`) or delete (`none`), by the operations `o`. -/
def Ops.apply (o : Ops α β) (a : α) : Option β → Store α β → Store α β
  | some b, s => o.write a b s
  | none, s => o.delete a s

/-- A history of writes and deletes run in order, each by `writeM`, its counts added up. -/
def runWrites (writeM : α → Option β → Store α β → TimeM ℕ (Store α β)) :
    List (α × Option β) → Store α β → TimeM ℕ (Store α β)
  | [], s => pure s
  | (a, v) :: rest, s => do
      let s' ← writeM a v s
      runWrites writeM rest s'

/-- **Argued, not proved:** a write that counts the entries it writes to disk, answers as the write
does, and over any history of `m` writes and deletes from an empty store at a usable shape writes
at most `m · (level0Runs + (ratio + 1) · L)` entries, `L` the number of levels at the end. The
counted unit: each entry of the run a flush seals, and each entry of every merge's result (level
0's merge, and every push down). The box's "rewritten several times on its way down": counted per
write, not per entry, since a key that stays put while others are rewritten around it is rewritten
at every merge into its level. Lean has no counted write, by choice, so `Contract` does not include
it. -/
def WriteRewrites (o : Ops α β)
    (writeM : α → Option β → Store α β → TimeM ℕ (Store α β)) : Prop :=
  (∀ a v s, (writeM a v s).ret = o.apply a v s) ∧
  ∀ sh, sh.Usable → ∀ hist : List (α × Option β),
    let run := runWrites writeM hist (o.empty sh)
    run.time ≤ hist.length * (sh.level0Runs + (sh.ratio + 1) * run.ret.levels.length)

end LSM

end AlgoDesign.Searching
