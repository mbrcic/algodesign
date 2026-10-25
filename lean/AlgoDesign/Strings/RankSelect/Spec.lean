/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic

/-!
# Rank and select: the specification

Sources: the Strings chapter, "Counting fast"; Jacobson, *Space-efficient static trees and graphs*
(FOCS 1989); Navarro, *Compact Data Structures*, §4.2–4.3 and Ch. 6.

`rank b i` counts the set bits before position `i`; `select b j` finds the position of the `j`-th
set bit; `occ` is `rank` over a larger alphabet. The two-level directory answers `rank` from two
small tables: an absolute count per superblock and a relative count per block. It is a supporting
structure with no box of its own; its `Valid` is the build's running state.

- Not in the box → `Directory.Valid` (`RunningTotalRight`, `OneSuperblockPerGroup`,
  `SuperblocksHoldTotals`, `OneEntryPerBlock`, `BlocksCountFromSuperblock`) →
  `Directory.valid_buildUpTo`, `Directory.valid_directory` (`Directory.lean`).

Operations and proofs: `Basic.lean` (`rank_select`, `select_eq_some_iff`, `select_rank`,
`occ_eq_rank`), `Directory.lean` (`rankTwoLevel_eq`, `occTwoLevel_eq`).
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Set bits strictly before position `i`. -/
def rank (b : List Bool) (i : Nat) : Nat := ((b.take i).filter id).length

/-- Position of the `j`-th set bit, zero-based, or `none` when there is no such bit. -/
def select (b : List Bool) (j : Nat) : Option Nat :=
  (List.range b.length).find? fun i => b[i]! && rank b i == j

/-- `rank` generalised from two symbols to `σ`: occurrences of `c` before `i`. -/
def occ (s : List Nat) (c i : Nat) : Nat := ((s.take i).filter (· == c)).length

/-- The two-level directory: an absolute count per superblock, a count relative to its superblock
per block, and the total. -/
structure Directory where
  /-- One absolute count per superblock: the set bits before it. -/
  supers : List Nat
  /-- One count per block, relative to its superblock. -/
  blocks : List Nat
  /-- The set bits in all blocks built so far. -/
  total : Nat
  deriving DecidableEq

namespace Directory

/-- The running total is the sum of the first `j` block counts. -/
def RunningTotalRight (counts : List Nat) (j : Nat) (d : Directory) : Prop :=
  d.total = (counts.take j).sum

/-- One superblock per `k` blocks begun. -/
def OneSuperblockPerGroup (k : Nat) (j : Nat) (d : Directory) : Prop :=
  d.supers.length = (j + k - 1) / k

/-- Every superblock holds the total of the blocks before it. -/
def SuperblocksHoldTotals (k : Nat) (counts : List Nat) (d : Directory) : Prop :=
  ∀ s (h : s < d.supers.length), d.supers[s] = (counts.take (s * k)).sum

/-- One block entry per block. -/
def OneEntryPerBlock (j : Nat) (d : Directory) : Prop := d.blocks.length = j

/-- Every block holds its total relative to its superblock. -/
def BlocksCountFromSuperblock (k : Nat) (counts : List Nat) (j : Nat) (d : Directory) : Prop :=
  ∀ i, i < j → d.blocks[i]? = some ((counts.take i).sum - (counts.take (i / k * k)).sum)

/-- Not in the box: the directory's invariant after the build's first `j` blocks. -/
def Valid (k : Nat) (counts : List Nat) (j : Nat) (d : Directory) : Prop :=
  RunningTotalRight counts j d ∧ OneSuperblockPerGroup k j d ∧ SuperblocksHoldTotals k counts d ∧
    OneEntryPerBlock j d ∧ BlocksCountFromSuperblock k counts j d

instance (counts : List Nat) (j : Nat) (d : Directory) : Decidable (RunningTotalRight counts j d) :=
  by unfold RunningTotalRight; infer_instance

instance (k j : Nat) (d : Directory) : Decidable (OneSuperblockPerGroup k j d) :=
  by unfold OneSuperblockPerGroup; infer_instance

instance (k : Nat) (counts : List Nat) (d : Directory) :
    Decidable (SuperblocksHoldTotals k counts d) :=
  inferInstanceAs (Decidable
    (∀ s (h : s < d.supers.length), d.supers[s] = (counts.take (s * k)).sum))

instance (j : Nat) (d : Directory) : Decidable (OneEntryPerBlock j d) :=
  by unfold OneEntryPerBlock; infer_instance

instance (k : Nat) (counts : List Nat) (j : Nat) (d : Directory) :
    Decidable (BlocksCountFromSuperblock k counts j d) :=
  inferInstanceAs (Decidable
    (∀ i, i < j → d.blocks[i]? = some ((counts.take i).sum - (counts.take (i / k * k)).sum)))

instance (k : Nat) (counts : List Nat) (j : Nat) (d : Directory) :
    Decidable (Valid k counts j d) :=
  inferInstanceAs (Decidable (RunningTotalRight counts j d ∧ OneSuperblockPerGroup k j d ∧
    SuperblocksHoldTotals k counts d ∧ OneEntryPerBlock j d ∧
    BlocksCountFromSuperblock k counts j d))

end Directory

end AlgoDesign.Strings
