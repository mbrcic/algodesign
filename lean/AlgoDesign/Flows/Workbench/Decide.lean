/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Workbench.Spec
public import AlgoDesign.Flows.Decide

/-! # The design project's contract: deciding its pieces on one network

Each piece of the contract asks something of every network. On one network and one candidate's
answer and rounds, each piece is a claim about them alone, and it decides, so `decide` judges small
networks. They are the pieces the Python bench checks, one function each
(`algodesign.flows.workbench`): `ReturnsAFlowOn` is `is_flow`, `CutMatchesFlowOn`
`is_cut_of_flow`, `AddsAlongAugmentingPathsOn` `adds_along_augmenting_paths`, and the speed
menu's `RoundsAtMostNOn`, `AugmentationsAtMostNMOn` and `BoundOn` are `rounds_at_most_n`,
`augmentations_at_most_nm` and `bounded_by`. Each `Ops` piece is its one-network piece on every
well-formed network (`returnsAFlow_iff` and the rest).

"The largest" speaks of every flow, and no bench tries them all. It needs no check of its own: an
answer beside a cut of the same amount is the largest, since no flow exceeds any cut
(`largestOn_of_cut`, from `value_le_cutCapacity`). "Some bound set by size" speaks of every
network, and no finite set of networks decides it: the bench checks a bound the reader states
(`BoundOn`), and the menu's piece is that some stated bound holds everywhere
(`boundSetBySize_iff`).

A rule that keeps the slot's promise (`PathRule.Promise`) keeps the contract for any speed
requirement it meets (`contract_of_promise`), so the library's three rules pass the bench. -/

@[expose] public section

namespace AlgoDesign.Flows.Workbench

/-! ## Augmenting paths, decided -/

instance (N : Network) (f : Flow) (p : List ResidualArrow) :
    Decidable (IsAugmentingPath N f p) := by
  unfold IsAugmentingPath; infer_instance

/-- Each added path augmenting when its turn comes, decided path by path. -/
instance decFitInTurn (N : Network) : (f : Flow) → (xs : List Augmentation) →
    Decidable (FitInTurn N f xs)
  | _, [] => isTrue trivial
  | f, x :: xs =>
    haveI := decFitInTurn N (x.apply f) xs
    decidable_of_iff ((IsAugmentingPath N f x.path ∧
      ∀ a ∈ x.path, x.amount ≤ a.residualCapacity N f) ∧ FitInTurn N (x.apply f) xs) Iff.rfl

/-! ## The pieces on one network -/

/-- **A flow**, on one network: it respects every arrow's capacity and loses nothing. -/
def ReturnsAFlowOn (N : Network) (a : Answer) : Prop := IsFlow N a.flow

/-- **A cut of the same amount**, on one network: the source on its side, the sink not, and the
capacities of arrows leaving it add up to the flow amount. -/
def CutMatchesFlowOn (N : Network) (a : Answer) : Prop :=
  N.source ∈ a.side ∧ N.sink ∉ a.side ∧ (cutCapacity N a.side : ℤ) = value N a.flow

/-- **The largest**, on one network: no flow has a larger amount. -/
def LargestOn (N : Network) (a : Answer) : Prop :=
  ∀ f, IsFlow N f → value N f ≤ value N a.flow

/-- **Along augmenting paths**, on one network: every path the rounds added was augmenting when
its turn came, its amount fitting every arrow on it, and carried at least one unit. -/
def AddsAlongAugmentingPathsOn (N : Network) (rounds : List (List Augmentation)) : Prop :=
  FitInTurn N (Flow.zero N) rounds.flatten ∧ ∀ x ∈ rounds.flatten, 1 ≤ x.amount

/-- **At most n rounds**, on one network of n vertices. -/
def RoundsAtMostNOn (N : Network) (rounds : List (List Augmentation)) : Prop :=
  rounds.length ≤ N.g.n

/-- **At most n·m added paths**, on one network of n vertices and m arrows. -/
def AugmentationsAtMostNMOn (N : Network) (rounds : List (List Augmentation)) : Prop :=
  rounds.flatten.length ≤ N.g.n * N.g.arrows.length

/-- **At most `b n m` added paths**, on one network of n vertices and m arrows, for a bound `b`
the reader states. -/
def BoundOn (b : ℕ → ℕ → ℕ) (N : Network) (rounds : List (List Augmentation)) : Prop :=
  rounds.flatten.length ≤ b N.g.n N.g.arrows.length

instance (N : Network) (a : Answer) : Decidable (ReturnsAFlowOn N a) := by
  unfold ReturnsAFlowOn; infer_instance

instance (N : Network) (a : Answer) : Decidable (CutMatchesFlowOn N a) := by
  unfold CutMatchesFlowOn; infer_instance

instance (N : Network) (rounds : List (List Augmentation)) :
    Decidable (AddsAlongAugmentingPathsOn N rounds) := by
  unfold AddsAlongAugmentingPathsOn; infer_instance

instance (N : Network) (rounds : List (List Augmentation)) :
    Decidable (RoundsAtMostNOn N rounds) := by
  unfold RoundsAtMostNOn; infer_instance

instance (N : Network) (rounds : List (List Augmentation)) :
    Decidable (AugmentationsAtMostNMOn N rounds) := by
  unfold AugmentationsAtMostNMOn; infer_instance

instance (b : ℕ → ℕ → ℕ) (N : Network) (rounds : List (List Augmentation)) :
    Decidable (BoundOn b N rounds) := by
  unfold BoundOn; infer_instance

/-- **An answer beside a cut of the same amount is the largest**, since no flow exceeds any cut. -/
theorem largestOn_of_cut {N : Network} (h : N.WellFormed) {a : Answer}
    (hc : CutMatchesFlowOn N a) : LargestOn N a :=
  fun _ hg => (value_le_cutCapacity h hg hc.1 hc.2.1).trans hc.2.2.le

/-! ## Each `Ops` piece is its one-network piece on every network -/

theorem returnsAFlow_iff (o : Flows.Ops) : o.ReturnsAFlow ↔
    ∀ N : Network, N.WellFormed → ReturnsAFlowOn N (o.maxFlow N) := Iff.rfl

theorem cutMatchesFlow_iff (o : Flows.Ops) : o.CutMatchesFlow ↔
    ∀ N : Network, N.WellFormed → CutMatchesFlowOn N (o.maxFlow N) := Iff.rfl

theorem largest_iff (o : Flows.Ops) : o.Largest ↔
    ∀ N : Network, N.WellFormed → LargestOn N (o.maxFlow N) := Iff.rfl

/-- The cut gives the third promise part: the bench checks two and gets all three. -/
theorem largest_of (o : Flows.Ops) (hc : o.CutMatchesFlow) : o.Largest :=
  (largest_iff o).2 fun N h => largestOn_of_cut h (hc N h)

theorem Ops.addsAlongAugmentingPaths_iff (o : Ops) : o.AddsAlongAugmentingPaths ↔
    ∀ N : Network, N.WellFormed → AddsAlongAugmentingPathsOn N (o.rule.run N).1 := Iff.rfl

theorem roundsAtMostN_iff (o : Flows.Ops) : o.RoundsAtMostN ↔
    ∀ N : Network, N.WellFormed → RoundsAtMostNOn N (o.rounds N) := Iff.rfl

theorem augmentationsAtMostNM_iff (o : Flows.Ops) : o.AugmentationsAtMostNM ↔
    ∀ N : Network, N.WellFormed → AugmentationsAtMostNMOn N (o.rounds N) := Iff.rfl

theorem boundSetBySize_iff (o : Flows.Ops) : o.BoundSetBySize ↔
    ∃ b : ℕ → ℕ → ℕ, ∀ N : Network, N.WellFormed → BoundOn b N (o.rounds N) := Iff.rfl


/-! ## A rule that keeps its promise keeps the contract -/

theorem fitInTurn_append {N : Network} {ys : List Augmentation} {f : Flow}
    {xs : List Augmentation} :
    FitInTurn N f (xs ++ ys) ↔ FitInTurn N f xs ∧ FitInTurn N (applyAll f xs) ys :=
  fitInTurn_append_iff

theorem runRounds_adds {r : PathRule} (hr : r.Promise) {N : Network} (h : N.WellFormed) :
    ∀ k m f, IsFlow N f → FitInTurn N f (r.runRounds N k m f).1.flatten ∧
      ∀ x ∈ (r.runRounds N k m f).1.flatten, 1 ≤ x.amount :=
  r.runRounds_augments hr h

/-- **A rule that keeps its promise keeps the contract**, for any speed requirement it meets: the
library's three rules are candidates that pass. -/
theorem contract_of_promise {r : PathRule} (hr : r.Promise) {speed : Flows.Ops → Prop}
    (hs : ∀ h, speed ((Ops.mk r).loop h)) : Contract ⟨r⟩ speed := by
  have hflow : ∀ N : Network, N.WellFormed → IsFlow N (r.run N).2 := fun N h => by
    have := (r.run_ends hr h).1 _ le_rfl
    rwa [List.take_length, ← r.run_walks] at this
  have hcut : (Ops.mk r).CutMatchesFlow := fun N h => reached_cut h (hflow N h)
    (r.run_ends hr h).2
  exact ⟨⟨fun N h => hflow N h, hcut, fun N h => largestOn_of_cut h (hcut N h),
    fun N h => runRounds_adds hr h _ _ _ (zero_isFlow N)⟩, hs⟩

end AlgoDesign.Flows.Workbench
