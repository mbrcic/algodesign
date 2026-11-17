/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Spec
public import AlgoDesign.Graphs.Blocks.Decide
public import AlgoDesign.Graphs.Blocks.Basic
public import AlgoDesign.Graphs.Blocks.Cycles
public import AlgoDesign.Graphs.Blocks.CycleTheory
public import AlgoDesign.Graphs.Blocks.Pieces
public import AlgoDesign.Graphs.Blocks.Walk
public import AlgoDesign.Graphs.Blocks.Inv
public import AlgoDesign.Graphs.Blocks.Tree
public import AlgoDesign.Graphs.Blocks.Groups
public import AlgoDesign.Graphs.Blocks.StepShape
public import AlgoDesign.Graphs.Blocks.StepClimb2
public import AlgoDesign.Graphs.Blocks.StepBlocks
public import AlgoDesign.Graphs.Blocks.Run
public import AlgoDesign.Graphs.Blocks.Final
public import AlgoDesign.Graphs.Blocks.Report
public import AlgoDesign.Graphs.Blocks.Separate
public import AlgoDesign.Graphs.Blocks.Forest
public import AlgoDesign.Graphs.Blocks.ForestRoot
public import AlgoDesign.Graphs.Blocks.ForestDfs
public import AlgoDesign.Graphs.Blocks.ForestPromise

/-! Bridges, cut vertices, blocks and the block-cut forest. The contract is in `Blocks/Spec.lean`;
this file imports the whole of it and proves the library meets it. -/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

open Walk

/-! ## Every state of the walk keeps its shape -/

/-- One step keeps the walk's shape. -/
theorem shape_step {g : Graph} (hg : g.WellFormed) {w : Walk} (hS : Shape (g := g) w)
    (hO : Outside (g := g) w) (hT : OpenTaken (g := g) w) :
    Shape (g := g) (step g w) ∧ Outside (g := g) (step g w) :=
  ⟨⟨entriesOk_step hg hS hO, pathOk_step hg hS hO, statusOk_step hg hS hO, treeOk_step hg hS hO,
    openBelow_step hg hS hO, takenOk_step hg hS hO, outerOk_step hg hS hO,
    childrenOk_step hg hS hO,
    ⟨by rw [step_g, hS.2.2.2.2.2.2.2.2.1.1], climb_step hg hS hO hT⟩, edges_nodup_step hg hS hO hT,
    edges_iff_step hg hS hO hT, stackOk_step hg hS hO hT, blocksOk_step hg hS hO hT,
    bridgesOk_step hg hS hO hT, cutOk_step hg hS hO hT⟩, outside_step hg hS hO⟩

/-- **Every state of the walk keeps its shape.** -/
theorem shape_run {g : Graph} (hg : g.WellFormed) : ∀ k,
    Shape (g := g) (run g k (start g)) ∧ Outside (g := g) (run g k (start g)) ∧
      OpenTaken (g := g) (run g k (start g)) ∧ RootsOk (g := g) (run g k (start g))
  | 0 => ⟨shape_start.1, shape_start.2, openTaken_start, rootsOk_start⟩
  | k + 1 => by
    obtain ⟨hS, hO, hT, hR⟩ := shape_run hg k
    rw [run_succ']
    exact ⟨(shape_step hg hS hO hT).1, (shape_step hg hS hO hT).2, openTaken_step hg hS hO hT,
      rootsOk_step hg hS hO hT hR⟩

/-- **The walk keeps its invariants**: every state of the walk on a well-formed graph is
`Valid`, the box's two invariants. -/
theorem valid_along {g : Graph} (hg : g.WellFormed) (k : ℕ) :
    Valid (run g k (start g)) :=
  valid_of_shape hg (shape_run hg k).1 (shape_run hg k).2.1

/-- The walk has finished when its fuel runs out. -/
theorem done_final' {g : Graph} (hg : g.WellFormed) : Done (g := g) (final g) :=
  done_final hg fun k => ⟨(shape_run hg k).1, (shape_run hg k).2.1⟩

/-! ## The library meets its contract -/

/-- The library's procedures, as the box names them: the walk and its report, and the separators
read off the block-cut forest. -/
def ops : Ops where
  start := start
  step := step
  blocks := blocks
  separators g u v := (forest g (blocks g)).separators u v
  Valid := Valid
  walks g := by
    change report g (run g (steps g) (start g)) = _
    rw [run_eq_iterate]; rfl
  carries _ := rfl
  keepsGraph := step_g
  stepKeeps g hg k := by
    rw [← run_eq_iterate]
    exact valid_along hg k

/-- **The walk's promise**: on a well-formed graph it reports exactly the bridges and the cut
vertices, and the network's blocks with their vertices. -/
theorem walk_promise {g : Graph} (hg : g.WellFormed) :
    (∀ e, e ∈ (blocks g).bridges ↔ IsBridge g e) ∧
    (∀ v, v ∈ (blocks g).cutVertices ↔ IsCutVertex g v) ∧
    BlocksAgree g (blocks g) ∧ VerticesAgree g (blocks g) ∧ (blocks g).cutVertices.Nodup :=
  report_promise hg (shape_run hg _).1 (shape_run hg _).2.1 (done_final' hg)

/-- **The forest's promise**: for two vertices in one piece, the separators listed are exactly the
vertices whose failure alone separates them; for vertices in different pieces, `none`. -/
theorem separators_promise {g : Graph} (hg : g.WellFormed) {u v : ℕ} (hu : u < g.n)
    (hv : v < g.n) :
    (g.Connected u v → ∃ l, ops.separators g u v = some l ∧ ∀ q, q ∈ l ↔ Separates g q u v) ∧
    (¬ g.Connected u v → ops.separators g u v = none) :=
  forest_promise hg (shape_run hg _).1 (shape_run hg _).2.1 (done_final' hg)
    (shape_run hg _).2.2.2 hu hv

/-- **The library meets its contract.** -/
theorem contract : Contract ops where
  promise :=
    ⟨fun _ hg => ⟨(walk_promise hg).1, (walk_promise hg).2.1⟩,
      fun _ hg _ hu _ hv => separators_promise hg hu hv⟩
  invariants _ := Iff.rfl
  cost g hg := by
    change Done (g := g) ((step g)^[steps g] (start g))
    rw [← run_eq_iterate]
    exact done_final' hg

end AlgoDesign.Graphs.Blocks
