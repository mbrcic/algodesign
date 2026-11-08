/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Walk

/-!
# Bridges, cut vertices and blocks: what the walk keeps

`Valid` holds the box's two invariants. The proof that every step keeps them needs more: the
shape of the depth-first walk. `Shape` gathers it, piece by piece: entry numbers, the frames of the
path, which vertices are entered, open or finished, the tree each vertex hangs in, which vertices
lie below an open one, that every row entry taken leads to a vertex above or below, the outer loop,
the root's children, the edge stack's order, and what the blocks, bridges and cut flags found so far
are, read off the tree and the climb-back numbers. Each piece speaks of vertices below `n` and is
decidable; `Outside` says that nothing beyond `n` is ever touched.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

/-! ## Reading the tree -/

/-- `x` is on the path. -/
def onPath (w : Walk) (x : ℕ) : Bool := w.path.any (·.vertex = x)

/-- `a` is `x` or above it in the walk's tree. -/
def Anc (w : Walk) (a x : ℕ) : Prop := a ∈ chain w g.n x

instance (w : Walk) (a x : ℕ) : Decidable (Anc (g := g) w a x) := by unfold Anc; infer_instance

/-- The later entry number of link `f`'s two ends: the entry number of its deeper end. -/
def deepEntry (w : Walk) (f : ℕ) : ℕ :=
  match g.links[f]? with
  | some (a, b) => max (w.entry a) (w.entry b)
  | none => 0

/-- `x` is the deeper end of link `f`: an end with the later entry number. -/
def Deep (w : Walk) (f x : ℕ) : Prop :=
  ∃ l ∈ g.links[f]?, (l.1 = x ∨ l.2 = x) ∧ w.entry x = deepEntry (g := g) w f

instance (w : Walk) (f x : ℕ) : Decidable (Deep (g := g) w f x) := by
  unfold Deep; infer_instance

/-- `x` hangs from `p` by a tree link. -/
def Child (w : Walk) (p x : ℕ) : Prop := w.entry x ≠ 0 ∧ w.arrival x ≠ none ∧ w.up x = p

instance (w : Walk) (p x : ℕ) : Decidable (Child w p x) := by unfold Child; infer_instance

/-- The number of vertices hanging from `p`. -/
def numChildren (w : Walk) (p : ℕ) : ℕ :=
  ((List.range g.n).filter fun x => decide (Child w p x)).length

/-- `c` is a finished vertex, not a root, whose subtree cannot climb above the vertex it hangs from:
the top of a block. -/
def BlockTop (w : Walk) (c : ℕ) : Prop :=
  w.finished c ∧ w.arrival c ≠ none ∧ w.entry (w.up c) ≤ w.low c

instance (w : Walk) (c : ℕ) : Decidable (BlockTop w c) := by unfold BlockTop; infer_instance

/-- `c` is the first block top on the way up from `x`. -/
def HeadIs (w : Walk) (x c : ℕ) : Prop :=
  Anc (g := g) w c x ∧ BlockTop w c ∧
    ∀ c' ∈ chain w g.n x, Anc (g := g) w c c' → c' ≠ c → ¬ BlockTop w c'

instance (w : Walk) (x c : ℕ) : Decidable (HeadIs (g := g) w x c) := by
  unfold HeadIs; infer_instance

/-- Link `f` belongs to the block topped by `c`: a taken link that is not a loop, whose deeper end
has `c` as its first block top. -/
def InGroup (w : Walk) (c f : ℕ) : Prop :=
  Taken (g := g) w f ∧ ∃ x < g.n, Deep (g := g) w f x ∧ HeadIs (g := g) w x c

instance (w : Walk) (c f : ℕ) : Decidable (InGroup (g := g) w c f) := by
  unfold InGroup; infer_instance

/-! ## The pieces -/

/-- Entry numbers: given to vertices of the graph, at most the count so far, never twice; the count
is the number of vertices entered. -/
def EntriesOk (w : Walk) : Prop :=
  (∀ x < g.n, w.entry x ≤ w.time) ∧
  (∀ x < g.n, ∀ y < g.n, w.entry x = w.entry y → w.entry x ≠ 0 → x = y) ∧
  w.time = ((List.range g.n).filter fun x => w.entry x ≠ 0).length

/-- Two frames, the upper one hanging from the lower by its arrival link. -/
def Hangs (w : Walk) (fr fr' : Frame) : Prop :=
  (∃ e ∈ fr.arrival, Joins g e fr'.vertex fr.vertex) ∧ w.up fr.vertex = fr'.vertex ∧
    w.entry fr'.vertex < w.entry fr.vertex

instance (w : Walk) (fr fr' : Frame) : Decidable (Hangs (g := g) w fr fr') := by
  unfold Hangs; infer_instance

/-- The frames: distinct open vertices of the graph, each hanging from the one below, the bottom a
root; each frame's arrival and position are the ones recorded for its vertex. -/
def PathOk (w : Walk) : Prop :=
  (w.path.map (·.vertex)).Nodup ∧ w.path.IsChain (Hangs (g := g) w) ∧
  (∀ fr ∈ w.path.getLast?, fr.arrival = none) ∧
  ∀ fr ∈ w.path, fr.vertex < g.n ∧ w.entry fr.vertex ≠ 0 ∧ w.arrival fr.vertex = fr.arrival ∧
    fr.pos = w.taken fr.vertex ∧ w.taken fr.vertex ≤ (g.adj fr.vertex).length

/-- Each vertex is not entered, open or finished; a finished vertex has taken its whole row, a
vertex not entered has nothing recorded. -/
def StatusOk (w : Walk) : Prop :=
  ∀ x < g.n, (w.entry x ≠ 0 ↔ (w.onPath x ∨ w.finished x)) ∧ ¬ (w.onPath x ∧ w.finished x) ∧
    (w.finished x → w.taken x = (g.adj x).length) ∧
    (w.entry x = 0 → w.taken x = 0 ∧ w.arrival x = none)

/-- Each entered vertex other than a root hangs by its arrival link from a vertex entered before
it. -/
def TreeOk (w : Walk) : Prop :=
  ∀ x < g.n, w.entry x ≠ 0 → ∀ e ∈ w.arrival x,
    Joins g e (w.up x) x ∧ w.up x < g.n ∧ w.entry (w.up x) ≠ 0 ∧ w.entry (w.up x) < w.entry x

/-- Every vertex entered after an open vertex lies below it. -/
def OpenBelow (w : Walk) : Prop :=
  ∀ v < g.n, w.onPath v → ∀ x < g.n, w.entry x ≠ 0 → w.entry v ≤ w.entry x → Anc (g := g) w v x

/-- Every row entry taken leads to an entered vertex, above or below unless it is a loop. -/
def TakenOk (w : Walk) : Prop :=
  ∀ x < g.n, ∀ s ∈ looked (g := g) w x, w.entry s.1 ≠ 0 ∧
    (s.1 ≠ x → Anc (g := g) w s.1 x ∨ Anc (g := g) w x s.1)

/-- The outer loop: with no path, every vertex before `next` entered and every entered vertex
finished; with a path, its root is the vertex just before `next` and every vertex before the root
finished. -/
def OuterOk (w : Walk) : Prop :=
  w.next ≤ g.n ∧
  (w.path = [] → ∀ x < g.n, (x < w.next → w.entry x ≠ 0) ∧ (w.entry x ≠ 0 → w.finished x)) ∧
  ∀ fr ∈ w.path.getLast?, fr.vertex + 1 = w.next ∧ ∀ x < fr.vertex, w.finished x

/-- `children` counts the current root's children. -/
def ChildrenOk (w : Walk) : Prop :=
  ∀ fr ∈ w.path.getLast?, w.children = numChildren (g := g) w fr.vertex

/-- The edge stack: no link twice, only links of the graph; every open vertex's arrival link is on
it, with exactly the links whose deeper end was entered no earlier than the vertex above it. -/
def StackOk (w : Walk) : Prop :=
  (∀ f ∈ w.edges, f < g.links.length) ∧
  ∀ fr ∈ w.path, ∀ e ∈ fr.arrival, e ∈ w.edges ∧ ∀ j < w.edges.length,
    (j < w.edges.idxOf e → w.entry fr.vertex ≤ deepEntry (g := g) w (w.edges.getD j 0)) ∧
    (w.edges.idxOf e < j → deepEntry (g := g) w (w.edges.getD j 0) < w.entry fr.vertex)

/-- `b` is the group of the block top `c`. -/
def IsGroupOf (w : Walk) (b : List ℕ) (c : ℕ) : Prop :=
  b ≠ [] ∧ BlockTop w c ∧ ∀ f < g.links.length, f ∈ b ↔ InGroup (g := g) w c f

instance (w : Walk) (b : List ℕ) (c : ℕ) : Decidable (IsGroupOf (g := g) w b c) := by
  unfold IsGroupOf; infer_instance

/-- `r` is a finished root with no children. -/
def LoneRoot (w : Walk) (r : ℕ) : Prop :=
  w.finished r ∧ w.arrival r = none ∧ numChildren (g := g) w r = 0

instance (w : Walk) (r : ℕ) : Decidable (LoneRoot (g := g) w r) := by
  unfold LoneRoot; infer_instance

/-- Block `k` has no links and holds `r` alone. -/
def EmptyAt (w : Walk) (k r : ℕ) : Prop := w.blocks.getD k [] = [] ∧ w.vertices.getD k [] = [r]

instance (w : Walk) (k r : ℕ) : Decidable (EmptyAt w k r) := by unfold EmptyAt; infer_instance

/-- The blocks emitted: each with links is the group of a block top and lists its vertices, each
block top's group is emitted, and each without links holds a finished root with no children, one
block for each such root. -/
def BlocksOk (w : Walk) : Prop :=
  w.vertices.length = w.blocks.length ∧
  (∀ k < w.blocks.length, w.blocks.getD k [] ≠ [] →
    w.vertices.getD k [] = verticesOf g (w.blocks.getD k [])) ∧
  (∀ k < w.blocks.length, w.blocks.getD k [] ≠ [] →
    ∃ c < g.n, IsGroupOf (g := g) w (w.blocks.getD k []) c) ∧
  (∀ k < w.blocks.length, w.blocks.getD k [] = [] → ∃ r < g.n, EmptyAt w k r ∧
    LoneRoot (g := g) w r) ∧
  (∀ c < g.n, BlockTop w c → ∃ k < w.blocks.length, IsGroupOf (g := g) w (w.blocks.getD k []) c) ∧
  (∀ r < g.n, LoneRoot (g := g) w r → ∃ k < w.blocks.length, EmptyAt w k r) ∧
  (∀ j < w.blocks.length, ∀ k < w.blocks.length, ∀ r < g.n, EmptyAt w j r → EmptyAt w k r →
    j = k) ∧
  w.blocks.flatten.Nodup ∧ ∀ b ∈ w.blocks, ∀ f ∈ b, f < g.links.length

/-- The bridges found: the arrival links of finished vertices whose subtree cannot climb back to the
vertex they hang from, each once. -/
def BridgesOk (w : Walk) : Prop :=
  w.bridges.Nodup ∧ (∀ f ∈ w.bridges, f < g.links.length) ∧ ∀ f < g.links.length, f ∈ w.bridges ↔
    ∃ c < g.n, w.finished c ∧ w.arrival c = some f ∧ w.entry (w.up c) < w.low c

/-- The cut flags: a vertex other than a root with a finished child that cannot climb above it, or
a finished root with two or more children. -/
def CutOk (w : Walk) : Prop :=
  ∀ x < g.n, (w.cut x = true ↔
    ((w.arrival x ≠ none ∧ ∃ c < g.n, Child w x c ∧ w.finished c ∧ w.entry x ≤ w.low c) ∨
      (w.arrival x = none ∧ w.finished x ∧ 2 ≤ numChildren (g := g) w x)))

/-- Nothing beyond the vertices of the graph is entered, flagged or recorded. -/
def Outside (w : Walk) : Prop :=
  ∀ x ≥ g.n, w.entry x = 0 ∧ w.cut x = false ∧ w.finished x = false ∧ w.taken x = 0 ∧
    w.arrival x = none

/-- **The shape of the walk**: every piece above, and `Valid`'s first invariant and the stack's
contents. -/
def Shape (w : Walk) : Prop :=
  EntriesOk (g := g) w ∧ PathOk (g := g) w ∧ StatusOk (g := g) w ∧ TreeOk (g := g) w ∧
  OpenBelow (g := g) w ∧ TakenOk (g := g) w ∧ OuterOk (g := g) w ∧ ChildrenOk (g := g) w ∧
  (w.g = g ∧ ClimbBackIsEarliest w) ∧ w.edges.Nodup ∧
  (∀ f < g.links.length, f ∈ w.edges ↔ Taken (g := g) w f ∧ f ∉ w.blocks.flatten) ∧
  StackOk (g := g) w ∧ BlocksOk (g := g) w ∧ BridgesOk (g := g) w ∧ CutOk (g := g) w

instance (w : Walk) : Decidable (EntriesOk (g := g) w) := by unfold EntriesOk; infer_instance
instance (w : Walk) : Decidable (PathOk (g := g) w) := by unfold PathOk; infer_instance
instance (w : Walk) : Decidable (StatusOk (g := g) w) := by unfold StatusOk; infer_instance
instance (w : Walk) : Decidable (TreeOk (g := g) w) := by unfold TreeOk; infer_instance
instance (w : Walk) : Decidable (OpenBelow (g := g) w) := by unfold OpenBelow; infer_instance
instance (w : Walk) : Decidable (TakenOk (g := g) w) := by unfold TakenOk; infer_instance
instance (w : Walk) : Decidable (OuterOk (g := g) w) := by unfold OuterOk; infer_instance
instance (w : Walk) : Decidable (ChildrenOk (g := g) w) := by unfold ChildrenOk; infer_instance
instance (w : Walk) : Decidable (StackOk (g := g) w) := by unfold StackOk; infer_instance
instance (w : Walk) : Decidable (BlocksOk (g := g) w) := by
  unfold BlocksOk
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_
    (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_))))) <;>
    infer_instance
instance (w : Walk) : Decidable (BridgesOk (g := g) w) := by unfold BridgesOk; infer_instance
instance (w : Walk) : Decidable (CutOk (g := g) w) := by unfold CutOk; infer_instance

instance (w : Walk) : Decidable (Shape (g := g) w) := by
  unfold Shape
  repeat' refine @instDecidableAnd _ _ ?_ ?_
  all_goals infer_instance

/-- What box invariant 1 says at one entered vertex of a walk of `g`. -/
theorem low_eq_climb {w : Walk} (hw : w.g = g) (h : ClimbBackIsEarliest w) {x : ℕ} (hx : x < g.n)
    (he : w.entry x ≠ 0) : w.low x = climb (g := g) w x := by
  subst hw
  exact h x hx he

/-- What box invariant 1 says at one entered vertex, in a walk with the whole shape. -/
theorem shape_low_eq {w : Walk} (hS : Shape (g := g) w) {x : ℕ} (hx : x < g.n)
    (he : w.entry x ≠ 0) : w.low x = climb (g := g) w x :=
  low_eq_climb hS.2.2.2.2.2.2.2.2.1.1 hS.2.2.2.2.2.2.2.2.1.2 hx he

/-- Each tree's root is its smallest vertex: the outer loop tries vertices `0` upward, and every
vertex below a root was entered before it. -/
def RootsOk (w : Walk) : Prop :=
  ∀ x < g.n, w.entry x ≠ 0 → ∀ r < g.n, Anc (g := g) w r x → w.arrival r = none → r ≤ x

instance (w : Walk) : Decidable (RootsOk (g := g) w) := by unfold RootsOk; infer_instance

/-- An open vertex has taken a row entry to an open vertex below it only by descending: the entry's
link is that vertex's arrival link. -/
def OpenTaken (w : Walk) : Prop :=
  ∀ x < g.n, w.onPath x → ∀ s ∈ looked (g := g) w x, w.onPath s.1 → w.entry x < w.entry s.1 →
    w.arrival s.1 = some s.2

instance (w : Walk) : Decidable (OpenTaken (g := g) w) := by unfold OpenTaken; infer_instance

variable (g) in
/-- `Shape` at each of the next `k + 1` states of a run. -/
def traceShape : ℕ → Walk → Bool
  | 0, w => decide (Shape (g := g) w)
  | k + 1, w => decide (Shape (g := g) w) && traceShape k (step g w)

end Walk

end AlgoDesign.Graphs.Blocks
