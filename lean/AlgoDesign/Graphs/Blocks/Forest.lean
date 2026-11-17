/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Walk

/-!
# Bridges, cut vertices and blocks: the block-cut forest

Source: Diestel, *Graph Theory* (5th ed.), §3.1, pp. 64–66: one node per block and one per cut
vertex, a cut vertex's node joined to every block that holds it, one tree per piece. The layout
follows OGDF's documented `BCTree` interface: a path starts at a cut vertex's own node, or at the
one block of any other vertex; "strictly between" is the book's own choice, where OGDF's path
includes both ends.

Nodes `0 .. b - 1` are the blocks, in the order the walk emitted them, then one node per cut vertex
in increasing vertex order. Each piece's tree is rooted at the node of its smallest vertex, found by
trying vertices `0` upward; the tree is walked from its root with a stack, as the Python and the
Rust do. `parent` (a root is its own parent) and `depth` read off the tree; `separators u v` climbs
from the deeper of the two nodes until they meet, and lists the cut vertices passed strictly between
them, or answers `none` on reaching two different roots.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

/-- **Each reported block's vertices**: a block's vertices are the ends of its links, increasing; a
block without links holds one isolated vertex, and no other block without links holds it. -/
def VerticesAgree (g : Graph) (r : Report) : Prop :=
  r.blockVertices.length = r.blocks.length ∧
  (∀ k < r.blocks.length,
    r.blocks.getD k [] ≠ [] → r.blockVertices.getD k [] = Walk.verticesOf g (r.blocks.getD k [])) ∧
  (∀ k < r.blocks.length, r.blocks.getD k [] = [] →
    (r.blockVertices.getD k []).length = 1 ∧ ∀ v ∈ r.blockVertices.getD k [], IsolatedVertex g v) ∧
  ∀ j < r.blocks.length, ∀ k < r.blocks.length, r.blocks.getD j [] = [] →
    r.blocks.getD k [] = [] → r.blockVertices.getD j [] = r.blockVertices.getD k [] → j = k

instance (g : Graph) (r : Report) : Decidable (VerticesAgree g r) := by
  unfold VerticesAgree
  refine @instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ (@instDecidableAnd _ _ ?_ ?_)) <;>
    infer_instance

/-- **The block-cut forest**, as arrays over its nodes. -/
structure Forest where
  /-- The number of blocks; the nodes below it are blocks. -/
  nBlocks : ℕ
  /-- The cut vertices, increasing; cut vertex `k` is node `nBlocks + k`. -/
  cutVertices : List ℕ
  /-- Each vertex's node: a cut vertex's own node, else its one block. -/
  nodeOf : List ℕ
  /-- Each node's parent; a root is its own parent. -/
  parent : List ℕ
  /-- Each node's number of steps up to its root. -/
  depth : List ℕ
deriving DecidableEq, Repr

namespace Forest

variable (r : Report)

/-- A cut vertex's node. -/
def cutNode (p : ℕ) : Option ℕ := (r.cutVertices.idxOf? p).map (r.blocks.length + ·)

/-- The nodes joined to node `x`: a block's cut vertices in increasing vertex order; a cut vertex's
blocks in emission order. -/
def around (x : ℕ) : List ℕ :=
  if x < r.blocks.length then (r.blockVertices.getD x []).filterMap (cutNode r)
  else (List.range r.blocks.length).filter fun k =>
    (r.cutVertices[x - r.blocks.length]?).any (· ∈ r.blockVertices.getD k [])

/-- A vertex's node: a cut vertex's own node, else the block holding it (the last, if several). -/
def nodeOfVertex (p : ℕ) : ℕ :=
  match cutNode r p with
  | some x => x
  | none => (List.range r.blocks.length).foldl
      (fun acc k => if p ∈ r.blockVertices.getD k [] then k else acc) 0

/-- Walk a tree from a stack of nodes, top first: take the top, give each node around it that has
no parent yet its parent and depth, and push it. -/
def explore : ℕ → (ℕ → Option ℕ) × (ℕ → ℕ) → List ℕ → (ℕ → Option ℕ) × (ℕ → ℕ)
  | 0, s, _ => s
  | _ + 1, s, [] => s
  | k + 1, (par, dep), x :: stack =>
    let t := (around r x).foldl (fun (t : (ℕ → Option ℕ) × (ℕ → ℕ) × List ℕ) y =>
      if t.1 y = none then
        (Function.update t.1 y (some x), Function.update t.2.1 y (t.2.1 x + 1), y :: t.2.2)
      else t) (par, dep, stack)
    explore k (t.1, t.2.1) t.2.2

/-- The number of nodes. -/
def size : ℕ := r.blocks.length + r.cutVertices.length

/-- Root each tree at the node of its smallest vertex, trying vertices `0` upward. -/
def root (n : ℕ) : (ℕ → Option ℕ) × (ℕ → ℕ) :=
  (List.range n).foldl (fun (s : (ℕ → Option ℕ) × (ℕ → ℕ)) p =>
    let top := nodeOfVertex r p
    if s.1 top = none then explore r (size r + 1) (Function.update s.1 top (some top), s.2) [top]
    else s) (fun _ => none, fun _ => 0)

end Forest

/-- **The block-cut forest** of a graph, from the walk's report. -/
def forest (g : Graph) (r : Report) : Forest :=
  let s := Forest.root r g.n
  ⟨r.blocks.length, r.cutVertices, (List.range g.n).map (Forest.nodeOfVertex r),
    (List.range (Forest.size r)).map fun x => (s.1 x).getD x,
    (List.range (Forest.size r)).map s.2⟩

namespace Forest

variable (f : Forest)

/-- Climb from the deeper of `x` and `y` until they meet, collecting the nodes stepped onto;
`none` on reaching two different roots. -/
def meet : ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _ => none
  | k + 1, x, y, passed =>
    if x = y then some passed
    else
      let (x, y) := if f.depth.getD x 0 < f.depth.getD y 0 then (y, x) else (x, y)
      let p := f.parent.getD x x
      if p = x then none else meet k p y (p :: passed)

/-- **The separators of `u` and `v`**: the cut vertices on the forest path strictly between their
nodes, increasing; `none` when they are in different pieces. -/
def separators (u v : ℕ) : Option (List ℕ) :=
  let x := f.nodeOf.getD u 0
  let y := f.nodeOf.getD v 0
  (meet f (2 * f.parent.length + 1) x y []).map fun passed =>
    (List.range f.cutVertices.length).filterMap fun k =>
      if f.nBlocks + k ∈ passed ∧ f.nBlocks + k ≠ x ∧ f.nBlocks + k ≠ y then f.cutVertices[k]?
      else none

end Forest

end AlgoDesign.Graphs.Blocks
