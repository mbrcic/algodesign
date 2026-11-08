/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Cycles

/-!
# Bridges, cut vertices and blocks: the walk

Sources: Drozdek, *Data Structures and Algorithms in C++* (4th ed.), §8.6.1, pp. 416–418, the
edge stack, its push rule, the test `pred(u) ≥ num(v)` with the pop, and the root rule; Hopcroft
and Tarjan, *Efficient algorithms for graph manipulation*, CACM 16 (1973); cp-algorithms,
"Finding bridges": the walk skips the link it arrived by, by its id, not the vertex it came from.

The walk keeps its path as frames (vertex, arrival link id, next row position), the current vertex
first, starts at vertices `0` upward, and gives each vertex an entry number from 1 in the order
vertices are first entered. A vertex's climb-back number `low` starts as its entry number. Walking
the row of the current vertex `v`, an entry (`x`, `e`) is skipped when it is a loop or when `e` is
the link `v` arrived by; when `x` was not entered, `e` goes on the edge stack and the walk descends
to `x`; when `x` was entered earlier than `v`, `e` goes on the edge stack and `low v` takes `x`'s
entry number if smaller (the classical rule); when `x` was entered later, `x` is below `v` and has
pushed `e` already. When a child `c` finishes under `v`, having arrived by `e`: `low v` takes
`low c` if smaller; if `low c ≥ entry v` the edge stack is popped down to and including `e`, one
block; if `low c > entry v`, `e` is a bridge. A vertex other than a root with such a child is a cut
vertex; a root is one when it has two or more children, and a root with none, a vertex whose links
are all loops, is a block of its own with no links.

One step looks at one row entry, finishes one vertex, or moves the outer loop on, so the walk is
executed with fuel: `2 n + 2 m` steps finish it. The state also carries what the invariants read
and the walk never does: the link and the vertex each vertex was entered from, which vertices have
finished, and how many entries of each row have been taken. `Valid` has one piece per box
invariant, each decidable; `traceValid` checks them at every step of a run, by `decide` on the
examples.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable (g : Graph)

/-- Nothing entered. -/
def start : Walk :=
  ⟨g, 0, fun _ => 0, fun _ => 0, [], [], fun _ => false, [], [], [], 0, 0, fun _ => none, id,
    fun _ => false, fun _ => 0⟩

/-- Enter `v` from `u` by link `arr`: the next entry number is both its entry and its climb-back
number. -/
def enter (w : Walk) (v : ℕ) (arr : Option ℕ) (u : ℕ) : Walk :=
  { w with time := w.time + 1, entry := Function.update w.entry v (w.time + 1),
           low := Function.update w.low v (w.time + 1), path := ⟨v, arr, 0⟩ :: w.path,
           arrival := Function.update w.arrival v arr, up := Function.update w.up v u }

/-- The vertices of a block's links, increasing. -/
def verticesOf (links : List ℕ) : List ℕ :=
  (List.range g.n).filter fun p => links.any fun i => (g.links[i]?).any fun l => l.1 = p || l.2 = p

/-- Pop the edge stack down to and including `e`: the block, in pop order, and what is left. -/
def popBlock (e : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | x :: rest =>
    if x = e then ([x], rest)
    else
      let r := popBlock e rest
      (x :: r.1, r.2)

/-- The current vertex `v`, entered by `arr`, takes the entry (`x`, `e`) of its row. -/
def look (w : Walk) (v : ℕ) (arr : Option ℕ) (x e : ℕ) (isRoot : Bool) : Walk :=
  if x = v ∨ arr = some e then w
  else if w.entry x = 0 then
    enter { w with edges := e :: w.edges,
                   children := if isRoot then w.children + 1 else w.children } x (some e) v
  else if w.entry x < w.entry v then
    { w with edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.entry x)) }
  else w

/-- `v` finishes under `u`, having arrived by `e`. -/
def finishUnder (w : Walk) (u v e : ℕ) (uIsRoot : Bool) : Walk :=
  let w : Walk := { w with low := Function.update w.low u (min (w.low u) (w.low v)) }
  let w : Walk :=
    if w.entry u ≤ w.low v then
      let r := popBlock e w.edges
      { w with edges := r.2, blocks := w.blocks ++ [r.1],
               vertices := w.vertices ++ [verticesOf g r.1],
               cut := if uIsRoot then w.cut else Function.update w.cut u true }
    else w
  if w.entry u < w.low v then { w with bridges := w.bridges ++ [e] } else w

/-- A root `v` finishes: a cut vertex with two or more children, a block of its own with none. -/
def finishRoot (w : Walk) (v : ℕ) : Walk :=
  let w : Walk := if 2 ≤ w.children then { w with cut := Function.update w.cut v true } else w
  if w.children = 0 then { w with blocks := w.blocks ++ [[]], vertices := w.vertices ++ [[v]] }
  else w

/-- **One step**: with no current vertex, enter the next root if it is not entered, else move the
outer loop on; otherwise take the current vertex's next row entry; at the end of its row, finish
the vertex. -/
def step (w : Walk) : Walk :=
  match w.path with
  | [] =>
    if w.next < g.n then
      if w.entry w.next = 0 then
        enter { w with next := w.next + 1, children := 0 } w.next none w.next
      else { w with next := w.next + 1 }
    else w
  | ⟨v, arr, i⟩ :: rest =>
    match (g.adj v)[i]? with
    | some (x, e) =>
      look { w with path := ⟨v, arr, i + 1⟩ :: rest, taken := Function.update w.taken v (i + 1) }
        v arr x e rest.isEmpty
    | none =>
      let w' : Walk := { w with path := rest, finished := Function.update w.finished v true }
      match rest, arr with
      | ⟨u, _, _⟩ :: above, some e => finishUnder g w' u v e above.isEmpty
      | _, _ => finishRoot w' v

/-- `fuel` steps. -/
def run : ℕ → Walk → Walk
  | 0, w => w
  | k + 1, w => run k (step g w)

/-! ### The walk keeps its graph -/

@[simp] theorem enter_g (w : Walk) (v : ℕ) (arr : Option ℕ) (u : ℕ) :
    (enter w v arr u).g = w.g := rfl

@[simp] theorem look_g (w : Walk) (v : ℕ) (arr : Option ℕ) (x e : ℕ) (isRoot : Bool) :
    (look w v arr x e isRoot).g = w.g := by
  unfold look
  repeat' split
  all_goals rfl

@[simp] theorem finishUnder_g (w : Walk) (u v e : ℕ) (uIsRoot : Bool) :
    (finishUnder g w u v e uIsRoot).g = w.g := by
  unfold finishUnder
  dsimp only
  repeat' split
  all_goals rfl

@[simp] theorem finishRoot_g (w : Walk) (v : ℕ) : (finishRoot w v).g = w.g := by
  unfold finishRoot
  dsimp only
  repeat' split
  all_goals rfl

@[simp] theorem step_g (w : Walk) : (step g w).g = w.g := by
  unfold step
  dsimp only
  repeat' split
  all_goals simp

@[simp] theorem run_g : ∀ (k : ℕ) (w : Walk), (run g k w).g = w.g
  | 0, _ => rfl
  | k + 1, w => (run_g k (step g w)).trans (step_g g w)

/-- `run` is the step iterated. -/
theorem run_eq_iterate : ∀ (k : ℕ) (w : Walk), run g k w = (step g)^[k] w
  | 0, _ => rfl
  | k + 1, w => run_eq_iterate k (step g w)

/-- Enough steps for the whole walk: each vertex passed by the outer loop and finished once, and
each row entry looked at once (a link has two). -/
def steps : ℕ := 2 * g.n + 2 * g.links.length

/-- The walk run to its end. -/
def final : Walk := run g (steps g) (start g)

end Walk

/-- **The bridges, cut vertices and blocks**, by one walk. -/
def blocks (g : Graph) : Report := report g (Walk.final g)

/-! ## The invariants -/

namespace Walk

variable {g : Graph}

instance (w : Walk) : Decidable (StackHoldsOpenLinks w) := by
  unfold StackHoldsOpenLinks; infer_instance

instance (w : Walk) : Decidable (Valid w) := by
  unfold Valid; infer_instance

variable (g) in
/-- At the start no row entry has been taken. -/
theorem looked_start (x : ℕ) : looked (g := g) (start g) x = [] := by
  simp [looked, start]

variable (g) in
/-- **The start is legal**: nothing entered, the stack empty, no block out. -/
theorem valid_start : Valid (start g) := by
  refine ⟨fun v _ hv => absurd rfl hv, List.nodup_nil, fun f _ => ?_, by simp [start],
    by simp [start]⟩
  simp [Taken, looked, start]

variable (g) in
/-- `Valid` at each of the next `k + 1` states of a run. -/
def traceValid : ℕ → Walk → Bool
  | 0, w => decide (Valid w)
  | k + 1, w => decide (Valid w) && traceValid k (step g w)

variable (g) in
theorem traceValid_spec : ∀ (k : ℕ) (w : Walk), traceValid g k w = true →
    ∀ j ≤ k, Valid (run g j w)
  | 0, w, h, j, hj => by
    obtain rfl : j = 0 := by omega
    simpa [traceValid, run] using h
  | k + 1, w, h, j, hj => by
    simp only [traceValid, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact traceValid_spec k _ h.2 j (by omega)

end Walk

end AlgoDesign.Graphs.Blocks
