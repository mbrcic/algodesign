/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Spec
public import AlgoDesign.Flows.MaxFlow.RulesBasic
public import AlgoDesign.Paths.Dijkstra.Goal

/-!
# Cheapest flow of a given amount: the steps

Sources: the Flow chapter, "Heights keep the search safe"; Ahuja, Magnanti and Orlin, *Network
Flows* (1993), §9.7 (successive shortest paths, p. 320) and p. 323 for the heights after a search
stopped at the sink.

One step searches the remaining capacity with chapter 6's best-first walk to one goal
(`Paths.Dijkstra.finalTo`): from the source, over the residual arrows with room, on changed costs,
stopped when the sink comes off the queue and is settled. The walk runs on a `Paths.Network` whose
arrows are the residual arrows with room (`roomy`), listed by arrow id, `along i` before `back i`,
each costing its changed cost (`searchNet`). The walk records each vertex's previous vertex; the
arrow from it is the first residual arrow out of it, in adjacency order (`Network.residualOut`),
that points to the vertex, has room, and whose changed cost is the difference of the two known
costs (`arrowInto`): the arrow whose strict improvement set the vertex's cost last.

If the search settles the sink, the step sends `min(bottleneck, amount still requested)` along the
path back from the sink, and raises the heights: every settled vertex adds its cost from the
source, every other vertex the sink's (`raise`). A search that does not settle the sink is not a
step: the steps end, nothing is recorded and the heights stay. The steps also end when the
requested amount is sent. The answer's side is always the max-flow search's `reached` set.
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

/-! ## The search of one step -/

/-- **The residual arrows with room** under the flow `f`, by arrow id, `along i` before `back i`. -/
def roomy (N : Network) (f : Flow) : List ResidualArrow :=
  N.ids.flatMap fun i =>
    (if 0 < (ResidualArrow.along i).residualCapacity N f then [ResidualArrow.along i] else []) ++
      (if 0 < (ResidualArrow.back i).residualCapacity N f then [ResidualArrow.back i] else [])

/-- **The network the search walks**: the vertices of `P.net`, one arrow per residual arrow with
room (arrow `j` is `(roomy P.net f)[j]`), each costing its changed cost under the heights `h`. -/
def searchNet (P : Problem) (f : Flow) (h : Heights) : Paths.Network :=
  ⟨⟨P.net.g.n, (roomy P.net f).map fun a => (a.tail P.net, a.head P.net)⟩,
    (roomy P.net f).map (changedCost P h)⟩

/-- **The search of one step**: chapter 6's walk from the source to the sink on changed costs, the
state it ends in. -/
def search (P : Problem) (f : Flow) (h : Heights) : Paths.Dijkstra.State :=
  Paths.Dijkstra.finalTo (searchNet P f h) P.net.source P.net.sink

/-- A known cost read as a number; 0 when there is none. -/
def dist (st : Paths.Dijkstra.State) (v : ℕ) : ℤ := (st.known v).getD 0

/-- **The arrow from `u` into `w`** the search recorded: the first residual arrow out of `u`, in
adjacency order, that points to `w`, has room, and whose changed cost is `w`'s known cost less
`u`'s. -/
def arrowInto (P : Problem) (f : Flow) (h : Heights) (st : Paths.Dijkstra.State) (u w : ℕ) :
    Option ResidualArrow :=
  (P.net.residualOut u).find? fun a =>
    a.head P.net = w ∧ 0 < a.residualCapacity P.net f ∧ changedCost P h a = dist st w - dist st u

/-- The arrow that labeled each vertex: the recorded arrow from its previous vertex. -/
def viaOf (P : Problem) (f : Flow) (h : Heights) (st : Paths.Dijkstra.State) (w : ℕ) :
    Option ResidualArrow :=
  (st.prev w).bind fun u => arrowInto P f h st u w

/-- **The heights after a search**: every settled vertex adds its cost from the source, every other
vertex the sink's. -/
def raise (P : Problem) (h : Heights) (st : Paths.Dijkstra.State) : Heights :=
  (List.range P.net.g.n).map fun v =>
    h.at v + if v ∈ st.settled then dist st v else dist st P.net.sink

/-- **One round's record**: the path it added with its amount, the heights after it, and the number
of vertices its search settled, the source and the sink included. -/
structure RoundRecord where
  /-- The path added, and the amount sent along it. -/
  sent : Augmentation
  /-- The heights after the round. -/
  heights : Heights
  /-- How many vertices the round's search settled. -/
  settled : ℕ
deriving DecidableEq, Repr

/-- **One step** with `left` still requested: none when the search does not settle the sink. -/
def step (P : Problem) (left : ℕ) (f : Flow) (h : Heights) : Option RoundRecord :=
  let st := search P f h
  if P.net.sink ∈ st.settled then
    match pathBack P.net (viaOf P f h st) P.net.g.n P.net.sink [] with
    | none => none
    | some p => some ⟨⟨p, min (bottleneck P.net f p) left⟩, raise P h st, st.settled.length⟩
  else none

/-- **The steps**, at most `fuel` of them, from the flow `f` and the heights `h` with `left` still
requested: they end when nothing is left to send or a search does not settle the sink. -/
def runSteps (P : Problem) : ℕ → ℕ → Flow → Heights → List RoundRecord
  | 0, _, _, _ => []
  | fuel + 1, left, f, h =>
    if left = 0 then []
    else
      match step P left f h with
      | none => []
      | some r => r :: runSteps P fuel (left - r.sent.amount) (r.sent.apply f) r.heights

/-- The heights at the start: all zero. -/
def startHeights (P : Problem) : Heights := List.replicate P.net.g.n 0

/-- **The run**: the steps from the zero flow and zero heights, enough of them for steps that each
send at least one unit. -/
def run (P : Problem) : List RoundRecord :=
  runSteps P (P.amount + 1) P.amount (Flow.zero P.net) (startHeights P)

/-- The paths the steps added, in order. -/
def steps (P : Problem) : List Augmentation := (run P).map (·.sent)

/-- The heights after the first `k` steps; the start's before the first. -/
def heightsAfter (P : Problem) (k : ℕ) : Heights :=
  (((run P).take k).getLast?.map (·.heights)).getD (startHeights P)

/-- **The answer**: what the steps sent, the heights after the last of them, and the vertices the
remaining capacity reaches from the source. -/
def minCostFlow (P : Problem) : Answer :=
  let f := applyAll (Flow.zero P.net) (steps P)
  ⟨f, heightsAfter P (steps P).length, reached P.net f⟩

/-- **The number of vertices each search settled**, in order: one per step, and one more for a
last search that did not settle the sink. -/
def settledEach (P : Problem) : List ℕ :=
  (run P).map (·.settled) ++
    let f := applyAll (Flow.zero P.net) (steps P)
    let h := heightsAfter P (steps P).length
    if (run P).length < P.amount + 1 ∧ value P.net f < P.amount then
      [(search P f h).settled.length]
    else []

end AlgoDesign.Flows.MinCostFlow
