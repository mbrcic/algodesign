import AlgoDesign
import Mathlib.Tactic

/-! Regression checks for the Paths chapter's specifications: the network, breadth-first search,
the cheapest paths and the search for one goal, Bellman–Ford, cheapest paths in a graph with no
cycle, knapsack as a longest path and Kruskal's cheapest spanning forest, each in its own
namespace. Run with `lake env lean -DwarningAsError=true AlgoDesignTests/Paths.lean`. -/

namespace AlgoDesignTests.PathsNetwork
open AlgoDesign.Paths

-- two arrows between the same vertices cost differently: the path names the arrow it takes
example : Network.Cheapest ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ 0 1 (some 3) := by decide
example : Network.IsPath ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ 0 [0] 1 := by decide
-- a path passes no vertex twice, so going round a loop is no path
example : ¬ Network.IsPath ⟨⟨1, [(0, 0)]⟩, [0]⟩ 0 [0] 0 := by decide
-- no path leads back against the arrows
example : Network.Cheapest ⟨⟨2, [(0, 1)]⟩, [4]⟩ 1 0 none := by decide
-- a cost list one short is not well formed
example : ¬ Network.WellFormed ⟨⟨2, [(0, 1), (1, 0)]⟩, [4]⟩ := by decide

end AlgoDesignTests.PathsNetwork

namespace AlgoDesignTests.PathsBfs
open AlgoDesign.Graphs AlgoDesign.Paths.Bfs

/-- A loop, a link back to the start, and an unreachable vertex. -/
def gA : Digraph := ⟨4, [(0, 1), (1, 2), (0, 2), (2, 2), (2, 0)]⟩

example : (List.range 4).map (bfs gA 0).dist = [some 0, some 1, some 1, none] := by decide
-- 2 is found first from 0, along the arrow 0 → 2, not later from 1
example : (List.range 4).map (bfs gA 0).prev = [none, some 0, some 0, none] := by decide
set_option maxRecDepth 100000 in
example : ∀ k < 5, Valid gA 0 (runSteps gA k (start 0)) := by decide

/-- Two paths of two arrows to 3, then one more to 4. -/
def gB : Digraph := ⟨5, [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (1, 1)]⟩

example : (List.range 5).map (bfs gB 0).dist = [some 0, some 1, some 1, some 2, some 3] := by
  decide
-- the frontier: distances 1, 1, then 2
example : (runSteps gB 1 (start 0)).queue = [(1, 1), (2, 1)] ∧
    (runSteps gB 2 (start 0)).queue = [(2, 1), (3, 2)] := by decide
set_option maxRecDepth 100000 in
example : ∀ k < 6, Valid gB 0 (runSteps gB k (start 0)) := by decide
-- a queue out of order is not a legal state
example : ¬ QueueInOrder ⟨[0], fun _ => some 1, fun _ => none, [(1, 2), (2, 1)]⟩ := by decide
example : Valid ⟨1, []⟩ 0 (start 0) ∧ (bfs ⟨1, []⟩ 0).dist 0 = some 0 := by decide

end AlgoDesignTests.PathsBfs

namespace AlgoDesignTests.PathsDijkstra
open AlgoDesign.Paths AlgoDesign.Paths.Dijkstra

/-! ### The chapter's three-vertex map: one arrow below zero, no cycle

The Bakery 0, the Square 1 and the Hilltop 2; the Bakery to the Square costs 2, the Bakery to the
Hilltop 4, and the Hilltop down to the Square −3. The walk settles the Square at 2 before it
settles the Hilltop, and never changes the Square again; the path over the Hilltop costs 1. With
one arrow below zero, a settled cost can be wrong. -/

/-- The chapter's three-vertex map. -/
def probe : Network := ⟨⟨3, [(0, 1), (0, 2), (2, 1)]⟩, [2, 4, -3]⟩

example : probe.WellFormed ∧ ¬ probe.NoArrowBelowZero := by decide
-- the walk settles the Square at 2, and the cheapest path to the Square costs 1
example : (dijkstra probe 0).cost 1 = some 2 := by decide
example : ¬ probe.Cheapest 0 1 (some 2) ∧ probe.Cheapest 0 1 (some 1) := by decide
-- the Square is settled second, at 2; the Hilltop, settled third, cannot lower it
example : (runSteps (step probe) 2 (start probe 0)).settled = [0, 1] := by decide
example : (dijkstra probe 0).prev 1 = some 0 := by decide
-- the box's first invariant fails the moment the Square is settled
example : Valid (runSteps (step probe) 1 (start probe 0)) ∧
    WellFormed (runSteps (step probe) 1 (start probe 0)) := by decide
example : ¬ SettledAreCheapest (runSteps (step probe) 2 (start probe 0)) := by decide
-- the paths back still cost what the walk reports: that part holds whatever the arrows cost
example : PreviousLeadsBack (runSteps (step probe) 4 (start probe 0)) := by decide

/-! ### A map with no arrow below zero

Vertex 0 has two arrows to 1, costing 3 and 1; 1 → 2 costs 2, 0 → 2 costs 5, and 2 has a loop of
cost 0. Vertex 3 cannot be reached. -/

/-- A map with no arrow below zero. -/
def roads : Network := ⟨⟨4, [(0, 1), (0, 1), (1, 2), (0, 2), (2, 2)]⟩, [3, 1, 2, 5, 0]⟩

example : roads.WellFormed ∧ roads.NoArrowBelowZero := by decide
example : (List.range 4).map (dijkstra roads 0).cost = [some 0, some 1, some 3, none] := by
  decide
example : (List.range 4).map (dijkstra roads 0).prev = [none, some 0, some 1, none] := by decide
set_option maxRecDepth 100000 in
example : roads.Cheapest 0 2 (some 3) ∧ roads.Cheapest 0 3 none := by decide
-- every state of the walk is legal, and the queue is empty after one step per entry
set_option maxRecDepth 100000 in
example : ∀ k < 7, Valid (runSteps (step roads) k (start roads 0)) ∧
    WellFormed (runSteps (step roads) k (start roads 0)) := by decide
example : (runSteps (step roads) 6 (start roads 0)).queue = [] := by decide
-- every arrow tried once, in each row's order; five entries for five arrows
example : tried roads (runSteps (step roads) 6 (start roads 0)) = [0, 1, 3, 2, 4] := by decide
example : (runSteps (step roads) 6 (start roads 0)).pushed = 5 := by decide

/-! ### Boundary cases -/

/-- Two vertices tie at cost 1; the smaller id comes off the queue first. -/
def tie : Network := ⟨⟨3, [(0, 2), (0, 1)]⟩, [1, 1]⟩

example : (step tie (start tie 0)).queue = [(1, 1), (1, 2)] := by decide
example : (runSteps (step tie) 2 (start tie 0)).settled = [0, 1] := by decide
set_option maxRecDepth 100000 in
example : ∀ k < 4, Valid (runSteps (step tie) k (start tie 0)) ∧
    WellFormed (runSteps (step tie) k (start tie 0)) := by decide

/-- One vertex with a loop: the start costs 0 and records no previous vertex. -/
def loop : Network := ⟨⟨1, [(0, 0)]⟩, [7]⟩

example : (dijkstra loop 0).cost 0 = some 0 ∧ (dijkstra loop 0).prev 0 = none := by decide
set_option maxRecDepth 100000 in
example : ∀ k < 3, Valid (runSteps (step loop) k (start loop 0)) ∧
    WellFormed (runSteps (step loop) k (start loop 0)) := by decide

/-- An equal cost through another vertex does not change the previous vertex: only a drop does. -/
def even : Network := ⟨⟨3, [(0, 2), (0, 1), (1, 2)]⟩, [2, 1, 1]⟩

example : (dijkstra even 0).cost 2 = some 2 ∧ (dijkstra even 0).prev 2 = some 0 := by decide

/-! ### The walk to one goal

It stops the moment the goal is settled, before the goal's arrows are tried: on `roads` with goal
1, vertex 2 keeps the cost 5 it was found at, and the settled vertices begin the whole walk's. -/

example : (dijkstraTo roads 0 1).cost 1 = some 1 ∧ (dijkstraTo roads 0 1).cost 2 = some 5 := by
  decide
example : (finalTo roads 0 1).settled = [0, 1] ∧ (final roads 0).settled = [0, 1, 2] := by decide
example : (finalTo roads 0 3).settled = (final roads 0).settled := by decide
example : (dijkstraTo roads 0 3).cost 3 = none := by decide

end AlgoDesignTests.PathsDijkstra

namespace AlgoDesignTests.PathsAStar
open AlgoDesign.Paths AlgoDesign.Paths.Dijkstra AlgoDesign.Paths.AStar

/-- 0 → 1 costs 1, 1 → 2 costs 1, 0 → 2 costs 3, 2 → 3 costs 5, 0 → 4 costs 1; the goal is 3. -/
def roads : Network := ⟨⟨5, [(0, 1), (1, 2), (0, 2), (2, 3), (0, 4)]⟩, [1, 1, 3, 5, 1]⟩

/-! ### An estimate that keeps the box's invariant

The cheapest cost still to go from each vertex: 7, 6, 5, 0, and 9 from 4 (it reaches no goal, so
any estimate at least zero that drops by no more than the arrows will do). -/

/-- An estimate that keeps box invariant 1. -/
def exact : List ℤ := [7, 6, 5, 0, 9]

example : Consistent roads 3 exact := by decide
example : (astar roads exact 0 3).cost 3 = some 7 := by decide
set_option maxRecDepth 100000 in
example : roads.Cheapest 0 3 (some 7) := by decide
example : (astar roads exact 0 3).prev 3 = some 2 ∧ (astar roads exact 0 3).prev 2 = some 1 := by
  decide
-- the search settles only the path; the walk to the goal without an estimate settles 4 too
example : (runTo (step roads) 3 6 (start roads exact 0 3)).settled = [0, 1, 2, 3] ∧
    (finalTo roads 0 3).settled = [0, 1, 4, 2, 3] := by decide
set_option maxRecDepth 100000 in
example : ∀ k < 4, Valid ((AStar.step roads)^[k] (start roads exact 0 3)) ∧
    WellFormed ((AStar.step roads)^[k] (start roads exact 0 3)) := by decide
-- the zero estimate is the walk to the goal itself
example : (astar roads [] 0 3).cost 3 = some 7 ∧
    (runTo (step roads) 3 6 (start roads [] 0 3)).settled = (finalTo roads 0 3).settled := by
  decide

/-! ### An estimate that never overstates but breaks the box's invariant

The lesson of petgraph's issue #378: at vertex 1 the estimate is 5, below the 6 still to go, but
the arrow 1 → 2 costs 1 while the estimate drops by 5. The search settles 2 at 3 from the start
before it settles 1, never reopens 2, and reports 8 for the goal, whose cheapest cost is 7. -/

/-- An estimate that never overstates the cost to go, and breaks box invariant 1. -/
def overeager : List ℤ := [0, 5, 0, 0, 0]

-- never above the cheapest cost still to go, at each vertex that reaches the goal
example : ∀ v ∈ [0, 1, 2, 3], estimate overeager v ≤ estimate exact v := by decide
example : ¬ Consistent roads 3 overeager := by decide
example : (astar roads overeager 0 3).cost 3 = some 8 := by decide
set_option maxRecDepth 100000 in
example : ¬ roads.Cheapest 0 3 (some 8) := by decide

end AlgoDesignTests.PathsAStar

namespace AlgoDesignTests.BellmanFord
open AlgoDesign.Paths AlgoDesign.Paths.BellmanFord

/-- The cost the answer gives a vertex, `none` when the answer is a cycle. -/
def costOf (r : Except (List ℕ) Dijkstra.Answer) (v : ℕ) : Option (Option ℤ) :=
  match r with
  | .ok a => some (a.cost v)
  | .error _ => none

/-- The cycle the answer gives, `none` when it gives costs. -/
def cycleOf (r : Except (List ℕ) Dijkstra.Answer) : Option (List ℕ) :=
  match r with
  | .ok _ => none
  | .error c => some c

/-- The chapter's Probe map: 0→1 costs 1, 0→2 costs 2, 2→1 costs −2. -/
def probe : Network := ⟨⟨3, [(0, 1), (0, 2), (2, 1)]⟩, [1, 2, -2]⟩

-- Bellman–Ford gives vertex 1 cost 0, through 2, where Dijkstra settles it at 1
example : (List.range 3).map (costOf (bellmanFord probe 0)) = [some (some 0), some (some 0),
    some (some 2)] := by decide
-- the second round lowers nothing, so the run stops there
example : (final probe 0).rounds = 2 ∧ (final probe 0).tried = 6 := by decide
-- the state after each round is legal
example : (Valid (start probe 0) ∧ WellFormed (start probe 0)) ∧
    (Valid (round probe (start probe 0)) ∧ WellFormed (round probe (start probe 0))) ∧
    (Valid (round probe (round probe (start probe 0))) ∧
      WellFormed (round probe (round probe (start probe 0)))) := by decide

/-- A negative arrow and no cycle below zero: 0→1 costs 5, 1→2 costs −3, 0→2 costs 4. -/
def downhill : Network := ⟨⟨3, [(0, 1), (1, 2), (0, 2)]⟩, [5, -3, 4]⟩

example : (List.range 3).map (costOf (bellmanFord downhill 0)) = [some (some 0), some (some 5),
    some (some 2)] := by decide
-- vertex 2's previous vertex is 1
example : (match bellmanFord downhill 0 with | .ok a => a.prev 2 | .error _ => none) = some 1 := by
  decide

/-- A cycle below zero that the start reaches: 0→1, then 1→2 costs −3 and 2→1 costs 1. -/
def loopy : Network := ⟨⟨3, [(0, 1), (1, 2), (2, 1)]⟩, [1, -3, 1]⟩

example : cycleOf (bellmanFord loopy 0) = some [2, 1, 2] := by decide
example : CycleBelowZero loopy 0 [2, 1, 2] := by decide
-- every one of the three rounds lowered a cost
example : (final loopy 0).rounds = 3 := by decide
-- the state the run ends in is legal: the cycle its previous vertices close, 1 and 2, is below
-- zero
set_option maxRecDepth 100000 in
example : Valid (final loopy 0) ∧ WellFormed (final loopy 0) := by decide
-- records that close a cycle costing 2 break the third piece
example : ¬ RecordedCyclesBelowZero
    { start ⟨⟨3, [(0, 1), (1, 2), (2, 1)]⟩, [1, 1, 1]⟩ 0 with
      prev := fun v => if v = 1 then some 2 else if v = 2 then some 1 else none } := by decide

/-- One vertex and an arrow to itself costing −1: the cycle is that arrow. -/
def selfLoop : Network := ⟨⟨1, [(0, 0)]⟩, [-1]⟩

example : cycleOf (bellmanFord selfLoop 0) = some [0, 0] := by decide
example : CycleBelowZero selfLoop 0 [0, 0] := by decide

/-- Two arrows from 1 back to 0, costing 5 and −3: the cycle is below zero by the cheaper one. -/
def twoWays : Network := ⟨⟨2, [(0, 1), (1, 0), (1, 0)]⟩, [1, 5, -3]⟩

example : cycleOf (bellmanFord twoWays 0) = some [0, 1, 0] := by decide
example : CycleBelowZero twoWays 0 [0, 1, 0] := by decide

/-- A cycle below zero that the start does not reach: 2→3 costs 1 and 3→2 costs −2. -/
def faraway : Network := ⟨⟨4, [(0, 1), (2, 3), (3, 2)]⟩, [-4, 1, -2]⟩

-- no cycle reported; the vertices the start reaches get their costs, the others none
example : (List.range 4).map (costOf (bellmanFord faraway 0)) = [some (some 0), some (some (-4)),
    some none, some none] := by decide
-- the cycle is there, below zero, but the start does not reach it
example : CycleBelowZero faraway 2 [2, 3, 2] := ⟨2, [1, 2], by decide, rfl, by decide, .refl⟩
example : ¬ faraway.g.Reaches 0 2 := by decide

/-- A cycle below zero that only the last round shows: 0→1→2→3 costs nothing, 3→1 costs −1. -/
def late : Network := ⟨⟨4, [(0, 1), (1, 2), (2, 3), (3, 1)]⟩, [0, 0, 0, -1]⟩

example : cycleOf (bellmanFord late 0) = some [3, 1, 2, 3] := by decide
example : CycleBelowZero late 0 [3, 1, 2, 3] := ⟨3, [3, 1, 2], by decide, rfl, by decide, by decide⟩

-- a state whose cost is no path's breaks the box's invariant
example : ¬ (Valid { start probe 0 with cost := fun _ => some 0 } ∧
    WellFormed { start probe 0 with cost := fun _ => some 0 }) := by decide

/-- Costs read as they are now: 0→1 costs 4, 0→2 costs 2, 2→1 costs −3, 1→3 costs 1, 2→3 costs 5.
A round that read only the last round's costs would leave vertex 1 at 4 and vertex 3 without a
cost after the first round. -/
def inPlace : Network := ⟨⟨4, [(0, 1), (0, 2), (2, 1), (1, 3), (2, 3)]⟩, [4, 2, -3, 1, 5]⟩

-- the first round lowers vertex 1 to −1 through 2, which it reached earlier in the same round
example : (List.range 4).map (round inPlace (start inPlace 0)).cost =
    [some 0, some (-1), some 2, some 5] := by decide
-- the second round carries that on to vertex 3
example : (List.range 4).map (round inPlace (round inPlace (start inPlace 0))).cost =
    [some 0, some (-1), some 2, some 0] := by decide
-- the third round lowers nothing, and the run stops there
example : (round inPlace (round inPlace (round inPlace (start inPlace 0)))).lowered = none ∧
    (final inPlace 0).rounds = 3 := by decide
example : (List.range 4).map (costOf (bellmanFord inPlace 0)) = [some (some 0), some (some (-1)),
    some (some 2), some (some 0)] := by decide
-- after one round vertex 1's cost is a path of two arrows, and the state is legal
set_option maxRecDepth 100000 in
example : Valid (round inPlace (start inPlace 0)) ∧ WellFormed (round inPlace (start inPlace 0)) :=
  by decide
-- the same costs after only one arrow tried break the second piece: vertex 1's path has two
example : ¬ PathWithinTries { round inPlace (start inPlace 0) with tried := 1 } := by
  decide

end AlgoDesignTests.BellmanFord

namespace AlgoDesignTests.DagOrder
open AlgoDesign.Paths AlgoDesign.Paths.DagOrder

/-- A negative arrow: the way round through 2 beats the direct arrow to 1. -/
def neg : Network := ⟨⟨4, [(0, 1), (0, 2), (2, 1), (1, 3)]⟩, [5, 2, -4, 1]⟩

-- Kahn's order, and the walk legal at the start and after every step
example : AlgoDesign.Graphs.TopoOrder.kahn neg.g = .ok [0, 2, 1, 3] := by decide
example : Valid neg 0 (start neg 0 [0, 2, 1, 3]) := by decide
example : Valid neg 0 (step neg (start neg 0 [0, 2, 1, 3])) := by decide
example : Valid neg 0 (step neg (step neg (start neg 0 [0, 2, 1, 3]))) := by decide
example : Valid neg 0 (final neg 0 [0, 2, 1, 3]) := by decide
-- every cost is the cheapest, checked against every path
example : ∀ v < 4, Network.Cheapest neg 0 v ((final neg 0 [0, 2, 1, 3]).known v) := by decide
-- an order that is not topological breaks `InOrder`
example : ¬ InOrder neg (start neg 0 [0, 1, 2, 3]) := by decide
-- from 2, vertex 0 cannot be reached
example : ((dagPaths neg 2).map fun a => (List.range 4).map a.cost) =
    .ok [none, some (-4), some 0, some (-3)] := by decide
-- two arrows from 0 to 1: the cheaper one, and the previous vertex is 0
example : ((dagPaths ⟨⟨2, [(0, 1), (0, 1)]⟩, [5, 3]⟩ 0).map fun a =>
    ((List.range 2).map a.cost, a.prev 1)) = .ok ([some 0, some 3], some 0) := by decide
-- a loop is a cycle: the stuck set
example : ((dagPaths ⟨⟨2, [(0, 1), (1, 1)]⟩, [1, 1]⟩ 0).map fun a => a.cost 1) = .error [1] := by
  decide
-- a cycle of two: the stuck set, the vertices after it included
example : ((dagPaths ⟨⟨3, [(0, 1), (1, 0), (1, 2)]⟩, [1, 1, 1]⟩ 0).map fun a => a.cost 2) =
    .error [0, 1, 2] := by decide

end AlgoDesignTests.DagOrder

namespace AlgoDesignTests.Knapsack
open AlgoDesign.Paths AlgoDesign.Paths.Knapsack

/-- The cargo box: greedy by value per weight takes item 0 and nothing else fits. -/
def cargo : List Item := [⟨6, 30⟩, ⟨5, 20⟩, ⟨5, 20⟩]

example : knapsack cargo 10 = ⟨40, [1, 2]⟩ := by decide
example : IsBest cargo 10 40 ∧ ¬ IsBest cargo 10 30 := by decide
-- the walk legal at the start and after every step
example : Valid cargo 10 (start cargo 10) := by decide
example : Valid cargo 10 (step cargo 10 (start cargo 10)) := by decide
example : Valid cargo 10 (final cargo 10) := by decide
-- at most two moves tried from each vertex before the last layer
example : (final cargo 10).tried ≤ 2 * (3 * 11) := by decide
-- a tie between taking and skipping: the item is taken
example : knapsack [⟨2, 5⟩, ⟨2, 5⟩] 2 = ⟨5, [1]⟩ := by decide
-- two weights tie in the last layer: the lighter one
example : knapsack [⟨1, 3⟩, ⟨2, 3⟩] 2 = ⟨3, [0]⟩ := by decide
-- an item weighing nothing gives two moves between the same two vertices; taking it wins
example : knapsack [⟨0, 4⟩, ⟨3, 2⟩] 2 = ⟨4, [0]⟩ := by decide
-- an item worth less than nothing is left out
example : knapsack [⟨1, -3⟩] 5 = ⟨0, []⟩ := by decide
-- no items, or no room
example : knapsack [] 5 = ⟨0, []⟩ := by decide
example : knapsack cargo 0 = ⟨0, []⟩ := by decide
-- a vertex no path reaches holds `none`
example : (final cargo 10).best 3 4 = none ∧ (final cargo 10).best 3 5 = some 20 := by decide

end AlgoDesignTests.Knapsack


namespace AlgoDesignTests.Kruskal
open AlgoDesign.Graphs AlgoDesign.Paths AlgoDesign.Paths.Kruskal

/-! ### Equal costs: the tie rule picks one of the cheapest -/

/-- A triangle whose three links all cost 1: any two of them are a cheapest spanning tree. -/
def triangle : LinkNetwork := ⟨⟨3, [(0, 1), (1, 2), (0, 2)]⟩, [1, 1, 1]⟩

-- equal costs go by id, so the walk keeps links 0 and 1; links 1 and 2 are as cheap
example : order triangle = [0, 1, 2] ∧ kruskal triangle = [0, 1] ∧
    triangle.CheapestForest [0, 1] ∧ triangle.CheapestForest [1, 2] := by
  decide

-- one group is left after two links, so the walk stops before trying link 2
example : (runSteps (step triangle) 3 (start triangle (order triangle))).tried = [0, 1] := by
  decide

-- every state the walk passes through is legal and well formed
example : (Valid (start triangle (order triangle)) ∧
      WellFormed (start triangle (order triangle))) ∧
    (Valid (step triangle (start triangle (order triangle))) ∧
      WellFormed (step triangle (start triangle (order triangle)))) ∧
    (Valid (runSteps (step triangle) 3 (start triangle (order triangle))) ∧
      WellFormed (runSteps (step triangle) 3 (start triangle (order triangle)))) := by
  decide

/-- The triangle with link 2 made dearer. -/
def dearTriangle : LinkNetwork := ⟨⟨3, [(0, 1), (1, 2), (0, 2)]⟩, [1, 1, 4]⟩

/-- The dear triangle's walk, had it kept link 2 first. -/
def keptDear : State := ⟨dearTriangle, [0, 1], [2], [2], (UnionFind.init 3).unions [(0, 2)]⟩

-- a state that has kept link 2 is part of no cheapest spanning tree: box invariant 1 fails alone
example : ¬ PartOfCheapest keptDear ∧ GroupsAreKeptJoins keptDear ∧ UnionFindReady keptDear ∧
    KeptClosesNoCycle keptDear ∧ RestCheapestFirst keptDear ∧ PassedAreJoined keptDear := by
  decide

-- a union-find whose groups are not the kept links' breaks box invariant 2
example : ¬ GroupsAreKeptJoins ⟨dearTriangle, [1, 2], [0], [0], UnionFind.init 3⟩ := by decide

/-! ### A graph in two pieces: a spanning forest -/

/-- Two pieces, `{0, 1}` and `{2, 3}`. -/
def twoPieces : LinkNetwork := ⟨⟨4, [(2, 3), (0, 1)]⟩, [5, 2]⟩

example : kruskal twoPieces = [1, 0] ∧ twoPieces.CheapestForest [1, 0] ∧
    ¬ twoPieces.Joins (kruskal twoPieces) 0 2 := by
  decide

/-! ### A loop and a doubled link -/

/-- A loop at 0 that costs below zero, and two links between 0 and 1. -/
def loopAndDouble : LinkNetwork := ⟨⟨2, [(0, 0), (0, 1), (0, 1)]⟩, [-1, 4, 3]⟩

-- the loop comes first and is skipped; of the two doubled links the cheaper is kept
example : order loopAndDouble = [0, 2, 1] ∧ kruskal loopAndDouble = [2] ∧
    loopAndDouble.CheapestForest [2] ∧ ¬ loopAndDouble.ClosesNoCycle [0] ∧
    ¬ loopAndDouble.ClosesNoCycle [1, 2] := by
  decide

/-! ### Everyone digs to the nearest neighbor: islands -/

/-- Two close pairs, `{0, 1}` and `{2, 3}`, far apart. -/
def islands : LinkNetwork := ⟨⟨4, [(0, 1), (2, 3), (1, 2), (0, 3)]⟩, [1, 1, 5, 6]⟩

-- each vertex's cheapest link is link 0 or link 1; together they leave two islands, while the walk
-- also keeps the cheapest link between them
example : ¬ islands.JoinsWhatGraphJoins [0, 1] ∧ kruskal islands = [0, 1, 2] ∧
    islands.JoinsWhatGraphJoins (kruskal islands) := by
  decide

end AlgoDesignTests.Kruskal

namespace AlgoDesignTests.PathsWorkbench
open AlgoDesign.Paths.Workbench

/-! ### The design project's contract, piece by piece on a three-place town

Each piece the Python judge checks (`is_real_trip` and the rest), decided on one small town with
a socket and the same town without: it holds of the right answer and fails on a broken one. -/

/-- Three places. The street from 0 to 1 takes 2 minutes and one level, the street from 1 to 2
takes 3 minutes and one level, and the street from 2 back to 0 runs downhill and gives a level
back. The battery holds one level, and the socket at 1 adds it in 5 minutes. -/
def town : Town := ⟨3, [⟨0, 1, 2, 1⟩, ⟨1, 2, 3, 1⟩, ⟨2, 0, 1, -1⟩], [1], 1, 5⟩

/-- The same town with no socket. -/
def dark : Town := { town with sockets := [] }

example : town.WellFormed ∧ dark.WellFormed := by decide

-- a trip that needs a charge: ride to 1, charge, ride to 2, in 10 minutes, and none is quicker
example : RealTripOn town 0 2 (some [.ride 1, .charge, .ride 2]) ∧
    NoneQuickerOn town 0 2 (some [.ride 1, .charge, .ride 2]) ∧
    SaysNoneOn town 0 2 (some [.ride 1, .charge, .ride 2]) ∧
    town.tripMinutes 0 [.ride 1, .charge, .ride 2] = 10 := by
  decide
-- without the charge the battery runs flat; a charge where there is no socket is no trip
example : ¬ RealTripOn town 0 2 (some [.ride 1, .ride 2]) ∧
    ¬ RealTripOn town 0 2 (some [.charge, .ride 1, .ride 2]) ∧ ¬ SaysNoneOn town 0 2 none := by
  decide
-- downhill at full stays full: back from 2 to 0 and on to 1 at level 0, never flat
example : RealTripOn town 2 1 (some [.ride 0, .ride 1]) ∧
    NoneQuickerOn town 2 1 (some [.ride 0, .ride 1]) := by
  decide
-- a slower trip is real and not the quickest
example : RealTripOn town 0 2 (some [.ride 1, .charge, .ride 2, .ride 0, .ride 1, .charge, .ride 2])
    ∧ ¬ NoneQuickerOn town 0 2
      (some [.ride 1, .charge, .ride 2, .ride 0, .ride 1, .charge, .ride 2]) := by
  decide
-- no socket: no trip from 0 to 2 never runs flat, so the answer is none
example : SaysNoneOn dark 0 2 none ∧ ¬ SaysNoneOn dark 0 2 (some [.ride 1, .ride 2]) ∧
    ¬ RealTripOn dark 0 2 (some [.ride 1, .charge, .ride 2]) := by
  decide

end AlgoDesignTests.PathsWorkbench
