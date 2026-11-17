import AlgoDesign.Flows.MaxFlow.EdmondsKarp
import AlgoDesign.Flows.MaxFlow.Dinic
import AlgoDesign.Flows.MaxFlow.CapacityScaling
import AlgoDesign.Flows.MinCostFlow
import AlgoDesign.Flows.Assignment
import AlgoDesign.Flows.Matching
import AlgoDesign.Flows.PushRelabel
import AlgoDesign.Flows.Workbench.Decide

/-! Regression checks for the Flows chapter: Edmonds–Karp's, Dinic's and capacity scaling's rounds
on small networks, path by path; the cheapest flow, the assignment, the matching, push-relabel's
checks and the workbench's requirements on the chapter's examples. Run with
`lake env lean -DwarningAsError=true AlgoDesignTests/Flows.lean`. -/

namespace AlgoDesignTests.Flows
open AlgoDesign.Flows ResidualArrow

/-- The 1-and-1000 network: s = 0, a = 1, b = 2, t = 3; a → b carries 1. -/
def nA : Network :=
  ⟨⟨4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]⟩, [1000, 1000, 1, 1000, 1000], 0, 3⟩

-- every rule reaches 2000; Edmonds–Karp in two rounds, Dinic in one
example : value nA (edmondsKarp.run nA).2 = 2000 := by decide
example : value nA (dinic.run nA).2 = 2000 := by decide
example : value nA (capacityScaling.run nA).2 = 2000 := by decide
example : (edmondsKarp.run nA).1 =
    [[⟨[along 0, along 3], 1000⟩], [⟨[along 1, along 4], 1000⟩]] := by decide
example : (dinic.run nA).1 = [[⟨[along 0, along 3], 1000⟩, ⟨[along 1, along 4], 1000⟩]] := by
  decide
-- capacity scaling starts from 512, the largest power of two not above 1000
example : topPowerOfTwo (maxCapacity nA) = 512 := by decide
example : (capacityScaling.run nA).1 =
    [[⟨[along 0, along 3], 1000⟩], [⟨[along 1, along 4], 1000⟩]] := by decide

/-- One phase of Dinic's rule adds two paths of two arrows, the next two of three. -/
def nB : Network :=
  ⟨⟨5, [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (1, 4), (2, 4)]⟩, [5, 5, 3, 4, 6, 2, 2], 0, 4⟩

example : (dinic.run nB).1 =
    [[⟨[along 0, along 5], 2⟩, ⟨[along 1, along 6], 2⟩],
      [⟨[along 0, along 2, along 4], 3⟩, ⟨[along 1, along 3, along 4], 3⟩]] := by decide
example : (edmondsKarp.run nB).1 =
    [[⟨[along 0, along 5], 2⟩], [⟨[along 1, along 6], 2⟩], [⟨[along 0, along 2, along 4], 3⟩],
      [⟨[along 1, along 3, along 4], 3⟩]] := by decide
-- the sweep steps of the first phase, the last one (the source a dead end) included
example : dinicSweepSteps nB (Flow.zero nB) = 19 := by decide
-- in the 1-and-1000 network: 4 moves and 4 pointer advances, 2 paths, 2 more advances after
-- the restarts, and the source found a dead end
example : dinicSweepSteps nA (Flow.zero nA) = 13 := by decide

/-- The sink cannot be reached. -/
def nC : Network := ⟨⟨3, [(0, 1), (2, 1)]⟩, [4, 4], 0, 2⟩

example : (edmondsKarp.round nC () (Flow.zero nC)).2 = [] := by decide
example : (dinic.round nC () (Flow.zero nC)).2 = [] := by decide
example : (capacityScaling.round nC (4 : ℕ) (Flow.zero nC)).2 = [] := by decide
example : dinicSweepSteps nC (Flow.zero nC) = 0 := by decide

/-- Parallel and antiparallel arrows. -/
def nD : Network :=
  ⟨⟨3, [(0, 1), (0, 1), (1, 0), (1, 2), (2, 1), (1, 2)]⟩, [2, 3, 7, 4, 1, 5], 0, 2⟩

example : value nD (edmondsKarp.run nD).2 = 5 ∧ value nD (dinic.run nD).2 = 5 ∧
    value nD (capacityScaling.run nD).2 = 5 := by decide
example : (dinic.run nD).1 =
    [[⟨[along 0, along 3], 2⟩, ⟨[along 1, along 3], 2⟩, ⟨[along 1, along 5], 1⟩]] := by decide
example : (capacityScaling.run nD).1 =
    [[⟨[along 0, along 3], 2⟩], [⟨[along 1, along 3], 2⟩], [⟨[along 1, along 5], 1⟩]] := by
  decide

/-- A later path takes back what an earlier one sent along c → b. -/
def nE : Network :=
  ⟨⟨6, [(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (3, 5), (4, 5)]⟩, [1, 1, 1, 1, 1, 1, 1], 0, 5⟩

example : (edmondsKarp.run nE).1 =
    [[⟨[along 0, along 2, along 5], 1⟩], [⟨[along 1, along 4, back 2, along 3, along 6], 1⟩]] := by
  decide
example : (dinic.run nE).1 =
    [[⟨[along 0, along 2, along 5], 1⟩], [⟨[along 1, along 4, back 2, along 3, along 6], 1⟩]] := by
  decide
example : value nE (capacityScaling.run nE).2 = 2 := by decide

end AlgoDesignTests.Flows

namespace AlgoDesignTests.Flows.MinCostFlow
open AlgoDesign.Flows AlgoDesign.Flows.MinCostFlow ResidualArrow

/-- The chapter's vehicles: source 0; flats Juan 1, Tomás 2, Anita 3, Daniel 4; van 5, car 6;
sink 7. Arrows: source to each flat (0-3); each flat to the van, then the car (4-11); van to the
sink (12), car to the sink (13). -/
def vehicles (amount : ℕ) : Problem :=
  ⟨⟨⟨8, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (2, 5), (2, 6), (3, 5), (3, 6),
      (4, 5), (4, 6), (5, 7), (6, 7)]⟩, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1], 0, 7⟩,
    [0, 0, 0, 0, 1, 100, 1, 100, 3, 2, 10, 5, 0, 0], amount⟩

-- Juan to the van, Tomás to the van, Anita to the car, then Daniel to the car with Anita sent
-- back to the van
example : steps (vehicles 4) =
    [⟨[along 0, along 4, along 12], 1⟩, ⟨[along 1, along 6, along 12], 1⟩,
      ⟨[along 2, along 9, along 13], 1⟩,
      ⟨[along 3, along 11, back 9, along 8, along 12], 1⟩] := by decide
example : (vehicles 4).flowCost (minCostFlow (vehicles 4)).flow = 10 := by decide
-- after the third step: Juan 1, Tomás 1, Anita 0, Daniel 0, van 2, car 2, sink 2
example : heightsAfter (vehicles 4) 3 = [0, 1, 1, 0, 0, 2, 2, 2] := by decide
example : heightsAfter (vehicles 4) 4 = [0, 5, 5, 3, 0, 6, 5, 6] := by decide
example : settledEach (vehicles 4) = [7, 7, 5, 8] := by decide

-- a shortfall: 5 requested, 4 fit; the fifth search misses the sink, the cut proves 4
example : (steps (vehicles 5)).length = 4 ∧
    value (vehicles 5).net (minCostFlow (vehicles 5)).flow = 4 := by decide
-- every arrow out of the source is full, so the side is the source alone
example : (minCostFlow (vehicles 5)).side = [0] := by decide
-- the fifth search settles only the source
example : settledEach (vehicles 5) = [7, 7, 5, 8, 1] := by decide
example : cutCapacity (vehicles 5).net (minCostFlow (vehicles 5)).side = 4 := by decide

/-- A tie: s = 0, a = 1, b = 2, t = 3, every arrow costing 1; a and b both offer t at 2, and two
parallel arrows a → t (2 and 3) cost the same. a is settled first and labels t first; of the two
parallel arrows, the first in adjacency order is recorded. -/
def tie : Problem :=
  ⟨⟨⟨4, [(0, 1), (0, 2), (1, 3), (1, 3), (2, 3)]⟩, [1, 1, 1, 1, 1], 0, 3⟩, [1, 1, 1, 1, 1], 2⟩

example : steps tie = [⟨[along 0, along 2], 1⟩, ⟨[along 1, along 4], 1⟩] := by decide
example : heightsAfter tie 1 = [0, 1, 1, 2] := by decide

end AlgoDesignTests.Flows.MinCostFlow

namespace AlgoDesignTests.Flows.AssignmentChecks
open AlgoDesign.Flows

/-- The chapter's 3×3 table: P1 (1, 3, 6), P2 (2, 8, 9), P3 (5, 4, 9). -/
def table3 : Assignment.Problem := ⟨[[1, 3, 6], [2, 8, 9], [5, 4, 9]]⟩

-- least cost 12: P1–Z, P2–X, P3–Y; the labels fit every pair and are exact on the chosen ones
example : (Assignment.assign table3).obj = [2, 0, 1] := by decide
example : Assignment.assignmentCost table3 (Assignment.assign table3).obj = 12 := by decide
example : (Assignment.assign table3).personLabel = [6, 7, 7] ∧
    (Assignment.assign table3).objectLabel = [-5, -3, 0] := by decide
example : ∀ i < 3, ∀ j < 3, (Assignment.assign table3).personLabel.at i +
    (Assignment.assign table3).objectLabel.at j ≤ table3.costAt i j := by decide
example : ∀ i < 3, (Assignment.assign table3).personLabel.at i +
    (Assignment.assign table3).objectLabel.at ((Assignment.assign table3).obj.getD i 0) =
      table3.costAt i ((Assignment.assign table3).obj.getD i 0) := by decide
-- the searches, person by person: objects settled, the path
example : (Assignment.trace table3).map (·.settled) = [[0], [0, 1], [1, 0, 2]] := by decide
example : (Assignment.trace table3).map (·.path) = [[0], [0, 1], [1, 2]] := by decide

/-- The rent story, cost = 900 − value; rows Juan, Anita, Daniel, Tomás; rooms 1–4. -/
def rent : Assignment.Problem :=
  ⟨[[550, 400, 700, 350], [700, 650, 400, 250], [900, 550, 300, 250],
    [650, 700, 400, 250]].map (·.map (900 - ·))⟩

-- Juan room 3, Anita room 4, Daniel room 1, Tomás room 2: total value 2,550
example : (Assignment.assign rent).obj = [2, 3, 0, 1] := by decide
example : Assignment.assignmentCost rent (Assignment.assign rent).obj = 4 * 900 - 2550 := by
  decide
-- room labels −450, −400, −150, 0: the printed prices 700, 650, 400, 250 less 250 each
example : (Assignment.assign rent).personLabel = [350, 650, 450, 600] ∧
    (Assignment.assign rent).objectLabel = [-450, -400, -150, 0] := by decide
example : ∀ i < 4, ∀ j < 4, (Assignment.assign rent).personLabel.at i +
    (Assignment.assign rent).objectLabel.at j ≤ rent.costAt i j := by decide

/-- A tie the free-object-first rule decides: person 1 sees object 0 (held) and object 1 (free)
at the same changed cost 0. -/
def tie : Assignment.Problem := ⟨[[1, 1], [0, 0]]⟩

-- person 1 picks the free object 1 at once; the lowest index (0) would have settled 0 first
example : (Assignment.trace tie).map (·.settled) = [[0], [1]] := by decide
example : (Assignment.assign tie).obj = [0, 1] := by decide

end AlgoDesignTests.Flows.AssignmentChecks

namespace AlgoDesignTests.Flows.Matching
open AlgoDesign.Flows AlgoDesign.Flows.Matching

/-- The chapter's rooms: Anita 0 accepts rooms 1 and 2, Daniel 1 room 1, Tomás 2 rooms 1 and 2,
Juan 3 rooms 3 and 4; room r is object r - 1. -/
def rooms : Problem := ⟨4, 4, [(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 2), (3, 3)]⟩

-- three pairs; the cover Juan, room 1, room 2; Anita, Daniel and Tomás accept only rooms 1 and 2
example : maxMatching rooms =
    ⟨[(0, 0), (2, 1), (3, 2)], [3], [0, 1], some ⟨[0, 1, 2], [0, 1]⟩⟩ := by decide
-- max flow added three paths, at most one per person
example : (ops.rounds rooms).flatten.length = 3 := by decide
-- everyone matched: no blocked group
example : (maxMatching ⟨2, 3, [(0, 0), (0, 1), (1, 1), (1, 2)]⟩).blocked = none := by decide
-- the network's arrows: the source to the people, the pairs, the objects to the sink
example : (Problem.network ⟨2, 2, [(1, 0), (0, 1)]⟩).g.arrows =
    [(0, 1), (0, 2), (2, 3), (1, 4), (3, 5), (4, 5)] := by decide

end AlgoDesignTests.Flows.Matching

namespace AlgoDesignTests.Flows.PushRelabel
open AlgoDesign.Flows AlgoDesign.Flows.PushRelabel

/-- The 1-and-1000 network; a claimed answer passes the checks only with a cut of its value. -/
def nA : Network :=
  ⟨⟨4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]⟩, [1000, 1000, 1, 1000, 1000], 0, 3⟩
example : PassesChecks nA ⟨[1000, 1000, 0, 1000, 1000], [0]⟩ := by decide
/-- A path of three arrows; its narrowest arrow, 1, is the answer. -/
def nPR : Network := ⟨⟨4, [(0, 1), (1, 2), (2, 3)]⟩, [5, 2, 1], 0, 3⟩
example : PassesChecks nPR ⟨[1, 1, 1], [0, 1, 2]⟩ := by decide
example : ¬ PassesChecks nA ⟨[1000, 1000, 0, 1000, 1000], [0, 1]⟩ := by decide

end AlgoDesignTests.Flows.PushRelabel

namespace AlgoDesignTests.Flows.WorkbenchChecks
open AlgoDesign.Flows AlgoDesign.Flows.Workbench

/-- Edmonds–Karp's rule for one round, then nothing: it breaks the promise. -/
def stopsEarly : PathRule where
  Memory := Bool
  start _ := false
  round N m f := if m then (true, []) else (true, (edmondsKarp.round N () f).2)

example : ReturnsAFlowOn nA (edmondsKarp.maxFlow nA) ∧
    CutMatchesFlowOn nA (edmondsKarp.maxFlow nA) ∧
    AddsAlongAugmentingPathsOn nA (edmondsKarp.run nA).1 ∧
    RoundsAtMostNOn nA (edmondsKarp.run nA).1 ∧
    AugmentationsAtMostNMOn nA (edmondsKarp.run nA).1 := by decide
example : ReturnsAFlowOn nA (dinic.maxFlow nA) ∧ CutMatchesFlowOn nA (dinic.maxFlow nA) ∧
    AddsAlongAugmentingPathsOn nA (dinic.run nA).1 ∧ RoundsAtMostNOn nA (dinic.run nA).1 := by
  decide
example : ReturnsAFlowOn nA (capacityScaling.maxFlow nA) ∧
    CutMatchesFlowOn nA (capacityScaling.maxFlow nA) ∧
    AddsAlongAugmentingPathsOn nA (capacityScaling.run nA).1 := by decide
-- the early stopper leaves a flow, but no cut of its amount
example : ReturnsAFlowOn nA (stopsEarly.maxFlow nA) ∧
    ¬ CutMatchesFlowOn nA (stopsEarly.maxFlow nA) ∧
    AddsAlongAugmentingPathsOn nA (stopsEarly.run nA).1 := by decide
example : ¬ AddsAlongAugmentingPathsOn nA [[⟨[.along 0, .along 2, .along 4], 2⟩]] := by decide
example : ¬ BoundOn (fun _ _ => 1) nA (edmondsKarp.run nA).1 := by decide

/-- Three vertices, arrows `(0,1)`, `(1,2)`, `(0,2)` with capacities 5, 5 and 4. -/
def n3 : Network := ⟨⟨3, [(0, 1), (1, 2), (0, 2)]⟩, [5, 5, 4], 0, 2⟩

/-- One added "path" of amount 1 that repeats arrows: it rebuilds the largest flow in one go. -/
def fake : Augmentation :=
  ⟨List.replicate 5 (.along 0) ++ List.replicate 5 (.along 1) ++ List.replicate 4 (.along 2), 1⟩

-- it rebuilds a flow of amount 9 in one added path
example : applyAll (Flow.zero n3) [fake] = [5, 5, 4] ∧ IsFlow n3 [5, 5, 4] ∧
    value n3 [5, 5, 4] = 9 := by decide
-- but it is no augmenting path
example : ¬ AddsAlongAugmentingPathsOn n3 [[fake]] := by decide
-- so no max-flow `Ops` can report it as its rounds
example : ¬ ∃ o : AlgoDesign.Flows.Ops, o.rounds n3 = [[fake]] := by
  rintro ⟨o, ho⟩
  have h := o.augments n3 (by decide)
  rw [ho] at h
  exact (by decide : ¬ AddsAlongAugmentingPathsOn n3 [[fake]]) h

end AlgoDesignTests.Flows.WorkbenchChecks
